(**************************************************************************)
(*                        Lem                                             *)
(*                                                                        *)
(*  Lean 4 backend                                                        *)
(*                                                                        *)
(*  Translates Lem definitions into Lean 4 syntax. Uses the shared        *)
(*  Backend_common infrastructure for identifier resolution and target    *)
(*  representation handling.                                               *)
(*                                                                        *)
(*  Key design decisions:                                                  *)
(*  - Block formatting is disabled (Lean 4 is whitespace-sensitive)       *)
(*  - UTF-8 output uses Meta_utf8 to avoid double-encoding (×, →, etc.)  *)
(*  - Constructors are exported via 'export TypeName (Ctor1 Ctor2 ...)'   *)
(*    after each inductive definition                                     *)
(*  - Class methods are brought into scope via 'open ClassName'           *)
(*  - Mutual inductives with heterogeneous parameter counts use indexed   *)
(*    types (parameters become indices with Type 1 universe)              *)
(*  - Target-specific class methods ({hol}, {coq}, etc.) are filtered     *)
(*    from both class and instance definitions                            *)
(*  - BEq is derived for types without function-typed constructor args    *)
(*  - Inhabited instances are DERIVED per constructor (bounded with      *)
(*    [Inhabited tv] where a type parameter is consumed); no DAEMON      *)
(*    fallback — underivable types get NO instance (fail-closed,         *)
(*    arc-8 S1)                                                          *)
(*  - EVERY failure site (failwith-mapped constants, L_undefined         *)
(*    literals) emits axiom-free failwithI (mirroring OCaml's raise;     *)
(*    audit fix, arc-8); tyvar-typed sites                               *)
(*    thread [Inhabited tv] binders onto the enclosing def's signature   *)
(*    (monotone over the call graph); legacy failwith and the            *)
(*    sorry-emission paths are gone (fail-closed, arc-8 S2)              *)
(*                                                                        *)
(**************************************************************************)

open Backend_common
open Output
open Typed_ast
open Typed_ast_syntax
open Target
open Types

let r = Ulib.Text.of_latin1

let print_and_fail l s =
  raise (Reporting_basic.err_general true l s)
;;

let lean_string_escape s =
  let buf = Buffer.create (String.length s) in
  String.iter (fun c -> match c with
    | '\\' -> Buffer.add_string buf "\\\\"
    | '"' -> Buffer.add_string buf "\\\""
    | '\n' -> Buffer.add_string buf "\\n"
    | '\t' -> Buffer.add_string buf "\\t"
    | '\000' -> Buffer.add_string buf "\\x00"
    | '\r' -> Buffer.add_string buf "\\r"
    | c -> Buffer.add_char buf c
  ) s;
  Buffer.contents buf
;;

(* Lean 4 syntax keywords that cannot be used as bare identifiers.
   When these appear as local variable names, they're escaped with «» guillemets. *)
let lean_syntax_keywords = [
  "def"; "class"; "instance"; "where"; "let"; "match"; "if"; "then"; "else";
  "do"; "return"; "import"; "open"; "namespace"; "structure"; "inductive";
  "theorem"; "example"; "variable"; "section"; "end"; "mutual"; "partial";
  "noncomputable"; "unsafe"; "private"; "protected"; "abbrev"; "fun"; "forall";
  "by"; "have"; "show"; "with"; "at"; "in"; "for"; "macro"; "syntax";
  "deriving"; "extends"; "set_option"; "attribute"; "meta"; "catch";
  "break"; "continue"; "try"; "finally"; "unless"; "suffices";
  "nomatch"; "nofun"; "coinductive"; "axiom"; "opaque"; "universe";
  "scoped"; "local"; "public"; "nonrec"; "omit";
  "notation"; "prefix"; "postfix"; "infixl"; "infixr"; "infix";
  "none"; "some"; "true"; "false"; "default";
  "this"; "rfl"; "calc"; "decide"; "sorry";
  "pure"; "get"; "set"; "throw"; "panic"; "admit"; "trivial"
]
(* Arc-8 S1 (derived Inhabited instances, replacing the DAEMON fallback):
   process-global census of the Inhabited instances this backend has
   emitted, keyed by type Path (modules are processed in dependency order
   within one lem invocation, so earlier types' instances are visible to
   later derivations — "cross-type dependencies resolve through the
   emitted instances themselves", design note
   lem-lean doc/notes/2026-08-20_arc8-inhabited-threading-design.md rule 4).
   Each emitted instance is recorded as the list of type-parameter
   POSITIONS that carry an [Inhabited _] bound; [] = unconditional.
   Inh_none records a type whose derivation FAILED: fail-closed, NO
   instance and NO fallback of any kind was emitted — any backend-visible
   Inhabited demand on such a type is a generation-time error (see
   inhabited_demand_check). *)
type inh_status =
  | Inh_instances of int list list
  | Inh_none
(* Arc-8 S1: per-type tier-2 derivation PLAN, computed by
   lean_inhabited_prepass (in declaration order) and only RENDERED at
   emission time. Needed because the main emission walks definitions
   with fold_right — side effects run last-to-first (see the
   lean_reader_prepass / St.mutual_records precedent) — so census
   population cannot be interleaved with emission. *)
type inh_plan =
  | Plan_variant of (int * string list) list
      (* usable constructor indices (into the Te_variant ctor list) with
         their [Inhabited tv] bound sets, in emission order: first at
         default priority, rest (priority := low) *)
  | Plan_record of string list  (* all fields derivable; bound set *)
  | Plan_none                   (* fail-closed: NO instance, no fallback *)

(* ===== Arc-14 S2 B1: the backend analysis-state module (be:G3) =====

   EVERY module-level mutable cell of this backend lives HERE — one
   declaration site, a stated lifetime class and invariant per field.
   (Previously: ~22 refs scattered across 1,100 lines — the "hidden
   global state machine" of the arc-14 backend audit.)

   LIFETIME CLASSES:
     [file]        reset at every lean_defs entry (St.reset_per_file);
                   meaningful only within one output file's emission.
     [invocation]  grows monotonically across the modules of ONE lem
                   invocation (lem processes modules in dependency
                   order, so earlier modules' facts must stay visible
                   to later ones: census, threading, reader lifting,
                   mutual-record accumulation, the reader-param cache).
                   Reset only by St.reset_invocation.
     [render]      save/restore-scoped around a single definition's
                   rendering (Fun.protect at every write site); at its
                   neutral value between definitions.

   REENTRANCY: emission is still effectful (the upstream-inherited
   fold_right skeleton — the effect-free-emission rewrite is the parked
   be:G3/S5 residual, priced L in the arc-14 disposition table), but
   the whole mutable surface is now resettable in one call:
   St.reset_invocation () gives a fresh backend within one process,
   where previously a second invocation inherited unspecified state. *)
module St = struct
  (* [file] Type namespace names that need 'open' in the auxiliary file. *)
  let auxiliary_opens : string list ref = ref []
  (* [file] Current namespace nesting, for qualified open names. *)
  let namespace_stack : string list ref = ref []
  (* [invocation] Record types that ended up in mutual blocks — rendered
     as inductives, not structures. Record construction ({..}) and field
     projection (.field) don't work for these; use constructor syntax and
     pattern matching instead. Accumulates across files so cross-file
     record updates on mutual-block records are detected. *)
  let mutual_records : Path.t list ref = ref []
  (* [file] Import module names — emitted at the top of the file before
     any other content. *)
  let collected_imports : string list ref = ref []
  (* [file] Locally-defined module names of the current file (Module
     definitions): namespaces, not separate files — never imports. *)
  let local_modules : string list ref = ref []
  (* [file] Fully-qualified paths of nested modules needing 'open' at
     file level (Lean's 'open' inside a namespace is scoped, so nested
     module opens are deferred to the enclosing top-level scope). *)
  let deferred_opens : string list ref = ref []
  (* [file] Set by process_file.ml before each lean_defs call — used for
     namespace wrapping. (The S15 interface-hygiene residual: this is a
     pre-call side channel no other backend needs.) *)
  let current_module_name : string ref = ref ""
  (* [invocation] The Inhabited-instance census (see the inh_status
     comment above). *)
  let inhabited_census : (Path.t * (string * inh_status)) list ref = ref []
  (* [invocation] Per-type tier-2 derivation plans (see inh_plan above). *)
  let inhabited_tier2_plans : (Path.t * inh_plan) list ref = ref []
  (* [render] When true, isEqual outputs propositional = instead of BEq
     ==. Set during indreln antecedent processing where Prop is needed
     (function types lack BEq; indreln antecedents live in Prop). *)
  let prop_equality : bool ref = ref false
  (* [file] Deferred abbrev definitions for types with TYR_subst target
     reps — collected during type processing, drained at the end of
     lean_defs after all definitions complete. *)
  let pending_abbrevs : Output.t list ref = ref []
  (* [render] const_descr_ref -> type-parameter names for polymorphic
     indreln: set during antecedent rendering so exp inserts type params
     for self-references in premises. *)
  let indreln_params : (Types.const_descr_ref * string) list ref = ref []
  (* [invocation] Reader lifting (declare {lean} reader val): crefs of
     lifted defs — a def is lifted if it (transitively) uses a reader
     constant or a lifted def. Grows monotonically (dependency order:
     callees registered before callers). *)
  let reader_lifted : Types.Cdset.t ref = ref Types.Cdset.empty
  (* [render] Set while rendering a lifted def so the three def-assembly
     sites emit the reader binder. *)
  let reader_binder : bool ref = ref false
  (* [render] Arc-8 S2: [Inhabited tv] instance-implicit binders for the
     def group being rendered (tyvar names in parameter-declaration
     order, from the threading census failwith_threaded below). *)
  let inhabited_binder : string list ref = ref []
  (* [render] Fuel emission (declare {lean} fuel val f = `sentinel`):
     the sentinel text while rendering a fuel'd def's clause (consumed
     by funcl_aux: rename to worker, add the Nat binder, wrap the body). *)
  let fuel_emit : string option ref = ref None
  (* [render] All fuel'd defs of the block being rendered (one entry for
     a plain fuel'd def; every member for a fuel'd mutual block —
     all-or-none, arc 3 B2). Self- and cross-member calls rewrite to
     '(worker lemFuel)'. *)
  let fuel_workers : (Types.const_descr_ref * string) list ref = ref []
  (* [render] reader_seed (declare {lean} reader_seed val f): while
     rendering a seed-marked def's body, the name of its first argument,
     which OVERRIDES the injected reader parameter name at every
     injection site within (lexically-scoped seeding, not dynamic
     rebinding). *)
  let reader_seed_param : string option ref = ref None
  (* [invocation] Cache of the (cref, param name) reader list computed
     from the whole constant environment (stable within an invocation). *)
  let reader_params_cache : (Types.const_descr_ref * string) list option ref = ref None
  (* [render] True while rendering a definition emitted only as a BLOCK
     COMMENT (a def whose Lean target uses an inline/target_rep — the
     `Comment` def form). Fail-closed generation-time errors (e.g. the
     arc-10 set-comprehension rejection) must not fire for such dead
     text; they emit the historical inert placeholder instead. *)
  let rendering_comment = ref false
  (* [invocation] Threaded-def census: cref -> ([Inhabited]-bound
     type-parameter positions (indices into const_tparams, for call-site
     propagation), bound tyvar names in parameter-declaration order (for
     signature rendering)). Persists across modules (dependency order —
     the reader_lifted precedent). *)
  let failwith_threaded : (int list * string list) Types.Cdmap.t ref = ref Types.Cdmap.empty
  (* [invocation] Synthesized-name counter (generate_fresh_name: x<n>). *)
  let fresh_name_counter = ref 0

  (* Reset the [file]-lifetime fields — called at every lean_defs entry.
     (current_module_name and local_modules are not cleared here: both
     are unconditionally re-SET before use on every file — the module
     name by process_file.ml before the call, local_modules by the
     pre-collection in lean_defs itself.) *)
  let reset_per_file () =
    auxiliary_opens := [];
    namespace_stack := [];
    collected_imports := [];
    pending_abbrevs := [];
    deferred_opens := []

  (* Full reset — the reentrancy hook (be:G3): a second lem invocation in
     one process starts from a fresh backend. Not called on the normal
     one-invocation path. *)
  let reset_invocation () =
    reset_per_file ();
    mutual_records := [];
    local_modules := [];
    current_module_name := "";
    inhabited_census := [];
    inhabited_tier2_plans := [];
    prop_equality := false;
    indreln_params := [];
    reader_lifted := Types.Cdset.empty;
    reader_binder := false;
    inhabited_binder := [];
    fuel_emit := None;
    fuel_workers := [];
    reader_seed_param := None;
    reader_params_cache := None;
    rendering_comment := false;
    failwith_threaded := Types.Cdmap.empty;
    fresh_name_counter := 0

  (* Warning-32 suppression for the reentrancy hook (no in-tree caller
     yet by design). *)
  let _ = reset_invocation
end
let inhabited_census_lookup (p : Path.t) : (string * inh_status) option =
  Option.map snd
    (List.find_opt (fun (q, _) -> Path.compare p q = 0) !St.inhabited_census)
let inhabited_census_debug = (try Sys.getenv "LEM_INH_DEBUG" <> "" with Not_found -> false)
let inhabited_census_add (p : Path.t) (name : string) (st : inh_status) : unit =
  St.inhabited_census := (p, (name, st)) :: !St.inhabited_census;
  if inhabited_census_debug then
    Printf.eprintf "CENSUS add %s (%s) %s\n%!" (Path.to_string p) name
      (match st with Inh_none -> "NONE" | Inh_instances es -> String.concat ";" (List.map (fun e -> Printf.sprintf "[%s]" (String.concat "," (List.map string_of_int e))) es))
(* Known bounded Inhabited instances for library/target types the census
   cannot see (their lem types carry target_reps, so the backend emits no
   instances for them). Positions index the type's arguments:
   - either -> Lean Sum: LemLib's bounded inl/inr pair
     (lean-lib/LemLib.lean:90-91) — left side first (default priority).
   - vector: inhabitation needs an element to replicate.
   Every other head defaults to [[]]: assume an unconditional instance
   exists. This is the same assumption the tier-1 machinery has always
   made when emitting `default` at an applied type; if it is wrong, Lean
   reports a loud 'failed to synthesize' error at the emitted instance —
   visible, never a hidden inconsistency. *)
let lean_builtin_inhabited_entries (p : Path.t) : int list list =
  match Name.to_string (Path.get_name p) with
    | "either" -> [[0]; [1]]
    | "vector" -> [[0]]
    | _ -> [[]]
let inhabited_plan_lookup (p : Path.t) : inh_plan option =
  Option.map snd
    (List.find_opt (fun (q, _) -> Path.compare p q = 0) !St.inhabited_tier2_plans)
let inhabited_plan_add (p : Path.t) (pl : inh_plan) : unit =
  St.inhabited_tier2_plans := (p, pl) :: !St.inhabited_tier2_plans

let lean_reader_is_reader env cref =
  let cd = c_env_lookup Ast.Unknown env.c_env cref in
  Targetset.mem Target_lean cd.reader

let lean_reader_is_seed env cref =
  let cd = c_env_lookup Ast.Unknown env.c_env cref in
  Targetset.mem Target_lean cd.reader_seed

let lean_reader_param_name env cref =
  let cd = c_env_lookup Ast.Unknown env.c_env cref in
  String.concat "" ["_lemReader_"; Name.to_string (Path.get_name cd.const_binding)]

let lean_reader_get_params env =
  match !St.reader_params_cache with
  | Some l -> l
  | None ->
    let l =
      List.filter_map (fun cref ->
          if lean_reader_is_reader env cref
          then Some (cref, lean_reader_param_name env cref)
          else None)
        (c_env_all_consts env.c_env) in
    let l = List.sort (fun (_, a) (_, b) -> String.compare a b) l in
    St.reader_params_cache := Some l; l

(* Pre-pass over one module's defs: grow St.reader_lifted to a fixpoint —
   a def is lifted if it (transitively) uses a reader constant or a lifted
   def. Must run BEFORE emission (defs renders last-to-first). The set
   persists across modules (processed in dependency order). Instance defs
   are never lifted (their methods cannot take extra parameters); an
   instance method that uses a lifted/reader constant fails closed at
   emission. Nested modules lift coarsely (all defs together — sound,
   possibly-unused parameter). *)
let lean_reader_prepass env (ds : def list) =
  if lean_reader_get_params env <> [] then begin
    let target = Target.Target_no_ident Target.Target_lean in
    (* Collect (defined, used) pairs at Val_def granularity, recursing into
       nested modules. Only Val_defs register their DEFINED constants:
       coarse add_def_entities on a whole Module def would also sweep class
       methods, val-spec-only constants, and indreln relation names into
       the lifted set (audit finding, 2026-08-18), and caller-side
       injection would then poison their uses program-wide. Instances are
       skipped (fail-closed at emission); Class/Val_spec/Indreln/etc.
       cannot be lifted — a reader use inside an indreln rule or lemma is
       unsupported and fails visibly at the Lean build. *)
    let rec def_infos acc (((d_aux, _), _, _) as d : def) =
      match d_aux with
      | Instance _ -> acc
      | Module (_, _, _, _, _, inner_ds, _) -> List.fold_left def_infos acc inner_ds
      | Val_def _ ->
        let defined = (add_def_entities target true empty_used_entities d).used_consts_set in
        (* reader_seed defs are never lifted: they inject their own first
           argument internally, and their callers pass it explicitly. *)
        if Types.Cdset.exists (lean_reader_is_seed env) defined then acc
        else
          let used = (add_def_entities target false empty_used_entities d).used_consts_set in
          (defined, used) :: acc
      | _ -> acc in
    let infos = List.rev (List.fold_left def_infos [] ds) in
    let changed = ref true in
    while !changed do
      changed := false;
      List.iter (fun (defined, used) ->
          if not (Types.Cdset.subset defined !St.reader_lifted) then begin
            let needs =
              Types.Cdset.exists (lean_reader_is_reader env) used
              || not (Types.Cdset.is_empty
                        (Types.Cdset.inter used !St.reader_lifted)) in
            if needs then begin
              St.reader_lifted := Types.Cdset.union defined !St.reader_lifted;
              changed := true
            end
          end) infos
    done
  end

(* Collect import for a qualified identifier from a target_rep.
   If the identifier has a module prefix (e.g., CerberusImpl.sizeof_ity),
   add the module to St.collected_imports for the current file. *)
(* Extract a module import from a CR_simple target rep body expression.
   Called via Backend_common.on_cr_simple_applied callback during rendering.
   Only fires for the current file's expressions — giving per-file scoping. *)
let collect_cr_simple_import (is_library : bool) (id_str : string) =
  (* Only collect imports for non-library target reps — library target reps
     reference Lean stdlib or LemLib names already available via import LemLib. *)
  if is_library then ()
  else
  match String.index_opt id_str '.' with
    | Some dot_pos when dot_pos > 0 ->
      let mod_name = String.sub id_str 0 dot_pos in
      if String.length mod_name > 0 &&
         Char.uppercase_ascii mod_name.[0] = mod_name.[0] &&
         not (List.mem mod_name !St.collected_imports) then
        St.collected_imports := mod_name :: !St.collected_imports
    | _ -> ()

(* Extract the name string from a type/numeric variable *)
let tnvar_to_string = function
  | Typed_ast.Tn_A (_, tv, _) -> Ulib.Text.to_string tv
  | Typed_ast.Tn_N (_, nv, _) -> Ulib.Text.to_string nv

let tnvar_kind = function
  | Typed_ast.Tn_A _ -> "Type"
  | Typed_ast.Tn_N _ -> "Nat"

(* Check if a constant's Lean target rep is == or != (BEq operators).
   Returns Some true for ==, Some false for !=, None otherwise. *)
let check_beq_target_rep c_descr =
  match Target.Targetmap.apply_target c_descr.target_rep (Target.Target_no_ident Target.Target_lean) with
  | Some (CR_infix (_, _, _, ident)) ->
    let name = Ident.to_string ident in
    if name = "==" || name = " ==" then Some true
    else if name = "!=" || name = " !=" then Some false
    else None
  | _ -> None

(* Library modules live under the LemLib.* namespace (e.g. "LemLib.Set").
   User modules have no namespace prefix. *)
let is_library_module mod_name =
  let prefix = "LemLib." in
  let plen = String.length prefix in
  String.length mod_name >= plen && String.sub mod_name 0 plen = prefix

(* Convert a module name like "LemLib.Set" to a flat namespace name "Lem_Set".
   Non-library modules are unchanged. *)
let lean_ns_name mod_name =
  let prefix = "LemLib." in
  let plen = String.length prefix in
  if is_library_module mod_name then
    String.concat "" ["Lem_"; String.sub mod_name plen (String.length mod_name - plen)]
  else mod_name

let lean_qualified_name name_str =
  match !St.namespace_stack with
    | [] -> name_str
    | ns -> String.concat "." (List.rev ns @ [name_str])

(* ===== Arc-8 S1: Inhabited derivation analysis (pre-pass side) =====
   Pure analysis helpers shared by the pre-pass (which computes the
   census + tier-2 plans in DECLARATION order) and the emission code
   (which only renders). Design note:
   doc/notes/2026-08-20_arc8-inhabited-threading-design.md rules 1-6. *)

(* Check if a source type references any of the given paths (mutual type detection) *)
let rec src_t_references_paths mutual_paths (s : src_t) : bool =
  match s.term with
    | Typ_wild _ | Typ_var _ | Typ_len _ -> false
    | Typ_tup seplist ->
        List.exists (src_t_references_paths mutual_paths) (Seplist.to_list seplist)
    | Typ_app (p, ts) ->
        List.exists (fun mp -> Path.compare mp p.descr = 0) mutual_paths ||
        List.exists (src_t_references_paths mutual_paths) ts
    | Typ_paren (_, inner, _) | Typ_with_sort (inner, _) ->
        src_t_references_paths mutual_paths inner
    | Typ_fn (dom, _, rng) ->
        src_t_references_paths mutual_paths dom || src_t_references_paths mutual_paths rng
    | Typ_backend (_, ts) ->
        List.exists (src_t_references_paths mutual_paths) ts

(* Check if a src_t is directly one of the mutual types (not wrapped
   in List, Option, etc.). Used for Inhabited generation: indirect
   references through containers are safe because List.default = [],
   Option.default = none, etc. — they don't evaluate the element's default. *)
let rec src_t_is_directly_mutual mutual_paths (s : src_t) : bool =
  match s.term with
    | Typ_app (id, _) ->
      List.exists (fun p -> Path.compare p id.descr = 0) mutual_paths
    | Typ_paren (_, t, _) -> src_t_is_directly_mutual mutual_paths t
    | Typ_with_sort (t, _) -> src_t_is_directly_mutual mutual_paths t
    | _ -> false

(* For mutual types, find a constructor whose args don't reference any mutual types.
   Prefers nullary constructors, then constructors with non-mutual args. *)
let find_safe_ctor_for_mutual mutual_paths ctors =
  let nullary = List.find_opt (fun (_, _, _, src_ts) ->
    Seplist.to_list src_ts = []
  ) ctors in
  match nullary with
    | Some _ -> nullary
    | None ->
      List.find_opt (fun (_, _, _, src_ts) ->
        let args = Seplist.to_list src_ts in
        not (List.exists (src_t_references_paths mutual_paths) args)
      ) ctors

(* Tier-1/tier-2 split (arc-8 S1). Tier 1 — unchanged from the DAEMON
   era — covers: non-parameterized types with a safe or safe-indirect
   constructor (or record/abbrev/opaque texps), and parameterized
   variants with a nullary constructor. Everything else is tier 2:
   per-constructor bounded derivation. *)
let inhabited_needs_tier2 mutual_paths ((_, tnvar_list, path, t, _)) : bool =
  if tnvar_list = [] then
    match t with
      | Te_variant (_, seplist) ->
        let ctors = Seplist.to_list seplist in
        (match find_safe_ctor_for_mutual mutual_paths ctors with
          | Some _ -> false
          | None ->
            not (List.exists (fun (_, _, _, src_ts) ->
              let args = Seplist.to_list src_ts in
              not (List.exists (src_t_is_directly_mutual [path]) args)) ctors))
      | Te_opaque ->
        (* Arc-8 S2 (D4): user-module opaque types are fail-closed — no
           constructors to derive through, so tier 2 records Plan_none /
           Inh_none (NO instance, no fallback; backend-visible demands
           are generation-time errors). The former non-parameterized
           `default := sorry` fallback instance is gone. *)
        true
      | _ -> false
  else
    match t with
      | Te_variant (_, seplist) ->
        not (List.exists (fun (_, _, _, src_ts) ->
          Seplist.to_list src_ts = []) (Seplist.to_list seplist))
      | _ -> true

(* Arc-8 S1 derivability analysis (design note rules 2 and 4) for a
   constructor-field type. Returns Some bound-tyvar-names — the
   [Inhabited tv] bounds the field's default needs — or None (field not
   derivably inhabitable). Recursively: type variables induce a bound;
   tuples combine; function types need only an inhabitable codomain
   (fun _ => default); applied types resolve through the instance
   census (an unconditional instance is preferred, else the first
   instance entry whose demanded argument positions are derivable —
   container heads like list/maybe/fmap are unconditional, so mutual
   references shielded by them stay derivable, the
   src_t_is_directly_mutual precedent). pending = paths with NO usable
   instance at this point: the type itself plus mutual siblings not yet
   emitted (rule 4: tier 2 skips self/mutual-referential constructors;
   earlier siblings and separate earlier types resolve through their
   already-recorded instances). *)
let derive_field_bounds (pending : Path.t list) (s : src_t) : string list option =
  let union a b = a @ List.filter (fun x -> not (List.mem x a)) b in
  let rec go (s : src_t) : string list option =
    match s.term with
      | Typ_var (_, v) -> Some [Ulib.Text.to_string (Tyvar.to_rope v)]
      | Typ_len _ -> Some []
      | Typ_wild _ -> None
      | Typ_paren (_, t, _) | Typ_with_sort (t, _) -> go t
      | Typ_tup seplist ->
          List.fold_left (fun acc t ->
            match acc with
              | None -> None
              | Some a -> (match go t with
                  | None -> None
                  | Some b -> Some (union a b)))
            (Some []) (Seplist.to_list seplist)
      | Typ_fn (_, _, rng) -> go rng
      | Typ_backend (_, _) -> Some []
      | Typ_app (id, ts) ->
          let p = id.descr in
          if List.exists (fun q -> Path.compare p q = 0) pending then None
          else
            let entries = match inhabited_census_lookup p with
              | Some (_, Inh_none) -> []
              | Some (_, Inh_instances es) -> es
              | None -> lean_builtin_inhabited_entries p
            in
            if List.exists (fun e -> e = []) entries then Some []
            else
              List.fold_left (fun acc e ->
                match acc with
                  | Some _ -> acc
                  | None ->
                    List.fold_left (fun acc2 i ->
                      match acc2 with
                        | None -> None
                        | Some a ->
                          (match List.nth_opt ts i with
                            | None -> None
                            | Some t -> (match go t with
                                | None -> None
                                | Some b -> Some (union a b))))
                      (Some []) e)
                None entries
  in go s

(* Derivability of a list of field types: all derivable, bounds unioned. *)
let derive_fields_bounds (pending : Path.t list) (ss : src_t list) : string list option =
  List.fold_left (fun acc t ->
    match acc with
      | None -> None
      | Some a -> (match derive_field_bounds pending t with
          | None -> None
          | Some b -> Some (a @ List.filter (fun x -> not (List.mem x a)) b)))
    (Some []) ss

(* Bound tyvar names -> parameter positions (for the census). *)
let inhabited_bounds_to_positions tnvar_list (bounds : string list) : int list =
  let rec go i = function
    | [] -> []
    | tv :: rest ->
      let tail = go (i + 1) rest in
      if List.mem (tnvar_to_string tv) bounds then i :: tail else tail
  in go 0 tnvar_list

(* Tier-2 plan for one type (arc-8 S1): one entry per usable
   constructor, in declaration order; Plan_none = fail-closed. *)
let inhabited_tier2_compute (pending : Path.t list) ((_, _, _, t, _)) : inh_plan =
  match t with
    | Te_variant (_, seplist) ->
      let ctors = Seplist.to_list seplist in
      let usable = List.concat (List.mapi (fun i (_, _, _, src_ts) ->
        match derive_fields_bounds pending (Seplist.to_list src_ts) with
          | Some bounds -> [(i, bounds)]
          | None -> []) ctors) in
      if usable = [] then Plan_none else Plan_variant usable
    | Te_record (_, _, fields, _) ->
      (match derive_fields_bounds pending
               (List.map (fun (_, _, _, s) -> s) (Seplist.to_list fields)) with
        | Some bounds -> Plan_record bounds
        | None -> Plan_none)
    | _ ->
      (* Te_opaque with parameters: no constructors to derive through.
         Te_abbrev never reaches tier 2 (skip_inhabited filters it). *)
      Plan_none

(* skip_inhabited_for_type, callable outside the backend functor *)
let skip_inhabited_for_type_env env t path =
  let l = Ast.Trans (false, "skip_inhabited_for_type", None) in
  let td = Types.type_defs_lookup l env.t_env path in
  (* Skip if declared with 'skip instances' for Lean *)
  Target.Targetset.mem Target.Target_lean td.Types.type_skip_instances ||
  match t with
    | Te_abbrev _ -> true
    | _ ->
      Target.Targetmap.apply_target td.Types.type_target_rep
        (Target.Target_no_ident Target.Target_lean) <> None

(* Arc-8 S1 Inhabited pre-pass: computes the instance census and the
   tier-2 derivation plans for a whole file IN DECLARATION ORDER,
   before emission (which walks definitions with fold_right, i.e.
   last-to-first side effects — the lean_reader_prepass /
   St.mutual_records precedent). Mirrors the emission dispatch
   exactly: Seplist.length > 1 -> the mutual machinery (all tier-1
   instances of a block precede all its tier-2 instances), otherwise
   the single-type path. The census persists across files (types from
   earlier modules resolve through it; lem processes modules in
   dependency order in one invocation). *)
let lean_inhabited_prepass env (ds : def list) =
  let census_name path = Name.to_string (Path.get_name path) in
  let record_tier2 pending (((_, _), tnvar_list, path, _, _) as td) =
    let plan = inhabited_tier2_compute pending td in
    inhabited_plan_add path plan;
    (if inhabited_census_debug then
      Printf.eprintf "PLAN %s: %s\n%!" (Path.to_string path)
        (match plan with
          | Plan_none -> "NONE"
          | Plan_record b -> Printf.sprintf "record[%s]" (String.concat "," b)
          | Plan_variant l -> String.concat ";" (List.map (fun (i, b) ->
              Printf.sprintf "ctor%d[%s]" i (String.concat "," b)) l)));
    match plan with
      | Plan_none -> inhabited_census_add path (census_name path) Inh_none
      | Plan_record bounds ->
        inhabited_census_add path (census_name path)
          (Inh_instances [inhabited_bounds_to_positions tnvar_list bounds])
      | Plan_variant usable ->
        inhabited_census_add path (census_name path)
          (Inh_instances (List.map (fun (_, b) ->
            inhabited_bounds_to_positions tnvar_list b) usable))
  in
  let process_block defs =
    let multi = Seplist.length defs > 1 in
    let ts_list = Seplist.to_list defs in
    let is_lib = is_library_module !St.current_module_name in
    let ts_list = if is_lib then List.filter (fun (_, _, _, t, _) -> t <> Te_opaque) ts_list else ts_list in
    let non_abbrev = List.filter (fun (_, _, _, t, _) ->
      match t with Te_abbrev _ -> false | _ -> true) ts_list in
    let active = List.filter (fun (_, _, path, t, _) ->
      not (skip_inhabited_for_type_env env t path)) ts_list in
    if multi then begin
      let mutual_paths = List.map (fun (_, _, path, _, _) -> path) non_abbrev in
      let tier1, tier2 = List.partition
        (fun td -> not (inhabited_needs_tier2 mutual_paths td)) active in
      (* Tier-1 census first: in the emitted file every tier-1 instance
         of a block precedes every tier-2 instance of that block. *)
      List.iter (fun (_, _, path, _, _) ->
        inhabited_census_add path (census_name path) (Inh_instances [[]])) tier1;
      let tier2_paths = List.map (fun (_, _, path, _, _) -> path) tier2 in
      ignore (List.fold_left (fun pending ((_, _, path, _, _) as td) ->
        record_tier2 pending td;
        List.filter (fun p -> Path.compare p path <> 0) pending)
        tier2_paths tier2)
    end else
      List.iter (fun ((_, _, path, _, _) as td) ->
        if inhabited_needs_tier2 [path] td then record_tier2 [path] td
        else inhabited_census_add path (census_name path) (Inh_instances [[]]))
        active
  in
  let rec walk (((d_aux, _), _, _) : def) =
    match d_aux with
    | Module (_, _, _, _, _, inner_ds, _) -> List.iter walk inner_ds
    | Type_def (_, defs) -> process_block defs
    | _ -> ()
  in List.iter walk ds

(* ===== Arc-8 S2: failwith -> failwithI + selective [Inhabited] threading =====
   Design note doc/notes/2026-08-20_arc8-inhabited-threading-design.md,
   section S2 (rules 1-6). EVERY failure site (failwith-mapped constants,
   plus the L_undefined literals from pattern compilation) now emits an
   Inhabited-backed failwithI (audit fix: L_undefined too mirrors
   OCaml's `failwith m`, src/backend.ml:864) — never legacy failwith,
   never sorry, never a silent default. Sites whose type mentions free
   type variables that are
   NOT discharged by the S1 instance census induce [Inhabited tv]
   instance-implicit binders on the ENCLOSING def's signature, computed
   here as a monotone fixpoint over the call graph (a caller that passes
   its own free tyvar into a threaded position inherits the binder).
   Instance-implicit binders need no call-site edits (S0 probe fact 2);
   the pass edits signatures only. Fail-closed guards (rules 3-4):
   - a tyvar failure site inside a generated instance method (binders
     impossible there) is a generation-time error naming the instance;
   - a demand on a tyvar that does not occur in the enclosing def's
     TYPE (a phantom tyvar — the undetermined function-field shape) is a
     generation-time error naming the def and the tyvar. *)

(* Expression destructor context for the pre-pass walk (no checking, no
   renaming — the same defs are re-walked by emission). *)
module ExpW = Exps_in_context(struct let env_opt = None let avoid = None end)

(* Types.t analog of derive_field_bounds: which tyvars must carry an
   [Inhabited tv] bound for the type to be synthesizable from the S1
   instance census. Some [] = discharged unconditionally; Some tvs =
   discharged given [Inhabited tv] for each; None = not derivable at all
   (an Inh_none-census type in a demanded position). Type abbreviations
   are head-normalized away first. *)
let rec typ_inhabited_bounds (d : Types.type_defs) (t : Types.t) : string list option =
  let union a b = a @ List.filter (fun x -> not (List.mem x a)) b in
  let t = Types.head_norm d t in
  match t.Types.t with
    | Types.Tvar v -> Some [Ulib.Text.to_string (Tyvar.to_rope v)]
    | Types.Tne _ -> Some []
    | Types.Tuvar _ -> Some []
    | Types.Tfn (_, cod) -> typ_inhabited_bounds d cod
    | Types.Tbackend _ -> Some []
    | Types.Ttup ts ->
      List.fold_left (fun acc t' ->
        match acc with
          | None -> None
          | Some a -> (match typ_inhabited_bounds d t' with
              | None -> None
              | Some b -> Some (union a b)))
        (Some []) ts
    | Types.Tapp (ts, p) ->
      let entries = match inhabited_census_lookup p with
        | Some (_, Inh_none) -> []
        | Some (_, Inh_instances es) -> es
        | None -> lean_builtin_inhabited_entries p
      in
      if List.exists (fun e -> e = []) entries then Some []
      else
        List.fold_left (fun acc e ->
          match acc with
            | Some _ -> acc
            | None ->
              List.fold_left (fun acc2 i ->
                match acc2 with
                  | None -> None
                  | Some a ->
                    (match List.nth_opt ts i with
                      | None -> None
                      | Some t' -> (match typ_inhabited_bounds d t' with
                          | None -> None
                          | Some b -> Some (union a b))))
                (Some []) e)
          None entries

(* ===== Arc-10 S2: derived structural comparisons for mutual blocks =====
   Shape analysis for constructor-field types, deciding how a derived
   BEq/compare body compares each field. Computed on SEMANTIC types
   (Types.t, head-normalized) so type abbreviations can never hide a
   mutual-sibling reference (the src_t_has_fn abbrev lesson). *)
type cmp_shape =
  | CSleaf                                   (* no sibling inside: instance-based == / Ord.compare *)
  | CSsibling of string                      (* Lean name: mutual call to <name>.beq_derived / .compare_derived *)
  | CStuple of cmp_shape list                (* destructure, compare componentwise *)
  | CSlist of Types.t * cmp_shape            (* element type + element shape: mutual list helper *)
  | CSoption of Types.t * cmp_shape          (* mutual option helper *)
  | CSsum of (Types.t * cmp_shape) * (Types.t * cmp_shape)  (* mutual sum helper *)
  | CSbad of string                          (* underivable: reason (fail-closed, type keeps its residual) *)

(* Does the (head-normalized) type reference any of the given paths? *)
let rec lean_typ_refs_paths (d : Types.type_defs) (paths : Path.t list) (t : Types.t) : bool =
  let t = Types.head_norm d t in
  match t.Types.t with
    | Types.Tvar _ | Types.Tne _ | Types.Tuvar _ -> false
    | Types.Tfn (a, b) -> lean_typ_refs_paths d paths a || lean_typ_refs_paths d paths b
    | Types.Ttup ts -> List.exists (lean_typ_refs_paths d paths) ts
    | Types.Tbackend (ts, _) -> List.exists (lean_typ_refs_paths d paths) ts
    | Types.Tapp (ts, p) ->
      List.exists (fun q -> Path.compare p q = 0) paths ||
      List.exists (lean_typ_refs_paths d paths) ts

(* Compute the comparison shape of a field type.
   derived: the mutual siblings currently in the derived set (path ->
   Lean name); sorried: sibling paths OUTSIDE the derived set (their
   instances stay sorried, so a reference makes this type underivable —
   underivability propagates rather than routing a "real" body through
   a sorry instance). Containers with a Lean-instance comparison story
   (list, maybe, either, tuples) recurse; any other head over a sibling
   is fail-closed CSbad. *)
let rec lean_cmp_shape (d : Types.type_defs) (derived : (Path.t * string) list)
    (sorried : Path.t list) (t : Types.t) : cmp_shape =
  let all_paths = List.map fst derived @ sorried in
  if not (lean_typ_refs_paths d all_paths t) then CSleaf
  else
    let bad_of = function CSbad r -> Some r | _ -> None in
    let t' = Types.head_norm d t in
    match t'.Types.t with
      | Types.Tfn _ -> CSbad "function type"  (* unreachable behind texp_can_derive_beq; belt *)
      | Types.Ttup ts ->
        let shs = List.map (lean_cmp_shape d derived sorried) ts in
        (match List.find_map bad_of shs with
          | Some r -> CSbad r
          | None -> CStuple shs)
      | Types.Tapp (ts, p) ->
        (match List.find_opt (fun (q, _) -> Path.compare p q = 0) derived with
          | Some (_, name) ->
            if List.exists (lean_typ_refs_paths d all_paths) ts
            then CSbad "mutual type applied to mutual-referencing arguments"
            else CSsibling name
          | None ->
            if List.exists (fun q -> Path.compare p q = 0) sorried then
              CSbad "reference to a mutual sibling outside the derived set"
            else
              (match Name.to_string (Path.get_name p), ts with
                | "list", [e] ->
                  let sh = lean_cmp_shape d derived sorried e in
                  (match bad_of sh with Some r -> CSbad r | None -> CSlist (e, sh))
                | "maybe", [e] ->
                  let sh = lean_cmp_shape d derived sorried e in
                  (match bad_of sh with Some r -> CSbad r | None -> CSoption (e, sh))
                | "either", [l; r] ->
                  let shl = lean_cmp_shape d derived sorried l in
                  let shr = lean_cmp_shape d derived sorried r in
                  (match bad_of shl, bad_of shr with
                    | Some r, _ | _, Some r -> CSbad r
                    | None, None -> CSsum ((l, shl), (r, shr)))
                | n, _ -> CSbad (Printf.sprintf "mutual reference under unsupported head '%s'" n)))
      | _ -> CSbad "unexpected shape"

let lean_cmp_shape_is_bad = function CSbad _ -> true | _ -> false

let lean_thread_lookup (c : Types.const_descr_ref) : (int list * string list) option =
  Types.Cdmap.apply !St.failwith_threaded c
let lean_thread_debug = (try Sys.getenv "LEM_THREAD_DEBUG" <> "" with Not_found -> false)

(* Constants whose LEAN target_rep is the bare identifier `failwith`
   (Assert_extra.failwith, cerberus's Utils.error, ...) — shared by the
   pre-pass and emission so the two can never disagree. *)
let lean_is_failwith_rep_env env cref =
  let cd = c_env_lookup Ast.Unknown env.c_env cref in
  match Target.Targetmap.apply_target cd.target_rep (Target.Target_no_ident Target.Target_lean) with
  | Some (CR_simple (_, _, _, e)) | Some (CR_inline (_, _, _, e)) ->
    (match ExpW.exp_to_term e with
     | Backend (_, i) -> Ident.to_string i = "failwith"
     | _ -> false)
  | _ -> false

let lean_typ_to_string (t : Types.t) : string =
  ignore (Format.flush_str_formatter ());
  Types.pp_type Format.str_formatter t;
  Format.flush_str_formatter ()

(* Collect, from one expression tree: failure SITES (the demanded
   Types.t of every failwith-rep application / bare reference and every
   L_undefined literal) and every constant REFERENCE with its type
   instantiation (for threading propagation). *)
type thread_scan = {
  mutable th_sites : (Types.t * Ast.l) list;
  mutable th_refs : (Types.const_descr_ref * Types.t list * Ast.l) list;
}

let lean_thread_scan_exp env (acc : thread_scan) (e : exp) : unit =
  let is_fw = lean_is_failwith_rep_env env in
  let sl_iter f sl = List.iter f (Seplist.to_list sl) in
  let rec go e =
    match ExpW.exp_to_term e with
    | App (e1, e2) ->
      let (e0, args) = strip_app_exp e in
      (match ExpW.exp_to_term e0 with
       | Constant cid when is_fw cid.descr && args <> [] ->
         (* record the FULL application's type once; skip the spine *)
         acc.th_sites <- (Typed_ast.exp_to_typ e, exp_to_locn e) :: acc.th_sites;
         List.iter go args
       | _ -> go e1; go e2)
    | Constant cid ->
      if is_fw cid.descr then
        (* bare / point-free reference: the demand is the (instantiated)
           codomain, reached through Tfn by typ_inhabited_bounds *)
        acc.th_sites <- (Typed_ast.exp_to_typ e, exp_to_locn e) :: acc.th_sites
      else
        acc.th_refs <- (cid.descr, cid.instantiation, exp_to_locn e) :: acc.th_refs
    | Lit l ->
      (match l.term with
       | L_undefined _ -> acc.th_sites <- (l.typ, exp_to_locn e) :: acc.th_sites
       | _ -> ())
    | Var _ | Nvar_e _ | Backend _ -> ()
    | Fun (_, _, _, e1) -> go e1
    | Function (_, pes, _) -> sl_iter (fun (_, _, e1, _) -> go e1) pes
    | Infix (e1, e2, e3) -> go e1; go e2; go e3
    | Record (_, fes, _) -> sl_iter (fun (_, _, e1, _) -> go e1) fes
    | Recup (_, e1, _, fes, _) -> go e1; sl_iter (fun (_, _, e2, _) -> go e2) fes
    | Field (e1, _, _) -> go e1
    | Vector (_, es, _) -> sl_iter go es
    | VectorSub (e1, _, _, _, _, _) -> go e1
    | VectorAcc (e1, _, _, _) -> go e1
    | Case (_, _, e1, _, pes, _) -> go e1; sl_iter (fun (_, _, e2, _) -> go e2) pes
    | Typed (_, e1, _, _, _) -> go e1
    | Let (_, lb, _, e1) ->
      (match lb with
       | (Let_val (_, _, _, e2), _) -> go e2
       | (Let_fun (_, _, _, _, e2), _) -> go e2);
      go e1
    | Tup (_, es, _) -> sl_iter go es
    | List (_, es, _) -> sl_iter go es
    | Paren (_, e1, _) -> go e1
    | Begin (_, e1, _) -> go e1
    | If (_, e1, _, e2, _, e3) -> go e1; go e2; go e3
    | Set (_, es, _) -> sl_iter go es
    | Setcomp (_, e1, _, e2, _, _) -> go e1; go e2
    | Comp_binding (_, _, e1, _, _, qbs, _, e2, _) ->
      go e1; List.iter go_qb qbs; go e2
    | Quant (_, qbs, _, e1) -> List.iter go_qb qbs; go e1
    | Do (_, _, dls, _, e1, _, _) ->
      List.iter (fun (Do_line (_, _, e2, _)) -> go e2) dls; go e1
  and go_qb = function
    | Qb_var _ -> ()
    | Qb_restr (_, _, _, _, e1, _) -> go e1
  in go e

(* One threading unit: the crefs a val_def group defines plus its scan.
   Fun_def clauses are grouped per constant (so and-chained siblings do
   not inherit each other's demands); a Let_def's bound names share the
   single body. *)
type thread_unit = {
  tu_crefs : Types.const_descr_ref list;
  tu_scan : thread_scan;
  tu_loc : Ast.l;
}

let lean_thread_cd_name (cd : const_descr) : string =
  Name.to_string (Path.get_name cd.const_binding)

(* The demand a scan makes RIGHT NOW: static failure-site demands plus,
   for every reference to an already-threaded def, the bounds of the
   instantiation types at the threaded positions. Errors are fail-closed
   generation-time failures naming the object and the escape hatches. *)
let lean_thread_demand env (where_ : string) (sc : thread_scan) : string list =
  let d = env.t_env in
  let union a b = a @ List.filter (fun x -> not (List.mem x a)) b in
  let dem = ref [] in
  List.iter (fun (t, l) ->
      match typ_inhabited_bounds d t with
      | Some names -> dem := union !dem names
      | None ->
        raise (Reporting_basic.err_general true l (Printf.sprintf
          "Lean backend: failure site (failwith/undefined default) in %s at type '%s' whose Inhabited instance cannot be derived; escape hatches: 'declare {lean} skip_instances' on the type plus a hand-written Lean instance, or a hand-written Lean target_rep"
          where_ (lean_typ_to_string t))))
    sc.th_sites;
  List.iter (fun (cref, inst, l) ->
      match lean_thread_lookup cref with
      | None -> ()
      | Some (poss, _) ->
        let callee = lean_thread_cd_name (c_env_lookup Ast.Unknown env.c_env cref) in
        List.iter (fun p ->
            match List.nth_opt inst p with
            | None -> ()
            | Some ti ->
              (match typ_inhabited_bounds d ti with
               | Some names -> dem := union !dem names
               | None ->
                 raise (Reporting_basic.err_general true l (Printf.sprintf
                   "Lean backend: call of '%s' (which carries an [Inhabited] binder) in %s at instantiation '%s' whose Inhabited instance cannot be derived; escape hatches: 'declare {lean} skip_instances' on the type plus a hand-written Lean instance, or a hand-written Lean target_rep"
                   callee where_ (lean_typ_to_string ti)))))
          poss)
    sc.th_refs;
  !dem

(* Pre-pass (runs after lean_inhabited_prepass, which populates the
   instance census this analysis reads): compute the threaded-def map to
   a fixpoint over this module's Val_defs, then guard-sweep Instance
   methods (rule 3). *)
let lean_failwith_thread_prepass env (ds : def list) =
  let target = Target.Target_no_ident Target.Target_lean in
  let in_lean targets = Typed_ast.in_targets_opt target targets in
  (* -- unit collection -- *)
  let scan_of_exps es =
    let sc = { th_sites = []; th_refs = [] } in
    List.iter (lean_thread_scan_exp env sc) es; sc in
  let units_of_val_def l (vd : val_def) : thread_unit list =
    match vd with
    | Let_def (_, targets, (_, name_map, _, _, e)) ->
      if in_lean targets then
        [{ tu_crefs = List.map snd name_map; tu_scan = scan_of_exps [e]; tu_loc = l }]
      else []
    | Fun_def (_, _, targets, funcls) ->
      if in_lean targets then begin
        (* group clauses by constant, preserving order (the emission's
           grouping rule) *)
        let order = ref [] in
        let tbl = Hashtbl.create 8 in
        List.iter (fun ((_, c, _, _, _, e) : funcl_aux) ->
            (if not (Hashtbl.mem tbl c) then order := c :: !order);
            let existing = match Hashtbl.find_opt tbl c with Some v -> v | None -> [] in
            Hashtbl.replace tbl c (existing @ [e]))
          (Seplist.to_list funcls);
        List.map (fun c ->
            { tu_crefs = [c]; tu_scan = scan_of_exps (Hashtbl.find tbl c); tu_loc = l })
          (List.rev !order)
      end else []
    | Let_inline _ -> []  (* expanded at call sites by the inline macro *)
  in
  let rec collect acc (((d_aux, _), l, _) : def) =
    match d_aux with
    | Module (_, _, _, _, _, inner_ds, _) -> List.fold_left collect acc inner_ds
    | Val_def vd -> acc @ units_of_val_def l vd
    | _ -> acc
  in
  let units = List.fold_left collect [] ds in
  (* -- fixpoint -- *)
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun u ->
        let where_ =
          match u.tu_crefs with
          | c :: _ -> Printf.sprintf "'%s'" (lean_thread_cd_name (c_env_lookup Ast.Unknown env.c_env c))
          | [] -> "a definition" in
        let dem = lean_thread_demand env where_ u.tu_scan in
        if dem <> [] then
          List.iter (fun c ->
              let cd = c_env_lookup Ast.Unknown env.c_env c in
              let name = lean_thread_cd_name cd in
              (* phantom guard (rule 4): every demanded tyvar must occur
                 in the def's TYPE, or the binder would be unbound *)
              let sig_names =
                List.map (fun tv -> Name.to_string (Types.tnvar_to_name tv))
                  (Types.TNset.elements (Types.free_vars cd.const_type)) in
              List.iter (fun n ->
                  if not (List.mem n sig_names) then
                    raise (Reporting_basic.err_general true u.tu_loc (Printf.sprintf
                      "Lean backend: failure at type variable '%s' which does not occur in the signature of '%s' — cannot thread an [Inhabited %s] binder; determine the type variable at the failure site or give '%s' a hand-written Lean target_rep"
                      n name n name)))
                dem;
              let tp_names = List.map (fun tv -> Name.to_string (Types.tnvar_to_name tv)) cd.const_tparams in
              let poss = List.concat (List.mapi (fun i n -> if List.mem n dem then [i] else []) tp_names) in
              let names_in_order = List.filter (fun n -> List.mem n dem) tp_names in
              (match lean_thread_lookup c with
               | Some (old_poss, _) when old_poss = poss -> ()
               | _ ->
                 St.failwith_threaded := Types.Cdmap.insert !St.failwith_threaded (c, (poss, names_in_order));
                 if lean_thread_debug then
                   Printf.eprintf "THREAD %s [%s]\n%!" (Path.to_string cd.const_binding)
                     (String.concat "," names_in_order);
                 changed := true))
            u.tu_crefs)
      units
  done;
  (* -- instance guard sweep (rule 3): binders cannot be added to
        instance methods, so ANY non-empty demand inside one is a
        generation-time error naming the instance -- *)
  let rec guard (((d_aux, _), l, _) : def) =
    match d_aux with
    | Module (_, _, _, _, _, inner_ds, _) -> List.iter guard inner_ds
    | Instance (_, _, (_, _, _, class_path, _, _), vals, _) ->
      let inst_name = Path.to_string class_path in
      List.iter (fun vd ->
          let vd_units = units_of_val_def l vd in
          List.iter (fun u ->
              let where_ = Printf.sprintf "an instance of class '%s'" inst_name in
              let dem = lean_thread_demand env where_ u.tu_scan in
              if dem <> [] then
                raise (Reporting_basic.err_general true u.tu_loc (Printf.sprintf
                  "Lean backend: type-variable failure site (failwith/undefined default, or a call needing [Inhabited '%s']) inside a generated method of instance of class '%s' — instance methods cannot carry [Inhabited] binders; escape hatches: give the method a Lean target_rep ('declare lean target_rep function ...') or restructure so the failure is at a concrete type"
                  (String.concat "', '" dem) inst_name)))
            vd_units)
        vals
    | _ -> ()
  in List.iter guard ds

(* Arc-8 S2: run the analysis pre-passes over EVERY typechecked module
   of the invocation — including the non-output LIBRARY modules — in
   dependency order, BEFORE any emission (called from
   process_file.output). Rationale: analysis knowledge must span
   invocation boundaries. `make lean-libs` regenerates the library with
   [Inhabited] binders threaded onto its failure-carrying defs
   (fromJust, head, fail, find0, ...); a later cerberus/test invocation
   only EMITS its own modules, but its defs CALL those library defs —
   so caller-side demand computation must see the library's instance
   census and threading map. This pass recomputes that knowledge from
   the very library sources the invocation already typechecked and
   transformed: the same analysis that emitted the library, never a
   hardcoded list. The per-module pre-passes in lean_defs then re-run
   over each output module; all the passes are monotone (their
   sets/maps only grow, and re-insertions are equal), so the re-run is
   harmless. *)
let lean_analysis_prepass_all env (mods : checked_module list) =
  let saved = !St.current_module_name in
  List.iter (fun m ->
      let (mod_path, mod_name) = Path.to_name_list m.module_path in
      let module_name = Name.to_string
          (Backend_common.get_module_name env (Target.Target_no_ident Target.Target_lean) mod_path mod_name) in
      St.current_module_name := module_name;
      let (ds, _) = m.typed_ast in
      lean_reader_prepass env ds;
      lean_inhabited_prepass env ds;
      lean_failwith_thread_prepass env ds)
    mods;
  St.current_module_name := saved

let wrap_lean_comment x = Ulib.Text.(^^^) (Ulib.Text.(^^^) (r"/- ") x) (r" -/")

let sanitize_tabs r =
  let s = Ulib.Text.to_string r in
  if String.contains s '\t' then
    Ulib.Text.of_string (String.map (fun c -> if c = '\t' then ' ' else c) s)
  else r

let rec lean_comment_to_rope =
  function
    | Ast.Chars r -> sanitize_tabs r
    | Ast.Comment coms -> wrap_lean_comment (Ulib.Text.concat (r"") (List.map lean_comment_to_rope coms))

let lex_skip =
  function
    | Ast.Com r -> lean_comment_to_rope r
    | Ast.Ws r -> sanitize_tabs r
    | Ast.Nl -> r"\n"
;;

let delim_regexp = Str.regexp "^\\([][`;,(){}]\\|;;\\)$"
;;

let symbolic_regexp = Str.regexp "^[-!$%&*+./:<=>?@^|~]+$"
;;

let is_delim s = Str.string_match delim_regexp s 0
;;

let is_symbolic s = Str.string_match symbolic_regexp s 0
;;

let need_space x y =
  let f x =
    match x with
      | Kwd'(s) ->
        if is_delim s then
          (true,false)
        else if is_symbolic s then
          (false,true)
        else
          (false,false)
      | Ident'(r) ->
        (false, is_symbolic @@ Ulib.Text.to_string r)
      | Num' _ ->
        (false,false)
  in
    let (d1,s1) = f x in
    let (d2,s2) = f y in
      not d1 && not d2 && s1 = s2
;;

let from_string x = meta_utf8 x

(* Lean 4 forbids tab characters. Replace tabs with spaces in whitespace and comment tokens. *)
let ws s =
  let sanitize_skip = function
    | Ast.Ws r -> Ast.Ws (sanitize_tabs r)
    | Ast.Com _ as c -> c  (* Comments sanitized in lean_comment_to_rope *)
    | skip -> skip
  in
  match s with
  | None -> Output.ws None
  | Some ts -> Output.ws (Some (List.map sanitize_skip ts))

let sep x s = ws s ^ x
let path_sep = r"."

(* Lean 4 is whitespace-sensitive, so disable auto-formatting blocks
   which can break indentation of match alternatives *)
let block _ _ t = t
let block_hov _ _ t = t

let flatten_newlines = Output.flatten_newlines

let tyvar (_, tv, _) = id Type_var (Ulib.Text.(^^^) (r"") tv)
let concat_str s = concat (from_string s)

(* Escape a string if it's a Lean syntax keyword, using «» guillemets *)
let lean_escape_keyword s =
  if List.mem s lean_syntax_keywords then
    String.concat "" ["\xC2\xAB"; s; "\xC2\xBB"]  (* «name» *)
  else s

let lskips_t_to_output name =
  let stripped = Name.strip_lskip name in
  let s = Ulib.Text.to_string (Name.to_rope stripped) in
  let escaped = lean_escape_keyword s in
  if escaped <> s then from_string escaped
  else Output.id Term_var (Name.to_rope stripped)
;;

(* Name output for variables with keyword escaping *)
let name_var_output v =
  let s = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip v)) in
  let escaped = lean_escape_keyword s in
  if escaped <> s then
    Output.flat [ws (Name.get_lskip v); from_string escaped]
  else
    Name.to_output Term_var v

(* If the type is a record rendered as a single-constructor inductive
   (due to being in a mutual block), return its path. Uses the per-compilation-unit
   list St.mutual_records which accumulates across files in one lem invocation. *)
let mutual_record_path typ : Path.t option =
  match typ.Types.t with
    | Types.Tapp (_, path) ->
        if List.exists (fun p -> Path.compare p path = 0) !St.mutual_records
        then Some path
        else None
    | _ -> None

let in_target targets = Typed_ast.in_targets_opt (Target.Target_no_ident Target.Target_lean) targets;;

let lean_infix_op a x =
  Output.flat [
    from_string "(fun x y => x "; id a x; from_string " y)"
  ]
;;

let lean_format_op use_infix a x =
  if use_infix then
    lean_infix_op a x
  else
    id a x


let generate_fresh_name () =
  let n = !St.fresh_name_counter in
  St.fresh_name_counter := n + 1;
  Stdlib.(^) "x" (string_of_int n)

type variable
  = Tyvar of Output.t
  | Nvar of Output.t

let tnvar_to_variable = function
  | Typed_ast.Tn_A _ as tv -> Tyvar (from_string (tnvar_to_string tv))
  | Typed_ast.Tn_N _ as nv -> Nvar (from_string (tnvar_to_string nv))
;;

module LeanBackendAux (A : sig val avoid : var_avoid_f option;; val env : env;; val dir : string;; val ascii_rep_set : Types.Cdset.t end) =
  struct

    module B = Backend_common.Make (
      struct
        let env = A.env
        let target = Target_no_ident Target_lean
        let id_format_args = (lean_format_op, path_sep)
        let dir = A.dir
      end);;

    module C = Exps_in_context (
      struct
        let env_opt = Some A.env
        let avoid = A.avoid
      end)
    ;;

(* Extract (class_name, type_var_name) pairs from @Class.method patterns
   in a TYR_subst RHS src_t. These patterns indicate that the type requires
   a typeclass instance parameter (e.g., @Size.size 'a _ means [Size 'a]). *)
let collect_class_constraints_from_src_t (st : Types.src_t) : (string * string) list =
  let rec collect (t : Types.src_t) = match t.term with
    | Types.Typ_backend (p, args) ->
      let path_str = Path.to_string p.descr in
      let at_constraints =
        if String.length path_str > 1 && path_str.[0] = '@' then
          match String.index_opt path_str '.' with
          | Some dot_pos ->
            let class_name = String.sub path_str 1 (dot_pos - 1) in
            List.filter_map (fun (arg : Types.src_t) ->
              match arg.term with
              | Types.Typ_var (_, v) ->
                Some (class_name, Ulib.Text.to_string (Types.tnvar_to_rope (Types.Ty v)))
              | _ -> None
            ) args
          | None -> []
        else []
      in
      at_constraints @ List.concat_map collect args
    | Types.Typ_app (_, args) -> List.concat_map collect args
    | Types.Typ_paren (_, t', _) -> collect t'
    | Types.Typ_fn (t1, _, t2) -> collect t1 @ collect t2
    | Types.Typ_tup sl -> List.concat_map collect (Seplist.to_list sl)
    | _ -> []
  in
  collect st
;;

(* Collect extra class constraints introduced by TYR_subst type target reps.
   When a type like mword has a TYR_subst mapping to BitVec (@Size.size 'a _),
   any function using mword 'a needs [Size 'a] but the Lem type doesn't
   carry this constraint. This function walks a Lem type and finds all such
   extra constraints by: (1) finding Tapp nodes whose type has a Lean TYR_subst,
   (2) extracting @Class.method patterns from the TYR_subst RHS via
   collect_class_constraints_from_src_t, (3) mapping TYR_subst type variables
   to actual type arguments. *)
let extra_constraints_for_tyr_subst (ty : Types.t) : (string * string) list =
  let constraints = ref [] in
  let rec walk (ty : Types.t) =
    match ty.t with
    | Types.Tapp (args, path) ->
      begin match Types.type_defs_lookup_tc A.env.t_env path with
      | Some (Types.Tc_type td) ->
        begin match Target.Targetmap.apply_target td.Types.type_target_rep
                (Target.Target_no_ident Target.Target_lean) with
        | Some (Types.TYR_subst (_, _, tvars, rhs_t)) ->
          let tvar_strs = List.map (fun tv ->
            Ulib.Text.to_string (Types.tnvar_to_rope tv)
          ) tvars in
          let var_map = List.combine tvar_strs args in
          let raw = collect_class_constraints_from_src_t rhs_t in
          List.iter (fun (cls, tv) ->
            match List.assoc_opt tv var_map with
            | Some actual_ty ->
              begin match actual_ty.t with
              | Types.Tvar v' ->
                let actual_tv = Ulib.Text.to_string (Tyvar.to_rope v') in
                if not (List.mem (cls, actual_tv) !constraints) then
                  constraints := (cls, actual_tv) :: !constraints
              | _ -> () (* Concrete type argument — no constraint needed *)
              end
            | None -> ()
          ) raw
        | _ -> ()
        end
      | Some (Types.Tc_class _) -> () (* Classes don't have TYR_subst *)
      | None -> ()
      end;
      List.iter walk args
    | Types.Tfn (t1, t2) -> walk t1; walk t2
    | Types.Ttup ts -> List.iter walk ts
    | Types.Tbackend (ts, _) -> List.iter walk ts
    | _ -> ()
  in
  walk ty;
  List.rev !constraints
;;

(* Filter out constraints that are already present in Lem's class_constraints. *)
let filter_new_tyr_constraints extras class_constraints =
  let existing = List.map (fun (path, tnvar) ->
    (Name.to_string (B.class_path_to_name path),
     Ulib.Text.to_string (Types.tnvar_to_rope tnvar))
  ) class_constraints in
  List.filter (fun c -> not (List.mem c existing)) extras
;;

(* Format extra TYR_subst constraints as Lean instance parameters: [Class tv] *)
let format_tyr_constraints extras =
  Output.flat (List.map (fun (cls, tv) ->
    Output.flat [from_string " ["; from_string cls; from_string " "; from_string tv; from_string "]"]
  ) extras)
;;

(* Lean-native constraints for default instances.
   Lem's default_instance declarations are unconstrained (forall 'a), but
   their method bodies reference Lean functions requiring typeclass instances:
   - Eq0 body uses == (BEq) and != (BEq)
   - SetType body uses defaultCompare (Ord)
   The other two defaults (OrdMaxMin, MapKeyType) already carry Lem-level
   constraints that provide what Lean needs.
   This extends the extra_constraints_for_tyr_subst pattern (above) to
   handle function target rep constraints in default instances. *)
let lean_default_instance_extra_constraints class_name =
  match class_name with
  | "Eq0" -> ["BEq"]
  | "SetType" -> ["Ord"]
  | _ -> []
;;

let use_ascii_rep_for_const (cd : const_descr_ref) : bool =
  Types.Cdset.mem cd A.ascii_rep_set
;;

let field_ident_to_output fd ascii_alternative =
  let ident = B.const_id_to_ident fd ascii_alternative in
  let name = Ident.get_name ident in
  let stripped = Name.strip_lskip name in
    from_string (Name.to_string stripped)
;;

(* Lean 4's greedy parser extends match/if/let/fun rightward, consuming
   subsequent tokens. These forms must be parenthesized when nested inside:
   - function arguments: f (match ...) instead of f match ...
   - match arm bodies: | p => (match ...) to avoid consuming outer | arms
   - if conditions: if (match ...) then ... to avoid misparsing *)
let needs_parens term =
  match term with
    | Case _ | If _ | Let _ | Fun _ -> true
    | _ -> false

(* Pattern rendering has two modes:
   - FunParam: adds type annotations to variables and wildcards (needed with
     autoImplicit=false), resolves wildcard types, wraps cons/unit in parens
   - MatchArm: bare output for match arms and let bindings *)
type pat_style = FunParam | MatchArm

    (* True iff the expression contains an application of a constant marked
       'declare {lean} effectful'. Defs containing such call sites must be
       emitted with @[never_extract, noinline]: never_extract stops Lean from
       caching a closed application (e.g. 'fresh ()') as a constant evaluated
       once at startup, and together with noinline it prevents CSE from
       merging identical call sites. The runEffectful thunk alone cannot
       achieve this, because identical closed thunks are themselves shared.
       Limitation: instance fields cannot carry attributes, so effectful
       calls inside instance methods are only protected one level down (by
       the attributes on runEffectful_impl itself). *)
    let exp_contains_effectful (e : exp) : bool =
      let ue = add_exp_entities empty_used_entities e in
      List.exists (fun cref ->
          let cd = c_env_lookup Ast.Unknown A.env.c_env cref in
          Targetset.mem Target_lean cd.effectful)
        ue.used_consts

    (* --- Reader lifting helpers (declare {lean} reader val) ---
       thin wrappers over the top-level env-parameterized versions;
       the pre-pass lives at module-emission level (lean_reader_prepass). *)
    let is_reader_cref = lean_reader_is_reader A.env
    let is_seed_cref = lean_reader_is_seed A.env
    let reader_param_name = lean_reader_param_name A.env
    let get_reader_params () = lean_reader_get_params A.env

    (* A reader val has type unit -> T; the parameter carries T. *)
    let reader_value_typ cref =
      let cd = c_env_lookup Ast.Unknown A.env.c_env cref in
      match cd.const_type.Types.t with
      | Types.Tfn (_, cod) -> cod
      | _ -> cd.const_type

    (* Does this expression force reader lifting of its enclosing def:
       a direct reader use, or a call to an already-lifted def. *)
    let exp_needs_reader (e : exp) : bool =
      let ue = add_exp_entities empty_used_entities e in
      List.exists (fun cref ->
          is_reader_cref cref || Types.Cdset.mem cref !St.reader_lifted)
        ue.used_consts

    (* Injection value name: the enclosing def's injected parameter, or —
       inside a reader_seed def — its first argument. *)
    let reader_inject_name pname =
      match !St.reader_seed_param with
      | Some seed -> seed
      | None -> pname

    let reader_args_output () =
      Output.flat (List.map (fun (_, pname) ->
          Output.flat [from_string " "; from_string (reader_inject_name pname)])
        (get_reader_params ()))

    (* Fuel sentinel for the Lean target, if declared for this constant. *)
    let fuel_sentinel_for cref =
      let cd = c_env_lookup Ast.Unknown A.env.c_env cref in
      Target.Targetmap.apply_target cd.fuel_sentinel (Target.Target_no_ident Target.Target_lean)

    (* Ground-site alternative head (declare {lean} ground_rep val f =
       `Ident`): emitted instead of the constant at applications whose
       result type is syntactically ground. See the failwith special case
       below — same classification rule, declare-driven. *)
    let ground_rep_for cref =
      let cd = c_env_lookup Ast.Unknown A.env.c_env cref in
      Target.Targetmap.apply_target cd.ground_rep (Target.Target_no_ident Target.Target_lean)

    (* Constants whose LEAN target_rep is the bare identifier `failwith`
       (Assert_extra.failwith, cerberus's Utils.error, ...). Arc-8 S2:
       EVERY such call site is re-emitted as LemLib.failwithI (opaque,
       [Inhabited]-bounded, axiom-free); tyvar-typed sites are
       discharged by the [Inhabited tv] binders the threading pre-pass
       put on the enclosing def (lean_failwith_thread_prepass). Legacy
       LemLib.failwith is never emitted. Shared with the pre-pass so
       the two can never disagree. *)
    let is_lean_failwith_rep cref = lean_is_failwith_rep_env A.env cref
    (* Rule-3 emission backstop (the pre-pass guard fires first with a
       better-named error): a failure site inside an instance method at
       a type not unconditionally discharged cannot be repaired by
       binder threading. *)
    let failwith_instance_guard inside_instance site_t =
      if inside_instance then
        match typ_inhabited_bounds A.env.t_env site_t with
        | Some [] -> ()
        | _ ->
          raise (Reporting_basic.err_general true Ast.Unknown
            "Lean backend: type-variable failure site inside a generated instance method — instance methods cannot carry [Inhabited] binders; escape hatches: give the method a Lean target_rep ('declare lean target_rep function ...') or restructure so the failure is at a concrete type")

    let rec def_extra (inside_instance: bool) (callback: def list -> Output.t) (inside_module: bool) (m: def_aux) =
      match m with
        | Lemma (skips, lemma_typ, targets, (name, _), skips', e) ->
          if in_target targets then
            let name_out = Name.to_output Term_var name in
            let name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip name)) in
            match lemma_typ with
            | Ast.Lemma_assert _ ->
              Output.flat [
                ws skips;
                from_string "#eval do\n";
                from_string ("  if ("); exp inside_instance e; from_string (" : Bool)\n");
                from_string (String.concat "" ["  then IO.println \"PASS: "; lean_string_escape name_str; "\"\n"]);
                from_string (String.concat "" ["  else throw (IO.userError \"FAIL: "; lean_string_escape name_str; "\")"])
              ]
            | Ast.Lemma_lemma _ | Ast.Lemma_theorem _ ->
              (* Skip lemma/theorem generation for Lean. These assert inline expansion
                 correctness but contain complex expressions (match, forall) that
                 cause parsing issues, and the proof is by sorry anyway. *)
              Output.flat [
                ws skips; from_string "/- removed theorem "; name_out; from_string " -/"
              ]
          else
            from_string "/- removed lemma intended for another backend -/"
        (* All non-Lemma defs are handled by def, not def_extra.
           Exhaustive match so new def_aux variants trigger a compiler warning. *)
        | Type_def _ | Val_def _ | Module _ | Rename _ | OpenImport _
        | OpenImportTarget _ | Indreln _ | Val_spec _ | Class _ | Instance _
        | Comment _ | Declaration _ -> emp
    and def (inside_instance: bool) (callback : def list -> Output.t) (inside_module : bool) (m : def_aux) =
      match m with
      | Type_def (skips, def) ->
          let type_output =
            if Seplist.length def = 1 then
              match Seplist.hd def with
              | ((n, _), tyvars, path, Te_abbrev (sk, t), _) ->
                  type_def_abbreviation n tyvars path sk t
              | (n, tyvars, path, (Te_record (_, _, fields, _) as ty), _) ->
                  type_def_record n tyvars path ty fields
              | _ -> type_def inside_module def
            else
              type_def inside_module def
          in
          let defaults =
            if Seplist.length def > 1 then
              generate_default_values_mutual def
            else
              generate_default_values def
          in
            Output.flat [
              ws skips; type_output;
              defaults;
            ]
      | Val_def (def) ->
          let class_constraints = val_def_get_class_constraints A.env def in
          let tv_set = val_def_get_free_tnvars A.env def in
          let (_, is_real_rec, try_term) =
            Typed_ast_syntax.try_termination_proof
              (Target_no_ident Target_lean) A.env.c_env m
          in
          val_def false None is_real_rec try_term def tv_set class_constraints
      | Module (skips, (name, l), mod_binding, skips', skips'', defs, skips''') ->
        let name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip name)) in
        St.local_modules := name_str :: !St.local_modules;
        St.namespace_stack := name_str :: !St.namespace_stack;
        (* Build fully-qualified path for this module *)
        let fq_path = String.concat "." (List.rev !St.namespace_stack) in
        let name = lskips_t_to_output name in
        let body = Fun.protect ~finally:(fun () ->
          St.namespace_stack := (match !St.namespace_stack with _ :: tl -> tl | [] -> [])
        ) (fun () -> callback defs) in
          (* In Lem, module contents are implicitly available after the module
             definition. Lean namespaces are not — we need an explicit 'open'.
             For top-level modules, emit 'open' directly plus any deferred
             opens from nested modules. For nested modules, defer the open
             since Lean's 'open' inside a namespace is scoped to that block. *)
          let is_top_level = !St.namespace_stack = [] in
          if is_top_level then
            let deferred = !St.deferred_opens in
            St.deferred_opens := [];
            let deferred_opens = flat @@ List.map (fun p ->
              from_string (String.concat "" ["\nopen "; p])
            ) deferred in
            Output.flat [
              ws skips; from_string "namespace "; name; ws skips'; ws skips'';
              body; from_string "\nend "; name;
              from_string "\nopen "; name; deferred_opens; ws skips'''
            ]
          else begin
            St.deferred_opens := fq_path :: !St.deferred_opens;
            Output.flat [
              ws skips; from_string "namespace "; name; ws skips'; ws skips'';
              body; from_string "\nend "; name;
              from_string "\nopen "; name; ws skips'''
            ]
          end
      | Rename (skips, name, mod_binding, skips', mod_descr) -> emp  (* Module renames not applicable in Lean *)
      | OpenImport (oi, ms) ->
          let (ms', sk) = B.open_to_open_target ms in
          if (ms' = []) then
             ws (oi_get_lskip oi)
          else (
            let d' = OpenImportTarget(oi, Targets_opt_none, ms') in
            def inside_instance callback inside_module d' ^ ws sk
          )
      | OpenImportTarget(oi, _, []) -> ws (oi_get_lskip oi)
      | OpenImportTarget (Ast.OI_open skips, targets, mod_descrs) ->
          ws skips ^
          let is_user_module = not (is_library_module !St.current_module_name) in
          let handle_mod (sk, md) =
            (if not (List.mem md !St.local_modules) then
              St.collected_imports := md :: !St.collected_imports);
            (* Emit 'open' for:
               - Local modules (defined in this file via Module) — they create namespaces
               - Library modules in library context — they have Lem_X namespaces
               User modules from other files have no namespace; import alone suffices.
               In non-library (user) modules, skip inline opens for library imports —
               transitive_opens will emit them for both main and auxiliary files. *)
            if List.mem md !St.local_modules then
              Output.flat [
                from_string "open"; ws sk; from_string md; from_string "\n"
              ]
            else if not (is_library_module md) then emp
            else if is_user_module then emp
            else
              let ns = lean_ns_name md in
              Output.flat [
                from_string "open"; ws sk; from_string ns; from_string "\n"
              ]
          in
          if (not (in_target targets)) then emp else Output.flat (List.map handle_mod mod_descrs)
      | OpenImportTarget _ ->
          (* Unreachable: def_trans converts all OI variants to OI_open *)
          raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: unexpected non-OI_open OpenImportTarget")
      | Indreln (skips, targets, names, cs) ->
          if in_target targets then
            let c = Seplist.to_list cs in
              clauses inside_instance c
          else
            ws skips ^ from_string "\n/- removed inductive relation intended for another target -/"
      | Val_spec val_spec -> from_string "\n/- removed value specification -/\n"
      | Class (Ast.Class_inline_decl (skips, _), _, _, _, _,_, _, _) -> ws skips
      | Class (Ast.Class_decl skips, skips', (name, l), tv, p, skips'', body, skips''') ->
          let name_str = Name.to_string (B.class_path_to_name p) in
          St.auxiliary_opens := lean_qualified_name name_str :: !St.auxiliary_opens;
          let name = from_string name_str in
          let tv_kind = tnvar_kind tv in
          let tv = from_string (tnvar_to_string tv) in
          let method_names = ref [] in
          let body_entries =
            List.filter_map (fun (skips, targets_opt, (name, l), const_descr_ref, ascii_rep_opt, skips', src_t) ->
              if in_target targets_opt then
                let name' = B.const_ref_to_name name true const_descr_ref in
                let name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip name')) in
                  method_names := name_str :: !method_names;
                  Some (Output.flat [
                    ws skips; from_string name_str; from_string " :"; ws skips'; pat_typ src_t
                  ])
              else
                None
            ) body
          in
          let body_out = Output.concat (from_string "\n") body_entries in
          (* If the class has an isEqual method (i.e., this is Lem's Eq class),
             emit a BEq bridge instance so that == works wherever [Eq0 a] is available.
             This is needed because isEqual is mapped to == (BEq) in Lean. *)
          let has_isEqual = List.exists (fun (_, _, (mn, _), cref, _, _, _) ->
            (* Check if any method has target_rep mapped to == (BEq).
               The method's original name might be = with isEqual as alternative,
               so check the const_descr for the Lean target rep. *)
            let cd = c_env_lookup Ast.Unknown A.env.c_env cref in
            match Target.Targetmap.apply_target cd.target_rep
                    (Target.Target_no_ident Target.Target_lean) with
            | Some (CR_infix(_, _, _, op_id)) ->
                Ident.to_string op_id = "=="
            | _ -> false
          ) body in
          (* Check if the class has a comparison method (returns LemOrdering).
             Known: setElemCompare (SetType), mapKeyCompare (MapKeyType).
             If so, derive BEq from the comparison function. *)
          let compare_method_names = ["setElemCompare"; "mapKeyCompare"] in
          let compare_method = List.find_opt (fun n ->
            List.mem n compare_method_names
          ) (List.rev !method_names) in
          let beq_bridge =
            if has_isEqual then
              Output.flat [
                from_string "\ninstance {"; tv; from_string " : "; from_string tv_kind;
                from_string "} ["; name; from_string " "; tv; from_string "] : BEq "; tv;
                from_string " where\n  beq := isEqual\n"
              ]
            else match compare_method with
            | Some cmp_name ->
              Output.flat [
                from_string "\ninstance {"; tv; from_string " : "; from_string tv_kind;
                from_string "} ["; name; from_string " "; tv; from_string "] : BEq "; tv;
                from_string (String.concat "" [" where\n  beq x y := match "; cmp_name; " x y with | .EQ => true | _ => false\n"])
              ]
            | None -> emp
          in
          (* Export class methods so they are visible to importing files.
             Skip names that clash with Lean stdlib globals — a clash here
             causes a Lean compile error (ambiguous name), not silent failure.
             Review this list when upgrading the Lean toolchain. *)
          let lean_global_names = ["max"; "min"; "compare"] in
          let exportable = List.filter (fun n ->
            not (List.mem n lean_global_names)
          ) (List.rev !method_names) in
          let class_export =
            if exportable = [] then
              Output.flat [from_string "\nopen "; name; from_string "\n"]
            else begin
              let names_str = String.concat "" ["("; String.concat " " exportable; ")"] in
              Output.flat [
                from_string "\nexport "; name; from_string " "; from_string names_str; from_string "\n"
              ]
            end
          in
          Output.flat [
            ws skips; from_string "class"; ws skips'; name; from_string " ("; tv; from_string " : "; from_string tv_kind; from_string ") where"
          ; ws skips''; from_string "\n"; body_out
          ; ws skips'''; from_string "\n"; class_export
          ; beq_bridge
          ]
      | Instance ((Ast.Inst_default skips | Ast.Inst_decl skips) as inst_kind, i_ref, inst, vals, skips') ->
        let is_default = match inst_kind with Ast.Inst_default _ -> true | _ -> false in
        (* Filter out instance methods whose corresponding class methods
           are not visible for the Lean target *)
        let instance_info = Types.i_env_lookup Ast.Unknown A.env.i_env i_ref in
        let class_method_visible (inst_cd_ref : Types.const_descr_ref) : bool =
          let found = List.filter (fun (_, inst_ref) -> inst_ref = inst_cd_ref) instance_info.inst_methods in
          match found with
          | (class_ref, _) :: _ ->
            let class_cd = c_env_lookup Ast.Unknown A.env.c_env class_ref in
            Typed_ast.in_target_set (Target.Target_no_ident Target.Target_lean) class_cd.const_targets
          | [] ->
            raise (Reporting_basic.err_general true Ast.Unknown
              "Lean backend: instance method has no corresponding class method in inst_methods")
        in
        let val_is_visible (d : Typed_ast.val_def) : bool =
          match d with
          | Let_def (_, _, (_, name_map, _, _, _)) ->
            List.for_all (fun (_, cd_ref) -> class_method_visible cd_ref) name_map
          | Fun_def (_, _, _, funcl_sep) ->
            Seplist.for_all (fun ({term = _}, c, _, _, _, _) -> class_method_visible c) funcl_sep
          | Let_inline _ ->
            raise (Reporting_basic.err_general true Ast.Unknown
              "Lean backend: unexpected Let_inline in instance body")
        in
        let vals = List.filter val_is_visible vals in
          let prefix =
            match inst with
              | (constraint_prefix_opt, skips, ident, path, src_t, skips') ->
                let tnvar_list_opt, tyvars, c =
                  begin
                  match constraint_prefix_opt with
                    | None -> None, emp, emp
                    | Some c ->
                      begin
                      match c with
                        | Cp_forall (skips, tnvar_list, skips', constraints_opt) ->
                            let tnvars =
                              Output.concat (from_string " ") (List.map (fun t ->
                                match t with
                                  | Typed_ast.Tn_A (_, var, _) ->
                                      from_string @@ Ulib.Text.to_string var
                                  | Typed_ast.Tn_N (_, var, _) ->
                                      from_string @@ Ulib.Text.to_string var
                              ) tnvar_list)
                            in
                            (* Use fully qualified paths from the type system
                               rather than parsing unqualified Idents from the AST.
                               The Cs_list Idents may be unqualified (e.g., "Eq"
                               instead of "Basic_classes.Eq"), which fails to look
                               up in t_env for class renaming. *)
                            let cs =
                              Output.concat (from_string " ") (List.map (fun (cpath, tnvar) ->
                                let class_name = B.class_path_to_name cpath in
                                let var = from_string @@ Ulib.Text.to_string @@ Types.tnvar_to_rope tnvar in
                                Output.flat [
                                  from_string "["; from_string (Name.to_string class_name);
                                  from_string " "; var; from_string "]"
                                ]
                              ) instance_info.Types.inst_constraints)
                            in
                            (* Add extra constraints from TYR_subst type target reps *)
                            let extra_tyr = extra_constraints_for_tyr_subst instance_info.Types.inst_type in
                            let new_extras = filter_new_tyr_constraints extra_tyr instance_info.Types.inst_constraints in
                            let cs = cs ^ format_tyr_constraints new_extras in
                            (* Add Lean-native constraints for default instances *)
                            let cs =
                              if is_default then
                                let target_class = Name.to_string (B.class_path_to_name path) in
                                let extra_classes = lean_default_instance_extra_constraints target_class in
                                let pairs = List.concat_map (fun cls ->
                                  List.filter_map (fun t ->
                                    match t with
                                    | Typed_ast.Tn_A (_, var, _) ->
                                      Some (cls, Ulib.Text.to_string var)
                                    | _ -> None
                                  ) tnvar_list
                                ) extra_classes in
                                cs ^ format_tyr_constraints pairs
                              else cs
                            in
                              Some tnvar_list, tnvars, cs
                      end
                  end
                in
                let id = from_string (Name.to_string (B.class_path_to_name path)) in
                let tyvars_typeset =
                  if tyvars = emp then
                    emp
                  else
                    match tnvar_list_opt with
                    | Some tnvar_list ->
                      let has_nvar = List.exists (fun t ->
                        match t with Typed_ast.Tn_N _ -> true | _ -> false) tnvar_list in
                      if has_nvar then
                        Output.concat (from_string " ") (List.map (fun t ->
                          match t with
                            | Typed_ast.Tn_A (_, var, _) ->
                              Output.flat [from_string "("; from_string @@ Ulib.Text.to_string var; from_string " : Type)"]
                            | Typed_ast.Tn_N (_, var, _) ->
                              Output.flat [from_string "("; from_string @@ Ulib.Text.to_string var; from_string " : Nat)"]
                        ) tnvar_list)
                      else
                        Output.flat [
                          from_string "("; tyvars; from_string " : Type)"
                        ]
                    | None ->
                      Output.flat [
                        from_string "("; tyvars; from_string " : Type)"
                      ]
                in
                  (* Wrap the class type argument in parens if it's a type application
                     (e.g., mem_constraint a → (mem_constraint a)). Without this,
                     Lean parses 'Constraints mem_constraint a' as two arguments. *)
                  let type_arg = match src_t.term with
                    | Typ_app (_, _ :: _) ->
                      Output.flat [from_string " ("; pat_typ src_t; from_string ")"]
                    | _ -> pat_typ src_t
                  in
                  Output.flat [
                    ws skips; tyvars_typeset; from_string " "; c; from_string " : "; id
                  ; type_arg
                  ]
          in
          let body =
            Output.concat (from_string "\n") (List.map (fun d -> val_def true (Some i_ref) false true d Types.TNset.empty []) vals)
          in
            let inst_kw = if is_default
              then from_string "instance (priority := low)"
              else from_string "instance" in
            Output.flat [
              ws skips; inst_kw; prefix; from_string " where";
              from_string "\n"; body;
              ws skips'
            ]
      | Comment c ->
        let ((def_aux, skips_opt), l, lenv) = c in
        let skips = match skips_opt with None -> from_string "\n" | Some s -> ws s in
        (* Check if this is a Type_def with a TYR_subst target rep for Lean.
           If so, emit an abbrev definition instead of just a block comment.
           This enables parameterized type mappings like mword 'a → BitVec (Size.size a). *)
        let abbrev_for_target_rep = match def_aux with
          | Type_def (_, sl) when Seplist.length sl = 1 ->
            let ((n0, _), tyvars, t_path, _, _) = Seplist.hd sl in
            let td = Types.type_defs_lookup l A.env.t_env t_path in
            begin match Target.Targetmap.apply_target td.Types.type_target_rep
                    (Target.Target_no_ident Target.Target_lean) with
            | Some (Types.TYR_subst (_, _, _, rhs_t)) ->
              let name = B.type_path_to_name n0 t_path in
              let name_out = Name.to_output (Type_ctor (false, false)) name in
              let tyvars_out = type_def_type_variables tyvars in
              let rhs_out = pat_typ rhs_t in
              let class_constraints = collect_class_constraints_from_src_t rhs_t in
              let constraints_out = Output.flat (List.map (fun (cls, tv) ->
                Output.flat [from_string "["; from_string cls; from_string " "; from_string tv; from_string "] "]
              ) class_constraints) in
              Some (Output.flat [
                from_string "\nabbrev "; name_out; from_string " "; tyvars_out;
                constraints_out;
                from_string " := "; rhs_out; from_string "\n"
              ])
            | _ -> None
            end
          | _ -> None
        in
        let comment =
          let saved = !St.rendering_comment in
          St.rendering_comment := true;
          Fun.protect ~finally:(fun () -> St.rendering_comment := saved) @@ fun () ->
          Output.flat [
            skips; from_string "/- "; def inside_instance callback inside_module def_aux; from_string " -/"
          ] in
        begin match abbrev_for_target_rep with
        | Some abbrev_out ->
          St.pending_abbrevs := abbrev_out :: !St.pending_abbrevs;
          comment
        | None -> comment
        end
      | Declaration (Decl_extra_import (_, _, _, _, mod_name)) ->
          (* Add user-requested import to this file's import list *)
          if not (List.mem mod_name !St.collected_imports) then
            St.collected_imports := mod_name :: !St.collected_imports;
          emp
      | Declaration _ -> emp  (* Other declarations processed earlier *)
      | Lemma _ -> emp  (* Lemmas are handled by def_extra, not def *)
    and val_def inside_instance i_ref_opt is_recursive try_term def tv_set class_constraints =
      begin
        let constraints =
          let body =
            Output.concat (from_string " ") (List.map (fun (path, tnvar) ->
              let name = from_string (Name.to_string (B.class_path_to_name path)) in
              let var = from_string @@ Ulib.Text.to_string @@ Types.tnvar_to_rope tnvar
              in
                Output.flat [
                  from_string "["; name; from_string " "; var; from_string "]"
                ]
            ) class_constraints)
          in
          (* Collect extra constraints introduced by TYR_subst type target reps.
             For example, mword 'a → BitVec (@Size.size 'a _) introduces [Size 'a].
             Skip when inside_instance — the instance header already has the constraint. *)
          let extra_tyr = if inside_instance then [] else
            let l_unk = Ast.Trans (true, "lean_tyr_extra", None) in
            let cs = match def with
              | Let_def(_, _, (_, nm, _, _, _)) -> List.map snd nm
              | Let_inline(_,_,_,_,c,_,_,_) -> [c]
              | Fun_def(_, _, _, funs) ->
                Seplist.to_list_map (fun ((_, c, _, _, _, _):funcl_aux) -> c) funs
            in
            let cds = List.map (c_env_lookup l_unk A.env.c_env) cs in
            let extras = List.concat_map (fun cd ->
              extra_constraints_for_tyr_subst cd.const_type
            ) cds in
            filter_new_tyr_constraints extras class_constraints
          in
          if List.length class_constraints = 0 && extra_tyr = [] then
            emp
          else
            body ^ format_tyr_constraints extra_tyr
        in
        match def with
          | Let_def (skips, targets, (p, name_map, topt, sk, e)) ->
              if in_target targets then
                (* Lean doesn't support destructuring in 'def' bindings.
                   Emit one def per bound name: def x : T := let PAT := EXPR; x *)
                let pat_out = def_pattern p in
                let exp_out = exp inside_instance e in
                let type_out = match topt with
                  | None -> emp
                  | Some (_, t) -> Output.flat [from_string " :"; pat_typ t]
                in
                let effectful_attr =
                  if (not inside_instance) && exp_contains_effectful e
                  then from_string "@[never_extract, noinline] " else emp in
                let let_lifted =
                  let lifted = List.exists (fun (_, cref) ->
                      Types.Cdset.mem cref !St.reader_lifted) name_map in
                  if exp_needs_reader e && inside_instance then
                    raise (Reporting_basic.err_general true Ast.Unknown
                      "Lean backend: reader-lifted call inside an instance method (unsupported: instance fields cannot take extra parameters)");
                  lifted && not inside_instance in
                let saved_reader_binder = !St.reader_binder in
                St.reader_binder := let_lifted;
                Fun.protect ~finally:(fun () -> St.reader_binder := saved_reader_binder) @@ fun () ->
                let defs = List.map (fun (_orig_name, cref) ->
                  let cd = c_env_lookup Ast.Unknown A.env.c_env cref in
                  let (_, renamed, _) = Typed_ast_syntax.constant_descr_to_name
                    (Target.Target_no_ident Target.Target_lean) cd in
                  let name_str = Name.to_string renamed in
                  let var_type = pat_typ (C.t_to_src_t cd.const_type) in
                  let defn = if inside_instance then emp else from_string "def " in
                  (* Arc-8 S2: [Inhabited tv] binders for a threaded
                     Let_def-bound constant. *)
                  let thread_out =
                    if inside_instance then emp
                    else match lean_thread_lookup cref with
                      | Some (_, ns) ->
                        Output.flat (List.map (fun n ->
                            Output.flat [from_string " [Inhabited "; from_string n; from_string "]"]) ns)
                      | None -> emp in
                  Output.flat [
                    from_string "\n"; effectful_attr; defn; from_string name_str;
                    reader_binder_output (); constraints; thread_out;
                    from_string "  : "; var_type;
                    from_string " :=\n  let "; pat_out; type_out;
                    ws sk; from_string " :="; exp_out;
                    from_string "\n  "; from_string name_str
                  ]
                ) name_map in
                Output.flat (ws skips :: defs)
              else
                ws skips ^ from_string "/- removed value definition intended for another target -/"
          | Fun_def (skips, rec_flag, targets, funcl_skips_seplist) ->
              if in_target targets then
                let skips' = match rec_flag with FR_non_rec -> None | FR_rec sk -> sk in
                let funcls = Seplist.to_list funcl_skips_seplist in
                (* Group clauses by function name, preserving definition order.
                   Lem allows interleaving, but Lean's equation compiler requires
                   all clauses for a function in sequence. Multi-clause groups
                   render as Lean 4 pattern-matching equations. *)
                let get_name ({term = n}, _, _, _, _, _) = Name.to_string (Name.strip_lskip n) in
                let groups =
                  let order = ref [] in
                  let tbl = Hashtbl.create 8 in
                  List.iter (fun fcl ->
                    let key = get_name fcl in
                    (if not (Hashtbl.mem tbl key) then
                      order := key :: !order);
                    let existing = match Hashtbl.find_opt tbl key with Some v -> v | None -> [] in
                    Hashtbl.replace tbl key (existing @ [fcl])
                  ) funcls;
                  List.map (fun key -> Hashtbl.find tbl key) (List.rev !order)
                in
                let num_functions = List.length groups in
                (* Acyclic de-mutualization (arc 3): a 'let rec ... and ...'
                   block whose call graph is a DAG (ignoring self-loops) is
                   emitted as SEQUENTIAL defs in dependency order — Lean's
                   'mutual' is reserved for genuine cycles. Lem sources use
                   rec-and chains freely for non-mutual defs; keeping them
                   mutual both blocks per-member termination handling and
                   forces fuel onto members that are not even recursive. *)
                let group_cref g = match g with
                  | (_, c, _, _, _, _) :: _ -> Some c
                  | [] -> None in
                let group_used g =
                  List.fold_left (fun acc (_, _, _, _, _, e) ->
                      let ue = add_exp_entities empty_used_entities e in
                      ue.used_consts @ acc) [] g in
                let group_self_recursive g = match group_cref g with
                  | Some c -> List.mem c (group_used g)
                  | None -> false in
                let demutualized =
                  if num_functions <= 1 then None
                  else begin
                    let arr = Array.of_list groups in
                    let n = Array.length arr in
                    let uses = Array.map group_used arr in
                    let dep i j =
                      i <> j
                      && (match group_cref arr.(j) with
                          | Some cj -> List.mem cj uses.(i)
                          | None -> false) in
                    (* Kahn's algorithm, stable: each round emits (in
                       original order) every def whose dependencies are all
                       emitted. No progress with nodes left = a cycle. *)
                    let emitted = Array.make n false in
                    let result = ref [] in
                    let count = ref 0 in
                    let progress = ref true in
                    while !count < n && !progress do
                      progress := false;
                      for i = 0 to n - 1 do
                        if not emitted.(i) then begin
                          let ready = ref true in
                          for j = 0 to n - 1 do
                            if (not emitted.(j)) && dep i j then ready := false
                          done;
                          if !ready then begin
                            emitted.(i) <- true;
                            result := arr.(i) :: !result;
                            incr count;
                            progress := true
                          end
                        end
                      done
                    done;
                    if !count = n then Some (List.rev !result) else None
                  end in
                let groups, is_truly_mutual = match demutualized with
                  | Some sorted -> sorted, false
                  | None -> groups, num_functions > 1 in
                let auto_term_for g = match group_cref g with
                  | Some c ->
                    let cd = c_env_lookup Ast.Unknown A.env.c_env c in
                    (match Target.Targetmap.apply_target cd.termination_setting
                             (Target.Target_no_ident Target.Target_lean) with
                     | Some (Ast.Termination_setting_automatic _) -> true
                     | _ -> false)
                  | None -> false in
                let def_keyword_for g =
                  if inside_instance then emp
                  else if demutualized <> None then
                    (* de-mutualized member: keyword by ITS OWN recursion
                       and ITS OWN termination declare *)
                    (if group_self_recursive g && not (auto_term_for g) then
                       from_string "partial def"
                     else from_string "def")
                  else if is_recursive && not try_term then
                    from_string "partial def"
                  else
                    from_string "def"
                in
                (* Defs containing effectful call sites need
                   @[never_extract, noinline] — see exp_contains_effectful. *)
                let attr_for group =
                  if (not inside_instance)
                     && List.exists (fun (_, _, _, _, _, e) ->
                            exp_contains_effectful e) group
                  then from_string "@[never_extract, noinline] " else emp
                in
                (* Reader lifting: the lifted set is computed by the module
                   pre-pass (see lean_reader_prepass); emission just consults
                   membership. Instance fields cannot take extra parameters:
                   fail closed if an instance method needs the reader. *)
                let register_group group =
                  let lifted = List.exists (fun (_, c, _, _, _, _) ->
                      Types.Cdset.mem c !St.reader_lifted) group in
                  let needs = List.exists (fun (_, _, _, _, _, e) ->
                      exp_needs_reader e) group in
                  if needs && inside_instance then
                    raise (Reporting_basic.err_general true Ast.Unknown
                      "Lean backend: reader-lifted call inside an instance method (unsupported: instance fields cannot take extra parameters)");
                  lifted && not inside_instance
                in
                let render_group group =
                  match group with
                  | [] -> emp
                  | [single_clause] ->
                    (* Single clause: render as before *)
                    funcl inside_instance i_ref_opt constraints tv_set single_clause
                  | first_clause :: rest_clauses ->
                    (* Multi-clause: use Lean 4 equation compiler syntax *)
                    let ({term = n}, c, pats, typ_opt, _skips, _e) = first_clause in
                    let n = B.const_ref_to_name n true c in
                    let name_skips = Name.get_lskip n in
                    let name = from_string (Name.to_string (Name.strip_lskip n)) in
                    (* Get the full type from the const_descr *)
                    let cd = c_env_lookup Ast.Unknown A.env.c_env c in
                    let full_type = pat_typ (C.t_to_src_t cd.const_type) in
                    let tv_set_out =
                      if inside_instance then emp
                      else
                        let tv = Types.free_vars cd.const_type in
                        if Types.TNset.cardinal tv = 0 then emp
                        else Output.flat [from_string " "; let_type_variables true tv]
                    in
                    let constraints_sep =
                      if constraints = emp then emp else from_string " "
                    in
                    (* Render each clause as | pat1, pat2, ... => body *)
                    let render_equation ({term = _}, _, pats, _, skips, e) =
                      let pat_out = concat_str ", " (List.map def_pattern pats) in
                      let body =
                        if needs_parens (C.exp_to_term e) then
                          Output.flat [from_string "("; exp inside_instance e; from_string ")"]
                        else exp inside_instance e
                      in
                      flatten_newlines (Output.flat [
                        from_string "\n  | "; pat_out; from_string " =>"; ws skips; from_string " "; body
                      ])
                    in
                    let equations = Output.flat (List.map render_equation (first_clause :: rest_clauses)) in
                    Output.flat [
                      ws name_skips; from_string " "; name; tv_set_out; constraints_sep; constraints;
                      inhabited_binder_output (); reader_binder_output ();
                      from_string " : "; full_type; equations
                    ]
                in
                (* Block-level fuel plan (arc 3, B2): every fuel'd def of
                   this block, so cross-member calls inside a fuel'd mutual
                   block rewrite to '(worker lemFuel)' — each hop passes the
                   decremented binder and Lean sees mutual structural
                   recursion on fuel. All-or-none per mutual block: a
                   non-fuel'd member calling a fuel'd sibling would use the
                   wrapper and reset the fuel, defeating termination. *)
                let fuel_plan =
                  List.filter_map (function
                    | [({term = n}, c, _, _, _, _)] when fuel_sentinel_for c <> None ->
                        let base = Name.to_string (Name.strip_lskip (B.const_ref_to_name n true c)) in
                        Some (c, String.concat "" [base; "_lemFuel"])
                    | (({term = _}, c, _, _, _, _) :: _ :: _) when fuel_sentinel_for c <> None ->
                        raise (Reporting_basic.err_general true Ast.Unknown
                          "Lean backend: 'declare {lean} fuel val' on a multi-clause definition (unsupported)")
                    | _ -> None) groups in
                if is_truly_mutual && fuel_plan <> []
                   && List.length fuel_plan <> List.length groups then
                  raise (Reporting_basic.err_general true Ast.Unknown
                    "Lean backend: fuel in a mutual block requires EVERY member to carry a 'declare {lean} fuel val' (all-or-none)");
                let saved_plan = !St.fuel_workers in
                St.fuel_workers := fuel_plan;
                Fun.protect ~finally:(fun () -> St.fuel_workers := saved_plan) @@ fun () ->
                let bodies = List.map (fun g ->
                    (* Fuel emission (declare {lean} fuel val): single-clause,
                       non-mutual, non-instance, not reader-lifted (extend on
                       need — fail closed on every unsupported combination). *)
                    let fuel_info = match g with
                      | [({term = n}, c, _, _, _, _)] ->
                          (match fuel_sentinel_for c with
                           | Some s -> Some (n, c, s)
                           | None -> None)
                      | (({term = _}, c, _, _, _, _) :: _) ->
                          (match fuel_sentinel_for c with
                           | Some _ ->
                             raise (Reporting_basic.err_general true Ast.Unknown
                               "Lean backend: 'declare {lean} fuel val' on a multi-clause definition (unsupported)")
                           | None -> None)
                      | [] -> None in
                    (* reader_seed defs: not lifted; their first argument
                       becomes the injection value for the body. Fail
                       closed on every unsupported combination. *)
                    let seed_info = match g with
                      | [(_, c, pats, _, _, _)] when is_seed_cref c ->
                          (match pats with
                           | p :: _ ->
                             (match p.term with
                              | P_var n | P_var_annot (n, _) ->
                                Some (Name.to_string (Name.strip_lskip n))
                              | _ ->
                                raise (Reporting_basic.err_general true Ast.Unknown
                                  "Lean backend: reader_seed def's first argument must be a simple variable"))
                           | [] ->
                             raise (Reporting_basic.err_general true Ast.Unknown
                               "Lean backend: reader_seed def must take the seed as its first argument"))
                      | (( _, c, _, _, _, _) :: _) when is_seed_cref c ->
                          raise (Reporting_basic.err_general true Ast.Unknown
                            "Lean backend: reader_seed on a multi-clause or mutual definition (unsupported)")
                      | _ -> None in
                    (match seed_info with
                     | Some _ when List.length (get_reader_params ()) <> 1 ->
                       (* The seed name overrides EVERY injected reader
                          parameter — with more than one reader that would
                          silently conflate them (audit finding). *)
                       raise (Reporting_basic.err_general true Ast.Unknown
                         "Lean backend: reader_seed requires exactly one declared reader")
                     | Some _ when is_truly_mutual ->
                       raise (Reporting_basic.err_general true Ast.Unknown
                         "Lean backend: reader_seed in a mutual block (unsupported; the mutual partner would escape lifting)")
                     | Some _ when inside_instance ->
                       raise (Reporting_basic.err_general true Ast.Unknown
                         "Lean backend: reader_seed inside an instance (unsupported)")
                     | Some _ when fuel_info <> None ->
                       raise (Reporting_basic.err_general true Ast.Unknown
                         "Lean backend: reader_seed combined with fuel (unsupported)")
                     | _ -> ());
                    let lifted = register_group g in
                    (match seed_info with
                     | Some _ when lifted ->
                       raise (Reporting_basic.err_general true Ast.Unknown
                         "Lean backend: reader_seed def unexpectedly reader-lifted")
                     | _ -> ());
                    let saved_seed = !St.reader_seed_param in
                    St.reader_seed_param := seed_info;
                    Fun.protect ~finally:(fun () -> St.reader_seed_param := saved_seed) @@ fun () ->
                    (match fuel_info with
                     | Some _ when inside_instance ->
                       raise (Reporting_basic.err_general true Ast.Unknown
                         "Lean backend: 'declare {lean} fuel val' inside an instance (unsupported)")
                     | Some _ when is_truly_mutual && lifted ->
                       raise (Reporting_basic.err_general true Ast.Unknown
                         "Lean backend: 'declare {lean} fuel val' in a mutual block combined with reader lifting (unsupported; extend when needed)")
                     | _ -> ());
                    (* fuel x reader composes (arc 3, B1): the worker's fuel
                       binder is emitted BEFORE the reader binders, so the
                       point-free wrapper 'worker lemDefaultFuel' has the
                       reader-prefixed type and lifted callers inject into
                       the wrapper as for any lifted def. *)
                    (* Arc-8 S2: [Inhabited tv] binders for this group,
                       from the threading pre-pass (instance methods are
                       never threaded — the pre-pass guard errors first). *)
                    let thread_names =
                      if inside_instance then []
                      else match group_cref g with
                        | Some c -> (match lean_thread_lookup c with
                            | Some (_, ns) -> ns
                            | None -> [])
                        | None -> [] in
                    let saved_inh = !St.inhabited_binder in
                    St.inhabited_binder := thread_names;
                    Fun.protect ~finally:(fun () -> St.inhabited_binder := saved_inh) @@ fun () ->
                    match fuel_info with
                    | None ->
                      let saved = !St.reader_binder in
                      St.reader_binder := lifted;
                      Fun.protect ~finally:(fun () -> St.reader_binder := saved)
                        (fun () -> (attr_for g, def_keyword_for g, render_group g, emp))
                    | Some (n, c, s) ->
                      let base_name = Name.to_string (Name.strip_lskip (B.const_ref_to_name n true c)) in
                      let worker = String.concat "" [base_name; "_lemFuel"] in
                      let cd = c_env_lookup Ast.Unknown A.env.c_env c in
                      let tv = Types.free_vars cd.const_type in
                      let tv_out =
                        if Types.TNset.cardinal tv = 0 then emp
                        else Output.flat [from_string " "; let_type_variables true tv] in
                      let saved_e = !St.fuel_emit in
                      let saved_rb = !St.reader_binder in
                      St.fuel_emit := Some s;
                      St.reader_binder := lifted;
                      (* worker name must agree with the block-level plan *)
                      assert (List.assoc_opt c !St.fuel_workers = Some worker);
                      Fun.protect ~finally:(fun () ->
                          St.fuel_emit := saved_e;
                          St.reader_binder := saved_rb)
                        (fun () ->
                          let body = render_group g in
                          (* Point-free wrapper at the default fuel: call sites
                             are unchanged, and proofs unfold wrapper → worker
                             definitionally. *)
                          (* The wrapper must carry the same never_extract
                             protection as the worker when the def contains
                             effectful calls: callers reference the WRAPPER,
                             and an unattributed wrapper would reopen the
                             closed-term-extraction hazard one level up
                             (audit finding, 2026-08-18). *)
                          (* A lifted worker's wrapper has the reader-prefixed
                             type (arc 3, B1): reader binders sit between the
                             fuel binder and the original arguments, so
                             'worker lemDefaultFuel' is reader-first. *)
                          let reader_arrows =
                            if not lifted then emp else
                            Output.flat (List.map (fun (cref, _) ->
                                Output.flat [from_string "(";
                                             pat_typ (C.t_to_src_t (reader_value_typ cref));
                                             from_string ") -> "])
                              (get_reader_params ())) in
                          (* class-constraint binders must be re-emitted on
                             the wrapper too (arc-3 batch D: [Eq0 a]-style
                             constrained defs failed to elaborate) *)
                          let cons_out =
                            if constraints = emp then emp
                            else Output.flat [from_string " "; constraints] in
                          let wrapper = Output.flat [
                            from_string "\n\n"; attr_for g;
                            from_string "def "; from_string base_name; tv_out; cons_out;
                            inhabited_binder_output ();
                            from_string " : "; reader_arrows;
                            pat_typ (C.t_to_src_t cd.const_type);
                            from_string " := "; from_string worker;
                            from_string " lemDefaultFuel\n"] in
                          (* Wrapper is returned separately: in a mutual
                             block it must be emitted AFTER 'end', or it
                             would join the recursion set (arc 3, B2). *)
                          (attr_for g, from_string "def", body, wrapper))
                  ) groups in
                let rec_skips =
                  if is_recursive && not inside_instance then
                    ws skips'
                  else emp
                in
                if is_truly_mutual then
                  Output.flat [
                    ws skips; from_string "mutual\n"; rec_skips;
                    concat_str "\n" (List.map (fun (a, k, b, _) -> Output.flat [a; k; b]) bodies);
                    from_string "\nend";
                    (* fuel wrappers of a mutual block, after 'end' *)
                    Output.flat (List.map (fun (_, _, _, w) -> w) bodies)
                  ]
                else
                  (* de-mutualized members need explicit separation: an
                     and-member's leading skips carry no newline *)
                  let sep = if demutualized <> None then from_string "\n" else emp in
                  Output.flat [
                    ws skips; rec_skips;
                    Output.flat (List.map (fun (a, k, b, w) ->
                        Output.flat [sep; a; k; b; w]) bodies)
                  ]
              else
                from_string "\n/- removed recursive definition intended for another target -/"
          | Let_inline (skips, _, _, _, _, _, _, _) ->
              (* Let_inline declarations are inlined at use sites during compilation.
                 The backend emits nothing — the definition body appears inline. *)
              ws skips
      end
    (* Inductive relation (indreln) rendering. Phases:
       1. Gather unique relation names with their const_descr_refs
       2. Set St.indreln_params so exp can insert type parameters for
          polymorphic self-references in premises
       3. Build inductive definitions using renamed names from const_descr
          (handles cross-module collisions like thread_trans → thread_trans0)
       4. Render clauses with St.prop_equality set so antecedents use
          propositional = instead of BEq ==
       St.indreln_params is saved/restored so nested indreln blocks don't
       clobber the outer scope. *)
    and clauses (inside_instance: bool) clause_list =
      (* Gather unique relation names from clauses, paired with their
         const_descr_ref so we can look up the renamed name for output *)
      let gather_names clause_list =
        let rec gather_names_aux buffer clauses =
          match clauses with
            | []    -> buffer
            | (Rule(_,_, _, _, _, _, _, name_lskips_annot, c, _),_)::xs ->
              let name = name_lskips_annot.term in
              let name = Name.strip_lskip name in
              if List.exists (fun (n, _) -> Stdlib.compare n name = 0) buffer then
                gather_names_aux buffer xs
              else
                gather_names_aux ((name, c)::buffer) xs
        in
          gather_names_aux [] clause_list
      in
      let gathered = gather_names clause_list in
      (* For polymorphic indreln: compute type parameter names per relation
         and set St.indreln_params so exp can insert them in premises. *)
      let saved_indreln_params = !St.indreln_params in
      St.indreln_params := List.filter_map (fun (_name, c_ref) ->
        let cd = c_env_lookup Ast.Unknown A.env.c_env c_ref in
        let tvs = Types.free_vars cd.const_type in
        if Types.TNset.cardinal tvs = 0 then None
        else
          let params_str = String.concat " " @@
            List.map (fun v -> Name.to_string (Types.tnvar_to_name v))
              (Types.TNset.elements tvs) in
          Some (c_ref, params_str)
      ) gathered;
      Fun.protect ~finally:(fun () -> St.indreln_params := saved_indreln_params) (fun () ->
      let compare_clauses_by_name name (Rule(_,_, _, _, _, _, _, name', _, _),_) =
        let name' = name'.term in
        let name' = Name.strip_lskip name' in
          Stdlib.compare name name' = 0
      in
      let indrelns =
        List.map (fun (name, c_ref) ->
          (* Use the renamed name from the constant descriptor, not the raw AST name.
             This handles cross-module collisions (e.g., indreln "thread_trans"
             renamed to "thread_trans0" to avoid conflict with imported type). *)
          let c_descr = c_env_lookup Ast.Unknown A.env.c_env c_ref in
          let (_, renamed_name, _) = Typed_ast_syntax.constant_descr_to_name (Target.Target_no_ident Target.Target_lean) c_descr in
          let name_string = Name.to_string renamed_name in
          let matching_clauses = List.filter (compare_clauses_by_name name) clause_list in
          let index_type_parts =
            match matching_clauses with
              | [] -> [from_string "Prop"]
              | (Rule(_,_, _, _, _, _, _, _, _, exp_list),_)::_ ->
                  List.map (fun t ->
                    Output.flat [
                      from_string "("; indreln_typ @@ C.t_to_src_t (Typed_ast.exp_to_typ t); from_string ")"
                    ]
                  ) exp_list
          in
          let clause_outputs =
            List.map (fun (Rule(name_lskips_t, skips0, skips, name_lskips_annot_list, skips', exp_opt, skips'', name_lskips_annot, c, exp_list),_) ->
              let constructor_name = from_string (Name.to_string (Name.strip_lskip name_lskips_t)) in
              let antecedent =
                match exp_opt with
                  | None -> emp
                  | Some e ->
                    match dest_and_exps A.env e with
                    | [] -> emp
                    | ants ->
                      (* Use propositional = in indreln antecedents instead of BEq ==.
                         Functions and other types without BEq need propositional equality. *)
                      let saved = !St.prop_equality in
                      St.prop_equality := true;
                      Fun.protect ~finally:(fun () -> St.prop_equality := saved) (fun () ->
                        flat [
                          concat_str " → "
                            (List.map (fun e ->
                                 flat [ from_string "(";
                                        exp inside_instance e;
                                        from_string ")" ]) ants);
                          from_string " → "
                        ]
                      )
              in
              let bound_variables =
                concat_str " " @@ List.map (fun b ->
                  match b with
                    | QName n -> from_string (lean_escape_keyword (Name.to_string (Name.strip_lskip n.term)))
                    | _ -> raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: unexpected binding form in indreln quantifier")
                ) name_lskips_annot_list
              in
              let binder, binder_sep =
                match name_lskips_annot_list with
                  | [] -> emp, emp
                  | _ -> from_string "∀ ", from_string ", "
              in
              let indices = concat_str " " @@ List.map (exp inside_instance) exp_list in
              let index_free_vars_set =
                List.fold_right Types.TNset.union
                  (List.map (fun t -> Types.free_vars (Typed_ast.exp_to_typ t)) exp_list)
                  Types.TNset.empty
              in
              let index_free_vars_typeset = concat_str " " @@ List.map (fun v -> from_string (Name.to_string (Types.tnvar_to_name v))) (Types.TNset.elements index_free_vars_set) in
              let relation_name = from_string name_string in
                Output.flat [
                  from_string "  | "; constructor_name; from_string " : ";
                  binder; bound_variables; binder_sep; antecedent;
                  relation_name; from_string " "; index_free_vars_typeset; from_string " "; indices
                ], index_free_vars_set
            ) matching_clauses
          in
          let all_free_vars =
            Types.TNset.elements @@
            List.fold_right Types.TNset.union (List.map snd clause_outputs) Types.TNset.empty
          in
          let free_vars_typeset =
            concat_str " " @@ List.map (fun v ->
              Output.flat [
                from_string "("; from_string (Name.to_string (Types.tnvar_to_name v)); from_string " : Type)"
              ]) all_free_vars
          in
          let index_type_sig =
            Output.flat [
              concat_str " → " index_type_parts; from_string " → Prop"
            ]
          in
          let clause_body = concat_str "\n" @@ List.map fst clause_outputs in
          Output.flat [
            from_string name_string; from_string " "; free_vars_typeset; from_string " : "; index_type_sig; from_string " where\n";
            clause_body
          ]
        ) gathered
      in
        let is_mutual = List.length indrelns > 1 in
        let prefix = if is_mutual then from_string "\nmutual" else emp in
        let suffix = if is_mutual then from_string "\nend" else emp in
        Output.flat [
          prefix;
          from_string "\ninductive "; concat_str "\ninductive " indrelns;
          suffix
        ]
      )
    and let_body inside_instance i_ref_opt top_level tv_set ((lb, _):letbind) =
      match lb with
        | Let_val (p, topt, skips, e) ->
            (* In Lean 4, `let (x : T) := val; body` is parsed as a pattern-matching
               let where x is NOT bound into body's scope. The correct syntax is
               `let x : T := val; body`. So when the pattern is P_typ at the top level,
               extract the inner pattern and emit the type annotation separately. *)
            let p_out, typ_from_pat = match p.term with
              | P_typ (_skips, inner_p, _skips', t, _skips'') ->
                  def_pattern inner_p, Some t
              | _ ->
                  def_pattern p, None
            in
            let tv_set_sep, tv_set =
              if Types.TNset.cardinal tv_set = 0 then
                let typ = Typed_ast.exp_to_typ e in
                let tv_set = Types.free_vars typ in
                  if Types.TNset.cardinal tv_set = 0 then
                    emp, tv_set
                  else
                    from_string " ", tv_set
              else
                from_string " ", tv_set
            in
            let tv_set = let_type_variables top_level tv_set in
            let topt =
              match topt with
                | None ->
                    (match typ_from_pat with
                      | None -> emp
                      | Some t ->
                          Output.flat [from_string " :"; pat_typ t])
                | Some (s, t) ->
                    Output.flat [
                      ws s; from_string " :"; pat_typ t
                    ]
            in
            let e = exp inside_instance e in
              Output.flat [
                p_out; tv_set_sep; tv_set; topt; ws skips; from_string " :="; e
              ]
        | Let_fun _ ->
            (* Pattern compilation transforms Let_fun into funcl before the backend *)
            raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: unexpected Let_fun in let_body (should be compiled away)")
    and funcl_aux inside_instance i_ref_opt constraints tv_set (n, pats, typ_opt, skips, e) =
      let name_skips = Name.get_lskip n in
      let name = from_string (Name.to_string (Name.strip_lskip n)) in
      let pat_skips =
        match pats with
          | [] -> emp
          | _  -> from_string " "
      in
      let constraints_sep =
        if constraints = emp then
          emp
        else
          from_string " "
      in
      let tv_set_sep, tv_set =
        if inside_instance then
          emp, emp
        else begin
          let tv_set =
            if Types.TNset.cardinal tv_set = 0 then
              Types.free_vars (Typed_ast.exp_to_typ e)
            else tv_set
          in
          (* Filter out phantom type variables that don't appear in any explicit
             parameter types or the return type. Lean can't infer these. *)
          let sig_tvs =
            let pat_tvs = List.fold_left (fun acc p ->
              Types.TNset.union acc (Types.free_vars p.typ)
            ) Types.TNset.empty pats in
            let ret_tvs = match typ_opt with
              | None -> Types.free_vars (Typed_ast.exp_to_typ e)
              | Some (_, t) -> Types.free_vars t.typ
            in
            Types.TNset.union pat_tvs ret_tvs
          in
          let tv_set = Types.TNset.inter tv_set sig_tvs in
          if Types.TNset.cardinal tv_set = 0 then
            emp, let_type_variables true tv_set
          else
            from_string " ", let_type_variables true tv_set
        end
      in
      let typ_opt =
        match typ_opt with
          | None -> emp
          | Some (s, t) ->
              Output.flat [
                ws s; from_string " : "; pat_typ t
              ]
      in
        let body = exp inside_instance e in
        (* Inside instance definitions, flatten newlines in the body expression.
           Without this, multiline bodies (e.g., sorry-based opaque type instances)
           can have arguments on a new line at field-name indentation, which Lean
           misparses as a new field definition. *)
        let body = if inside_instance then flatten_newlines body else body in
        (match !St.fuel_emit with
         | Some sentinel ->
           Output.flat [
             ws name_skips; from_string " "; name; from_string "_lemFuel";
             tv_set_sep; tv_set; constraints_sep; constraints; inhabited_binder_output ();
             from_string " (lemFuel : Nat)"; reader_binder_output (); pat_skips;
             fun_pattern_list inside_instance pats; ws skips; typ_opt;
             from_string " := match lemFuel with\n  | 0 => (";
             from_string sentinel;
             (* the succ-arm body is parenthesized like the sentinel: a
                hoisted infix head (e.g. a bind rendered prefix) followed by
                argument lines at low indentation would otherwise escape the
                match arm (arc-3 batch E: full_eval_pexpr) *)
             from_string ")\n  | Nat.succ lemFuel => (";
             body;
             from_string ")"
           ]
         | None ->
           Output.flat [
             ws name_skips; from_string " "; name; tv_set_sep; tv_set; constraints_sep; constraints;
             inhabited_binder_output (); reader_binder_output (); pat_skips;
             fun_pattern_list inside_instance pats; ws skips; typ_opt; from_string " := "; body
           ])
    and reader_binder_output () =
      if not !St.reader_binder then emp else
      Output.flat (List.map (fun (cref, pname) ->
          Output.flat [
            from_string " ("; from_string pname; from_string " : ";
            pat_typ (C.t_to_src_t (reader_value_typ cref)); from_string ")"])
        (get_reader_params ()))
    (* Arc-8 S2: [Inhabited tv] instance-implicit binders for a threaded
       def (zero call-site rewrites — Lean synthesizes the instance
       arguments at every application). *)
    and inhabited_binder_output () =
      Output.flat (List.map (fun n ->
          Output.flat [from_string " [Inhabited "; from_string n; from_string "]"])
        !St.inhabited_binder)

    and funcl inside_instance i_ref_opt constraints tv_set ({term = n}, c, pats, typ_opt, skips, e) =
      let n =
        if inside_instance then
          match i_ref_opt with
            | None -> B.const_ref_to_name n true c
            | Some i_ref ->
              begin
                let instance = Types.i_env_lookup Ast.Unknown A.env.i_env i_ref in
                let filtered = List.filter (fun x -> snd x = c) instance.inst_methods in
                  match filtered with
                    | x::xs -> B.const_ref_to_name n true (fst x)
                    | _ ->
                      let method_name = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip n)) in
                      raise (Reporting_basic.err_general true Ast.Unknown
                        (String.concat "" ["Lean backend: instance method not found for '"; method_name; "'"]))
              end
        else
          B.const_ref_to_name n true c
      in
        funcl_aux inside_instance i_ref_opt constraints tv_set (n, pats, typ_opt, skips, e)
    and let_type_variables top_level tv_set =
      if Types.TNset.is_empty tv_set || not top_level then
        emp
      else
      let bindings =
        List.map (fun tv -> match tv with
          | Types.Ty tv ->
            Output.flat [from_string "{"; id Type_var (Tyvar.to_rope tv); from_string " : Type}"]
          | Types.Nv nv ->
            Output.flat [from_string "{"; id Type_var (Nvar.to_rope nv); from_string " : Nat}"])
        (Types.TNset.elements tv_set)
      in
        from_string " " ^ concat_str " " bindings
    (* Expression rendering. Lean 4 parser-specific rules:
       - Match/if/let/fun in function args or case bodies are parenthesized
         (Lean's greedy rightward match would otherwise consume too much)
       - In indreln antecedents (St.prop_equality), == and != become = and ≠
       - For polymorphic indreln self-references (St.indreln_params), explicit
         type parameters are inserted since Lean can't infer them
       - Class method constants get explicit @ type application when used bare *)
    and exp inside_instance e =
      let is_user_exp = Typed_ast_syntax.is_pp_exp e in
        match C.exp_to_term e with
          | Var v ->
              name_var_output v
          | Backend (sk, i) ->
              ws sk ^
              Ident.to_output (Term_const (false, true)) path_sep i
          | Lit l -> literal l
          | Do (skips, _mod_descr_id, do_line_list, _skips', e, _skips'', _type_int) ->
              let lines = List.map (fun (Do_line (p, _s1, body, _s2)) ->
                let (body', _) = Typed_ast.alter_init_lskips (fun sk -> (Typed_ast.no_lskips, sk)) body in
                Output.flat [
                  from_string "    let "; fun_pattern p; from_string " ← "; exp inside_instance body'; from_string "\n"
                ]
              ) do_line_list in
              let (e', _) = Typed_ast.alter_init_lskips (fun sk -> (Typed_ast.no_lskips, sk)) e in
              Output.flat [
                ws skips; from_string "(do\n";
                concat emp lines;
                from_string "    "; exp inside_instance e'; from_string "\n";
                from_string "  )"
              ]
          | App (e1, e2) ->
              let trans e_inner =
                if needs_parens (C.exp_to_term e_inner) then
                  Output.flat [from_string "("; exp inside_instance e_inner; from_string ")"]
                else exp inside_instance e_inner
              in
              let sep = from_string " " in
              let oL = begin
              let (e0, args) = strip_app_exp e in
                match C.exp_to_term e0 with
                  | Constant cd ->
                    let c_descr = c_env_lookup Ast.Unknown A.env.c_env cd.descr in
                    (* Check if this function is marked effectful for Lean *)
                    let is_effectful = Target.Targetset.mem Target.Target_lean c_descr.effectful in
                    (* In indreln antecedents (Prop context), == and != applied via
                       App nodes (e.g. from <> decomposition: not (isEqual x y)) must
                       use propositional =/≠ instead of BEq ==/!=. *)
                    let raw_output = begin match !St.prop_equality, args, check_beq_target_rep c_descr with
                    | true, [arg0; arg1], Some is_eq ->
                      let l_out = trans arg0 in
                      let r_out = trans arg1 in
                      if is_eq then [Output.flat [l_out; from_string "  =  "; r_out]]
                      else [Output.flat [l_out; meta_utf8 "  \xe2\x89\xa0  "; r_out]]
                    | _ ->
                      let is_fuel_self =
                        (* only while rendering a fuel'd body: elsewhere the
                           lemFuel binder is not in scope *)
                        !St.fuel_emit <> None
                        && List.mem_assoc cd.descr !St.fuel_workers in
                      if is_fuel_self then
                        (* Self-call in a fuel'd worker: 'trans e0' reaches the
                           bare-Constant case, which rewrites to
                           '(worker lemFuel)'; apply the original arguments. *)
                        let func_out = trans e0 in
                        let args_out = List.map trans args in
                        [Output.flat (func_out
                          :: List.map (fun a -> Output.flat [from_string " "; a]) args_out)]
                      else if is_reader_cref cd.descr then
                        (* Application of the reader constant itself: 'tagDefs ()'
                           becomes the reader parameter. The only argument is unit. *)
                        [from_string (reader_inject_name (reader_param_name cd.descr))]
                      else if ground_rep_for cd.descr <> None
                              && Types.TNset.is_empty (Types.free_vars (Typed_ast.exp_to_typ e)) then
                        (* Ground-typed site of a ground_rep constant:
                           swap the head, keep the arguments, ascribe the
                           type so the instance resolves exactly here. *)
                        let rep = match ground_rep_for cd.descr with
                          | Some r -> r | None -> assert false in
                        let args_out = List.map trans args in
                        [Output.flat ([from_string "(("; from_string rep; from_string ")"]
                          @ List.map (fun a -> Output.flat [from_string " "; a]) args_out
                          @ [from_string " : "; pat_typ (C.t_to_src_t (Typed_ast.exp_to_typ e)); from_string ")"])]
                      else if is_lean_failwith_rep cd.descr && args <> [] then begin
                        (* Failure site (arc-8 S2: EVERY site, ground or
                           tyvar-typed): axiom-free failwithI, with an
                           ascription so the instance resolves at exactly
                           this type. Tyvar sites resolve through the S1
                           derived instances and/or the [Inhabited tv]
                           binders threaded onto the enclosing def. *)
                        let site_t = Typed_ast.exp_to_typ e in
                        failwith_instance_guard inside_instance site_t;
                        [Output.flat ([from_string "(failwithI"]
                          @ List.map (fun a -> Output.flat [from_string " "; trans a]) args
                          @ [from_string " : "; pat_typ (C.t_to_src_t site_t);
                             from_string ")"])]
                      end
                      else if Types.Cdset.mem cd.descr !St.reader_lifted then
                        (* Call of a lifted def: `trans e0` reaches the bare-
                           Constant case, which injects the reader parameters
                           exactly once; just apply the original arguments. *)
                        let func_out = trans e0 in
                        let args_out = List.map trans args in
                        [Output.flat (func_out
                          :: List.map (fun a -> Output.flat [from_string " "; a]) args_out)]
                      else
                      begin match List.assoc_opt cd.descr !St.indreln_params with
                      | Some params_str ->
                        let func_out = trans e0 in
                        let args_out = List.map trans args in
                        [Output.flat ([func_out; from_string " "; from_string params_str]
                          @ List.map (fun a -> Output.flat [from_string " "; a]) args_out)]
                      | None ->
                        B.function_application_to_output (exp_to_locn e) trans false e cd args (use_ascii_rep_for_const cd.descr)
                      end
                    end in
                    (* Wrap effectful calls in runEffectful with a thunk to prevent CSE.
                       Each call site creates a fresh lambda closure, preventing Lean's
                       CSE from merging calls to side-effecting functions. *)
                    if is_effectful then
                      [Output.flat [from_string "(runEffectful (fun () => "; Output.concat (from_string " ") raw_output; from_string "))"]]
                    else raw_output
                  | Backend (_, i) when Ident.to_string i = "sorry" ->
                    (* sorry is a term, not a function — drop applied arguments.
                       Annotate with the expression's type so Lean can infer it
                       in contexts like let bindings. *)
                    let typ = Typed_ast.exp_to_typ e in
                    let src_t = C.t_to_src_t typ in
                    [Output.flat [from_string "(sorry : "; pat_typ src_t; from_string ")"]]
                  | _ ->
                    List.map trans (e0 :: args)
              end in
              Output.concat sep oL
          | Paren (skips, e, skips') ->
              Output.flat [
                ws skips; from_string "("; exp inside_instance e; ws skips'; from_string ")";
              ]
          | Typed (skips, e, skips', t, skips'') ->
              Output.flat [
                ws skips; from_string "("; exp inside_instance e; from_string " :"; ws skips'; pat_typ t; ws skips''; from_string ")";
              ]
          | Tup (skips, es, skips') ->
              let tups = flat @@ Seplist.to_sep_list (exp inside_instance) (sep (from_string ",")) es in
                Output.flat [
                  ws skips; from_string "("; tups; from_string ")"; ws skips'
                ]
          | List (skips, es, skips') ->
              let lists = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun _ -> from_string " ")) (exp inside_instance) (sep @@ from_string ",") es in
                Output.flat [
                  ws skips; from_string "["; lists; from_string "]"; ws skips'
                ]
          | Let (skips, bind, _skips', e) ->
              let body = flatten_newlines (let_body inside_instance None false Types.TNset.empty bind) in
                Output.flat [
                  ws skips; from_string "let "; body; from_string "; "; exp inside_instance e
                ]
          | Constant const ->
              let c_descr = c_env_lookup Ast.Unknown A.env.c_env const.descr in
              let default_const_output () =
                Output.concat emp (B.function_application_to_output (exp_to_locn e) (exp inside_instance) false e const [] (use_ascii_rep_for_const const.descr))
              in
              begin match (if !St.fuel_emit = None then None
                           else List.assoc_opt const.descr !St.fuel_workers) with
              | Some w ->
                (* Self- or cross-member call inside a fuel'd block: recurse
                   on the decremented fuel binder; a lifted worker also
                   re-injects its reader binders (arc 3, B1/B2). *)
                let readers =
                  if !St.reader_binder then reader_args_output () else emp in
                Output.flat [from_string "("; from_string w;
                             from_string " lemFuel"; readers; from_string ")"]
              | None ->
              if is_reader_cref const.descr then
                (* Bare reference to the reader constant (unapplied):
                   eta-expand so the unit-function type is preserved. *)
                Output.flat [from_string "(fun (_ : Unit) => ";
                             from_string (reader_inject_name (reader_param_name const.descr)); from_string ")"]
              else if Types.Cdset.mem const.descr !St.reader_lifted then
                (* Bare reference to a lifted def (e.g. passed to a HOF):
                   partially apply the reader parameters. *)
                Output.flat [from_string "("; default_const_output ();
                             reader_args_output (); from_string ")"]
              else if is_lean_failwith_rep const.descr then begin
                (* Bare / point-free failure reference (arc-8 S2): the
                   ascription (String -> tau) determines failwithI's
                   type argument; Inhabited tau resolves as at applied
                   sites. Legacy failwith is never emitted. *)
                let site_t = Typed_ast.exp_to_typ e in
                failwith_instance_guard inside_instance site_t;
                Output.flat [from_string "(failwithI : ";
                             pat_typ (C.t_to_src_t site_t); from_string ")"]
              end
              else
              (* Class method constants used bare (no explicit arguments) need explicit
                 @ type application in Lean 4. Without it, Lean can't infer the class
                 type parameter for nullary methods like `size : {a : Type} → [Size a] → Nat`
                 because the return type `Nat` doesn't mention the type parameter `a`.
                 Using `@size a _` provides the type argument explicitly.
                 Skip this for class methods that have a Lean target rep, since the
                 target rep already handles resolution. *)
              if c_descr.const_class <> [] then begin
                match Target.Targetmap.apply_target c_descr.target_rep
                        (Target.Target_no_ident Target.Target_lean) with
                | Some _ -> default_const_output ()
                | None ->
                  let i = B.const_id_to_ident const false in
                  let sk = Ident.get_lskip i in
                  let type_args = List.map (fun t ->
                    let src_t = C.t_to_src_t t in
                    Output.flat [from_string " ("; pat_typ src_t; from_string ")"]
                  ) const.instantiation in
                  let num_classes = List.length c_descr.const_class in
                  let class_holes = List.init num_classes (fun _ -> from_string " _") in
                  (* Parenthesize the @name (type) _ expression so it can safely
                     appear as an argument to another function *)
                  Output.flat ([ws sk; from_string "(@"; Ident.to_output (Term_const (false, true)) path_sep (Ident.replace_lskip i no_lskips)] @ type_args @ class_holes @ [from_string ")"])
              end else
                default_const_output ()
              end
          | Fun (skips, ps, skips', e) ->
              let ps = fun_pattern_list inside_instance ps in
                block_hov (Typed_ast_syntax.is_pp_exp e) 2 (
                  Output.flat [
                    ws skips; from_string "fun"; ps; ws skips'; from_string "=> "; exp inside_instance e
                  ])
          | Function _ ->
              print_and_fail (Typed_ast.exp_to_locn e) "illegal function in extraction, should have been previously macro'd away"
          | Set (skips, es, skips') ->
            let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun _ -> emp)) (exp inside_instance) (sep @@ from_string ", ") es in
            let skips =
              if skips = Typed_ast.no_lskips then
                from_string " "
              else
                ws skips
            in
              block is_user_exp 0 (
                if Seplist.is_empty es then
                  Output.flat [
                    skips; from_string "(setEmpty)"
                  ]
                else
                  (* Comparator-keyed literal (arc-14 S2 B3, be:G4): set
                     literals dedupe by the SetType comparator — matching
                     OCaml lem's comparator-keyed Pset — never by BEq
                     (a BEq finer than the comparator, e.g. cerberus sym,
                     could otherwise keep comparator-EQ duplicates). The
                     lem type of a set literal carries SetType 'a, so the
                     instance is resolvable at every splice site. *)
                  Output.flat [
                    skips; from_string "(setFromListBy setElemCompare ["; body; from_string "])"; ws skips'
                  ])
          | Begin (skips, e, skips') ->
              (* Lem's begin...end is a grouping construct. In Lean, use parens. *)
              Output.flat [
                ws skips; from_string "("; exp inside_instance e; ws skips';
                from_string ")"
              ]
          | Record (skips, fields, skips') ->
            let typ = Typed_ast.exp_to_typ e in
            (match mutual_record_path typ with
            | Some path ->
              (* Mutual records are rendered as inductives, not structures.
                 Use constructor syntax: TypeName.mk val1 val2 ... *)
              let field_vals = Seplist.to_list fields in
              let vals = List.map (fun (_, _, e_val, _) ->
                Output.flat [from_string " ("; exp inside_instance e_val; from_string ")"]
              ) field_vals in
              let n0 = Name.add_lskip (Path.get_name path) in
              let n = B.type_path_to_name n0 path in
              let type_name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip n)) in
              Output.flat ([
                ws skips; from_string "("; from_string type_name_str; from_string ".mk"
              ] @ vals @ [
                ws skips'; from_string ")"
              ])
            | None ->
              let body = flatten_newlines (flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun _ -> emp)) (field_update inside_instance) (sep @@ from_string ",") fields) in
              (* Add type ascription so Lean can resolve the record type from
                 field names. Without it, { field := value } fails when the
                 expected type isn't known from context (e.g., in a let binding). *)
              let src_t = C.t_to_src_t typ in
                Output.flat [
                  ws skips; from_string "(({ "; body; ws skips'; from_string " } : "; pat_typ src_t; from_string "))"
                ]
            )
          | Field (e, skips, fd) ->
            let name = field_ident_to_output fd (use_ascii_rep_for_const fd.descr) in
            (* Dot notation works for both structures (.field accessor) and
               mutual records (we generate explicit accessor functions).
               Parenthesize match/if/let/fun: without parens, .field binds
               to the last arm body, not the whole expression. *)
            let e_out =
              if needs_parens (C.exp_to_term e) then
                Output.flat [from_string "("; exp inside_instance e; from_string ")"]
              else exp inside_instance e
            in
              Output.flat [
                e_out; from_string "."; ws skips; name
              ]
          | Recup (skips, e, skips', fields, skips'') ->
            let e_typ = Typed_ast.exp_to_typ e in
            (match mutual_record_path e_typ with
            | Some path ->
              (* Mutual records are inductives — { r with ... } doesn't work.
                 Look up all fields from the type definition, reconstruct with
                 accessor functions for unchanged fields and new values for updated ones. *)
              let updated = Seplist.to_list fields in
              let updated_names = List.map (fun (fd, _, _, _) ->
                let c_descr = c_env_lookup Ast.Unknown A.env.c_env fd.descr in
                Name.to_string (Path.get_name c_descr.const_binding)
              ) updated in
              let updated_map = List.map2 (fun name (_, _, e_val, _) -> (name, e_val)) updated_names updated in
              (* Look up the type's fields from the environment *)
              (match Types.type_defs_lookup_typ Ast.Unknown A.env.t_env e_typ with
                | Some td ->
                  let all_fields = match td.Types.type_fields with
                    | Some fs -> fs | None -> [] in
                  let field_vals = List.map (fun f_ref ->
                    let c_descr = c_env_lookup Ast.Unknown A.env.c_env f_ref in
                    let fname = Name.to_string (
                      Path.get_name c_descr.const_binding) in
                    match List.assoc_opt fname updated_map with
                      | Some e_val -> Output.flat [from_string " ("; exp inside_instance e_val; from_string ")"]
                      | None -> Output.flat [from_string " ("; exp inside_instance e; from_string "."; from_string fname; from_string ")"]
                  ) all_fields in
                  let n0 = Name.add_lskip (Path.get_name path) in
                  let n = B.type_path_to_name n0 path in
                  let type_name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip n)) in
                  Output.flat ([
                    ws skips; from_string "("; from_string type_name_str; from_string ".mk"
                  ] @ field_vals @ [
                    from_string ")"
                  ])
                | None ->
                  raise (Reporting_basic.err_general true (Typed_ast.exp_to_locn e)
                    "Lean backend: mutual record update could not find type definition")
              )
            | None ->
              let body = flatten_newlines (flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun _ -> emp)) (field_update inside_instance) (sep @@ from_string ",") fields) in
              let skips'' =
                if skips'' = Typed_ast.no_lskips then
                  from_string " "
                else
                  ws skips''
              in
                Output.flat [
                   ws skips; from_string "{ "; exp inside_instance e; ws skips'; from_string " with "; body; skips''; from_string " }"
                ]
            )
          | Case (_, skips, e, skips', cases, skips'') ->
            let case_sep _ = from_string " " in
            let has_vec = Seplist.exists (fun (p, _, _, _) -> pat_has_vector p) cases in
            (* Use multi-discriminant match for tuple scrutinees:
               match l1, l2 with | [], [] => ... instead of
               match (l1, l2) with | ([], []) => ...
               This lets Lean's termination checker see structural recursion.
               Only apply when ALL case arm patterns are P_tup or P_wild. *)
            let pat_is_tup_or_wild (p, _, _, _) = match p.term with
              | P_tup _ | P_wild _ -> true
              | P_paren (_, p', _) -> (match p'.term with P_tup _ | P_wild _ -> true | _ -> false)
              | _ -> false
            in
            (* Extract tuple elements if the scrutinee is a tuple and all patterns
               are tuples/wilds. Yields (arity, elements) for multi-discriminant match. *)
            let tuple_elems = match C.exp_to_term e with
              | Tup (_, es, _) when Seplist.for_all pat_is_tup_or_wild cases ->
                  Some (Seplist.length es, Seplist.to_list es)
              | _ -> None
            in
            let case_line' = match tuple_elems with
              | Some (arity, _) -> case_line_multi inside_instance arity
              | None -> case_line inside_instance
            in
            let body = flat @@ Seplist.to_sep_list_last Seplist.Optional case_line' case_sep cases in
            let match_suffix = if has_vec then from_string ".toList" else emp in
            let match_expr = match tuple_elems with
              | Some (_, elems) ->
                  Output.concat (from_string ", ") (List.map (exp inside_instance) elems)
              | None -> exp inside_instance e
            in
                Output.flat [
                  ws skips; from_string "match "; match_expr; match_suffix; from_string " with "; body; ws skips''
                ]
          | Infix (l, c, r) ->
              let trans e =
                if needs_parens (C.exp_to_term e) then
                  Output.flat [from_string "("; exp inside_instance e; from_string ")"]
                else exp inside_instance e
              in
              let sep = from_string " " in
              begin
                (* NOTE (audit, 2026-08-18): this Infix path has NONE of the
                   reader/fuel/effectful hooks. A lifted, fuel'd, or
                   effectful constant used in infix position emits without
                   injection/wrapping — every such case fails VISIBLY at the
                   Lean build (missing binder / unknown worker / unrun
                   BaseIO), never silently. Hook here if a legitimate infix
                   use ever appears. *)
                match C.exp_to_term c with
                  | Constant cd ->
                    begin
                      (* In indreln antecedents (Prop context), == and != must use
                         propositional =/≠. This handles the Infix AST case;
                         the App case above handles decomposed forms like not(isEqual x y). *)
                      let c_descr = c_env_lookup Ast.Unknown A.env.c_env cd.descr in
                      match !St.prop_equality, check_beq_target_rep c_descr with
                      | true, Some is_eq ->
                        (* Parenthesize both sides to avoid chained = ambiguity *)
                        let l_out = Output.flat [from_string "("; trans l; from_string ")"] in
                        let r_out = Output.flat [from_string "("; trans r; from_string ")"] in
                        if is_eq then Output.flat [l_out; from_string "  =  "; r_out]
                        else Output.flat [l_out; meta_utf8 "  \xe2\x89\xa0  "; r_out]
                      | _ -> begin
                        let pieces = B.function_application_to_output (exp_to_locn e) trans true e cd [l; r] (use_ascii_rep_for_const cd.descr) in
                        Output.concat sep pieces
                      end
                    end
                  | _           ->
                    begin
                      let mapped = List.map trans [l; c; r] in
                      Output.concat sep mapped
                    end
              end
          | If (skips, test, skips', t, skips'', f) ->
              let cond =
                if needs_parens (C.exp_to_term test) then
                  Output.flat [from_string "("; exp inside_instance test; from_string ")"]
                else exp inside_instance test
              in
              Output.flat [
                ws skips; from_string "if";
                from_string " "; cond;
                ws skips'; from_string "then"; from_string " ";
                exp inside_instance t;
                ws skips''; from_string " else "; exp inside_instance f
              ]
          | Quant (quant, quant_binding_list, skips, e) ->
            let quant =
              match quant with
                | Ast.Q_forall _ -> from_string "∀"
                | Ast.Q_exists _ -> from_string "∃"
            in
            let bindings =
              Output.concat (from_string " ") (
                List.map (fun quant_binding ->
                  match quant_binding with
                    | Typed_ast.Qb_var name_lskips_annot ->
                      let name = name_lskips_annot.term in
                      let skip = Name.get_lskip name in
                      let name = Name.strip_lskip name in
                      let name = lean_escape_keyword (Ulib.Text.to_string (Name.to_rope name)) in
                        Output.flat [
                          ws skip; from_string name
                        ]
                    | Typed_ast.Qb_restr (_bool, skips, pat, skips', e, skips'') ->
                      let pat_out = fun_pattern pat in
                        Output.flat [
                          ws skips; pat_out; ws skips'; from_string " : ";
                          exp inside_instance e; ws skips''
                        ]
                ) quant_binding_list)
            in
              Output.flat [
                quant; from_string " "; bindings; from_string ", ("; ws skips;
                exp inside_instance e; from_string " : Prop)"
              ]
          | Comp_binding (_, _, _, _, _, _, _, _, _) ->
              (* Set-comprehension binding — not supported in Lean. Library
                 functions with comprehensions have Lean target reps that
                 bypass this code path (their lem definitions render only as
                 block comments, guarded below); anything LIVE is
                 FAIL-CLOSED: a loud generation-time error (arc-10 S2,
                 decision log D1 ruling 3 — formerly an opaque `(sorry ...)`
                 stub). *)
              if !St.rendering_comment then
                from_string "(sorry /- Lean backend: set comprehension binding not supported -/)"
              else
                raise (Reporting_basic.err_general true (exp_to_locn e)
                  "Lean backend: set comprehensions ({ e | bindings ... }) are not supported by the Lean backend; workarounds: rewrite using explicit Set/List library functions (e.g. Set.filter / Set.map / Set.cross, which have Lean target reps), or give the enclosing definition a 'declare lean target_rep'")
          | Setcomp (_, _, _, _, _, _) ->
              if !St.rendering_comment then
                from_string "(sorry /- Lean backend: set comprehension not supported -/)"
              else
                raise (Reporting_basic.err_general true (exp_to_locn e)
                  "Lean backend: set comprehensions ({ e | condition }) are not supported by the Lean backend; workarounds: rewrite using explicit Set/List library functions (e.g. Set.filter / Set.map, which have Lean target reps), or give the enclosing definition a 'declare lean target_rep'")
          | Nvar_e (skips, nvar) ->
            let nvar = id Nexpr_var @@ Ulib.Text.(^^^) (r "") (Nvar.to_rope nvar) in
              Output.flat [
                ws skips; nvar
              ]
          | VectorAcc (e, skips, nexp, skips') ->
              (* Parenthesize match/if/let/fun in function argument position *)
              let e_out =
                if needs_parens (C.exp_to_term e) then
                  Output.flat [from_string "("; exp inside_instance e; from_string ")"]
                else exp inside_instance e
              in
              Output.flat [
                from_string "Vector.get "; e_out;
                from_string " "; src_nexp nexp; ws skips'
              ]
          | VectorSub (e, skips, nexp, skips', nexp', skips'') ->
              let e_out =
                if needs_parens (C.exp_to_term e) then
                  Output.flat [from_string "("; exp inside_instance e; from_string ")"]
                else exp inside_instance e
              in
              Output.flat [
                from_string "Vector.slice "; e_out;
                from_string " "; src_nexp nexp;
                from_string " "; src_nexp nexp'; ws skips''
              ]
          | Vector (skips, es, skips') ->
            let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun _ -> emp)) (exp inside_instance) (sep @@ from_string ", ") es in
            let skips =
              if skips = Typed_ast.no_lskips then
                from_string " "
              else
                ws skips
            in
              block is_user_exp 0 (
                if Seplist.is_empty es then
                  Output.flat [
                    skips; from_string "#v[]"
                  ]
                else
                  Output.flat [
                    skips; from_string "#v["; body; ws skips'; from_string "]"
                  ])
    and src_nexp n =
      match n.nterm with
        | Nexp_var (skips, nvar) ->
          let nvar = id Nexpr_var @@ Ulib.Text.(^^^) (r"") (Nvar.to_rope nvar) in
            Output.flat [
              ws skips; nvar
            ]
        | Nexp_const (skips, i) ->
            Output.flat [
              ws skips; from_string (Z.to_string i)
            ]
        | Nexp_mult (nexp, skips, nexp') ->
            Output.flat [
              src_nexp nexp; ws skips; from_string "*"; src_nexp nexp'
            ]
        | Nexp_add (nexp, skips, nexp') ->
            Output.flat [
              src_nexp nexp; ws skips; from_string "+"; src_nexp nexp'
            ]
        | Nexp_paren (skips, nexp, skips') ->
            Output.flat [
              ws skips; from_string "("; src_nexp nexp; ws skips'; from_string ")"
            ]
    and pat_has_vector (p : pat) : bool =
      match p.term with
        | P_vector _ | P_vectorC _ -> true
        | P_paren (_, p, _) | P_typ (_, p, _, _, _) | P_as (_, p, _, _, _) -> pat_has_vector p
        | P_tup (_, ps, _) | P_list (_, ps, _) -> Seplist.exists pat_has_vector ps
        | P_cons (p1, _, p2) -> pat_has_vector p1 || pat_has_vector p2
        | P_const (_, ps) -> List.exists pat_has_vector ps
        | _ -> false
    and case_line inside_instance (p, skips, e, _) =
        let body =
          if needs_parens (C.exp_to_term e) then
            Output.flat [from_string "("; exp inside_instance e; from_string ")"]
          else exp inside_instance e
        in
        flatten_newlines (Output.flat [
          from_string "| "; def_pattern p; from_string " => "; body
        ])
    (* Multi-discriminant case line: unwrap P_tup pattern into comma-separated
       elements for match l1, l2, ... with | p1, p2, ... => body syntax.
       P_wild is expanded to arity-many wildcards: _ => _, _, ... *)
    and case_line_multi inside_instance arity (p, skips, e, l) =
        let body =
          if needs_parens (C.exp_to_term e) then
            Output.flat [from_string "("; exp inside_instance e; from_string ")"]
          else exp inside_instance e
        in
        let unwrap_tup p = match p.term with
          | P_tup (_, ps, _) ->
            Output.concat (from_string ", ") (List.map def_pattern (Seplist.to_list ps))
          | P_wild _ ->
            Output.concat (from_string ", ") (List.init arity (fun _ -> from_string "_"))
          | _ -> def_pattern p
        in
        let pat_out = match p.term with
          | P_paren (_, p', _) -> unwrap_tup p'
          | _ -> unwrap_tup p
        in
        flatten_newlines (Output.flat [
          from_string "| "; pat_out; from_string " => "; body
        ])
    and field_update inside_instance (fd, skips, e, _) =
      let name = field_ident_to_output fd (use_ascii_rep_for_const fd.descr) in
      (* Flatten newlines in record field values to prevent multiline expressions
         (e.g., lambdas containing match) from breaking record { with } syntax. *)
      let value = flatten_newlines (exp inside_instance e) in
        Output.flat [
          name; ws skips; from_string " := "; value
        ]
    and literal l =
      match l.term with
        | L_true skips -> ws skips ^ from_string "true"
        | L_false skips -> ws skips ^ from_string "false"
        | L_num (skips, n, _) -> ws skips ^ num n
        | L_string (skips, s, _) ->
            let escaped = lean_string_escape s in
            ws skips ^ from_string (String.concat "" ["\""; escaped; "\""])
        | L_unit (skips, skips') -> ws skips ^ from_string "()" ^ ws skips'
        | L_zero s ->
          Output.flat [
            ws s; from_string "false"
          ]
        | L_one s ->
          Output.flat [
            ws s; from_string "true"
          ]
        | L_char (s, c, _) ->
          let c = from_string (Printf.sprintf "'%s'" (Char.escaped c)) in
          Output.flat [
            ws s; c
          ]
        | L_numeral (skips, i, _) ->
          let i = from_string @@ Z.to_string i in
            Output.flat [
              ws skips; i
            ]
        | L_vector (s, prefix, bits) ->
            Output.flat [
              ws s; from_string (String.concat "" [prefix; bits])
            ]
        | L_undefined (skips, explanation) ->
          (* Arc-8 audit fix (auditor A F1): mirror the OCaml backend,
             which renders L_undefined as a RAISE carrying the
             incomplete-pattern message — `failwith m`
             (src/backend.ml:864, `const_undefined` in module Ocaml at
             src/backend.ml:830) — never a silent default value. The
             Lean rendering is failwithI with the same message, ascribed
             like every other failure site so the Inhabited instance
             resolves at exactly this type; bare-tyvar sites are
             discharged by the threaded [Inhabited tv] binders (the
             pre-pass records L_undefined sites as failure sites,
             renderer-independently: lean_thread_scan_exp). The
             explanation is emitted verbatim between quotes — it is
             pre-escaped with String.escaped at construction
             (src/patterns.ml:1594,1644), exactly as the OCaml backend's
             `str` output relies on. *)
          let typ = l.typ in
          let src_t = C.t_to_src_t typ in
            Output.flat [
              ws skips; from_string "(failwithI \""; from_string explanation;
              from_string "\" : "; pat_typ src_t; from_string ")"
            ]
    and fun_pattern_list inside_instance ps =
      let style = if inside_instance then MatchArm else FunParam in
        Output.flat [
          from_string " "; (concat_str " " @@ List.map (pattern ~style) ps)
        ]
    and src_t_has_wild t =
      match t.term with
        | Typ_wild _ -> true
        | Typ_fn (t1, _, t2) -> src_t_has_wild t1 || src_t_has_wild t2
        | Typ_tup ts -> Seplist.exists src_t_has_wild ts
        | Typ_app (_, ts) -> List.exists src_t_has_wild ts
        | Typ_paren (_, t, _) -> src_t_has_wild t
        | _ -> false
    and pattern ~(style : pat_style) p =
      let self p = pattern ~style p in
      let bare p = pattern ~style:MatchArm p in
      match p.term with
        | P_wild skips ->
          let skips_out =
            if skips = Typed_ast.no_lskips then
              from_string " "
            else
              ws skips
          in
            (match style with
            | FunParam ->
              let t = C.t_to_src_t p.typ in
              Output.flat [from_string "("; skips_out; from_string "_ : "; pat_typ t; from_string ")"]
            | MatchArm ->
              Output.flat [skips_out; from_string "_"])
        | P_var v ->
            (match style with
            | FunParam ->
              let name = lskips_t_to_output v in
              let t = C.t_to_src_t p.typ in
              Output.flat [from_string "("; name; from_string " : "; pat_typ t; from_string ")"]
            | MatchArm ->
              name_var_output v)
        | P_lit l ->
            (match style, l.term with
            | FunParam, L_unit _ -> from_string "(_ : Unit)"
            | _ -> literal l)
        | P_as (skips, p, skips', (n, l), skips'') ->
          let name = name_var_output n in
            Output.flat [
              ws skips; name; from_string "@("; self p; from_string ")"; ws skips''
            ]
        | P_typ (skips, p, skips', t, skips'') ->
            (match style with
            | FunParam ->
              (* When source type has wildcards, use the resolved type from Lem's
                 type checker instead — Lean can't resolve partial wildcards like
                 `rel _ _` with autoImplicit=false *)
              let actual_t = if src_t_has_wild t then C.t_to_src_t p.typ else t in
              Output.flat [
                ws skips; from_string "("; bare p; ws skips'; from_string " :";
                ws skips''; pat_typ actual_t; from_string ")"
              ]
            | MatchArm ->
              Output.flat [
                ws skips; from_string "("; self p; from_string " : "; pat_typ t; from_string ")"; ws skips'
              ])
        | P_tup (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list self (sep @@ from_string ", ") ps in
            (match style with
            | FunParam ->
              Output.flat [ws skips; from_string "("; body; ws skips'; from_string ")"]
            | MatchArm ->
              Output.flat [ws skips; from_string "("; body; from_string ")"; ws skips'])
        | P_record (_, fields, _) ->
            print_and_fail p.locn "illegal record pattern in code extraction, should have been compiled away"
        | P_cons (p1, skips, p2) ->
            (match style with
            | FunParam ->
              Output.flat [
                from_string "("; bare p1; ws skips; from_string " :: "; bare p2; from_string ")"
              ]
            | MatchArm ->
              Output.flat [
                self p1; ws skips; from_string " :: "; self p2
              ])
        | P_var_annot (n, t) ->
            (match style with
            | FunParam ->
              let name = lskips_t_to_output n in
              Output.flat [from_string "("; name; from_string " : "; pat_typ t; from_string ")"]
            | MatchArm ->
              name_var_output n)
        | P_list (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list_last Seplist.Optional self (sep @@ from_string ", ") ps in
            Output.flat [
              ws skips; from_string "["; body; from_string "]"; ws skips'
            ]
        | P_vector (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list_last Seplist.Optional self (sep @@ from_string ", ") ps in
            Output.flat [
              ws skips; from_string "["; body; from_string "]"; ws skips'
            ]
        | P_vectorC _ ->
            raise (Reporting_basic.err_general true p.locn
              "Lean backend: vector concatenation patterns are not supported")
        | P_paren (skips, p, skips') ->
            (match style with
            | FunParam ->
              Output.flat [ws skips; from_string "("; self p; ws skips'; from_string ")"]
            | MatchArm ->
              Output.flat [from_string "("; ws skips; self p; ws skips'; from_string ")"])
        | P_const(cd, ps) ->
            let oL = B.pattern_application_to_output p.locn self cd ps (use_ascii_rep_for_const cd.descr) in
            concat (from_string " ") oL
        | P_backend(sk, i, _, ps) ->
            let name = Output.flat [ws sk;
              Ident.to_output (Term_const (false, true)) path_sep (Ident.replace_lskip i Typed_ast.no_lskips)]
            in
            concat (from_string " ") (name :: List.map self ps)
        | P_num_add ((name, l), skips, skips', k) ->
            (* n+k patterns should be desugared by is_lean_pattern_match before
               reaching the backend. If one arrives here (e.g., in library code),
               emit the pattern as (name + k) — invalid Lean but visible in output. *)
            let name = lskips_t_to_output name in
              Output.flat [
                ws skips; from_string "("; name; from_string " + "; from_string (Z.to_string k); from_string ")"
              ]
    and fun_pattern p = pattern ~style:FunParam p
    and def_pattern p = pattern ~style:MatchArm p
    and src_t_has_fn (t : src_t) : bool =
      match t.term with
        | Typ_fn _ -> true
        | Typ_tup ts -> Seplist.exists src_t_has_fn ts
        | Typ_app (id, ts) ->
          (* Check type arguments for functions *)
          List.exists src_t_has_fn ts ||
          (* Also check if the type itself is an abbreviation expanding to a function type.
             This catches cases like stateM 'a 'st = 'st -> maybe ('a * 'st) where the
             abbreviation hides a function type. *)
          (match Types.type_defs_lookup_tc A.env.t_env id.descr with
           | Some (Types.Tc_type td) ->
             (match td.Types.type_abbrev with
               | Some expanded_t ->
                 (* Check if the expanded type contains a function.
                    Use head_norm to fully expand nested abbreviations
                    (e.g., wrap = fn, fn = nat -> bool). *)
                 let rec types_t_has_fn (ty : Types.t) =
                   let ty = Types.head_norm A.env.t_env ty in
                   match ty.Types.t with
                     | Types.Tfn _ -> true
                     | Types.Ttup ts -> List.exists types_t_has_fn ts
                     | Types.Tapp (ts, _) -> List.exists types_t_has_fn ts
                     | _ -> false
                 in
                 types_t_has_fn expanded_t
               | None -> false)
           | _ -> false)
        | Typ_backend (_, ts) -> List.exists src_t_has_fn ts
        | Typ_paren (_, t, _) -> src_t_has_fn t
        | Typ_with_sort (t, _) -> src_t_has_fn t
        | Typ_wild _ | Typ_var _ | Typ_len _ -> false
    and texp_can_derive_beq (t : texp) : bool =
      match t with
        | Te_variant (_, ctors) ->
          not (Seplist.exists (fun (_, _, _, args) ->
            Seplist.exists src_t_has_fn args
          ) ctors)
        | Te_record (_, _, fields, _) ->
          not (Seplist.exists (fun (_, _, _, src_t) -> src_t_has_fn src_t) fields)
        | Te_opaque | Te_abbrev _ -> false
    (* --- Type definition rendering ---
       Dispatch by type form:
       - Te_abbrev → type_def_abbreviation (Lean abbrev)
       - Te_record → type_def_record (Lean structure)
       - Te_variant, single type → type_def_variant (Lean inductive)
       - Te_variant, mutual types with equal params → type_def_variant (mutual block)
       - Te_variant, mutual types with unequal params → type_def_indexed
         (parameters promoted to indices, all types in Type 1 universe)
       After each inductive/structure, constructors are exported and
       BEq/Ord/Inhabited instances are generated. *)
    and type_def_abbreviation n tyvars path skips t =
      let n = B.type_path_to_name n path in
      let name = Name.to_output (Type_ctor (false, false)) n in
      let tyvars' = type_def_type_variables tyvars in
      let tyvar_sep = if List.length tyvars = 0 then emp else from_string " " in
      let body = pat_typ t in
        Output.flat [
          from_string "abbrev"; name; tyvar_sep; tyvars';
          ws skips; from_string " := "; body; from_string "\n";
        ]
    and type_def_record (n', _) tyvars path ty fields =
      let n' = B.type_path_to_name n' path in
      let name = Name.to_output (Type_ctor (false, false)) n' in
      let field_list = Seplist.to_list fields in
      let body = concat_str "\n" (List.map field field_list) in
      let tyvars' = type_def_type_variables tyvars in
      let tyvar_sep = if List.length tyvars = 0 then emp else from_string " " in
      let deriving_clause = if texp_can_derive_beq ty then
        from_string "  deriving BEq, Ord\n"
      else emp in
        Output.flat [
          from_string "structure"; name; tyvar_sep; tyvars';
          from_string " where\n"; body; from_string "\n"; deriving_clause;
        ]
    and type_def inside_module defs =
      (* Collect type names and their constructor names for "export" declarations.
         Using "export" instead of "open" ensures constructors are visible
         in files that import this module, not just in the defining file. *)
      let type_info = List.filter_map (fun ((n0, _), _, t_path, ty, _) ->
        match ty with
          | Te_abbrev _ -> None  (* Abbreviations don't create namespaces *)
          | Te_opaque ->
            (* Opaque types with target_rep become abbrevs — no namespace *)
            let l = Ast.Trans (false, "type_info", None) in
            let td = Types.type_defs_lookup l A.env.t_env t_path in
            (match Target.Targetmap.apply_target td.Types.type_target_rep
                    (Target.Target_no_ident Target.Target_lean) with
              | Some (Types.TYR_simple _) -> None
              | _ ->
                let n = B.type_path_to_name n0 t_path in
                Some (Name.to_string (Name.strip_lskip n), []))
          | _ ->
            (* Check if this type has a target_rep — if so, it becomes
               an abbrev and doesn't create a namespace *)
            let l = Ast.Trans (false, "type_info", None) in
            let td = Types.type_defs_lookup l A.env.t_env t_path in
            if Target.Targetmap.apply_target td.Types.type_target_rep
                 (Target.Target_no_ident Target.Target_lean) <> None then None
            else
            let n = B.type_path_to_name n0 t_path in
            let name_str = Name.to_string (Name.strip_lskip n) in
            let ctor_names = match ty with
              | Te_variant (_, ctors) ->
                Seplist.to_list_map (fun ((ctor_n, _), ctor_ref, _, _) ->
                  let cn = B.const_ref_to_name ctor_n false ctor_ref in
                  Name.to_string (Name.strip_lskip cn)
                ) ctors
              | _ -> []
            in
            Some (name_str, ctor_names)
      ) (Seplist.to_list defs) in
      let type_names = List.map fst type_info in
      (* Also register these for the auxiliary file (with namespace qualification) *)
      St.auxiliary_opens := !St.auxiliary_opens @ List.map lean_qualified_name type_names;
      let open_decls = flat (List.map (fun (name_str, ctor_names) ->
        if ctor_names = [] then
          (* Records/opaque types: just open *)
          from_string (String.concat "" ["\nopen "; name_str])
        else
          (* Inductive types: export constructors for cross-file visibility *)
          let ctors_str = String.concat " " ctor_names in
          from_string (String.concat "" ["\nexport "; name_str; " ("; ctors_str; ")"])
      ) type_info) in
      let n = Seplist.length defs in
      if n > 1 then
        (* Separate abbreviations from the mutual block — they are just type aliases
           and can't participate in mutual recursion. Emit them after the mutual block. *)
        let all_defs = Seplist.to_list defs in
        (* Partition into abbreviations (with extracted Te_abbrev data) and mutual types.
           Abbreviations can't participate in mutual recursion — they're type aliases.
           Extract Te_abbrev fields during partitioning so downstream code doesn't
           need to re-match on Te_abbrev. *)
        let mutual_defs, abbrev_extracted = List.fold_right (fun (((n0, _), tyvars, path, ty, _) as d) (mut, abbs) ->
          match ty with
          | Te_abbrev (skips, t) -> (mut, (n0, tyvars, path, skips, t) :: abbs)
          | _ -> (d :: mut, abbs)
        ) all_defs ([], []) in
        (* Collect mutual type paths to check if abbreviations reference them *)
        let mutual_paths = List.map (fun ((_, _), _, path, _, _) -> path) mutual_defs in
        (* Split abbreviations: those referencing mutual types go after,
           others go before (they may be needed by the mutual types). *)
        let abbrevs_before, abbrevs_after = List.partition
          (fun (_, _, _, _, t) -> not (src_t_references_paths mutual_paths t))
          abbrev_extracted in
        let render_abbrev (n0, tyvars, path, skips, t) =
          let n = B.type_path_to_name n0 path in
          let name = Name.to_output (Type_ctor (false, false)) n in
          let tyvars' = type_def_type_variables tyvars in
          let tyvar_sep = if List.length tyvars = 0 then emp else from_string " " in
          Output.flat [
            from_string "\nabbrev"; name; tyvar_sep; tyvars';
            ws skips; from_string " := "; pat_typ t
          ]
        in
        let abbrevs_before_output = flat @@ List.map render_abbrev abbrevs_before in
        let abbrevs_after_output = flat @@ List.map render_abbrev abbrevs_after in
        let mutual_n = List.length mutual_defs in
        (* Note: mutual record names are pre-collected in lean_defs before the
           main fold_right, so we don't register them here. See St.mutual_records
           pre-collection near St.local_modules. *)
        let mutual_output =
          if mutual_n > 1 then
            let mutual_sep = Seplist.from_list_default None mutual_defs in
            (* Check if all types in mutual block have the same number of type params *)
            let param_counts = List.map (fun (_, ty_vars, _, _, _) ->
              List.length ty_vars
            ) mutual_defs in
            let all_same = match param_counts with
              | [] -> true
              | x :: xs -> List.for_all (fun y -> y = x) xs
            in
            if all_same then
              let body = flat @@ Seplist.to_sep_list (type_def_variant false) (sep @@ from_string "\ninductive") mutual_sep in
              Output.flat [ from_string "mutual\ninductive"; body; from_string "\nend" ]
            else
              let body = flat @@ Seplist.to_sep_list type_def_indexed (sep @@ from_string "\ninductive") mutual_sep in
              Output.flat [ from_string "mutual\ninductive"; body; from_string "\nend" ]
          else if mutual_n = 1 then
            let single_sep = Seplist.from_list_default None mutual_defs in
            let body = flat @@ Seplist.to_sep_list (type_def_variant true) (sep @@ from_string "\n") single_sep in
            Output.flat [ from_string "inductive"; body ]
          else
            emp  (* All were abbreviations *)
        in
        (* Generate accessor functions for record types in the mutual block.
           Lean 4 doesn't create .field projectors for inductives in mutual blocks,
           so we emit explicit defs to enable dot notation. *)
        let accessor_defs = flat @@ List.filter_map (fun ((n0, _), ty_vars_raw, path, ty, _) ->
          match ty with
            | Te_record (_, _, fields, _) ->
              let n = B.type_path_to_name n0 path in
              let type_name = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip n)) in
              let tv_decl = String.concat "" @@ List.map (fun tv ->
                let s = tnvar_to_string tv in
                match tv with
                  | Typed_ast.Tn_A _ -> String.concat "" [" {"; s; " : Type}"]
                  | Typed_ast.Tn_N _ -> String.concat "" [" {"; s; " : Nat}"]
              ) ty_vars_raw in
              let tv_applied = String.concat " " @@ List.map tnvar_to_string ty_vars_raw in
              let tv_sep = if List.length ty_vars_raw = 0 then "" else " " in
              let field_list = Seplist.to_list fields in
              let n_fields = List.length field_list in
              let accessors = List.mapi (fun i ((fname, _), f_ref, _, src_t) ->
                let field_name = B.const_ref_to_name fname false f_ref in
                let field_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip field_name)) in
                let pre_wildcards = String.concat "" (List.init i (fun _ -> " _")) in
                let post = if i < n_fields - 1 then " .." else "" in
                Output.flat [
                  from_string (String.concat "" [
                    "\n@[inline] def "; type_name; "."; field_str;
                    tv_decl;
                    " (self : "; type_name; tv_sep; tv_applied;
                    ") : "
                  ]);
                  pat_typ src_t;
                  from_string (String.concat "" [
                    " :=\n  match self with | .mk";
                    pre_wildcards; " "; field_str; post; " => "; field_str
                  ])
                ]
              ) field_list in
              Some (flat accessors)
            | _ -> None
        ) mutual_defs in
        (* Abbreviations that don't reference mutual types go BEFORE (they may be
           needed by the mutual types). Abbreviations that DO reference mutual types
           go AFTER (they alias types defined in the block). *)
        let before_sep = if abbrevs_before = [] then emp else from_string "\n" in
        Output.flat [ abbrevs_before_output; before_sep; mutual_output; abbrevs_after_output; open_decls; accessor_defs; from_string "\n" ]
      else
        (* Check if this type has a Lean target_rep type (TYR_simple).
           If so, emit abbrev instead of inductive — the type is defined
           in external Lean code. Works for both opaque types and types
           with constructors that have their own target_reps. *)
        let ((n0, _), tyvars, t_path, ty, _) = Seplist.hd defs in
        let target_rep_abbrev =
            let l = Ast.Trans (false, "type_def", None) in
            let td = Types.type_defs_lookup l A.env.t_env t_path in
            begin match Target.Targetmap.apply_target td.Types.type_target_rep
                    (Target.Target_no_ident Target.Target_lean) with
              | Some (Types.TYR_simple (_, _, target_ident)) ->
                (* Collect import for the type target rep's module *)
                let target_id_str = Ident.to_string target_ident in
                (match String.index_opt target_id_str '.' with
                  | Some dot_pos when dot_pos > 0 ->
                    let mod_name = String.sub target_id_str 0 dot_pos in
                    if String.length mod_name > 0 &&
                       Char.uppercase_ascii mod_name.[0] = mod_name.[0] &&
                       not (List.mem mod_name !St.collected_imports) then
                      St.collected_imports := mod_name :: !St.collected_imports
                  | _ -> ());
                let name = B.type_path_to_name n0 t_path in
                let name_out = Name.to_output (Type_ctor (false, false)) name in
                let tyvars_out = type_def_type_variables tyvars in
                let tyvar_sep = if List.length tyvars = 0 then emp else from_string " " in
                Some (Output.flat [
                  from_string "abbrev "; name_out; tyvar_sep; tyvars_out;
                  from_string " := ";
                  Ident.to_output (Type_ctor (false, true)) (r".") target_ident;
                  from_string "\n"
                ])
              | _ -> None
            end
        in
        match target_rep_abbrev with
          | Some abbrev_out -> abbrev_out
          | None ->
            let body = flat @@ Seplist.to_sep_list (type_def_variant true) (sep @@ from_string "\n") defs in
            Output.flat [ from_string "inductive"; body; open_decls; from_string "\n" ]
    and type_def_variant emit_deriving ((n0, l), ty_vars, t_path, ty, _) =
      let n = B.type_path_to_name n0 t_path in
      let name = Name.to_output (Type_ctor (false, false)) n in
      let ty_vars =
        List.map tnvar_to_variable ty_vars
      in
        match ty with
          | Te_opaque ->
              Output.flat [
                inductive ty_vars n; from_string " : Type where"
              ]
          | _ ->
            Output.flat [
              inductive ty_vars n; from_string " : Type"; tyexp emit_deriving name ty_vars ty
            ]
    and type_def_indexed ((n0, l), ty_vars, t_path, ty, _) =
      (* Emit type with indices instead of parameters, for heterogeneous mutual blocks.
         Parameters become indices: inductive v : (a : Type) → (b : Type) → Type 1 where *)
      let n = B.type_path_to_name n0 t_path in
      let name = Name.to_output (Type_ctor (false, false)) n in
      let ty_vars_list =
        List.map tnvar_to_variable ty_vars
      in
      let indices =
        if List.length ty_vars_list = 0 then emp
        else
          let mapped = List.map (fun v ->
            match v with
              | Tyvar x -> Output.flat [ from_string "("; x; from_string " : Type) → " ]
              | Nvar x -> Output.flat [ from_string "("; x; from_string " : Nat) → " ]
          ) ty_vars_list in
          concat emp mapped
      in
      (* All types in a heterogeneous mutual block must live in the same universe.
         Since at least one type has indices (parameters promoted to indices),
         that type lives in Type 1, so ALL types must be Type 1. *)
      let universe = from_string "Type 1" in
      let ty_vars_names =
        concat_str " " @@ List.map (fun v ->
          match v with
            | Tyvar out -> out
            | Nvar out -> out
        ) ty_vars_list
      in
      let ty_vars_names_space = if List.length ty_vars_list = 0 then emp else from_string " " in
      match ty with
        | Te_variant (skips, ctors) ->
          let body = flat @@ Seplist.to_sep_list_first Seplist.Optional
            (constructor_indexed name ty_vars_list ty_vars_names ty_vars_names_space) (sep @@ from_string "\n") ctors in
          Output.flat [
            from_string " "; name; from_string " : "; indices; universe; from_string " where";
            ws skips; from_string "\n"; body
          ]
        | Te_opaque ->
          Output.flat [
            from_string " "; name; from_string " : "; indices; universe; from_string " where"
          ]
        | Te_record (_, _, fields, _) ->
          (* Records in heterogeneous mutual blocks: emit as single-constructor
             indexed inductive with named fields.  Use the same (fname : type) →
             syntax as tyexp's Te_record case but prefix implicit type bindings
             (like constructor_indexed) since parameters are promoted to indices. *)
          let field_list = Seplist.to_list fields in
          let mk_args = flat @@ List.map (fun ((n, _), f_ref, _skips, t) ->
            let fname = Name.add_lskip (Name.strip_lskip (B.const_ref_to_name n false f_ref)) in
            Output.flat [
              from_string "(";
              Name.to_output Term_field fname;
              from_string " :"; pat_typ t;
              from_string ") → "
            ]
          ) field_list in
          let implicit_bindings =
            if List.length ty_vars_list = 0 then emp
            else
              let mapped = List.map (fun v ->
                match v with
                  | Tyvar x -> Output.flat [ from_string "{"; x; from_string " : Type} → " ]
                  | Nvar x -> Output.flat [ from_string "{"; x; from_string " : Nat} → " ]
              ) ty_vars_list in
              concat emp mapped
          in
          Output.flat [
            from_string " "; name; from_string " : "; indices; universe; from_string " where\n";
            from_string "  | mk : "; implicit_bindings; mk_args;
            name; ty_vars_names_space; ty_vars_names
          ]
        | _ ->
          (* Te_abbrev is filtered out before reaching here; this catch-all
             handles any unexpected future type forms. *)
          Output.flat [
            from_string " "; name; from_string " : "; indices; universe; from_string " where"
          ]
    and constructor_indexed ind_name (ty_vars : variable list) ty_vars_names ty_vars_names_space ((name0, _), c_ref, skips, args) =
      let ctor_name = B.const_ref_to_name name0 false c_ref in
      let ctor_name = Name.to_output (Type_ctor (false, false)) ctor_name in
      let body = flat @@ Seplist.to_sep_list pat_typ (sep @@ from_string " → ") args in
      (* For indexed inductives, constructors must bind all type variables implicitly *)
      let implicit_bindings =
        if List.length ty_vars = 0 then emp
        else
          let mapped = List.map (fun v ->
            match v with
              | Tyvar x -> Output.flat [ from_string "{"; x; from_string " : Type} → " ]
              | Nvar x -> Output.flat [ from_string "{"; x; from_string " : Nat} → " ]
          ) ty_vars in
          concat emp mapped
      in
      let tail =
        Output.flat [
          from_string " → "; ind_name; ty_vars_names_space; ty_vars_names
        ]
      in
        if Seplist.length args = 0 then
          Output.flat [
            from_string "  | "; ctor_name; from_string " :"; ws skips; implicit_bindings; ind_name
          ; ty_vars_names_space; ty_vars_names
          ]
        else
          Output.flat [
            from_string "  | "; ctor_name; from_string " :"; ws skips; implicit_bindings; body; tail
          ]
    and inductive ty_vars name =
      let ty_var_sep = if List.length ty_vars = 0 then emp else from_string " " in
      let ty_vars = inductive_type_variables ty_vars in
      let name = Name.to_output (Type_ctor (false, false)) name in
        Output.flat [
          from_string " "; name; ty_var_sep; ty_vars
        ]
    and inductive_type_variables vars =
      let mapped = List.map (fun v ->
          match v with
            | Tyvar x ->
              Output.flat [
                from_string "("; x; from_string " : Type)"
              ]
            | Nvar x ->
              Output.flat [
                from_string "("; x; from_string " : Nat)"
              ]) vars
      in
        concat_str " " mapped
    and tyexp emit_deriving name ty_vars ty =
      match ty with
        | Te_opaque ->
            (* Unreachable: type_def_variant handles Te_opaque directly *)
            raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: unexpected Te_opaque in tyexp")
        | Te_abbrev _ ->
            (* Unreachable: def dispatches abbreviations to type_def_abbreviation *)
            raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: unexpected Te_abbrev in tyexp")
        | Te_record (_, _, fields, _) ->
            (* Records in mutual blocks: emit as single-constructor inductive
               (Lean 4 mutual blocks cannot contain structure definitions) *)
            let field_list = Seplist.to_list fields in
            let mk_args = flat @@ List.map (fun ((n, _), f_ref, _skips, t) ->
              let fname = Name.add_lskip (Name.strip_lskip (B.const_ref_to_name n false f_ref)) in
              Output.flat [
                from_string " (";
                Name.to_output Term_field fname;
                from_string " :"; pat_typ t;
                from_string ")"
              ]
            ) field_list in
            (* Build return type with applied type variables: e.g. "statement a" *)
            let ty_vars_applied =
              concat_str " " @@ List.map (fun v ->
                match v with
                  | Tyvar out -> out
                  | Nvar out -> out
              ) ty_vars
            in
            let ty_vars_sep = if List.length ty_vars = 0 then emp else from_string " " in
            Output.flat [
              from_string " where\n  | mk"; mk_args; from_string " : "; name; ty_vars_sep; ty_vars_applied
            ]
        | Te_variant (skips, ctors) ->
          let body = flat @@ Seplist.to_sep_list_first Seplist.Optional (constructor name ty_vars) (sep @@ from_string "\n") ctors in
          let is_all_nullary = Seplist.for_all (fun (_, _, _, args) -> Seplist.to_list args = []) ctors in
          let deriving_clause = if (emit_deriving || is_all_nullary) && texp_can_derive_beq ty then
            from_string "\n  deriving BEq, Ord"
          else emp in
            Output.flat [
              from_string " where"; ws skips; from_string "\n"; body; deriving_clause
            ]
    and constructor ind_name (ty_vars : variable list) ((name0, _), c_ref, skips, args) =
      let ctor_name = B.const_ref_to_name name0 false c_ref in
      let ctor_name = Name.to_output (Type_ctor (false, false)) ctor_name in
      let body = flat @@ Seplist.to_sep_list pat_typ (sep @@ from_string " → ") args in
      let ty_vars_typeset =
        concat_str " " @@ List.map (fun v ->
          match v with
            | Tyvar out -> out
            | Nvar out -> out
        ) ty_vars
      in
      let tail =
        Output.flat [
          from_string " → "; ind_name; from_string " "; ty_vars_typeset
        ]
      in
        if Seplist.length args = 0 then
          Output.flat [
            from_string "  | "; ctor_name; from_string " :"; ws skips; ind_name
          ; from_string " "; ty_vars_typeset
          ]
        else
          Output.flat [
            from_string "  | "; ctor_name; from_string " :"; ws skips; body; tail
          ]
    and pat_typ t =
      match t.term with
        | Typ_wild skips -> ws skips ^ from_string "_"
        | Typ_var (skips, v) ->
            Output.flat [
              ws skips; id Type_var @@ Ulib.Text.(^^^) (r"") (Tyvar.to_rope v)
            ]
        | Typ_fn (t1, skips, t2) ->
            if skips = Typed_ast.no_lskips then
              pat_typ t1 ^ from_string " → " ^ ws skips ^ pat_typ t2
            else
              pat_typ t1 ^ from_string " →" ^ ws skips ^ pat_typ t2
        | Typ_tup ts ->
            let body = flat @@ Seplist.to_sep_list pat_typ (sep @@ from_string " ×") ts in
              from_string "(" ^ body ^ from_string ")"
        | Typ_app (p, ts) ->
            if Path.compare p.descr Path.unitpath = 0 then
              let sk = Typed_ast.ident_get_lskip p in
              Output.flat [ ws sk; from_string "Unit" ]
            else
            let (ts_list, head) = B.type_app_to_output pat_typ p ts in
            let ts_out = concat_str " " @@ List.map pat_typ ts_list in
            let space = if ts_list = [] then emp else from_string " " in
              Output.flat [
                head; space; ts_out
              ]
        | Typ_paren(skips, t, skips') ->
            ws skips ^ from_string "(" ^ pat_typ t ^ ws skips' ^ from_string ")"
        | Typ_with_sort(t,_) -> raise (Reporting_basic.err_general true t.locn "Lean backend: target sort annotations are not supported")
        | Typ_len nexp -> src_nexp nexp
        | Typ_backend (p, ts) ->
          let i = Path.to_ident (ident_get_lskip p) p.descr in
          let i = Ident.to_output (Type_ctor (false, true)) path_sep i in
          let ts_out = List.map pat_typ ts in
          let space = if ts_out = [] then emp else from_string " " in
            Output.flat [
              i; space; concat_str " " ts_out
            ]
    and type_def_type_variables tvs =
      match tvs with
        | [] -> emp
        | [Typed_ast.Tn_A tv] -> from_string "(" ^ tyvar tv ^ from_string " : Type)"
        | tvs ->
          let mapped = List.map (fun t ->
            let name = tnvar_to_string t in
            Output.flat [from_string "("; from_string name; from_string " : "; from_string (tnvar_kind t); from_string ")"]
          ) tvs
          in
            Output.flat [
              from_string " "; concat_str " " mapped
            ]
    and indreln_typ t =
      match t.term with
        | Typ_wild skips -> ws skips ^ from_string "_"
        | Typ_var (skips, v) -> ws skips ^ (id Type_var @@ Ulib.Text.(^^^) (r"") (Tyvar.to_rope v))
        | Typ_fn (t1, skips, t2) ->
          begin
            match t2.term with
              | Typ_app (p, []) ->
                if p.descr = Path.boolpath then
                  indreln_typ t1 ^ ws skips ^ from_string " → " ^ from_string "Prop"
                else
                  indreln_typ t1 ^ ws skips ^ from_string " → " ^ indreln_typ t2
              | _ ->
                indreln_typ t1 ^ ws skips ^ from_string " → " ^ indreln_typ t2
          end
        | Typ_tup ts ->
            let body = flat @@ Seplist.to_sep_list indreln_typ (sep @@ from_string " ×") ts in
              from_string "(" ^ body ^ from_string ")"
        | Typ_app (p, ts) ->
          (* Use type_app_to_output to handle target reps (e.g. set → List) *)
          let (remaining_ts, name_output) = B.type_app_to_output indreln_typ p ts in
          let args = concat_str " " @@ List.map indreln_typ remaining_ts in
          let args_space = if remaining_ts <> [] then from_string " " else emp in
            Output.flat [
              name_output; args_space; args
            ]
        | Typ_paren(skips, t, skips') ->
            ws skips ^ from_string "(" ^ indreln_typ t ^ from_string ")" ^ ws skips'
        | Typ_with_sort(t, _) -> indreln_typ t
        | Typ_len nexp -> src_nexp nexp
        | Typ_backend (p, ts) ->
          let i = Path.to_ident (ident_get_lskip p) p.descr in
          let i = Ident.to_output (Type_ctor (false, true)) path_sep i in
          let ts_out = List.map indreln_typ ts in
          let space = if ts_out = [] then emp else from_string " " in
            Output.flat [
              i; space; concat_str " " ts_out
            ]
    and field ((n, _), f_ref, _skips, t) =
      let fname = Name.add_lskip (Name.strip_lskip (B.const_ref_to_name n false f_ref)) in
      Output.flat [
          from_string "  ";
          Name.to_output Term_field fname;
          from_string " :"; pat_typ t
      ]
    (* --- Instance generation ---
       For each type definition, generates:
       1. Inhabited instance(s): tier 1 (safe constructor) or tier-2
          per-constructor bounded derivation (arc-8 S1; fail-closed —
          underivable types get no instance and backend-visible demands
          on them are generation-time errors)
       2. BEq + Ord (via `deriving` if possible; otherwise derived
          structural comparisons (arc-10 S2b) or loud failwithI residuals
          — NO sorry emission path; Type-1 blocks are a generation-time
          error (arc-10 audit fix), fail-closed like the Inhabited path)
       3. SetType / Eq0 / Ord0 instances (with [BEq]/[Ord] constraints for parameterized types)
       Mutual types use find_safe_ctor_for_mutual to avoid self-referential defaults.
       Library opaque types (phantom types like ty1..ty4096) skip instance generation. *)
    (* src_t_references_paths / src_t_is_directly_mutual /
       find_safe_ctor_for_mutual / the derivability analysis now live at
       top level (shared with lean_inhabited_prepass, arc-8 S1). *)
    (* Arc-8 S1 fail-closed demand check (design note rule 5, charter
       durability req 2): the backend is about to emit a value-level
       `default` — an Inhabited demand it KNOWS about, inside a generated
       instance body — at an applied type. If the census says derivation
       FAILED for that type (Inh_none), refuse at generation time, naming
       the type and both escape hatches. *)
    and inhabited_demand_check (p : Path.t) : unit =
      if inhabited_census_debug then
        Printf.eprintf "DEMAND check %s -> %s\n%!" (Path.to_string p)
          (match inhabited_census_lookup p with None -> "absent" | Some (_, Inh_none) -> "NONE" | Some (_, Inh_instances _) -> "inst");
      match inhabited_census_lookup p with
        | Some (n, Inh_none) ->
          raise (Reporting_basic.err_general true Ast.Unknown (Printf.sprintf
            "Lean backend: cannot derive an Inhabited instance for type '%s' (no constructor with derivably-inhabitable fields), but generated code demands one; escape hatches: 'declare {lean} skip_instances type %s' plus a hand-written Lean instance, or 'declare lean target_rep type %s' mapping it to a hand-written Lean type" n n n))
        | _ -> ()
    (* Render the [Inhabited tv] binders for the bound tyvars, in the
       type's parameter declaration order. *)
    and inhabited_bound_binders tnvar_list (bounds : string list) : Output.t =
      Output.flat (List.filter_map (fun tv ->
        let n = tnvar_to_string tv in
        if List.mem n bounds then
          Some (Output.flat [from_string " [Inhabited "; from_string n; from_string "]"])
        else None) tnvar_list)
    (* Default value for a source type in Inhabited context.
       mutual_name_map: when non-empty, direct references to mutual types use
       TypeName.default_inhabited instead of default (for mutual def blocks
       where Inhabited instances don't exist yet). *)
    and default_value_inhabited ?(mutual_name_map=[]) (s : src_t) : Output.t =
      let recurse = default_value_inhabited ~mutual_name_map in
      match s.term with
        | Typ_app (id, _) when mutual_name_map <> [] ->
          (match List.assoc_opt id.descr mutual_name_map with
            | Some type_name_str -> from_string (String.concat "" [type_name_str; ".default_inhabited"])
            | None -> (inhabited_demand_check id.descr; from_string "default"))
        | Typ_app (id, _) -> inhabited_demand_check id.descr; from_string "default"
        | Typ_wild _ | Typ_var _ | Typ_backend _ -> from_string "default"
        | Typ_len _ -> from_string "0"
        | Typ_tup seplist ->
            let mapped = List.map recurse (Seplist.to_list seplist) in
            Output.flat [from_string "("; concat_str ", " mapped; from_string ")"]
        | Typ_paren (_, src_t, _)
        | Typ_with_sort (src_t, _) -> recurse src_t
        | Typ_fn (dom, _, rng) ->
            let v = generate_fresh_name () in
            Output.flat [
              from_string "(fun ("; from_string v; from_string " : "; pat_typ dom;
              from_string ") => "; recurse rng; from_string ")"
            ]
    and generate_default_value_texp (t: texp) =
      match t with
        | Te_opaque ->
          (* Arc-8 S2 (D4): opaque types are tier-2/fail-closed — they
             never reach the tier-1 default renderer. The former
             `default := sorry` fallback instance is gone. *)
          raise (Reporting_basic.err_general true Ast.Unknown
            "Lean backend: Te_opaque in generate_default_value_texp is unreachable (opaque types are fail-closed, arc-8 S2)")
        | Te_abbrev (_, src_t) -> default_value_inhabited src_t
        | Te_record (_, _, seplist, _) ->
            let fields = Seplist.to_list seplist in
            let mapped = List.map (fun ((name, _), const_descr_ref, _, src_t) ->
              let name = B.const_ref_to_name name true const_descr_ref in
              let o = lskips_t_to_output name in
              let s = default_value_inhabited src_t in
              Output.flat [o; from_string " := "; s]
            ) fields in
            Output.flat [from_string "{ "; concat_str ", " mapped; from_string " }"]
        | Te_variant _ ->
            raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: Te_variant in generate_default_value_texp is unreachable")
    (* Render a constructor call for an Inhabited default value *)
    and render_ctor_default ?(mutual_name_map=[]) ((ctor_name, _), ctor_ref, _, src_ts) =
      let n = B.const_ref_to_name ctor_name false ctor_ref in
      let ys = Seplist.to_list src_ts in
      let mapped = List.map (default_value_inhabited ~mutual_name_map) ys in
      let sep = if List.length mapped = 0 then emp else from_string " " in
      Output.flat [lskips_t_to_output n; sep; concat_str " " mapped]
    (* Compute whether to skip Inhabited for this type (abbreviations, types with
       target_rep, or types annotated with 'declare {lean} skip instances') *)
    and skip_inhabited_for_type t path =
      skip_inhabited_for_type_env A.env t path
    (* Compute the default value expression for a TIER-1 Inhabited instance.
       mutual_name_map: (Path.t * string) list mapping mutual type paths to their
       Lean names. When non-empty, uses TypeName.default_inhabited for mutual type
       args (for use inside mutual def blocks where Inhabited instances don't exist yet). *)
    (* Returns None when tier 1 has no safe constructor: the caller must
       then render the pre-pass tier-2 plan (per-constructor bounded
       instances — arc-8 S1; the DAEMON fallback is gone). The tier
       split itself is inhabited_needs_tier2 (top level, shared with the
       pre-pass so the plan and the emission can never disagree). *)
    and inhabited_default_expr ?(mutual_name_map=[]) mutual_paths (((name, _), tnvar_list, path, t, _) as td) : Output.t option =
      if inhabited_needs_tier2 mutual_paths td then None
      else if tnvar_list = [] then
        Some (match t with
          | Te_variant (_, seplist) ->
            let ctors = Seplist.to_list seplist in
            (match find_safe_ctor_for_mutual mutual_paths ctors with
              | Some ctor -> render_ctor_default ~mutual_name_map ctor
              | None ->
                let safe_indirect = List.find_opt (fun (_, _, _, src_ts) ->
                  let args = Seplist.to_list src_ts in
                  not (List.exists (src_t_is_directly_mutual [path]) args)
                ) ctors in
                (match safe_indirect with
                  | Some ctor -> render_ctor_default ~mutual_name_map ctor
                  | None ->
                    raise (Reporting_basic.err_general true Ast.Unknown
                      "Lean backend: inhabited_default_expr tier-1 variant disagrees with inhabited_needs_tier2 (internal)")))
          | Te_record (_, _, fields, _) when List.length mutual_paths > 1 ->
            let field_list = Seplist.to_list fields in
            let field_defaults = List.map (fun (_, _, _, src_t) -> default_value_inhabited ~mutual_name_map src_t) field_list in
            let type_name = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip (B.type_path_to_name name path))) in
            Output.flat [from_string type_name; from_string ".mk "; concat_str " " field_defaults]
          | _ -> generate_default_value_texp t)
      else
        (* Parameterized types: tier 1 covers nullary constructors only. *)
        Some (match t with
          | Te_variant (_, seplist) ->
            let ctors = Seplist.to_list seplist in
            (match List.find_opt (fun (_, _, _, src_ts) ->
              Seplist.to_list src_ts = []) ctors with
              | Some ctor -> render_ctor_default ~mutual_name_map ctor
              | None ->
                raise (Reporting_basic.err_general true Ast.Unknown
                  "Lean backend: inhabited_default_expr tier-1 parameterized disagrees with inhabited_needs_tier2 (internal)"))
          | _ ->
            raise (Reporting_basic.err_general true Ast.Unknown
              "Lean backend: inhabited_default_expr tier-1 non-variant parameterized disagrees with inhabited_needs_tier2 (internal)"))
    (* Type variable binding + type args for Inhabited instance header *)
    and inhabited_type_parts tnvar_list =
      let tnvar_list' =
        if tnvar_list = [] then emp
        else
          (* Unconstrained {a : Type} bindings. Tier-1 instances (nullary/
             safe ctors) need no [Inhabited a] constraints; tier-2 derived
             instances append their [Inhabited tv] binders separately
             (inhabited_bound_binders, arc-8 S1). *)
          let tvs = List.map (fun tv ->
            match tv with
            | Typed_ast.Tn_A (_, r, _) -> Types.Ty (Tyvar.from_rope r)
            | Typed_ast.Tn_N (_, r, _) -> Types.Nv (Nvar.from_rope r)
          ) tnvar_list in
          let_type_variables true (Types.TNset.of_list tvs)
      in
      let tnvar_names = concat_str " " @@ List.map (fun x -> from_string (tnvar_to_string x)) tnvar_list in
      let type_args =
        if List.length tnvar_list = 0 then emp
        else Output.flat [from_string " "; tnvar_names]
      in
      (tnvar_list', type_args)
    (* Arc-8 S1 tier 2: per-constructor bounded derivation (design note
       rules 2-5), replacing the DAEMON fallback. For each constructor
       whose fields are all derivably inhabitable, emit one bounded
       instance — the first at default priority, the rest at
       (priority := low), the LemLib Sum inl/inr pair precedent
       (lean-lib/LemLib.lean:90-91). Fail-closed: no usable constructor
       -> NO instance and NO fallback of any kind; the type is
       census-recorded Inh_none so any backend-visible demand on it is a
       generation-time error (inhabited_demand_check). The derivation
       itself was computed by lean_inhabited_prepass in DECLARATION
       order (emission runs fold_right, last-to-first); this function
       only renders the stored plan. *)
    and generate_tier2_inhabited (((name, _), tnvar_list, path, t, _)) : Output.t =
      let type_name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip (B.type_path_to_name name path))) in
      let name_out = lskips_t_to_output (B.type_path_to_name name path) in
      let (tnvar_list', type_args) = inhabited_type_parts tnvar_list in
      let emit_instances (bodies : (Output.t * string list) list) : Output.t =
        Output.flat (List.mapi (fun i (body, bounds) ->
          let inst_kw = if i = 0 then "instance" else "\ninstance (priority := low)" in
          Output.flat [
            from_string inst_kw; tnvar_list'; inhabited_bound_binders tnvar_list bounds;
            from_string " : Inhabited ("; name_out; type_args;
            from_string ") where\n  default := "; body;
          ]) bodies)
      in
      match inhabited_plan_lookup path, t with
        | (None | Some Plan_none), _ ->
          (* Fail-closed: no usable constructor -> no instance, no
             fallback of any kind. Demands error via inhabited_demand_check. *)
          emp
        | Some (Plan_variant usable), Te_variant (_, seplist) ->
          let ctors = Array.of_list (Seplist.to_list seplist) in
          emit_instances (List.map (fun (i, bounds) ->
            (render_ctor_default ctors.(i), bounds)) usable)
        | Some (Plan_record bounds), Te_record (_, _, fields, _) ->
          let field_list = Seplist.to_list fields in
          let field_defaults = List.map (fun (_, _, _, src_t) -> default_value_inhabited src_t) field_list in
          let body = Output.flat [from_string type_name_str; from_string ".mk "; concat_str " " field_defaults] in
          emit_instances [(body, bounds)]
        | _ ->
          raise (Reporting_basic.err_general true Ast.Unknown (Printf.sprintf
            "Lean backend: tier-2 Inhabited plan for type '%s' does not match its definition shape (internal pre-pass/emission mismatch)" type_name_str))
    (* Generate a single Inhabited instance (non-mutual or single-type blocks) *)
    and generate_inhabited_instance mutual_paths (((name, _), tnvar_list, path, t, _) as td) : Output.t =
      if skip_inhabited_for_type t path then emp
      else
      let name_out = lskips_t_to_output (B.type_path_to_name name path) in
      match inhabited_default_expr mutual_paths td with
        | None -> generate_tier2_inhabited td
        | Some default ->
          let (tnvar_list', type_args) = inhabited_type_parts tnvar_list in
          Output.flat [
            from_string "instance"; tnvar_list'; from_string " : Inhabited ("; name_out;
            type_args;
            from_string ") where\n  default := "; default;
          ]
    (* Generate mutual def + instance pairs for Inhabited on mutual type blocks.
       Uses `mutual def ... end` so forward references between defaults are allowed,
       then non-mutual `instance` declarations referencing those defs. *)
    and generate_inhabited_mutual mutual_paths ts_list : Output.t =
      (* Filter to types that need Inhabited *)
      let active = List.filter (fun (_, _, path, t, _) ->
        not (skip_inhabited_for_type t path)) ts_list in
      if active = [] then emp
      else if List.length active = 1 then
        (* Single type remaining: no need for mutual def *)
        generate_inhabited_instance mutual_paths (List.hd active)
      else
      (* Build path → type name mapping for mutual def references.
         Inside the mutual def block, we can't use `default` (Inhabited not defined yet),
         so direct mutual type args use TypeName.default_inhabited instead. *)
      let mutual_name_map = List.map (fun ((name, _), _, path, _, _) ->
        let type_name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip (B.type_path_to_name name path))) in
        (path, type_name_str)
      ) active in
      (* Compute defaults and split into tier 1 (real ctors, need mutual def)
         and tier 2 (arc-8 S1: per-constructor derived bounded instances
         rendered from the pre-pass plan). *)
      let typed_defaults = List.map (fun (((name, _), tnvar_list, path, _, _) as td) ->
        let type_name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip (B.type_path_to_name name path))) in
        let name_out = lskips_t_to_output (B.type_path_to_name name path) in
        let default_opt = inhabited_default_expr ~mutual_name_map mutual_paths td in
        (type_name_str, name_out, tnvar_list, default_opt, td)
      ) active in
      let tier1 = List.filter_map (fun (tns, no, tvs, d, td) ->
        match d with Some d -> Some (tns, no, tvs, d, td) | None -> None) typed_defaults in
      let tier2 = List.filter_map (fun (_, _, _, d, td) ->
        match d with None -> Some td | Some _ -> None) typed_defaults in
      (* Tier 1: mutual def block with real constructor defaults *)
      let mutual_block = if tier1 = [] then emp else
        let defs = List.map (fun (type_name_str, name_out, tnvar_list, default, _) ->
          let (tnvar_list', type_args) = inhabited_type_parts tnvar_list in
          Output.flat [
            from_string "def "; from_string type_name_str; from_string ".default_inhabited";
            tnvar_list'; from_string " : "; name_out; type_args;
            from_string " := "; default;
          ]
        ) tier1 in
        let instances = List.map (fun (type_name_str, _, tnvar_list, _, _) ->
          let (tnvar_list', type_args) = inhabited_type_parts tnvar_list in
          Output.flat [
            from_string "\ninstance"; tnvar_list'; from_string " : Inhabited (";
            from_string type_name_str; type_args;
            from_string ") where\n  default := "; from_string type_name_str;
            from_string ".default_inhabited";
          ]
        ) tier1 in
        Output.flat [
          from_string "mutual\n"; concat_str "\n" defs;
          from_string "\nend"; concat emp instances;
        ]
      in
      (* Tier 2 (arc-8 S1): per-constructor derived instances (from the
         pre-pass plan), emitted in declaration order after the tier-1
         instances — so tier-2 bodies may resolve through every tier-1
         instance of the block and every EARLIER tier-2 sibling's
         instances, exactly as the pre-pass assumed. *)
      let tier2_instances = List.map (fun td ->
        Output.flat [from_string "\n"; generate_tier2_inhabited td]) tier2 in
      Output.flat [mutual_block; concat emp tier2_instances]
    and generate_beq_ord_instances ?(is_type1=false) ?(emit_deriving=true) ?derived_cmp ((name, _), tnvar_list, path, t, _) : Output.t =
      (* Skip instance generation for abbreviations, types with target reps,
         and types annotated with 'declare {lean} skip instances'. *)
      let skip_instances = match t with
        | Te_abbrev _ -> true
        | _ ->
          let l = Ast.Trans (false, "generate_beq_ord_instances", None) in
          let td = Types.type_defs_lookup l A.env.t_env path in
          (* Skip if declared with 'skip instances' for Lean *)
          Target.Targetset.mem Target.Target_lean td.Types.type_skip_instances ||
          Target.Targetmap.apply_target td.Types.type_target_rep
            (Target.Target_no_ident Target.Target_lean) <> None
      in
      if skip_instances then emp
      else
      match t with
        | Te_abbrev _ ->
          raise (Reporting_basic.err_general true Ast.Unknown
            "Lean backend: Te_abbrev in generate_beq_ord_instances should be unreachable (skip_instances handles it)")
        | _ ->
          let n = B.type_path_to_name name path in
          let o = lskips_t_to_output n in
          let tnvar_names = concat_str " " @@ List.map (fun x -> from_string (tnvar_to_string x)) tnvar_list in
          let type_args =
            if List.length tnvar_list = 0 then emp
            else Output.flat [from_string " "; tnvar_names]
          in
          (* If the type uses deriving BEq, Ord (emitted by tyexp), skip sorry
             BEq/Ord instances. Mutual types normally can't use deriving
             (emit_deriving=false), but all-nullary enums in mutual blocks
             CAN derive — they have no args so no dependency on other types. *)
          let is_all_nullary = match t with
            | Te_variant (_, ctors) ->
              Seplist.for_all (fun (_, _, _, args) -> Seplist.to_list args = []) ctors
            | _ -> false
          in
          let has_deriving = (emit_deriving || is_all_nullary) && texp_can_derive_beq t in
          let type_name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip n)) in
          let bare_tvs = concat emp @@ List.map (fun t ->
            let name = tnvar_to_string t in
            let kind = tnvar_kind t in
            Output.flat [from_string " {"; from_string name; from_string " : "; from_string kind; from_string "}"]
          ) tnvar_list in
          (* Arc-10 S2: render " [Cls tv]" binders for the given tyvar names,
             in parameter-declaration order (the inhabited_bound_binders
             pattern applied to comparison classes). *)
          let cls_bounds cls (bounds : string list) : Output.t =
            Output.flat (List.filter_map (fun tv ->
              let tn = tnvar_to_string tv in
              if List.mem tn bounds then
                Some (Output.flat [from_string " ["; from_string cls; from_string " "; from_string tn; from_string "]"])
              else None) tnvar_list)
          in
          (* All Type-kind parameters — the bound set used for the
             deriving-bridge on PARAMETERIZED deriving types (Lean's own
             derived BEq/Ord instances carry per-parameter constraints). *)
          let all_ty_tvs = List.filter_map (fun tv ->
            match tv with
              | Typed_ast.Tn_A _ -> Some (tnvar_to_string tv)
              | Typed_ast.Tn_N _ -> None) tnvar_list in
          (* Loud residual body (arc-10 S2): failwithI replaces the historical
             `sorry` bodies — axiom-free, honest-panic (the arc-8 convention;
             mirrors OCaml raising Invalid_argument when polymorphic
             comparison reaches a closure). Two labeled residual classes:
             - "carries function-typed fields": the type itself is
               underivable (OCaml comparison would raise on its closures);
             - "unconstrained type variable": the bounded real instance
               exists but a lem default-instance use site erased the
               dictionary (fallback, priority below the bounded instance). *)
          let residual_body cls reason =
            String.concat "" ["failwithI \"Lean backend: comparison residual: "; cls; " ("; type_name_str; "): "; reason; "\""] in
          let fn_reason = "type carries function-typed fields (OCaml polymorphic comparison raises on closures)" in
          let tv_reason = "demanded at an unconstrained type variable (lem default instance erased the dictionary); the bounded real instance needs concrete comparable arguments" in
          let residual_beq_ord reason priority_kw =
            (Output.flat [
              from_string priority_kw; bare_tvs; from_string " : BEq ("; o;
              type_args;
              from_string ") where\n  beq _ _ := "; from_string (residual_body "BEq" reason);
            ],
            Output.flat [
              from_string priority_kw; bare_tvs; from_string " : Ord ("; o;
              type_args;
              from_string ") where\n  compare _ _ := "; from_string (residual_body "Ord" reason);
            ])
          in
          let beq_instance, ord_instance =
            if has_deriving then (emp, emp)
            else if is_type1 then
              (* Type-1 universe (heterogeneous parameter counts in the
                 mutual block): FAIL-CLOSED (arc-10 audit fix, auditor A
                 F1). The historical `:= sorry` residual bodies are
                 DELETED — no opaque-inhabitant emission path may remain
                 (the arc-8 convention; population is empty today, so
                 any future Type-1 type reaching instance emission is a
                 loud generation-time error naming the escape hatches,
                 exactly like the Inhabited path). *)
              raise (Reporting_basic.err_general true Ast.Unknown
                (Printf.sprintf
                  "Lean backend: cannot derive BEq/Ord instances for type '%s': heterogeneous type-parameter counts put its mutual block in the Type 1 universe (the historical sorry-bodied residual instances are deleted, arc-10 audit fix); escape hatches: 'declare {lean} skip_instances type %s' plus hand-written Lean instances where demanded, or 'declare lean target_rep type %s' mapping it to a hand-written Lean type"
                  type_name_str type_name_str type_name_str))
            else match derived_cmp with
              | Some bounds ->
                (* Arc-10 S2: REAL instances over the derived structural
                   comparison functions (emitted by
                   generate_derived_comparisons in this type's mutual
                   block). DEFAULT priority — the same standing Lean's own
                   `deriving BEq, Ord` instances get: LemLib's generic
                   default-priority bridges ([MapKeyType a] : BEq a,
                   [Eq0 a] : BEq a, [SetType a] : BEq a) would otherwise
                   shadow a low-priority real instance and complete
                   through the unconstrained failwithI fallback.
                   Hand-written override instance files still win: equal
                   priority resolves newest-declaration-first, and
                   override files import the generated module. *)
                (Output.flat [
                  from_string "\ninstance"; bare_tvs; cls_bounds "BEq" bounds;
                  from_string " : BEq ("; o; type_args;
                  from_string ") where\n  beq := "; from_string type_name_str; from_string ".beq_derived";
                ],
                Output.flat [
                  from_string "\ninstance"; bare_tvs; cls_bounds "Ord" bounds;
                  from_string " : Ord ("; o; type_args;
                  from_string ") where\n  compare := "; from_string type_name_str; from_string ".compare_derived";
                ])
              | None -> residual_beq_ord fn_reason "\ninstance (priority := low)"
          in
          (* Unconstrained fallbacks for bounded real instances (parameterized
             types only): lem's unconstrained default instances mean generated
             polymorphic code may demand these classes at OPEN type variables
             (no dictionary); priority strictly below the bounded instance so
             it is only reached when the bounds cannot be synthesized. *)
          let fallback_beq_ord =
            match derived_cmp with
              | Some bounds when tnvar_list <> [] && bounds <> [] ->
                let (b, o_) = residual_beq_ord tv_reason "\ninstance (priority := 50)" in
                Output.flat [b; o_]
              | _ -> emp
          in
          (* SetType/Eq0/Ord0 are defined for (a : Type) only, skip for Type 1 *)
          if is_type1 then Output.flat [beq_instance; ord_instance]
          else
            (* SetType/Eq0/Ord0 (lem classes): bridge to the Lean BEq/Ord
               instances wherever those are real — derived-with-`deriving`
               (monomorphic: unconditional, default priority — the
               historical emission; parameterized: [BEq tv]/[Ord tv]
               bounds, arc-10 S2) or comparison-derived (bounds from the
               derivation plan). Residual types (and the open-tyvar fallback
               for parameterized ones) carry loud failwithI bodies. *)
            let real_trio (bounds : string list) (inst_kw : string) : Output.t =
              Output.flat [
                from_string inst_kw; bare_tvs; cls_bounds "Ord" bounds;
                from_string " : Lem_Basic_classes.SetType ("; o; type_args;
                from_string ") where\n  setElemCompare := defaultCompare";
                from_string inst_kw; bare_tvs; cls_bounds "BEq" bounds;
                from_string " : Lem_Basic_classes.Eq0 ("; o; type_args;
                from_string ") where\n  isEqual x y := x == y\n  isInequal x y := !(x == y)";
                from_string inst_kw; bare_tvs; cls_bounds "Ord" bounds;
                from_string " : Lem_Basic_classes.Ord0 ("; o; type_args;
                from_string ") where\n  compare := defaultCompare\n  isLess := defaultLess\n  isLessEqual := defaultLessEq\n  isGreater := defaultGreater\n  isGreaterEqual := defaultGreaterEq";
              ]
            in
            (* Trio for comparison-DERIVED types: bodies call the derived
               functions DIRECTLY (no `==`/defaultCompare instance
               indirection, which LemLib's generic default-priority
               bridges could reroute through a fallback). *)
            let derived_trio (bounds : string list) : Output.t =
              let bd = from_string type_name_str in
              let lem_of_cmp x y =
                Output.flat [
                  from_string "match "; bd; from_string ".compare_derived "; from_string x;
                  from_string " "; from_string y;
                  from_string " with | .lt => LemOrdering.LT | .eq => LemOrdering.EQ | .gt => LemOrdering.GT";
                ] in
              let bool_of_cmp x y arms =
                Output.flat [
                  from_string "match "; bd; from_string ".compare_derived "; from_string x;
                  from_string " "; from_string y; from_string (String.concat "" [" with "; arms]);
                ] in
              Output.flat [
                from_string "\ninstance"; bare_tvs; cls_bounds "Ord" bounds;
                from_string " : Lem_Basic_classes.SetType ("; o; type_args;
                from_string ") where\n  setElemCompare x y := "; lem_of_cmp "x" "y";
                from_string "\ninstance"; bare_tvs; cls_bounds "BEq" bounds;
                from_string " : Lem_Basic_classes.Eq0 ("; o; type_args;
                from_string ") where\n  isEqual := "; bd; from_string ".beq_derived";
                from_string "\n  isInequal x y := !("; bd; from_string ".beq_derived x y)";
                from_string "\ninstance"; bare_tvs; cls_bounds "Ord" bounds;
                from_string " : Lem_Basic_classes.Ord0 ("; o; type_args;
                from_string ") where\n  compare x y := "; lem_of_cmp "x" "y";
                from_string "\n  isLess x y := "; bool_of_cmp "x" "y" "| .lt => true | _ => false";
                from_string "\n  isLessEqual x y := "; bool_of_cmp "x" "y" "| .gt => false | _ => true";
                from_string "\n  isGreater x y := "; bool_of_cmp "x" "y" "| .gt => true | _ => false";
                from_string "\n  isGreaterEqual x y := "; bool_of_cmp "x" "y" "| .lt => false | _ => true";
              ]
            in
            let residual_trio reason inst_kw : Output.t =
              Output.flat [
                from_string inst_kw; bare_tvs; from_string " : Lem_Basic_classes.SetType ("; o;
                type_args;
                from_string ") where\n  setElemCompare _ _ := "; from_string (residual_body "SetType" reason);
                from_string inst_kw; bare_tvs; from_string " : Lem_Basic_classes.Eq0 ("; o;
                type_args;
                from_string ") where\n  isEqual _ _ := "; from_string (residual_body "Eq0" reason);
                from_string "\n  isInequal _ _ := "; from_string (residual_body "Eq0" reason);
                from_string inst_kw; bare_tvs; from_string " : Lem_Basic_classes.Ord0 ("; o;
                type_args;
                from_string ") where\n  compare _ _ := "; from_string (residual_body "Ord0" reason);
                from_string "\n  isLess _ _ := "; from_string (residual_body "Ord0" reason);
                from_string "\n  isLessEqual _ _ := "; from_string (residual_body "Ord0" reason);
                from_string "\n  isGreater _ _ := "; from_string (residual_body "Ord0" reason);
                from_string "\n  isGreaterEqual _ _ := "; from_string (residual_body "Ord0" reason);
              ]
            in
            (* Fallback trio for any parameterized type whose trio is real
               (deriving-bridge or derived): the open-tyvar demand class. *)
            let fallback_trio =
              if tnvar_list = [] then emp
              else if has_deriving || derived_cmp <> None
              then residual_trio tv_reason "\ninstance (priority := 50)"
              else emp
            in
            Output.flat [
              beq_instance;
              ord_instance;
              fallback_beq_ord;
              (if has_deriving && tnvar_list = [] then real_trio [] "\ninstance"
               else if has_deriving then real_trio all_ty_tvs "\ninstance"
               else match derived_cmp with
                 | Some bounds -> derived_trio bounds
                 | None -> residual_trio fn_reason "\ninstance (priority := low)");
              fallback_trio;
            ]
    (* ===== Arc-10 S2: derived structural comparisons for mutual blocks =====
       For every derivable type of a (homogeneous-parameter) mutual block,
       emit total mutual `beq_derived` / `compare_derived` functions plus
       the specialized container helpers structural recursion needs, then
       let generate_beq_ord_instances bridge the BEq/Ord/SetType/Eq0/Ord0
       instances onto them.

       PARITY CONVENTION (OCaml polymorphic (=) / compare, the arc-4
       CerbStepInstances precedent):
       - equality is structural: same constructor + equal fields;
       - compare ranks constructors like the OCaml runtime
         (runtime/compare.c): NULLARY constructors are immediates and sort
         BELOW every non-nullary (block) constructor; within each class,
         declaration order; equal constructors compare fields left-to-right
         lexicographically (ctor_rank_ocaml encodes the two-class rank);
       - list: [] (immediate) < _::_ (block), then elementwise lex;
         maybe: None < Some; either: Left/inl < Right/inr — each matching
         the OCaml value representation of the corresponding lem library
         type;
       - leaf fields (no mutual sibling inside) compare through their Lean
         BEq/Ord instances. NOTE (registered): for MIXED nullary/non-nullary
         variants whose Ord comes from Lean `deriving Ord`, that leaf order
         is Lean's flat constructor index, which diverges from the OCaml
         two-class rank — a pre-existing deriving-path divergence, recorded
         in the arc-10 register, NOT introduced here.

       FAIL-CLOSED: types whose comparison cannot be honestly derived
       (function-typed fields anywhere — where OCaml (=)/compare RAISE —
       or references to such siblings, or siblings under unsupported
       container heads) are left exactly as before: sorried residual
       instances, explicitly counted, overridable by hand instance files.
       Underivability PROPAGATES: a "derived" body is never routed through
       a sorried instance. *)
    and lean_output_str (o : Output.t) : string =
      Ulib.Text.to_string (to_rope (r"\"") lex_skip need_space o)
    and lean_typ_render (ty : Types.t) : string =
      lean_output_str (pat_typ (C.t_to_src_t ty))
    and generate_derived_comparisons ts_list : Output.t * (Path.t * string list) list =
      let d = A.env.t_env in
      let l = Ast.Trans (false, "generate_derived_comparisons", None) in
      let non_abbrev = List.filter (fun (_, _, _, t, _) ->
        match t with Te_abbrev _ -> false | _ -> true) ts_list in
      let skip_type path =
        let td = Types.type_defs_lookup l A.env.t_env path in
        Target.Targetset.mem Target.Target_lean td.Types.type_skip_instances ||
        Target.Targetmap.apply_target td.Types.type_target_rep
          (Target.Target_no_ident Target.Target_lean) <> None
      in
      let deriving_covered t = match t with
        | Te_variant (_, ctors) ->
          Seplist.for_all (fun (_, _, _, args) -> Seplist.to_list args = []) ctors
          && texp_can_derive_beq t
        | _ -> false
      in
      (* Candidates: (path, Lean type name, tnvar_list, ctors) with
         ctor = (Lean ctor name, field semantic types). Instance-backed
         block members (skip_instances / deriving-covered) are LEAVES;
         everything else that fails candidacy is a SORRIED sibling —
         referencing it poisons the referencing type (fail-closed). *)
      let candidates, sorried0 =
        List.fold_right (fun (((name, _), tnvar_list, path, t, _)) (cs, os) ->
          if skip_type path then (cs, os)
          else if deriving_covered t then (cs, os)
          else if not (texp_can_derive_beq t) then (cs, path :: os)
          else
            let type_name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip (B.type_path_to_name name path))) in
            (match t with
              | Te_variant (_, seplist) ->
                let ctors = List.map (fun ((cn, _), c_ref, _, args) ->
                  let cname = B.const_ref_to_name cn false c_ref in
                  let cn_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip cname)) in
                  (cn_str, List.map (fun (s : src_t) -> s.typ) (Seplist.to_list args))
                ) (Seplist.to_list seplist) in
                ((path, type_name_str, tnvar_list, ctors) :: cs, os)
              | Te_record (_, _, fields, _) ->
                let ctors = [("mk", List.map (fun (_, _, _, (s : src_t)) -> s.typ) (Seplist.to_list fields))] in
                ((path, type_name_str, tnvar_list, ctors) :: cs, os)
              | _ -> (cs, path :: os))
        ) non_abbrev ([], [])
      in
      (* Fixpoint: drop candidates with any underivable field shape;
         dropped candidates become sorried siblings for the next round. *)
      let rec solve cands sorried =
        let derived_map = List.map (fun (p, nm, _, _) -> (p, nm)) cands in
        let ok, bad = List.partition (fun (_, _, _, ctors) ->
          List.for_all (fun (_, args) ->
            List.for_all (fun ty ->
              not (lean_cmp_shape_is_bad (lean_cmp_shape d derived_map sorried ty))) args) ctors)
          cands
        in
        if bad = [] then (ok, sorried)
        else solve ok (List.map (fun (p, _, _, _) -> p) bad @ sorried)
      in
      let derived, sorried = solve candidates sorried0 in
      if derived = [] then (emp, [])
      else begin
        let derived_map = List.map (fun (p, nm, _, _) -> (p, nm)) derived in
        let shape_of ty = lean_cmp_shape d derived_map sorried ty in
        (* Bound tyvars of a type: Type-kind parameters free in some field
           (covers transitive needs — a sibling application's arguments are
           part of the field type), in parameter-declaration order. *)
        let bounds_of tnvar_list ctors =
          let fvs = List.fold_left (fun acc (_, args) ->
            List.fold_left (fun acc ty -> Types.TNset.union acc (Types.free_vars ty)) acc args)
            Types.TNset.empty ctors in
          let free_names = List.map (fun tnv -> Ulib.Text.to_string (Types.tnvar_to_rope tnv))
            (Types.TNset.elements fvs) in
          List.filter_map (fun tv ->
            match tv with
              | Typed_ast.Tn_A _ ->
                let nm = tnvar_to_string tv in
                if List.mem nm free_names then Some nm else None
              | Typed_ast.Tn_N _ -> None) tnvar_list
        in
        (* Helper-def machinery: one specialized def per (kind, container
           type), memoized per block, emitted inside the same mutual block
           (classical structural recursion — the CerbStepInstances
           beqLoadedValueList pattern, generated). *)
        let helper_defs : string list ref = ref [] in
        let helper_memo : (string, string) Hashtbl.t = Hashtbl.create 16 in
        let helper_ctr = ref 0 in
        let first_name = match derived with (_, nm, _, _) :: _ -> nm | [] -> assert false in
        (* {tv : Type} [Cls tv] / {nv : Nat} binders for the tyvars free in
           the given types (helper signatures). *)
        let tv_binders_of (tys : Types.t list) (cls : string) : string =
          let fvs = List.fold_left (fun acc ty -> Types.TNset.union acc (Types.free_vars ty))
            Types.TNset.empty tys in
          let bs = List.map (fun tnv ->
            let nm = Ulib.Text.to_string (Types.tnvar_to_rope tnv) in
            match tnv with
              | Types.Ty _ -> Printf.sprintf "{%s : Type} [%s %s]" nm cls nm
              | Types.Nv _ -> Printf.sprintf "{%s : Nat}" nm)
            (Types.TNset.elements fvs) in
          (match bs with [] -> "" | _ -> String.concat "" [" "; String.concat " " bs])
        in
        (* Build ctor-argument patterns; tuples destructure in-pattern.
           Returns (x-pattern, y-pattern, leaves = (xvar, yvar, shape)). *)
        let rec build_pats (ctr : int ref) (sh : cmp_shape) : string * string * (string * string * cmp_shape) list =
          match sh with
            | CStuple shs ->
              let parts = List.map (build_pats ctr) shs in
              (Printf.sprintf "(%s)" (String.concat ", " (List.map (fun (a, _, _) -> a) parts)),
               Printf.sprintf "(%s)" (String.concat ", " (List.map (fun (_, b, _) -> b) parts)),
               List.concat_map (fun (_, _, ls) -> ls) parts)
            | _ ->
              incr ctr;
              let x = Printf.sprintf "x%d" !ctr and y = Printf.sprintf "y%d" !ctr in
              (x, y, [(x, y, sh)])
        in
        let rec beq_leaf (x, y, sh) : string =
          match sh with
            | CSleaf -> Printf.sprintf "%s == %s" x y
            | CSsibling nm -> Printf.sprintf "%s.beq_derived %s %s" nm x y
            | CSlist (et, esh) -> Printf.sprintf "%s %s %s" (helper "beq" (CSlist (et, esh))) x y
            | CSoption (et, esh) -> Printf.sprintf "%s %s %s" (helper "beq" (CSoption (et, esh))) x y
            | CSsum (a, b) -> Printf.sprintf "%s %s %s" (helper "beq" (CSsum (a, b))) x y
            | CStuple _ | CSbad _ -> assert false (* destructured / fail-closed upstream *)
        and cmp_leaf (x, y, sh) : string =
          match sh with
            | CSleaf -> Printf.sprintf "Ord.compare %s %s" x y
            | CSsibling nm -> Printf.sprintf "%s.compare_derived %s %s" nm x y
            | CSlist (et, esh) -> Printf.sprintf "%s %s %s" (helper "cmp" (CSlist (et, esh))) x y
            | CSoption (et, esh) -> Printf.sprintf "%s %s %s" (helper "cmp" (CSoption (et, esh))) x y
            | CSsum (a, b) -> Printf.sprintf "%s %s %s" (helper "cmp" (CSsum (a, b))) x y
            | CStuple _ | CSbad _ -> assert false
        and beq_conj (leaves : (string * string * cmp_shape) list) : string =
          match leaves with
            | [] -> "true"
            | _ -> String.concat " && " (List.map beq_leaf leaves)
        and cmp_chain (leaves : (string * string * cmp_shape) list) : string =
          match leaves with
            | [] -> "Ordering.eq"
            | [lf] -> cmp_leaf lf
            | lf :: rest ->
              Printf.sprintf "(match %s with | .lt => Ordering.lt | .gt => Ordering.gt | .eq => %s)"
                (cmp_leaf lf) (cmp_chain rest)
        (* Named helper for a container shape; generated on first demand. *)
        and helper (kind : string) (sh : cmp_shape) : string =
          let key = String.concat "" [kind; "|"; (match sh with
            | CSlist (et, _) -> String.concat "" ["list|"; lean_typ_render et]
            | CSoption (et, _) -> String.concat "" ["option|"; lean_typ_render et]
            | CSsum ((lt_, _), (rt_, _)) -> String.concat "" ["sum|"; lean_typ_render lt_; "|"; lean_typ_render rt_]
            | _ -> assert false)]
          in
          match Hashtbl.find_opt helper_memo key with
            | Some nm -> nm
            | None ->
              incr helper_ctr;
              let nm = Printf.sprintf "%s.%s_deriv_aux%d" first_name kind !helper_ctr in
              Hashtbl.add helper_memo key nm;
              (* Elements destructure via build_pats, so tuple-shaped
                 elements (e.g. List ((pattern × pexpr))) compare
                 componentwise inside the helper's own arm. *)
              let elem kind0 esh =
                let ctr = ref 0 in
                let (px, py, leaves) = build_pats ctr esh in
                (px, py, (if kind0 = "beq" then beq_conj leaves else cmp_chain leaves))
              in
              let def_text =
                match sh, kind with
                  | CSlist (et, esh), "beq" ->
                    let ety = lean_typ_render et in
                    let (px, py, body) = elem "beq" esh in
                    Printf.sprintf
                      "def %s%s (cmpx_ cmpy_ : List (%s)) : Bool := match cmpx_, cmpy_ with\n  | [], [] => true\n  | %s :: xs0, %s :: ys0 => %s && %s xs0 ys0\n  | _, _ => false\ntermination_by structural cmpx_"
                      nm (tv_binders_of [et] "BEq") ety
                      px py body nm
                  | CSlist (et, esh), "cmp" ->
                    let ety = lean_typ_render et in
                    let (px, py, body) = elem "cmp" esh in
                    Printf.sprintf
                      "def %s%s (cmpx_ cmpy_ : List (%s)) : Ordering := match cmpx_, cmpy_ with\n  | [], [] => Ordering.eq\n  | [], _ :: _ => Ordering.lt\n  | _ :: _, [] => Ordering.gt\n  | %s :: xs0, %s :: ys0 => (match %s with | .lt => Ordering.lt | .gt => Ordering.gt | .eq => %s xs0 ys0)\ntermination_by structural cmpx_"
                      nm (tv_binders_of [et] "Ord") ety
                      px py body nm
                  | CSoption (et, esh), "beq" ->
                    let ety = lean_typ_render et in
                    let (px, py, body) = elem "beq" esh in
                    Printf.sprintf
                      "def %s%s (cmpx_ cmpy_ : Option (%s)) : Bool := match cmpx_, cmpy_ with\n  | none, none => true\n  | some %s, some %s => %s\n  | _, _ => false\ntermination_by structural cmpx_"
                      nm (tv_binders_of [et] "BEq") ety
                      px py body
                  | CSoption (et, esh), "cmp" ->
                    let ety = lean_typ_render et in
                    let (px, py, body) = elem "cmp" esh in
                    Printf.sprintf
                      "def %s%s (cmpx_ cmpy_ : Option (%s)) : Ordering := match cmpx_, cmpy_ with\n  | none, none => Ordering.eq\n  | none, some _ => Ordering.lt\n  | some _, none => Ordering.gt\n  | some %s, some %s => %s\ntermination_by structural cmpx_"
                      nm (tv_binders_of [et] "Ord") ety
                      px py body
                  | CSsum ((lt_, shl), (rt_, shr)), "beq" ->
                    let lty = lean_typ_render lt_ and rty = lean_typ_render rt_ in
                    let (plx, ply, lbody) = elem "beq" shl in
                    let (prx, pry, rbody) = elem "beq" shr in
                    Printf.sprintf
                      "def %s%s (cmpx_ cmpy_ : Sum (%s) (%s)) : Bool := match cmpx_, cmpy_ with\n  | Sum.inl %s, Sum.inl %s => %s\n  | Sum.inr %s, Sum.inr %s => %s\n  | _, _ => false\ntermination_by structural cmpx_"
                      nm (tv_binders_of [lt_; rt_] "BEq") lty rty
                      plx ply lbody prx pry rbody
                  | CSsum ((lt_, shl), (rt_, shr)), "cmp" ->
                    let lty = lean_typ_render lt_ and rty = lean_typ_render rt_ in
                    let (plx, ply, lbody) = elem "cmp" shl in
                    let (prx, pry, rbody) = elem "cmp" shr in
                    Printf.sprintf
                      "def %s%s (cmpx_ cmpy_ : Sum (%s) (%s)) : Ordering := match cmpx_, cmpy_ with\n  | Sum.inl %s, Sum.inl %s => %s\n  | Sum.inl _, Sum.inr _ => Ordering.lt\n  | Sum.inr _, Sum.inl _ => Ordering.gt\n  | Sum.inr %s, Sum.inr %s => %s\ntermination_by structural cmpx_"
                      nm (tv_binders_of [lt_; rt_] "Ord") lty rty
                      plx ply lbody prx pry rbody
                  | _ -> assert false
              in
              helper_defs := def_text :: !helper_defs;
              nm
        in
        (* Signature pieces per type. *)
        let sig_of tnvar_list bounds cls =
          let binders = String.concat "" (List.map (fun tv ->
            let nm = tnvar_to_string tv in
            let base = Printf.sprintf " {%s : %s}" nm (tnvar_kind tv) in
            if List.mem nm bounds then Printf.sprintf "%s [%s %s]" base cls nm else base)
            tnvar_list) in
          let args = String.concat "" (List.map (fun tv -> String.concat "" [" "; tnvar_to_string tv]) tnvar_list) in
          (binders, args)
        in
        (* Two-class OCaml rank def (only needed with >1 constructor). *)
        let rank_def type_name tnvar_list ctors : string =
          let nullary_rank = ref 0 in
          let nnullary = List.length (List.filter (fun (_, args) -> args = []) ctors) in
          let block_rank = ref 0 in
          let arms = List.map (fun (cn, args) ->
            let rank =
              if args = [] then (let r0 = !nullary_rank in incr nullary_rank; r0)
              else (let r0 = nnullary + !block_rank in incr block_rank; r0)
            in
            let wilds = String.concat "" (List.map (fun _ -> " _") args) in
            Printf.sprintf "  | .%s%s => %d" cn wilds rank) ctors in
          let (binders, args) = sig_of tnvar_list [] "" in
          Printf.sprintf
            "/- OCaml polymorphic-compare constructor rank: nullary constructors\n   (immediates) sort below non-nullary (blocks); declaration order within\n   each class. -/\ndef %s.ctor_rank_ocaml%s : %s%s → Nat\n%s"
            type_name binders type_name args (String.concat "\n" arms)
        in
        let beq_def (type_name, tnvar_list, bounds, ctors) : string =
          let (binders, args) = sig_of tnvar_list bounds "BEq" in
          let arms = List.map (fun (cn, argtys) ->
            let ctr = ref 0 in
            let parts = List.map (fun ty -> build_pats ctr (shape_of ty)) argtys in
            let px = String.concat " " (List.map (fun (a, _, _) -> a) parts) in
            let py = String.concat " " (List.map (fun (_, b, _) -> b) parts) in
            let leaves = List.concat_map (fun (_, _, ls) -> ls) parts in
            let sp = if argtys = [] then "" else " " in
            Printf.sprintf "  | .%s%s%s, .%s%s%s => %s" cn sp px cn sp py (beq_conj leaves)) ctors in
          let fallback = if List.length ctors > 1 then ["  | _, _ => false"] else [] in
          Printf.sprintf "def %s.beq_derived%s (cmpx_ cmpy_ : %s%s) : Bool := match cmpx_, cmpy_ with\n%s\ntermination_by structural cmpx_"
            type_name binders type_name args
            (String.concat "\n" (arms @ fallback))
        in
        let cmp_def (type_name, tnvar_list, bounds, ctors) : string =
          let (binders, args) = sig_of tnvar_list bounds "Ord" in
          let arms = List.filter_map (fun (cn, argtys) ->
            if argtys = [] then None  (* nullary pairs: rank fallback yields .eq *)
            else begin
              let ctr = ref 0 in
              let parts = List.map (fun ty -> build_pats ctr (shape_of ty)) argtys in
              let px = String.concat " " (List.map (fun (a, _, _) -> a) parts) in
              let py = String.concat " " (List.map (fun (_, b, _) -> b) parts) in
              let leaves = List.concat_map (fun (_, _, ls) -> ls) parts in
              Some (Printf.sprintf "  | .%s %s, .%s %s => %s" cn px cn py (cmp_chain leaves))
            end) ctors in
          let fallback =
            if List.length ctors > 1 then
              [Printf.sprintf "  | xg, yg => Ord.compare (%s.ctor_rank_ocaml xg) (%s.ctor_rank_ocaml yg)" type_name type_name]
            else [] in
          Printf.sprintf "def %s.compare_derived%s (cmpx_ cmpy_ : %s%s) : Ordering := match cmpx_, cmpy_ with\n%s\ntermination_by structural cmpx_"
            type_name binders type_name args
            (String.concat "\n" (arms @ fallback))
        in
        (* Render: rank defs (non-recursive, before the block), then the
           mutual block. Type-def bodies are rendered FIRST so helper
           demand is populated; helpers can demand further helpers. *)
        let per_type = List.map (fun (path, nm, tnvar_list, ctors) ->
          (path, nm, tnvar_list, bounds_of tnvar_list ctors, ctors)) derived in
        let type_defs_text = List.concat_map (fun (_, nm, tvs, bounds, ctors) ->
          [beq_def (nm, tvs, bounds, ctors); cmp_def (nm, tvs, bounds, ctors)]) per_type in
        let rank_defs_text = List.filter_map (fun (_, nm, tvs, _, ctors) ->
          if List.length ctors > 1 then Some (rank_def nm tvs ctors) else None) per_type in
        let all_mutual = type_defs_text @ List.rev !helper_defs in
        let text = String.concat "" [
          "\n/- Arc-10 S2: derived structural comparisons (OCaml polymorphic\n";
          "   (=)/compare parity at this type's constructors: structural equality;\n";
          "   nullary-below-block constructor rank, declaration order within each\n";
          "   class; left-to-right lexicographic fields; leaf fields via their\n";
          "   Lean BEq/Ord instances). -/\n";
          (match rank_defs_text with [] -> "" | rs -> String.concat "" [String.concat "\n" rs; "\n"]);
          "mutual\n";
          String.concat "\n" all_mutual;
          "\nend\n";
        ] in
        (from_string text, List.map (fun (path, _, _, bounds, _) -> (path, bounds)) per_type)
      end
    and generate_default_values ts : Output.t =
      let ts = Seplist.to_list ts in
      (* In library modules, skip instance generation for opaque types
         (zero-constructor inductives like phantom types ty1..ty4096).
         These types carry only type-level information (e.g., bit widths
         via Size) and are never used as data — sorry-based instances are
         useless and produce compiler warnings.
         In user modules, opaque types (e.g., tid, location in cmm.lem) may
         appear as constructor arguments, so downstream types need their
         BEq/Ord instances for deriving to work. *)
      let is_lib = is_library_module !St.current_module_name in
      let ts = if is_lib then List.filter (fun (_, _, _, t, _) -> t <> Te_opaque) ts else ts in
      (* Treat each single type like a mutual block of one, so self-referential
         constructors (e.g. Unop : op → op0 → op1 → op1) are detected and
         avoided when generating the Inhabited instance. *)
      let mapped = List.map (fun (((_, _), _, path, _, _) as t) ->
        generate_inhabited_instance [path] t) ts in
      let beq_instances = List.map generate_beq_ord_instances ts in
        Output.flat [concat_str "\n" mapped; concat emp beq_instances]
    and generate_default_values_mutual ts : Output.t =
      let ts_list = Seplist.to_list ts in
      let is_lib = is_library_module !St.current_module_name in
      let ts_list = if is_lib then List.filter (fun (_, _, _, t, _) -> t <> Te_opaque) ts_list else ts_list in
      (* Filter out abbreviations for mutual_paths, is_type1, and emit_deriving decisions.
         Abbreviations don't participate in mutual recursion or instance generation. *)
      let non_abbrev = List.filter (fun (_, _, _, t, _) ->
        match t with Te_abbrev _ -> false | _ -> true) ts_list in
      let mutual_paths = List.map (fun ((_, _), _, path, _, _) -> path) non_abbrev in
      (* Check if the non-abbreviation types have heterogeneous param counts *)
      let param_counts = List.map (fun (_, ty_vars, _, _, _) -> List.length ty_vars) non_abbrev in
      let is_type1 = match param_counts with
        | [] -> false
        | x :: xs -> not (List.for_all (fun y -> y = x) xs)
      in
      let inhabited_output =
        if List.length non_abbrev > 1 then
          generate_inhabited_mutual mutual_paths ts_list
        else
          let mapped = List.map (generate_inhabited_instance mutual_paths) ts_list in
          concat_str "\n" mapped
      in
      (* If only 1 non-abbreviation type remains, it was rendered with deriving
         (not as a mutual block), so emit_deriving:true to avoid duplicate instances. *)
      let emit_deriving = List.length non_abbrev <= 1 in
      (* Arc-10 S2: derived structural comparisons for the block's
         derivable types (real mutual beq/compare defs; fail-closed
         residual for the rest). Homogeneous-parameter multi-type blocks
         only: single-type blocks keep the historical emission, and
         Type-1 (indexed) blocks are a fail-closed generation-time
         error in generate_beq_ord_instances (arc-10 audit fix,
         auditor A F1 — the sorried Type-1 residual is deleted;
         population empty). *)
      let (cmp_defs, derived_info) =
        if is_type1 || emit_deriving then (emp, [])
        else generate_derived_comparisons ts_list
      in
      let beq_instances = List.map (fun (((_, _), _, path, _, _) as td) ->
        let derived_cmp =
          Option.map snd (List.find_opt (fun (p, _) -> Path.compare p path = 0) derived_info) in
        generate_beq_ord_instances ~is_type1 ~emit_deriving ?derived_cmp td) ts_list in
        Output.flat [inhabited_output; from_string "\n"; cmp_defs; concat emp beq_instances]
    (* Arc-8 S2 (D4): the former `default_value` (the L_undefined
       renderer whose Typ_var case emitted `sorry`) is DELETED —
       L_undefined renders as failwithI (audit fix; mirrors OCaml's
       `failwith m`, src/backend.ml:864), which never emits an opaque
       inhabitant or a silent default. *)
      ;;
end
;;


module CdsetE = Util.ExtraSet(Types.Cdset)

module LeanBackend (A : sig val avoid : var_avoid_f option;; val env : env;; val dir : string end) =
  struct

    (* Main definition processor: emits def output with location comments.
       Intentionally parallel to defs_extra below — they share the module
       setup but differ in which method they call (C.def vs C.def_extra)
       and whether location comments are prepended. Unifying them would
       require first-class modules which adds more complexity than the
       duplication costs. *)
    let rec defs inside_instance inside_module (ds : def list) =
        List.fold_right (fun (((d, s), l, lenv):def) y ->
          let ue = add_def_entities (Target_no_ident Target_lean) true empty_used_entities ((d,s),l,lenv) in
          let callback = defs false true in
          let module C = LeanBackendAux (
            struct
              let avoid = A.avoid;;
              let env = {A.env with local_env = lenv};;
              let ascii_rep_set = CdsetE.from_list ue.used_consts;;
              let dir = A.dir;;
            end)
          in
          let (before_out, d') = Backend_common.def_add_location_comment ((d,s),l,lenv) in
          before_out ^
          match s with
            | None   -> C.def inside_instance callback inside_module d' ^ y
            | Some s -> C.def inside_instance callback inside_module d' ^ ws s ^ y
        ) ds emp
    (* Auxiliary file processor: emits def_extra output without location comments. *)
    and defs_extra inside_instance inside_module (ds: def list) =
        List.fold_right (fun (((d, s), l, lenv):def) y ->
          let ue = add_def_entities (Target_no_ident Target_lean) true empty_used_entities ((d,s),l,lenv) in
          let module C = LeanBackendAux (
            struct
              let avoid = A.avoid;;
              let env = {A.env with local_env = lenv};;
              let ascii_rep_set = CdsetE.from_list ue.used_consts;;
              let dir = A.dir;;
            end)
          in
          let callback = defs false true in
          match s with
            | None   -> C.def_extra inside_instance callback inside_module d ^ y
            | Some s -> C.def_extra inside_instance callback inside_module d ^ ws s ^ y
        ) ds emp
    ;;

    (* --- Import and namespace management ---
       Library modules: wrapped in 'namespace Lem_ModuleName ... end' with imports at top.
       User modules: no namespace wrapper; automatically open all transitive library
       namespaces so types/classes from Pervasives etc. are in scope.
       Abbrev definitions may be deferred (St.pending_abbrevs) until after their
       dependencies are defined (e.g., abbrev mword after class Size). *)
    let lean_defs ((ds : def list), end_lex_skips) =
      St.reset_per_file ();
      (* Set callback for per-file CR_simple import collection *)
      Backend_common.on_cr_simple_applied := collect_cr_simple_import;
      (* Note: St.mutual_records is NOT reset — [invocation] lifetime: it
         accumulates across files so that cross-file record updates on
         mutual-block records are detected. *)
      (* Pre-collect local module names before main processing, because
         defs uses fold_right (processes last-to-first). Without this,
         'open Operators' would be processed before 'module Operators',
         causing a spurious import. *)
      (* Recursively collect local module names including nested ones *)
      let rec collect_local_modules (ds : def list) : string list =
        List.concat_map (fun (((d, _), _, _) : def) ->
          match d with
          | Module (_, (name, _), _, _, _, defs, _) ->
            let name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip name)) in
            name_str :: collect_local_modules defs
          | _ -> []
        ) ds
      in
      St.local_modules := collect_local_modules ds;
      (* Pre-collect mutual record type names. Type_def blocks with >1 member
         that contain Te_record entries will render records as inductives.
         We need this list before defs runs (fold_right = last-to-first). *)
      St.mutual_records := !St.mutual_records @ List.concat_map (fun (((d, _), _, _) : def) ->
        match d with
        | Type_def (_, defs) when Seplist.length defs > 1 ->
            let all = Seplist.to_list defs in
            let non_abbrev = List.filter (fun (_, _, _, ty, _) ->
              match ty with Te_abbrev _ -> false | _ -> true
            ) all in
            if List.length non_abbrev > 1 then
              List.filter_map (fun (_, _, path, ty, _) ->
                match ty with
                  | Te_record _ -> Some path
                  | _ -> None
              ) non_abbrev
            else []
        | _ -> []
      ) ds;
      let mod_name = !St.current_module_name in
      let ns_name = lean_ns_name mod_name in
      let is_library = ns_name <> mod_name in
      (* For library modules, push the top-level namespace so that
         lean_qualified_name returns qualified names (e.g. "Lem_Basic_classes.Eq0"
         instead of bare "Eq0"). Auxiliary files need these qualified opens
         since they don't have the namespace wrapper. *)
      if is_library then
        St.namespace_stack := [ns_name];
      lean_reader_prepass A.env ds;
      (* Arc-8 S1: compute the Inhabited census + tier-2 plans in
         declaration order before emission (defs is fold_right). *)
      lean_inhabited_prepass A.env ds;
      (* Arc-8 S2: compute the [Inhabited] threading census (failure
         sites at tyvar-typed positions -> signature binders, monotone
         over the call graph) — needs the S1 census, so runs after it.
         Also guard-sweeps instance methods (rule 3). *)
      lean_failwith_thread_prepass A.env ds;
      let lean_defs = defs false false ds in
      (* Drain any deferred abbrevs (e.g., abbrev mword after class Size) *)
      let deferred = Output.flat (List.rev !St.pending_abbrevs) in
      St.pending_abbrevs := [];
      let lean_defs = lean_defs ^ deferred in
      let lean_defs_extra = defs_extra false false ds in
      (* Ensure LemLib.Pervasives is always imported for non-library modules.
         This guarantees the standard namespace opens (Lem_Basic_classes, etc.)
         are available for auto-generated instances even when the source .lem file
         doesn't explicitly import Pervasives (e.g., linux.lem). *)
      let _ = if not is_library &&
                not (List.mem "LemLib.Pervasives" !St.collected_imports) then
        St.collected_imports := "LemLib.Pervasives" :: !St.collected_imports
      in
      (* Imports for target_rep references are collected per-file during rendering:
         - Function CR_simple target reps: via Backend_common.on_cr_simple_applied callback
         - Type TYR_simple target reps: directly in type_def_variant
         This ensures each file only imports modules it actually references. *)
      (* Prepend collected imports (deduplicated, in order) to main body *)
      let imports = List.rev !St.collected_imports in
      let seen = Hashtbl.create 16 in
      let unique_imports = List.filter (fun m ->
        if Hashtbl.mem seen m then false
        else (Hashtbl.add seen m true; true)
      ) imports in
      let imports_output = Output.flat (List.map (fun m ->
        from_string (String.concat "" ["import "; m; "\n"])
      ) unique_imports) in
      let ns_start = if is_library then
        from_string (String.concat "" ["\nnamespace "; ns_name; "\n"])
      else emp in
      let ns_end = if is_library then
        from_string (String.concat "" ["\nend "; ns_name; "\n"])
      else emp in
      (* For non-library modules, open all imported library namespaces so that
         class/type names from transitive dependencies are in scope.
         This is needed because Lean namespaces don't re-export opens.
         We scan the imports collected by THIS file and open the corresponding
         library namespaces. For transitive deps that come through Pervasives,
         we derive all library namespaces from the module environment. *)
      let transitive_opens = if not is_library then begin
        let all_imports = List.rev !St.collected_imports in
        let has_pervasives = List.exists (fun m ->
          m = "LemLib.Pervasives" || m = "LemLib.Pervasives_extra"
        ) all_imports in
        if has_pervasives then
          (* Pervasives imports all core library modules; open their namespaces.
             Also import Pervasives_extra for bridge instances (NumAdd → Add etc.).
             Derive the list of library namespaces from the module environment
             (all modules with a Coq rename are library modules). *)
          let has_pervasives_extra = List.exists (fun m ->
            m = "LemLib.Pervasives_extra"
          ) all_imports in
          let extra_import = if has_pervasives_extra then emp
            else from_string "import LemLib.Pervasives_extra\n" in
          let has_bridges = List.exists (fun m ->
            m = "LemLib.Bridges"
          ) all_imports in
          let bridges_import = if has_bridges then emp
            else from_string "import LemLib.Bridges\n" in
          let lib_namespaces = Types.Pfmap.fold (fun acc _path md ->
            let has_coq_rename =
              Target.Targetmap.apply_target md.Typed_ast.mod_target_rep
                (Target.Target_no_ident Target.Target_coq) <> None in
            if has_coq_rename then begin
              let mod_name = Path.to_string md.Typed_ast.mod_binding in
              let lean_mod = String.concat "" ["LemLib."; String.capitalize_ascii mod_name] in
              let ns = lean_ns_name lean_mod in
              if List.mem ns acc then acc else ns :: acc
            end else acc
          ) [] A.env.e_env in
          let lib_namespaces = List.rev lib_namespaces in
          Output.flat (extra_import :: bridges_import :: List.map (fun ns ->
            from_string (String.concat "" ["open "; ns; "\n"])
          ) lib_namespaces)
        else
          (* Just open namespaces for direct imports *)
          let ns_list = List.filter_map (fun m ->
            let ns = lean_ns_name m in
            if ns <> m then Some ns else None
          ) all_imports in
          Output.flat (List.map (fun ns ->
            from_string (String.concat "" ["open "; ns; "\n"])
          ) ns_list)
      end else emp in
      (* Emit open statements for type/class namespaces so auxiliary file
         can reference constructors and class methods unqualified *)
      let opens = List.map (fun name_str ->
        from_string (String.concat "" ["open "; name_str; "\n"])
      ) !St.auxiliary_opens in
      let opens_output = Output.flat opens in
        ((to_rope (r"\"") lex_skip need_space @@ imports_output ^ transitive_opens ^ ns_start ^ lean_defs ^ ns_end ^ ws end_lex_skips),
          to_rope (r"\"") lex_skip need_space @@ transitive_opens ^ opens_output ^ lean_defs_extra ^ ws end_lex_skips)
    ;;
  end
