Theory sourceConstEnv
Ancestors
  sourceConstEval alist list rich_list

(* TOP-LEVEL: source_const_resolve. Opt-in dependency resolution over ALREADY
   RESOLVED declaration paths. A path is a component list, never a joined name
   or compiler source_id. The caller must resolve aliases/shadowing/builtin
   identities first. This module does not canonicalize JSON imports.
   Seed bindings describe imported constants AND runtime/immutable/local names;
   dynamic bindings are preserved, never promoted to constants.
   Declarations are (canonical path, original initializer) pairs. *)

Datatype:
  source_const_env_result =
      SCEnv_Resolved (((string list) # source_const_binding) list)
    | SCEnv_BadIdentity ((string list) list)
    | SCEnv_Duplicate ((string list) list)
    | SCEnv_BadSeed
    | SCEnv_Missing (((string list) # (string list)) list)
    | SCEnv_Cycle ((string list) list)
    | SCEnv_NotConstant (string list)
    | SCEnv_Invalid (string list) source_const_error
    | SCEnv_Unsupported (string list) source_const_unsupported
End

(* ===== Dependency discovery (including eager/unsupported children) ===== *)

Definition source_const_names_def:
  source_const_names (SCE_Literal lit) = [] /\
  source_const_names (SCE_Name path) = [path] /\
  source_const_names SCE_Dynamic = [] /\
  source_const_names (SCE_BytesType fixed e) = source_const_names e /\
  source_const_names (SCE_Unary op e) = source_const_names e /\
  source_const_names (SCE_Binary op l r) =
    source_const_names l ++ source_const_names r /\
  source_const_names (SCE_Boolean op es) = FLAT (MAP source_const_names es) /\
  source_const_names (SCE_Compare op l r) =
    source_const_names l ++ source_const_names r /\
  source_const_names (SCE_List es) = FLAT (MAP source_const_names es) /\
  source_const_names (SCE_Tuple es) = FLAT (MAP source_const_names es) /\
  source_const_names (SCE_Subscript e i) =
    source_const_names e ++ source_const_names i /\
  source_const_names (SCE_Builtin b args kws) =
    FLAT (MAP source_const_names args) ++
    FLAT (MAP (\kw. source_const_names (SND kw)) kws) /\
  source_const_names (SCE_Call callee args kws) =
    source_const_names callee ++ FLAT (MAP source_const_names args) ++
    FLAT (MAP (\kw. source_const_names (SND kw)) kws) /\
  source_const_names (SCE_Unsupported tag es) = FLAT (MAP source_const_names es)
End

Definition source_const_ready_def:
  source_const_ready env expr =
    EVERY (\path. MEM path (MAP FST env)) (source_const_names expr)
End

(* Remove exactly one ready declaration, maintaining the remaining order. *)
Definition source_const_pick_def:
  source_const_pick env [] = NONE /\
  source_const_pick env (d::ds) =
    if source_const_ready env (SND d) then SOME (d,ds)
    else OPTION_MAP (\(chosen,rest). (chosen,d::rest))
           (source_const_pick env ds)
End

(* Helper needed by the termination proof; public picker properties are in
   sourceConstEnvProps. Each recursive step removes exactly one declaration. *)
Theorem source_const_pick_length:
  !ds d rest. source_const_pick env ds = SOME (d,rest) ==>
              LENGTH ds = SUC (LENGTH rest)
Proof
  Induct >> simp[source_const_pick_def] >> rpt gen_tac >>
  Cases_on `source_const_ready env (SND h)` >> simp[] >>
  Cases_on `source_const_pick env ds` >> simp[] >>
  rename1 `SOME pair` >> PairCases_on `pair` >> simp[] >>
  strip_tac >> gvs[] >> res_tac >> simp[]
QED

(* ===== Terminating topological evaluation ===== *)

(* Cycle payload is the blocked region, including dependents of cycles, NOT
   a claimed simple-cycle witness. Missing paths are checked before this phase.
   There is no retry budget/exhaustion fallback: LENGTH pending strictly falls.
   The append-only accumulator makes preservation of imported/dynamic bindings
   independent even of the validation wrapper. *)
Definition source_const_resolve_pending_def:
  source_const_resolve_pending env pending =
    if pending = [] then SCEnv_Resolved env
    else case source_const_pick env pending of
    | NONE => SCEnv_Cycle (MAP FST pending)
    | SOME ((path,expr),rest) =>
        case source_const_eval env expr of
        | SC_Value v =>
            if source_const_value_ok v then
              source_const_resolve_pending (env ++ [(path,SC_Constant v)]) rest
            else SCEnv_Invalid path SCErr_Domain
        | SC_NotConstant => SCEnv_NotConstant path
        | SC_Invalid e => SCEnv_Invalid path e
        | SC_Unsupported u => SCEnv_Unsupported path u
Termination
  WF_REL_TAC `measure (LENGTH o SND)` >> rpt strip_tac >>
  imp_res_tac source_const_pick_length >> simp[]
End

(* ===== Input validation and public API ===== *)

Definition source_const_identity_ok_def:
  source_const_identity_ok path = (path <> [] /\ EVERY (\s. s <> "") path)
End

Definition source_const_binding_ok_def:
  source_const_binding_ok SC_DynamicBinding = T /\
  source_const_binding_ok (SC_Constant v) = source_const_value_ok v
End

Definition source_const_missing_def:
  source_const_missing keys decls =
    FLAT (MAP (\(path,expr).
      MAP (\dep. (path,dep))
        (FILTER (\dep. ~MEM dep keys) (source_const_names expr))) decls)
End

(* Duplicates include seed/seed, declaration/declaration and seed/declaration
   collisions. A dynamic name cannot be overwritten by a constant declaration.
   BadIdentity/Duplicate payloads retain the input keys for diagnostics.
   Missing payloads retain both the owning declaration and missing path.
   This required-constant API rejects genuinely dynamic forms separately from
   unsupported rules and invalid arithmetic. No compiler metadata fallback. *)
Definition source_const_resolve_def:
  source_const_resolve seed decls =
    let keys = MAP FST seed ++ MAP FST decls in
    if ~EVERY source_const_identity_ok keys then SCEnv_BadIdentity keys
    else if ~ALL_DISTINCT keys then SCEnv_Duplicate keys
    else if ~EVERY (source_const_binding_ok o SND) seed then SCEnv_BadSeed
    else let missing = source_const_missing keys decls in
      if missing <> [] then SCEnv_Missing missing
      else source_const_resolve_pending seed decls
End
