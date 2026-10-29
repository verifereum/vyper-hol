Theory vyperState
Ancestors
  arithmetic alist combin option list finite_map pair rich_list
  cv cv_std cv_string_fmap vfmTypes vfmState vfmContext vfmExecution[ignore_grammar]
  vyperAST vyperMisc vyperNsidFmap vyperValue vyperValueOperation
  vyperStorage vyperContext extCallOracle[ignore_grammar]
Libs
  cv_transLib wordsLib monadsyntax

(* `subscript`s are the possible kinds of keys into HashMaps *)

Datatype:
  subscript
  = ValueSubscript value
  | AttrSubscript identifier
End

(* A location is captured once; reading it is a separate operation. *)
Datatype:
  place = StoragePlace bool bytes32 type_value
        | MemoryPlace identifier (subscript list)
        | ImmutablePlace (num option) identifier (subscript list)
End

Theorem place_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vyperState",Tyop="place"}));

(* Mappings await a key and cannot be read as values. Immediate aggregate
   indexing uses the expression's declared type; locations carry their type. *)
Datatype:
  eval_result = Value value
              | PlaceR place
              | HashMapRef bool bytes32 type value_type
End

Theorem eval_result_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vyperState",Tyop="eval_result"}));

Definition is_Value_def[simp]:
  (is_Value (Value _) ⇔ T) ∧
  (is_Value _ ⇔ F)
End

val () = cv_auto_trans is_Value_def;

Definition is_HashMapRef_def[simp]:
  (is_HashMapRef (HashMapRef _ _ _ _) ⇔ T) ∧
  (is_HashMapRef _ ⇔ F)
End

val () = cv_auto_trans is_HashMapRef_def;

(* exception type for interpreter control flow *)
Datatype:
  exception
  = Error error
  | AssertException string
  | BreakException
  | ContinueException
  | ReturnException value
  | HaltException
End

(* Machinery for managing variables (local, top-level, mutable, immutable), and
* other stateful data during execution (e.g., EVM account states, logs)*)

(* Local identifiers are the keys of runtime scopes. The live value carries
   dynamic lengths. Popped snapshots retain contents for locations captured
   before a shrink; new subscripts still check the live length. Reads prefer
   live contents, then search retained ancestors newest first. Nested pops
   update those ancestor views and retain their removed child separately. *)

Datatype:
  scope_entry = <|
    assignable: bool
  ; type: type_value
  ; value: value
  ; popped: (subscript list # value) list
  |>
End

Type scope = “:string |-> scope_entry”;

(* find a variable in a list of nested scopes *)
Definition lookup_scopes_def:
  lookup_scopes id [] = NONE ∧
  lookup_scopes id ((env: scope)::rest) =
  case FLOOKUP env id of NONE =>
    lookup_scopes id rest
  | SOME entry => SOME entry
End

(* lookup only the value (discarding the type) *)
Definition lookup_scopes_val_def:
  lookup_scopes_val id [] = NONE ∧
  lookup_scopes_val id ((env: scope)::rest) =
  case FLOOKUP env id of NONE =>
    lookup_scopes_val id rest
  | SOME entry => SOME entry.value
End

val () = cv_auto_trans lookup_scopes_val_def;

(* find the location of a variable in a list of nested scopes (as well as its
* entry): this is used when assigning to that variable *)
Definition find_containing_scope_def:
  find_containing_scope id ([]:scope list) = NONE ∧
  find_containing_scope id (env::rest) =
  case FLOOKUP env id of NONE =>
    OPTION_MAP (λ(p,q). (env::p, q)) (find_containing_scope id rest)
  | SOME entry => SOME ([], env, entry, rest)
End

val () = cv_auto_trans find_containing_scope_def;

(* Transaction-level, externally observable EVM event. *)
Type log = “:event”;

(* Module-aware immutables: keyed by source_id *)
(* NONE = main contract, SOME n = module with source_id n *)
Type module_immutables = “:(num option, string |-> (type_value # value)) alist”

Definition empty_immutables_def:
  empty_immutables : module_immutables = []
End

val () = cv_auto_trans empty_immutables_def;

Datatype:
  evaluation_state = <|
    immutables: (address, module_immutables) alist
  ; logs: log list
  ; scopes: scope list
  ; accounts: evm_accounts
  ; tStorage: transient_storage
  ; pending_deletions: address list
  ; outcomes: extCallOracle$call_outcome list option
  ; requests: extCallOracle$call_request list
  |>
End

Definition empty_state_def:
  empty_state : evaluation_state = <|
    accounts := empty_accounts;
    immutables := [];
    logs := [];
    scopes := [];
    tStorage := empty_transient_storage;
    pending_deletions := [];
    outcomes := NONE;
    requests := []
  |>
End

val () = cv_trans empty_state_def;

(* state-exception monad used for the main interpreter *)

Type evaluation_result = “:(α + exception) # evaluation_state”

Definition return_def:
  return x s = (INL x, s) : α evaluation_result
End

val () = cv_auto_trans return_def;

(* writing logs *)

Definition push_log_def:
  push_log log st = return () $ st with logs := st.logs ++ [log]
End

val () = cv_auto_trans push_log_def;

Definition append_logs_def:
  append_logs logs st = return () $ st with logs := st.logs ++ logs
End

val () = cv_auto_trans append_logs_def;

Definition raise_def:
  raise e s = (INR e, s) : α evaluation_result
End

val () = cv_auto_trans raise_def;

Definition bind_def:
  bind f g (s: evaluation_state) : α evaluation_result =
  case f s of (INL x, s) => g x s | (INR e, s) => (INR e, s)
End

Definition ignore_bind_def:
  ignore_bind f g = bind f (λx. g)
End

Definition assert_def:
  assert b e s = ((if b then INL () else INR e), s) : unit evaluation_result
End

val () = cv_auto_trans assert_def;

Definition check_def:
  check b str = assert b (Error (RuntimeError str))
End

val () = cv_auto_trans check_def;

Definition type_check_def:
  type_check b str = assert b (Error (TypeError str))
End

val () = cv_auto_trans type_check_def;

val () = declare_monad ("vyper_evaluation",
  { bind = “bind”, unit = “return”,
    ignorebind = SOME “ignore_bind”, choice = NONE,
    fail = SOME “raise”, guard = SOME “assert”
  });
val () = enable_monad "vyper_evaluation";
val () = enable_monadsyntax();

Theorem bind_apply:
  !f g s. (do v <- f; g v od) s =
    case f s of (INL v,s') => g v s' | (INR e,s') => (INR e,s')
Proof
  rpt gen_tac >> simp[bind_def, pairTheory.UNCURRY]
QED

Theorem ignore_bind_apply:
  !f g s. (do f; g od) s =
    case f s of (INL x,s') => g s' | (INR e,s') => (INR e,s')
Proof
  EVAL_TAC >> simp[bind_def]
QED

Definition try_def:
  try f h s : α evaluation_result =
  case f s of (INR e, s) => h e s | x => x
End

Definition finally_def:
  finally f g s : α evaluation_result =
  case f s of (INL x, s) => ignore_bind g (return x) s
     | (INR e, s) => ignore_bind g (raise e) s
End

(* Scope restoration belongs inside this action; a successful EVM halt skips
   only the outer nonreentrant unlock. Other results retain normal cleanup. *)
Definition finally_unless_halt_def:
  finally_unless_halt f g s : α evaluation_result =
  case f s of
  | (INR HaltException, st) => (INR HaltException, st)
  | (INL value, st) => ignore_bind g (return value) st
  | (INR error, st) => ignore_bind g (raise error) st
End

Definition lift_option_def:
  lift_option x str =
    case x of SOME v => return v | NONE => raise $ Error (RuntimeError str)
End

val () = lift_option_def
  |> SRULE [FUN_EQ_THM, option_CASE_rator]
  |> cv_auto_trans;

Definition lift_sum_def:
  lift_sum x =
    case x of INL v => return v | INR e => raise $ Error e
End

val () = lift_sum_def
  |> SRULE [FUN_EQ_THM, sum_CASE_rator]
  |> cv_auto_trans;

Definition lift_sum_runtime_def:
  lift_sum_runtime x =
    case x of INL v => return v | INR str => raise $ Error (RuntimeError str)
End

val () = lift_sum_runtime_def
  |> SRULE [FUN_EQ_THM, sum_CASE_rator]
  |> cv_auto_trans;

Definition lift_option_type_def:
  lift_option_type x str =
    case x of SOME v => return v | NONE => raise $ Error (TypeError str)
End

val () = lift_option_type_def
  |> SRULE [FUN_EQ_THM, option_CASE_rator]
  |> cv_auto_trans;

Theorem lift_option_type_SOME[simp]:
  lift_option_type (SOME v) msg st = (INL v, st)
Proof
  simp[lift_option_type_def, return_def]
QED

Theorem lift_option_type_NONE[simp]:
  lift_option_type NONE msg st = (INR (Error (TypeError msg)), st)
Proof
  simp[lift_option_type_def, raise_def]
QED

(* reading from the state *)

Definition get_address_immutables_def:
  get_address_immutables cx st =
    lift_option_type (ALOOKUP st.immutables cx.txn.target) "get_address_immutables" st
End

val () = get_address_immutables_def
  |> SRULE [lift_option_type_def, option_CASE_rator]
  |> cv_auto_trans;

(* Helper: get immutables for a source_id, or empty if not present *)
Definition get_source_immutables_def:
  get_source_immutables src_id_opt (imms: module_immutables) =
    case ALOOKUP imms src_id_opt of
      NONE => FEMPTY
    | SOME imm => imm
End

val () = cv_auto_trans get_source_immutables_def;

(* Helper: set immutables for a source_id *)
Definition set_source_immutables_def:
  set_source_immutables src_id_opt imm (imms: module_immutables) =
    (src_id_opt, imm) :: ADELKEY src_id_opt imms
End

val () = cv_auto_trans set_source_immutables_def;

(* Find a storage variable or hashmap declaration in toplevels *)
Datatype:
  var_decl_info
  = StorageVarDecl bool type            (* is_transient, type *)
  | HashMapVarDecl bool type value_type (* is_transient, key type, value type *)
End

Theorem var_decl_info_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vyperState",Tyop="var_decl_info"}));

(* Look up variable slot from storage_layout *)
Definition lookup_var_slot_from_layout_def:
  lookup_var_slot_from_layout cx is_transient src_id_opt var_name =
    case ALOOKUP cx.layouts cx.txn.target of
    | NONE => NONE
    | SOME (storage_lay, transient_lay) =>
        ALOOKUP (if is_transient then transient_lay else storage_lay) (src_id_opt, var_name)
End

val () = cv_auto_trans lookup_var_slot_from_layout_def;

(* Find a storage or hashmap declaration by its source identifier. *)
Definition find_var_decl_by_name_def:
  find_var_decl_by_name name [] = NONE ∧
  find_var_decl_by_name name (VariableDecl _ mut vid typ _ :: ts) =
    (if (mut = Storage ∨ mut = Transient) ∧ vid = name
     then SOME (StorageVarDecl (mut = Transient) typ, vid)
     else find_var_decl_by_name name ts) ∧
  find_var_decl_by_name name (HashMapDecl _ is_transient vid kt vt _ :: ts) =
    (if vid = name then SOME (HashMapVarDecl is_transient kt vt, vid)
     else find_var_decl_by_name name ts) ∧
  find_var_decl_by_name name (_ :: ts) = find_var_decl_by_name name ts
End

val () = cv_auto_trans find_var_decl_by_name_def;

Definition get_accounts_def:
  get_accounts st = return st.accounts st
End

val () = cv_auto_trans get_accounts_def;

Definition update_accounts_def:
  update_accounts f st = return () (st with accounts updated_by f)
End

Definition get_transient_storage_def:
  get_transient_storage st = return st.tStorage st
End

val () = cv_auto_trans get_transient_storage_def;

Definition update_transient_def:
  update_transient f st = return () (st with tStorage updated_by f)
End

Definition get_pending_deletions_def:
  get_pending_deletions st = return st.pending_deletions st
End

val () = cv_auto_trans get_pending_deletions_def;

Definition update_pending_deletions_def:
  update_pending_deletions f st =
    return () (st with pending_deletions updated_by f)
End

Definition get_storage_backend_def:
  get_storage_backend cx T = do
    tStore <- get_transient_storage;
    return $ vfmExecution$lookup_transient_storage cx.txn.target tStore
  od ∧
  get_storage_backend cx F = do
    accts <- get_accounts;
    return $ (lookup_account cx.txn.target accts).storage
  od
End

val () = get_storage_backend_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM]
  |> cv_auto_trans;

Definition set_storage_backend_def:
  set_storage_backend cx T storage' =
    update_transient (vfmExecution$update_transient_storage cx.txn.target storage') ∧
  set_storage_backend cx F storage' = do
    accts <- get_accounts;
    acc <<- lookup_account cx.txn.target accts;
    update_accounts (update_account cx.txn.target (acc with storage := storage'))
  od
End

val () = set_storage_backend_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM, update_transient_def, update_accounts_def]
  |> cv_auto_trans;

(* Read a value from storage at a slot *)
Definition read_storage_slot_def:
  read_storage_slot cx is_transient (slot : bytes32) tv = do
    storage <- get_storage_backend cx is_transient;
    lift_option (decode_value storage (w2n slot) tv)
      "read_storage_slot decode"
  od
End

val () = read_storage_slot_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM]
  |> cv_auto_trans;

(* Write a value to storage at a slot *)
Definition write_storage_slot_def:
  write_storage_slot cx is_transient slot tv v = do
    storage <- get_storage_backend cx is_transient;
    writes <- lift_option_type (encode_value tv v) "write_storage_slot encode";
    storage' <<- apply_writes slot writes storage;
    set_storage_backend cx is_transient storage'
  od
End

val () = write_storage_slot_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM, set_storage_backend_def,
            update_transient_def, update_accounts_def]
  |> cv_auto_trans;

(* Module-aware immutables lookup *)
Definition get_immutables_def:
  get_immutables cx src_id_opt = do
    imms <- get_address_immutables cx;
    return (get_source_immutables src_id_opt imms)
  od
End

val () = get_immutables_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM]
  |> cv_auto_trans;

(* Module-aware global lookup: look up identifier n in module src_id_opt. *)
Definition lookup_global_def:
  lookup_global cx src_id_opt n = do
    ts <- lift_option_type (get_module_code cx src_id_opt) "lookup_global get_module_code";
    tenv <<- get_tenv cx;
    case find_var_decl_by_name n ts of
    | NONE => do
        imms <- get_immutables cx src_id_opt;
        case FLOOKUP imms n of
        | SOME tvv => return (PlaceR (ImmutablePlace src_id_opt n []))
        | NONE => raise $ Error (TypeError "lookup_global: var not found")
      od
    | SOME (StorageVarDecl tr typ, id) => do
        slot <- lift_option_type (lookup_var_slot_from_layout cx tr src_id_opt id) "lookup_global var_slot";
        tv <- lift_option_type (evaluate_type tenv typ) "lookup_global evaluate_type";
        return (PlaceR (StoragePlace tr (n2w slot) tv))
      od
    | SOME (HashMapVarDecl tr kt vt, id) => do
        slot <- lift_option_type (lookup_var_slot_from_layout cx tr src_id_opt id) "lookup_global hashmap var_slot";
        return (HashMapRef tr (n2w slot) kt vt)
      od
  od
End

val () = lookup_global_def
  |> SRULE [bind_def, FUN_EQ_THM, option_CASE_rator,
            prod_CASE_rator, var_decl_info_CASE_rator, UNCURRY, LET_THM]
  |> cv_auto_trans;

Definition update_immutable_def:
  update_immutable src_id key tv v (imms: module_immutables) =
    let imm = get_source_immutables src_id imms in
    set_source_immutables src_id (imm |+ (key, (tv, v))) imms
End

val () = cv_auto_trans update_immutable_def;

(* Convert subscript back to a value for hashmap key encoding *)
Definition subscript_to_value_def:
  subscript_to_value (ValueSubscript v) = SOME v ∧
  subscript_to_value (AttrSubscript _) = NONE  (* Attributes are not valid hashmap keys *)
End

val () = cv_auto_trans subscript_to_value_def;

(* Compute final slot from base slot, key types, and list of subscripts *)
Definition compute_hashmap_slot_def:
  compute_hashmap_slot slot [] [] = SOME slot ∧
  compute_hashmap_slot slot (kt::kts) (k::ks) =
    (case subscript_to_value k of
     | NONE => NONE
     | SOME v =>
       let slot = hashmap_slot slot $ encode_hashmap_key kt v in
         compute_hashmap_slot slot kts ks) ∧
  compute_hashmap_slot _ _ _ = NONE
End

val compute_hashmap_slot_pre_def = cv_auto_trans_pre
  "compute_hashmap_slot_pre" compute_hashmap_slot_def;

Theorem compute_hashmap_slot_pre[cv_pre]:
  ∀x y z. compute_hashmap_slot_pre x y z
Proof
  ho_match_mp_tac compute_hashmap_slot_ind
  \\ rw[]
  \\ CONV_TAC (ONCE_REWRITE_CONV [compute_hashmap_slot_pre_def])
  \\ rw[]
QED

(* Get the final value type after traversing hashmap keys.
   Returns (final_type, key_types, remaining_subs) for nested access within the value. *)
Definition split_hashmap_subscripts_def:
  split_hashmap_subscripts (Type t) subs = SOME (t, [], subs) ∧
  split_hashmap_subscripts (HashMapT kt vt) [] = NONE ∧  (* Not enough subscripts *)
  split_hashmap_subscripts (HashMapT kt vt) (_::ks) =
    (case split_hashmap_subscripts vt ks of
     | SOME (t, kts, remaining) => SOME (t, kt::kts, remaining)
     | NONE => NONE)
End

val () = cv_auto_trans split_hashmap_subscripts_def;

Definition get_scopes_def:
  get_scopes st = return st.scopes st
End

val () = cv_auto_trans get_scopes_def;

Definition lookup_flag_def:
  lookup_flag fid [] = NONE ∧
  lookup_flag fid (FlagDecl id ls :: ts) =
    (if fid = id then SOME ls else lookup_flag fid ts) ∧
  lookup_flag fid (t :: ts) = lookup_flag fid ts
End

val () = cv_auto_trans lookup_flag_def;

Definition lookup_flag_mem_def:
  lookup_flag_mem cx (src_id_opt, fid) mid =
  case get_module_code cx src_id_opt
    of NONE => raise $ Error (TypeError "lookup_flag_mem code")
     | SOME ts =>
  case lookup_flag fid ts
    of NONE => raise $ Error (TypeError "lookup_flag")
     | SOME ls =>
  case INDEX_OF mid ls
    of NONE => raise $ Error (TypeError "lookup_flag_mem index")
     | SOME i => return $ Value $ FlagV (2 ** i)
End

val () = lookup_flag_mem_def
  |> SRULE [FUN_EQ_THM, option_CASE_rator]
  |> cv_auto_trans;

(* writing to the state *)

Definition set_address_immutables_def:
  set_address_immutables cx imms st =
  let addr = cx.txn.target in
    return () $ st with immutables updated_by
      (λal. (addr, imms) :: (ADELKEY addr al))
End

val () = cv_auto_trans set_address_immutables_def;

(* Module-aware global set: write a value to EVM storage *)
Definition set_global_def:
  set_global cx src_id_opt n v = do
    ts <- lift_option_type (get_module_code cx src_id_opt) "set_global get_module_code";
    tenv <<- get_tenv cx;
    case find_var_decl_by_name n ts of
    | NONE => raise $ Error (TypeError "set_global: var not found")
    | SOME (StorageVarDecl is_transient typ, id) => do
        var_slot <- lift_option_type (lookup_var_slot_from_layout cx is_transient src_id_opt id) "set_global var_slot";
        tv <- lift_option_type (evaluate_type tenv typ) "set_global evaluate_type";
        write_storage_slot cx is_transient (n2w var_slot) tv v
      od
    | SOME (HashMapVarDecl _ kt vt, id) =>
        raise $ Error (TypeError "set_global: cannot set hashmap directly")
  od
End

val () = set_global_def
  |> SRULE [bind_def, FUN_EQ_THM, option_CASE_rator,
            prod_CASE_rator, var_decl_info_CASE_rator, UNCURRY, LET_THM]
  |> cv_auto_trans;

Definition set_immutable_def:
  set_immutable cx src_id_opt n tv v = do
    imms <- get_address_immutables cx;
    let imm = get_source_immutables src_id_opt imms in
    set_address_immutables cx $ set_source_immutables src_id_opt (imm |+ (n, (tv, v))) imms
  od
End

val () = set_immutable_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM]
  |> cv_auto_trans;

Definition set_scopes_def:
  set_scopes env st = return () $ st with scopes := env
End

val () = cv_auto_trans set_scopes_def;

Definition push_scope_def:
  push_scope st = return () $ st with scopes updated_by CONS FEMPTY
End

val () = cv_auto_trans push_scope_def;

Definition push_scope_with_var_def:
  push_scope_with_var nm tv v st =
    return () $ st with scopes updated_by
      CONS (FEMPTY |+ (nm, <| assignable := F; type := tv; value := v; popped := [] |>))
End

val () = cv_auto_trans push_scope_with_var_def;

Definition pop_scope_def:
  pop_scope st =
    case st.scopes
    of [] => raise (Error (TypeError "pop_scope")) st
       | _::tl => return () (st with scopes := tl)
End

val () = cv_auto_trans pop_scope_def;

(* writing variables *)

Definition new_variable_def:
  new_variable id tv v = do
    env <- get_scopes;
    type_check (IS_NONE (lookup_scopes id env)) "new_variable bound";
    case env of [] => raise $ Error (TypeError "new_variable null")
    | e::es => set_scopes ((e |+ (id, <| assignable := T; type := tv; value := v; popped := [] |>))::es)
  od
End

val () = new_variable_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def,
            LET_RATOR, list_CASE_rator]
  |> cv_auto_trans;

Definition set_variable_def:
  set_variable id v = do
    sc <- get_scopes;
    (pre, env, entry, rest) <-
      lift_option_type (find_containing_scope id sc) "set_variable not found";
    type_check entry.assignable "set_variable not assignable";
    set_scopes (pre ++ (env |+ (id, entry with <| value := v; popped := [] |>))::rest)
  od
End

val () = set_variable_def
  |> SRULE [FUN_EQ_THM, bind_def, lift_option_def,
            ignore_bind_def, LET_RATOR, UNCURRY, option_CASE_rator]
  |> cv_auto_trans;

(* assignment to existing locations *)

(* Type paths are independent of the current dynamic lengths. *)
Definition subscript_type_def:
  subscript_type (ArrayTV tv bd) (ValueSubscript (IntV i)) =
    (if 0 <= i /\ Num i < bound_length bd then SOME tv else NONE) /\
  subscript_type (TupleTV tvs) (ValueSubscript (IntV i)) =
    (if 0 <= i /\ Num i < LENGTH tvs then SOME (EL (Num i) tvs) else NONE) /\
  subscript_type (StructTV fields) (AttrSubscript id) = ALOOKUP fields id /\
  subscript_type _ _ = NONE
End

val subscript_type_pre_def = cv_auto_trans_pre "subscript_type_pre" subscript_type_def;

Theorem subscript_type_pre[cv_pre]:
  !tv sb. subscript_type_pre tv sb
Proof
  Cases_on `tv` >> Cases_on `sb` >> simp[subscript_type_pre_def] >>
  rpt strip_tac >> gvs[]
QED

Definition evaluate_subscripts_def:
  evaluate_subscripts tv a [] = INL a ∧
  evaluate_subscripts tv a ((ValueSubscript (IntV i))::is) =
  (case a of ArrayV av =>
   (let elem_tv = (case tv of ArrayTV t _ => t | _ =>
      (case subscript_type tv (ValueSubscript (IntV i)) of
         SOME t => t | NONE => NoneTV)) in
    case array_index tv av i of SOME v =>
    (case evaluate_subscripts elem_tv v is of INL vj => INL vj
     | INR err => INR err)
    | _ => INR (RuntimeError "evaluate_subscripts array_index"))
   | _ => INR (TypeError "evaluate_subscripts type")) ∧
  evaluate_subscripts tv (StructV al) ((AttrSubscript id)::is) =
  (let field_tv = (case tv of StructTV args =>
      (case ALOOKUP args id of SOME t => t | NONE => NoneTV) | _ => NoneTV) in
   case ALOOKUP al id of SOME v =>
    (case evaluate_subscripts field_tv v is of INL v' => INL v'
     | INR err => INR err)
   | _ => INR (TypeError "evaluate_subscripts AttrSubscript")) ∧
  evaluate_subscripts _ _ _ = INR (TypeError "evaluate_subscripts")
End

val evaluate_subscripts_pre_def =
  cv_auto_trans_pre "evaluate_subscripts_pre" evaluate_subscripts_def;

(* Cache only the constructor/boolean rules needed by the CV preconditions;
   avoid traversing the large semantic context with the ambient simpset. *)
val subscript_pre_ss = boolSimps.bool_ss ++ rewrites [LET_THM, value_11];

(* Unwind translator-generated equalities before descending into their bodies.
   In particular, an impossible constructor premise discards its whole branch. *)
val pre_constructor_rewrites = Rewrite.add_rewrites Rewrite.bool_rewrites
  (GSYM AND_IMP_INTRO ::
   List.concat (map (fn ty => #rewrs (TypeBase.simpls_of ty))
    [``:value``, ``:array_value``, ``:type_value``, ``:subscript``,
     ``:value option``, ``:subscript list``, ``:num # num``]));
fun mk_pre_cleanup_conv rewrites =
  let
    val root = CHANGED_CONV (FIRST_CONV
      [Rewrite.REWRITES_CONV rewrites, Unwind.UNWIND_FORALL_CONV])
    (* Only traverse logical structure: semantic expressions in equality
       premises are opaque. Reduce a false premise before visiting its body. *)
    fun cleanup tm =
      ((root THENC cleanup) ORELSEC
       (if is_forall tm then
          QUANT_CONV cleanup THENC TRY_CONV (root THENC cleanup)
        else if is_imp tm orelse is_conj tm then
          RATOR_CONV (RAND_CONV cleanup) THENC
          ((root THENC cleanup) ORELSEC
           (RAND_CONV cleanup THENC TRY_CONV (root THENC cleanup)))
        else ALL_CONV)) tm
  in cleanup end;

(* List induction keeps the IH universal in every non-subscript argument.
   Only this unconditional IH is added to the goal-only cleanup rules. *)
Theorem evaluate_subscripts_pre[cv_pre]:
  !a b c. evaluate_subscripts_pre a b c
Proof
  Induct_on `c` \\ rpt gen_tac
  \\ CONV_TAC (ONCE_REWRITE_CONV [evaluate_subscripts_pre_def])
  \\ ASSUM_LIST (fn ihs => CONV_TAC (mk_pre_cleanup_conv
       (Rewrite.add_rewrites pre_constructor_rewrites ihs)))
QED

(* mutating inside arrays, structs, hashmaps *)

Datatype:
  assign_operation
  = Replace value
  | AppendOp value
  | PopOp
End

Theorem assign_operation_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vyperState",Tyop="assign_operation"}));

Definition assign_subscripts_def:
  (* TODO(semantic-limitation): replacement currently trusts callers/type
     checks to provide a value castable to the target type. *)
  assign_subscripts tv a [] (Replace v) = INL v ∧
  assign_subscripts tv a [] (AppendOp v) = append_element tv a v ∧
  assign_subscripts tv a [] PopOp = pop_element a ∧
  assign_subscripts tv a ((ValueSubscript (IntV i))::is) ao =
  (case a of ArrayV av =>
   (let elem_tv = (case tv of ArrayTV t _ => t | _ =>
      (case subscript_type tv (ValueSubscript (IntV i)) of
         SOME t => t | NONE => NoneTV)) in
    case array_index tv av i of SOME v =>
    (case assign_subscripts elem_tv v is ao of INL vj =>
       array_set_index tv av i vj
     | INR err => INR err)
    | _ => INR (RuntimeError "assign_subscripts array_index"))
   | _ => INR (TypeError "assign_subscripts type")) ∧
  assign_subscripts tv (StructV al) ((AttrSubscript id)::is) ao =
  (let field_tv = (case tv of StructTV args =>
      (case ALOOKUP args id of SOME t => t | NONE => NoneTV) | _ => NoneTV) in
   case ALOOKUP al id of SOME v =>
    (case assign_subscripts field_tv v is ao of INL v' =>
      INL $ StructV $ AFUPDKEY id (K v') al
     | INR err => INR err)
   | _ => INR (TypeError "assign_subscripts AttrSubscript")) ∧
  assign_subscripts _ _ _ _ = INR (TypeError "assign_subscripts")
End

val assign_subscripts_pre_def =
  cv_auto_trans_pre "assign_subscripts_pre" assign_subscripts_def;

Theorem assign_subscripts_pre[cv_pre]:
  !a b c d. assign_subscripts_pre a b c d
Proof
  Induct_on `c` \\ rpt gen_tac
  \\ CONV_TAC (ONCE_REWRITE_CONV [assign_subscripts_pre_def])
  \\ ASSUM_LIST (fn ihs => CONV_TAC (mk_pre_cleanup_conv
       (Rewrite.add_rewrites pre_constructor_rewrites ihs)))
QED

(* Walk through nested array subscripts computing the final element slot *)
Definition resolve_array_element_def:
  resolve_array_element cx is_transient base_slot (ArrayTV elem_tv bd) ((ValueSubscript (IntV idx))::rest) = do
    elem_offset <- (case bd of
     | Fixed n => do
         check (0 ≤ idx ∧ Num idx < n) "array fixed oob";
         return 0
       od
     | Dynamic n => do
         check (0 ≤ idx ∧ Num idx < n) "array dynamic capacity oob";
         storage <- get_storage_backend cx is_transient;
         stored_len <<- w2n (lookup_storage base_slot storage);
         check (Num idx < stored_len) "array dynamic length oob";
         return 1
       od);
    elem_slot <<- base_slot + n2w (elem_offset + Num idx * type_slot_size elem_tv);
    resolve_array_element cx is_transient elem_slot elem_tv rest
  od ∧
  resolve_array_element _ _ _ (ArrayTV _ _) (_::_) =
    raise (Error (TypeError "resolve_array_element: array needs int subscript")) ∧
  resolve_array_element _ _ base_slot tv rest = return (base_slot, tv, rest)
End

val resolve_array_element_pre_def = resolve_array_element_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM, check_def,
            ignore_bind_def, bound_CASE_rator]
  |> cv_auto_trans_pre "resolve_array_element_pre";

Theorem resolve_array_element_pre[cv_pre]:
  ∀a b c d e f. resolve_array_element_pre a b c d e f
Proof
  Induct_on `e` \\ rpt gen_tac
  \\ CONV_TAC (ONCE_REWRITE_CONV [resolve_array_element_pre_def])
  \\ ASSUM_LIST (fn ihs => CONV_TAC (mk_pre_cleanup_conv
       (Rewrite.add_rewrites pre_constructor_rewrites ihs)))
QED

(* Record the value left in a popped memory slot. Earlier snapshots remain
   available when a later pop removes an enclosing array. *)
Definition record_pop_def:
  record_pop path arr p history =
    case arr of
    | ArrayV (DynArrayV vs) =>
        (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))], p)::history
    | _ => history
End

val () = cv_auto_trans record_pop_def;

Definition subscripts_type_def:
  subscripts_type tv [] = SOME tv /\
  subscripts_type tv (sb::path) =
    case subscript_type tv sb of
    | NONE => NONE
    | SOME etv => subscripts_type etv path
End

val () = cv_auto_trans subscripts_type_def;


(* Search newest first. A matching popped ancestor may itself lack a later
   suffix, in which case an older, deeper snapshot still supplies that slot. *)
Definition read_popped_def:
  read_popped tv path [] = NONE /\
  read_popped tv path ((prefix,v)::history) =
    if IS_PREFIX path prefix then
      case subscripts_type tv prefix of
      | NONE => read_popped tv path history
      | SOME ptv =>
          (case evaluate_subscripts ptv v (DROP (LENGTH prefix) path) of
           | INL w => SOME w
           | INR err => read_popped tv path history)
    else read_popped tv path history
End

val read_popped_pre_def = cv_auto_trans_pre "read_popped_pre" read_popped_def;

Theorem read_popped_pre[cv_pre]:
  !tv path history. read_popped_pre tv path history
Proof
  Induct_on `history` >> rpt gen_tac >>
  simp[Once read_popped_pre_def]
QED

(* Follow the same owner selection as read_popped. A pop removes its child
   from that owner before recording the child, so retained snapshots created
   by pops have disjoint live contents. Older missing suffixes remain intact. *)
Definition replace_popped_def:
  replace_popped tv path replacement [] = NONE /\
  replace_popped tv path replacement ((prefix,old)::history) =
    if IS_PREFIX path prefix then
      case subscripts_type tv prefix of
      | NONE => OPTION_MAP (CONS (prefix,old))
          (replace_popped tv path replacement history)
      | SOME ptv =>
          (case evaluate_subscripts ptv old (DROP (LENGTH prefix) path) of
           | INL _ =>
               (case assign_subscripts ptv old (DROP (LENGTH prefix) path)
                       (Replace replacement) of
                | INL updated => SOME ((prefix,updated)::history)
                | INR _ => NONE)
           | INR _ => OPTION_MAP (CONS (prefix,old))
                 (replace_popped tv path replacement history))
    else OPTION_MAP (CONS (prefix,old))
      (replace_popped tv path replacement history)
End

val replace_popped_pre_def = cv_auto_trans_pre "replace_popped_pre" replace_popped_def;

Theorem replace_popped_pre[cv_pre]:
  !tv path replacement history. replace_popped_pre tv path replacement history
Proof
  Induct_on `history` >> rpt gen_tac >>
  simp[Once replace_popped_pre_def]
QED

Definition read_memory_path_def:
  read_memory_path entry path =
    case evaluate_subscripts entry.type entry.value path of
    | INL v => INL v
    | INR err =>
        (case read_popped entry.type path entry.popped of
         | SOME v => INL v
         | NONE => INR err)
End

val () = cv_auto_trans read_memory_path_def;

Definition read_place_def:
  read_place cx (StoragePlace tr slot tv) = read_storage_slot cx tr slot tv /\
  read_place cx (MemoryPlace id path) = do
    sc <- get_scopes;
    entry <- lift_option_type (lookup_scopes id sc) "read_place local";
    lift_sum (read_memory_path entry path)
  od /\
  read_place cx (ImmutablePlace src id path) = do
    imms <- get_immutables cx src;
    tva <- lift_option_type (FLOOKUP imms id) "read_place immutable";
    lift_sum (evaluate_subscripts (FST tva) (SND tva) path)
  od
End

val () = read_place_def
  |> SRULE [FUN_EQ_THM, bind_def, LET_THM]
  |> cv_auto_trans;

Definition place_type_value_def:
  place_type_value cx (StoragePlace tr slot tv) = return tv /\
  place_type_value cx (MemoryPlace id path) = do
    sc <- get_scopes;
    entry <- lift_option_type (lookup_scopes id sc) "place_type_value local";
    lift_option_type (subscripts_type entry.type path) "place_type_value path"
  od /\
  place_type_value cx (ImmutablePlace src id path) = do
    imms <- get_immutables cx src;
    tva <- lift_option_type (FLOOKUP imms id) "place_type_value immutable";
    lift_option_type (subscripts_type (FST tva) path) "place_type_value path"
  od
End

val () = place_type_value_def
  |> SRULE [FUN_EQ_THM, bind_def, LET_THM]
  |> cv_auto_trans;

(* Data-valued replacement keeps the stale-memory no-op separate from the
   state transformer, and gives consumers a small write boundary. *)
Definition replace_memory_entry_def:
  replace_memory_entry entry path v =
    case evaluate_subscripts entry.type entry.value path of
    | INR err => INL entry
    | INL old =>
        (case assign_subscripts entry.type entry.value path (Replace v) of
         | INR err => INR err
         | INL new => INL (entry with <|value := new; popped := []|>))
End

val () = cv_auto_trans replace_memory_entry_def;

Definition write_place_def:
  write_place cx (StoragePlace tr slot tv) v = write_storage_slot cx tr slot tv v /\
  write_place cx (MemoryPlace id path) v = do
    sc <- get_scopes;
    (pre,env,entry,rest) <- lift_option_type
      (find_containing_scope id sc) "write_place local";
    type_check entry.assignable "write_place not assignable";
    entry' <- lift_sum (replace_memory_entry entry path v);
    set_scopes (pre ++ (env |+ (id,entry'))::rest)
  od /\
  write_place cx (ImmutablePlace src id path) v = do
    imms <- get_immutables cx src;
    tva <- lift_option_type (FLOOKUP imms id) "write_place immutable";
    new <- lift_sum (assign_subscripts (FST tva) (SND tva) path (Replace v));
    set_immutable cx src id (FST tva) new
  od
End

val () = write_place_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def, LET_RATOR, UNCURRY,
            prod_CASE_rator, option_CASE_rator, sum_CASE_rator, lift_option_def]
  |> cv_auto_trans;

(* Force a captured result at the caller's chosen point in the evaluation. *)
Definition read_result_def:
  read_result cx (Value v) = return v /\
  read_result cx (PlaceR p) = read_place cx p /\
  read_result cx (HashMapRef _ _ _ _) =
    raise (Error (TypeError "read_result mapping"))
End

val () = read_result_def |> SRULE [FUN_EQ_THM] |> cv_auto_trans;

(* Read staged call arguments in their source order. *)
Definition read_results_def:
  read_results cx [] = return [] /\
  read_results cx (res::rest) = do
    v <- read_result cx res;
    vs <- read_results cx rest;
    return (v::vs)
  od
End

val read_results_pre_def = read_results_def
  |> SRULE [FUN_EQ_THM, bind_def, prod_CASE_rator, sum_CASE_rator]
  |> cv_auto_trans_pre "read_results_pre";

Theorem read_results_pre[cv_pre]:
  !cx results st. read_results_pre cx results st
Proof
  gen_tac >> Induct >> rpt gen_tac >> simp[Once read_results_pre_def]
QED

(* A conditional loads primitive words and copies non-memory aggregates.
   Memory aggregates, including dynamic bytes and strings, retain their view. *)
Definition conditional_result_def:
  conditional_result cx (PlaceR p) = do
    tv <- place_type_value cx p;
    if (case p of MemoryPlace _ _ =>
          (case tv of
           | ArrayTV _ _ => T | TupleTV _ => T | StructTV _ => T
           | BaseTV (BytesT (Dynamic _)) => T | BaseTV (StringT _) => T
           | _ => F)
        | _ => F)
    then return (PlaceR p)
    else do v <- read_place cx p; return (Value v) od
  od /\
  conditional_result cx (Value v) = return (Value v) /\
  conditional_result cx (HashMapRef _ _ _ _) =
    raise (Error (TypeError "conditional mapping"))
End

val () = conditional_result_def
  |> SRULE [FUN_EQ_THM, bind_def, LET_THM, COND_RATOR, place_CASE_rator,
            type_value_CASE_rator, base_type_CASE_rator, bound_CASE_rator]
  |> cv_auto_trans;

Definition result_array_length_def:
  result_array_length cx (PlaceR (StoragePlace tr slot (ArrayTV tv (Fixed n)))) =
    return n /\
  result_array_length cx (PlaceR (StoragePlace tr slot (ArrayTV tv (Dynamic n)))) = do
    storage <- get_storage_backend cx tr;
    return (w2n (lookup_storage slot storage))
  od /\
  result_array_length cx res = do
    v <- read_result cx res;
    case v of
    | ArrayV (DynArrayV vs) => return (LENGTH vs)
    | ArrayV (SArrayV vs) => return (LENGTH vs)
    | ArrayV (TupleV vs) => return (LENGTH vs)
    | BytesV bs => return (LENGTH bs)
    | StringV bs => return (LENGTH bs)
    | _ => raise (Error (TypeError "result_array_length"))
  od
End

val () = result_array_length_def
  |> SRULE [FUN_EQ_THM, bind_def, LET_THM, eval_result_CASE_rator,
            place_CASE_rator, type_value_CASE_rator, bound_CASE_rator,
            value_CASE_rator, array_value_CASE_rator]
  |> cv_auto_trans;

(* The offset is the sum of the preceding fields' complete slot sizes. *)
Definition struct_field_slot_def:
  struct_field_slot [] id = NONE /\
  struct_field_slot ((name,tv)::fields) id =
    if name = id then SOME (0,tv)
    else OPTION_MAP (\(off,ftv). (type_slot_size tv + off,ftv))
           (struct_field_slot fields id)
End

val () = cv_auto_trans struct_field_slot_def;

(* Slot offset follows encode_tuple/decode_tuple's left-to-right layout. *)
Definition tuple_prefix_slot_size_def:
  tuple_prefix_slot_size 0 tvs = 0 /\
  tuple_prefix_slot_size (SUC n) [] = 0 /\
  tuple_prefix_slot_size (SUC n) (tv::tvs) =
    type_slot_size tv + tuple_prefix_slot_size n tvs
End

val () = cv_auto_trans tuple_prefix_slot_size_def;

Theorem tuple_prefix_slot_size_sum:
  !n tvs. tuple_prefix_slot_size n tvs = SUM (MAP type_slot_size (TAKE n tvs))
Proof
  Induct >> Cases_on `tvs` >> simp[tuple_prefix_slot_size_def]
QED

Definition extend_storage_place_def:
  extend_storage_place cx tr slot (StructTV fields) (AttrSubscript id) = do
    (off,tv) <- lift_option_type (struct_field_slot fields id) "place struct field";
    return (StoragePlace tr (slot + n2w off) tv)
  od /\
  extend_storage_place cx tr slot (ArrayTV etv bd) (ValueSubscript (IntV i)) = do
    (slot',tv,rest) <- resolve_array_element cx tr slot (ArrayTV etv bd)
                       [ValueSubscript (IntV i)];
    return (StoragePlace tr slot' tv)
  od /\
  extend_storage_place cx tr slot (TupleTV tvs) (ValueSubscript (IntV i)) = do
    check (0 <= i /\ Num i < LENGTH tvs) "tuple index oob";
    tv <- lift_option_type (oEL (Num i) tvs) "tuple component type";
    return (StoragePlace tr
      (slot + n2w (tuple_prefix_slot_size (Num i) tvs)) tv)
  od /\
  extend_storage_place cx tr slot tv sb =
    raise (Error (TypeError "extend_storage_place"))
End

val () = extend_storage_place_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def, LET_RATOR, UNCURRY]
  |> cv_auto_trans;

Definition extend_memory_place_def:
  extend_memory_place (MemoryPlace id path) sb = MemoryPlace id (path ++ [sb]) /\
  extend_memory_place (ImmutablePlace src id path) sb = ImmutablePlace src id (path ++ [sb]) /\
  extend_memory_place p sb = p
End

val () = cv_auto_trans extend_memory_place_def;

(* Extend a resolved location or mapping root. No invented value type is
   needed for targets: their metadata determines every step. *)
Theorem value_type_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vyperAST",Tyop="value_type"}));

Definition extend_place_def:
  extend_place cx (PlaceR (StoragePlace tr slot tv)) sb = do
    p <- extend_storage_place cx tr slot tv sb;
    return (PlaceR p)
  od /\
  extend_place cx (PlaceR p) sb = do
    tv <- place_type_value cx p;
    v <- read_place cx p;
    lift_sum (evaluate_subscripts tv v [sb]);
    return (PlaceR (extend_memory_place p sb))
  od /\
  extend_place cx (HashMapRef tr slot kt vt) (ValueSubscript kv) =
    (let slot' = hashmap_slot slot (encode_hashmap_key kt kv) in
     case vt of
     | HashMapT kt' vt' => return (HashMapRef tr slot' kt' vt')
     | Type ty => do
         tv <- lift_option_type (evaluate_type (get_tenv cx) ty)
                 "mapping element type";
         return (PlaceR (StoragePlace tr slot' tv))
       od) /\
  extend_place cx _ _ = raise (Error (TypeError "extend_place"))
End

val () = extend_place_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def, LET_RATOR,
            value_type_CASE_rator]
  |> cv_auto_trans;

(* Immediate aggregates have no address; their syntax supplies the type needed
   to interpret sparse array defaults. Located bases use their own metadata. *)
Definition select_result_def:
  select_result cx ty (Value v) sb = do
    tv <- lift_option_type (evaluate_type (get_tenv cx) ty) "selection base type";
    w <- lift_sum (evaluate_subscripts tv v [sb]);
    return (Value w)
  od /\
  select_result cx ty res sb = extend_place cx res sb
End

val () = select_result_def
  |> SRULE [FUN_EQ_THM, bind_def, LET_RATOR] |> cv_auto_trans;

Definition get_place_def:
  get_place (PlaceR p) = return p /\
  get_place _ = raise (Error (TypeError "target is not a place"))
End

val () = get_place_def |> SRULE [FUN_EQ_THM] |> cv_auto_trans;

(* Storage pop changes only the length. Its result is the retained element
   address, so a subsequent append may overwrite it before the caller reads. *)
Definition pop_place_def:
  pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) = do
    storage <- get_storage_backend cx tr;
    len <<- w2n (lookup_storage slot storage);
    check (0 < len) "pop empty storage array";
    write_storage_slot cx tr slot (BaseTV (UintT 256)) (IntV &(len - 1));
    return (PlaceR (StoragePlace tr (slot + n2w (1 + (len - 1) * type_slot_size tv)) tv))
  od /\
  pop_place cx (MemoryPlace id path) = do
    sc <- get_scopes;
    (pre,env,entry,rest) <- lift_option_type
      (find_containing_scope id sc) "pop_place local";
    type_check entry.assignable "pop_place not assignable";
    arr <- lift_sum (read_memory_path entry path);
    vs <- lift_option_type
      (case arr of ArrayV (DynArrayV vs) => SOME vs | _ => NONE)
      "pop_place not dynamic array";
    check (vs <> []) "pop empty memory array";
    popped <- lift_sum (popped_value arr);
    shortened <- lift_sum (pop_element arr);
    (updated,prior_history) <- lift_sum
      (case evaluate_subscripts entry.type entry.value path of
       | INL _ =>
           (case assign_subscripts entry.type entry.value path (Replace shortened) of
            | INL updated => INL (updated,entry.popped)
            | INR err => INR err)
       | INR err =>
           (case replace_popped entry.type path shortened entry.popped of
            | SOME history => INL (entry.value,history)
            | NONE => INR err));
    history <<- record_pop path arr popped prior_history;
    set_scopes (pre ++ (env |+ (id,entry with <|value := updated; popped := history|>))::rest);
    return (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))])))
  od /\
  (* The source compiler rejects immutable mutation after initialization. Keep
     the existing value semantics for this checker-accepted extension. *)
  pop_place cx (ImmutablePlace src id path) = do
    imms <- get_immutables cx src;
    tva <- lift_option_type (FLOOKUP imms id) "pop_place immutable";
    arr <- lift_sum (evaluate_subscripts (FST tva) (SND tva) path);
    popped <- lift_sum (popped_value arr);
    updated <- lift_sum (assign_subscripts (FST tva) (SND tva) path PopOp);
    set_immutable cx src id (FST tva) updated;
    return (Value popped)
  od /\
  pop_place cx _ = raise (Error (TypeError "pop_place"))
End

val () = pop_place_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def, LET_RATOR, UNCURRY,
            prod_CASE_rator, option_CASE_rator, value_CASE_rator,
            array_value_CASE_rator] |> cv_auto_trans;

Definition append_place_def:
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) v = do
    storage <- get_storage_backend cx tr;
    len <<- w2n (lookup_storage slot storage);
    check (len < n) "append full storage array";
    write_storage_slot cx tr (slot + n2w (1 + len * type_slot_size tv)) tv v;
    write_storage_slot cx tr slot (BaseTV (UintT 256)) (IntV &(len + 1))
  od /\
  append_place cx p v = do
    tv <- place_type_value cx p;
    old <- read_place cx p;
    updated <- lift_sum (append_element tv old v);
    write_place cx p updated
  od
End

val () = append_place_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def, LET_RATOR,
            place_CASE_rator, type_value_CASE_rator, bound_CASE_rator]
  |> cv_auto_trans;

Theorem lookup_global_mapping:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name n ts = SOME (HashMapVarDecl tr kt vt, id) /\
  lookup_var_slot_from_layout cx tr src id = SOME slot ==>
  lookup_global cx src n st =
    (INL (HashMapRef tr (n2w slot) kt vt), st)
Proof
  simp[lookup_global_def, bind_def, lift_option_type_def, return_def]
QED

Theorem extend_place_nested_mapping:
  extend_place cx (HashMapRef tr slot kt (HashMapT kt' vt'))
    (ValueSubscript kv) st =
  (INL (HashMapRef tr (hashmap_slot slot (encode_hashmap_key kt kv)) kt' vt'), st)
Proof
  simp[extend_place_def,
       lift_option_type_def, bind_def, return_def]
QED

Theorem extend_place_mapping_leaf:
  evaluate_type (get_tenv cx) typ = SOME tv ==>
  extend_place cx (HashMapRef tr slot kt (Type typ))
    (ValueSubscript kv) st =
  (INL (PlaceR (StoragePlace tr (hashmap_slot slot (encode_hashmap_key kt kv)) tv)), st)
Proof
  simp[extend_place_def,
       lift_option_type_def, bind_def, return_def]
QED

Theorem place_delayed_pop_read[local]:
  read_memory_path
    <|assignable := T; type := ArrayTV (BaseTV (UintT 256)) (Dynamic 3);
      value := ArrayV (DynArrayV []);
      popped := [([ValueSubscript (IntV 0)],IntV 5)]|>
    [ValueSubscript (IntV 0)] = INL (IntV 5)
Proof
  EVAL_TAC >> simp[]
QED

Theorem place_nested_pop_read[local]:
  let tv = ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 3)) (Dynamic 3);
      entry = <|assignable := T; type := tv; value := ArrayV (DynArrayV []);
        popped := [([ValueSubscript (IntV 0)],ArrayV (DynArrayV [IntV 1]));
                   ([ValueSubscript (IntV 0); ValueSubscript (IntV 1)],IntV 2)]|>
  in read_memory_path entry [ValueSubscript (IntV 0); ValueSubscript (IntV 0)] = INL (IntV 1) /\
     read_memory_path entry [ValueSubscript (IntV 0); ValueSubscript (IntV 1)] = INL (IntV 2)
Proof
  EVAL_TAC >> simp[subscript_type_def] >> EVAL_TAC
QED

Theorem place_fixed_extension_oob[local]:
  !cx st. extend_storage_place cx F 0w (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
    (ValueSubscript (IntV 1)) st =
    (INR (Error (RuntimeError "array fixed oob")),st)
Proof
  EVAL_TAC >> simp[]
QED

Theorem place_pop_then_delayed_read[local]:
  !cx.
  let entry = <|assignable := T;
      type := ArrayTV (BaseTV (UintT 256)) (Dynamic 3);
      value := ArrayV (DynArrayV [IntV 5]); popped := []|>;
      st = empty_state with scopes := [FEMPTY |+ ("d",entry)]
  in FST ((do
      pop_place cx (MemoryPlace "d" []);
      read_place cx (MemoryPlace "d" [ValueSubscript (IntV 0)])
    od) st) = INL (IntV 5)
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

(* Place reads are observations, even when lookup or decoding fails. *)
Theorem read_storage_slot_state_snd:
  SND (read_storage_slot cx tr slot tv st) = st
Proof
  Cases_on `tr` >>
  simp[read_storage_slot_def, get_storage_backend_def, get_accounts_def,
       get_transient_storage_def, bind_def, return_def, lift_option_def,
       raise_def, AllCaseEqs()] >>
  rpt BasicProvers.TOP_CASE_TAC >> simp[return_def, raise_def]
QED

Theorem read_place_state:
  read_place cx p st = (r,st') ==> st' = st
Proof
  Cases_on `p` >>
  simp[read_place_def, get_scopes_def, get_immutables_def,
       get_address_immutables_def, bind_def, return_def,
       lift_option_type_def, lift_sum_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  metis_tac[read_storage_slot_state_snd, SND]
QED

Theorem place_type_value_state:
  place_type_value cx p st = (r,st') ==> st' = st
Proof
  Cases_on `p` >>
  simp[place_type_value_def, get_scopes_def, get_immutables_def,
       get_address_immutables_def, bind_def, return_def,
       lift_option_type_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def])
QED

Theorem read_result_state:
  read_result cx res st = (r,st') ==> st' = st
Proof
  Cases_on `res` >> simp[read_result_def, return_def, raise_def] >>
  metis_tac[read_place_state]
QED

Theorem read_results_state:
  !results st r st'. read_results cx results st = (r,st') ==> st' = st
Proof
  Induct >> simp[read_results_def, return_def] >>
  rpt gen_tac >> simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
  imp_res_tac read_result_state >> gvs[return_def] >> metis_tac[]
QED

Theorem read_results_length:
  !results st vs st'.
    read_results cx results st = (INL vs,st') ==> LENGTH vs = LENGTH results
Proof
  Induct >> simp[read_results_def, return_def] >>
  rpt gen_tac >> simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[return_def] >> first_x_assum drule >> simp[]
QED

Theorem place_nested_pop_sequence[local]:
  !cx.
  let entry = <|assignable := T;
      type := ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 3)) (Dynamic 3);
      value := ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 1; IntV 2])]);
      popped := []|>;
      st = empty_state with scopes := [FEMPTY |+ ("d",entry)]
  in FST ((do
      pop_place cx (MemoryPlace "d" [ValueSubscript (IntV 0)]);
      pop_place cx (MemoryPlace "d" []);
      a <- read_place cx (MemoryPlace "d" [ValueSubscript (IntV 0)]);
      b <- read_place cx (MemoryPlace "d" [ValueSubscript (IntV 0); ValueSubscript (IntV 0)]);
      c <- read_place cx (MemoryPlace "d" [ValueSubscript (IntV 0); ValueSubscript (IntV 1)]);
      return (a,b,c)
    od) st) = INL (ArrayV (DynArrayV [IntV 1]),IntV 1,IntV 2)
Proof
  rpt (CHANGED_TAC (EVAL_TAC >>
    simp[lookup_scopes_def, FLOOKUP_UPDATE, FLOOKUP_EMPTY,
         subscript_type_def, return_def]))
QED

Theorem place_repeated_pop_sequence[local]:
  !cx.
  let entry = <|assignable := T;
      type := ArrayTV (BaseTV (UintT 256)) (Dynamic 3);
      value := ArrayV (DynArrayV [IntV 1; IntV 2]); popped := []|>;
      st = empty_state with scopes := [FEMPTY |+ ("d",entry)]
  in FST ((do
      pop_place cx (MemoryPlace "d" []);
      pop_place cx (MemoryPlace "d" []);
      a <- read_place cx (MemoryPlace "d" [ValueSubscript (IntV 0)]);
      b <- read_place cx (MemoryPlace "d" [ValueSubscript (IntV 1)]);
      return (a,b)
    od) st) = INL (IntV 1,IntV 2)
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[return_def]
QED

Theorem place_memory_write_reset[local]:
  !cx.
  let entry = <|assignable := T;
      type := ArrayTV (BaseTV (UintT 256)) (Dynamic 3);
      value := ArrayV (DynArrayV [IntV 1]);
      popped := [([ValueSubscript (IntV 1)],IntV 2)]|>;
      st = empty_state with scopes := [FEMPTY |+ ("d",entry)]
  in FST ((do
      write_place cx (MemoryPlace "d" [ValueSubscript (IntV 0)]) (IntV 7);
      a <- read_place cx (MemoryPlace "d" [ValueSubscript (IntV 0)]);
      sc <- get_scopes;
      return (a, OPTION_MAP (\e. e.popped) (lookup_scopes "d" sc))
    od) st) = INL (IntV 7,SOME [])
Proof
  rpt (CHANGED_TAC (EVAL_TAC >>
    simp[lookup_scopes_def, FLOOKUP_UPDATE, FLOOKUP_EMPTY, return_def]))
QED

Theorem place_storage_raw_write[local]:
  !cx.
  FST ((do
      write_place cx (StoragePlace T 7w (BaseTV (UintT 256))) (IntV 10);
      read_place cx (StoragePlace T 7w (BaseTV (UintT 256)))
    od) empty_state) = INL (IntV 10)
Proof
  EVAL_TAC >> simp[]
QED

Theorem place_memory_extension_bounds[local]:
  !cx.
  let entry = <|assignable := T;
      type := ArrayTV (BaseTV (UintT 256)) (Dynamic 3);
      value := ArrayV (DynArrayV [IntV 5]); popped := []|>;
      st = empty_state with scopes := [FEMPTY |+ ("d",entry)]
  in extend_place cx (PlaceR (MemoryPlace "d" []))
       (ValueSubscript (IntV 0)) st =
       (INL (PlaceR (MemoryPlace "d" [ValueSubscript (IntV 0)])),st) /\
     ISL (FST (extend_place cx (PlaceR (MemoryPlace "d" []))
       (ValueSubscript (IntV 1)) st)) = F
Proof
  rpt (CHANGED_TAC (EVAL_TAC >>
    simp[lookup_scopes_def, FLOOKUP_UPDATE, FLOOKUP_EMPTY, return_def]))
QED

Theorem place_struct_fixed_path[local]:
  !cx.
  let entry = <|assignable := T;
      type := StructTV [("a",ArrayTV (BaseTV (UintT 256)) (Fixed 2))];
      value := StructV [("a",ArrayV (DynArrayV [IntV 3; IntV 4]))]; popped := []|>;
      st = empty_state with scopes := [FEMPTY |+ ("s",entry)]
  in FST ((do
      pv <- extend_place cx
        (PlaceR (MemoryPlace "s" [])) (AttrSubscript "a");
      pv' <- extend_place cx pv (ValueSubscript (IntV 1));
      read_result cx pv'
    od) st) = INL (IntV 4)
Proof
  rpt (CHANGED_TAC (EVAL_TAC >>
    simp[lookup_scopes_def, FLOOKUP_UPDATE, FLOOKUP_EMPTY,
         subscript_type_def, return_def]))
QED
