(*
 * Builtin, type-builtin, binop, account/env, and call-target typing lemmas.
 *)

Theory vyperTypeBuiltins
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair
  words byte keccak vyperAST vyperValue vyperValueOperation vyperMisc
  vyperABI vyperInterpreter vyperState vyperContext vyperStorage
  vyperTyping vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeValues
  vyperTypeBytesCrypto vyperTypeDefaults vyperTypeConversions vyperTypeABI
Libs
  wordsLib

(* ===== Environment/account items ===== *)

Theorem Env_builtin_no_type_error:
  context_well_typed cx /\ item <> MsgGas ==>
  !msg. evaluate_builtin cx acc (env_item_type item) (Env item) [] <> INR (TypeError msg)
Proof
  strip_tac >> Cases_on `item` >>
  gvs[evaluate_builtin_def, env_item_type_def]
  >> rw[evaluate_block_hash_def]
QED

Theorem Env_builtin_success_type:
  context_well_typed cx /\ evaluate_type tenv (env_item_type item) = SOME tv /\
  evaluate_builtin cx acc (env_item_type item) (Env item) [] = INL v ==>
  value_has_type tv v
Proof
  strip_tac >> Cases_on `item` >>
  gvs[evaluate_builtin_def, env_item_type_def, evaluate_type_def,
      value_has_type_def, context_well_typed_def]
  >> rw[value_has_type_def]
  >> gvs[evaluate_block_hash_def, AllCaseEqs(), LET_THM, value_has_type_def]
  >> simp[LENGTH_word_to_bytes,word_to_bytes_be_def]
QED

Theorem account_well_typed_op:
  account_well_typed a /\ evaluate_type tenv (account_item_type item) = SOME tv /\
  value_has_type (BaseTV AddressT) addr_v ==>
  value_has_type tv (evaluate_account_op item (case addr_v of BytesV bs => bs | _ => []) a)
Proof
  strip_tac >> Cases_on `addr_v` >> gvs[value_has_type_def] >>
  Cases_on `item` >>
  gvs[account_well_typed_def, account_item_type_def, evaluate_account_op_def,
      evaluate_type_def, value_has_type_def, LENGTH_Keccak_256_w64]
QED

Theorem Acc_builtin_sound:
  accounts_well_typed acc /\ evaluate_type tenv (account_item_type item) = SOME tv /\
  value_has_type (BaseTV AddressT) addr_v ==>
  ?v. evaluate_builtin cx acc (account_item_type item) (Acc item) [addr_v] = INL v /\
      value_has_type tv v
Proof
  Cases_on `addr_v` >> rw[value_has_type_def] >>
  simp[evaluate_builtin_def] >>
  drule_at Any account_well_typed_op >>
  simp[Once(oneline value_has_type_def)] >>
  disch_then(qspec_then`BytesV l`mp_tac) >> simp[] >>
  disch_then irule >>
  gvs[accounts_well_typed_def]
QED

(* ===== Binary operations ===== *)

Theorem well_typed_binop_no_type_error:
  well_typed_binop ty bop t1 t2 /\
  evaluate_type tenv ty = SOME result_tv /\
  evaluate_type tenv t1 = SOME tv1 /\ evaluate_type tenv t2 = SOME tv2 /\
  value_has_type tv1 v1 /\ value_has_type tv2 v2 /\
  u = (case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u) ==>
  !msg. evaluate_binop u result_tv bop v1 v2 <> INR (TypeError msg)
Proof
  cheat
QED

Theorem well_typed_binop_success_type:
  well_typed_binop ty bop t1 t2 /\
  evaluate_type tenv ty = SOME result_tv /\
  evaluate_type tenv t1 = SOME tv1 /\ evaluate_type tenv t2 = SOME tv2 /\
  value_has_type tv1 v1 /\ value_has_type tv2 v2 /\
  u = (case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u) /\
  evaluate_binop u result_tv bop v1 v2 = INL v ==>
  value_has_type result_tv v
Proof
  cheat
QED

(* ===== Builtins ===== *)

Theorem well_typed_builtin_app_length:
  well_typed_builtin_app ty blt ts ==> builtin_args_length_ok blt (LENGTH ts)
Proof
  simp[oneline well_typed_builtin_app_def] >>
  CASE_TAC >> rw[builtin_args_length_ok_def] >>
  pop_assum mp_tac >> CASE_TAC >> rw[]
QED

Theorem well_typed_builtin_app_no_type_error:
  well_typed_builtin_app ty blt ts /\ blt <> Len /\
  MAP (evaluate_type tenv) ts = MAP SOME tvs /\
  evaluate_type tenv ty = SOME tv /\
  LIST_REL value_has_type tvs vs /\ context_well_typed cx /\ accounts_well_typed acc /\
  (!item. blt = Env item ==> item <> MsgGas) ==>
  !msg. evaluate_builtin cx acc ty blt vs <> INR (TypeError msg)
Proof
  cheat
QED

Theorem well_typed_builtin_app_success_type:
  well_typed_builtin_app ty blt ts /\ blt <> Len /\
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  LIST_REL value_has_type tvs vs /\ context_well_typed cx /\ accounts_well_typed acc /\
  evaluate_builtin cx acc ty blt vs = INL v ==>
  value_has_type tv v
Proof
  cheat
QED

Theorem Len_result_fits_uint256:
  well_typed_builtin_app ty Len [arg_ty] /\
  evaluate_type tenv arg_ty = SOME arg_runtime_tv /\
  well_formed_type_value arg_runtime_tv /\
  toplevel_value_typed arg_tv arg_runtime_tv /\
  toplevel_array_length cx arg_tv st = (INL n, st') ==>
  n < dimword(:256)
Proof
  strip_tac >> gvs[well_typed_builtin_app_def] >>
  Cases_on `arg_ty` >> gvs[is_sized_type_def, evaluate_type_def]
  >- (
    rename1 `BaseT bt` >> Cases_on `bt` >>
    gvs[is_sized_type_def, evaluate_type_def, AllCaseEqs(), LET_THM]
    >- (
      rename1 `StringT max` >>
      Cases_on `arg_tv` >>
      gvs[toplevel_value_typed_def, oneline toplevel_array_length_def,
          return_def, raise_def, value_has_type_def, AllCaseEqs(), bind_def,
          get_storage_backend_def, get_accounts_def, value_CASE_rator,
          get_transient_storage_def]) >>
    gvs[evaluate_type_def, compatible_bound_def, AllCaseEqs(), LET_THM] >>
    Cases_on `arg_tv` >>
    gvs[toplevel_value_typed_def, oneline toplevel_array_length_def,
        return_def, raise_def, value_has_type_def, AllCaseEqs(), bind_def,
        get_storage_backend_def, get_accounts_def, get_transient_storage_def,
        value_CASE_rator] >>
    gvs[well_formed_type_value_def]
  ) >>
  gvs[AllCaseEqs()] >>
  Cases_on `arg_tv` >>
  gvs[toplevel_value_typed_def, oneline toplevel_array_length_def, return_def,
      raise_def, value_has_type_def, AllCaseEqs(), bind_def,
      ignore_bind_def, value_CASE_rator, array_value_CASE_rator,
      get_storage_backend_def, get_accounts_def, get_transient_storage_def,
      well_formed_type_value_def, type_slot_size_def] >>
  qmatch_asmsub_rename_tac`ArrayTV _ bd` >> Cases_on`bd` >>
  gvs[value_has_type_def, return_def, type_slot_size_def]
  >- (
    qmatch_assum_abbrev_tac`n * tz < bn` >>
    reverse(Cases_on`0 < n`) >- gvs[] >>
    reverse(Cases_on`1 < tz`) >- (
      `tz = 1` by gvs[] >> gvs[] ) >>
    `n < n * tz` by gvs[] >>
    irule LESS_TRANS >>
    goal_assum drule >>
    first_assum ACCEPT_TAC
  ) >>
  gvs[bind_def,AllCaseEqs(),return_def] >>
  qmatch_goalsub_abbrev_tac`w2n w` >>
  Q.ISPEC_THEN`w`mp_tac w2n_lt >>
  simp[]
QED

Theorem Len_builtin_sound:
  well_typed_builtin_app ty Len [arg_ty] /\
  evaluate_type tenv ty = SOME tv /\ evaluate_type tenv arg_ty = SOME arg_runtime_tv /\
  toplevel_value_typed arg_tv arg_runtime_tv /\
  toplevel_array_length cx arg_tv st = (INL n, st') ==>
  value_has_type tv (IntV (&n))
Proof
  strip_tac >>
  `well_formed_type_value arg_runtime_tv` by metis_tac[evaluate_type_well_formed_type_value] >>
  `n < dimword(:256)` by (drule_all Len_result_fits_uint256 >> simp[]) >>
  gvs[well_typed_builtin_app_def, evaluate_type_def, value_has_type_def]
QED

(* ===== Type builtins ===== *)

Theorem well_typed_type_builtin_args_length:
  well_typed_type_builtin_args tb target_ty ts ==> type_builtin_args_length_ok tb (LENGTH ts)
Proof
  simp[oneline well_typed_type_builtin_args_def] >>
  CASE_TAC >> rw[type_builtin_args_length_ok_def] >>
  Cases_on`ts` >> gvs[]
QED

Theorem well_typed_type_builtin_no_type_error:
  type_builtin_result_ok tb result_ty target_ty ts /\
  well_typed_type_builtin_args tb target_ty ts /\
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs /\
  evaluate_type (get_tenv cx) result_ty = SOME result_tv /\
  LIST_REL value_has_type tvs vs /\ context_well_typed cx ==>
  !msg. evaluate_type_builtin cx tb target_ty vs <> INR (TypeError msg)
Proof
  cheat
QED

Theorem well_typed_type_builtin_success_type:
  type_builtin_result_ok tb result_ty target_ty ts /\
  well_typed_type_builtin_args tb target_ty ts /\
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs /\
  evaluate_type (get_tenv cx) result_ty = SOME result_tv /\
  LIST_REL value_has_type tvs vs /\ context_well_typed cx /\
  evaluate_type_builtin cx tb target_ty vs = INL v ==>
  value_has_type result_tv v
Proof
  Cases_on `tb` >>
  rw[type_builtin_result_ok_def, well_typed_type_builtin_args_def,
     evaluate_type_builtin_def, AllCaseEqs(), LET_THM] >>
  gvs[]
  >- (drule default_value_has_type_thm >> simp[])
  >- metis_tac[evaluate_max_value_well_typed]
  >- metis_tac[evaluate_max_value_well_typed]
  >- metis_tac[evaluate_min_value_well_typed]
  >- metis_tac[evaluate_min_value_well_typed]
  >- gvs[evaluate_type_def, evaluate_type_builtin_def,
         within_int_bound_def, value_has_type_def]
  >- (gvs[LENGTH_EQ_NUM_compute] >>
      drule_all valid_conversion_success_type >> simp[])
  >- suspend"extract32"
  >- suspend"abi_decode"
  >- suspend"abi_encode"
  >- suspend"encode_tuple"
  >- suspend"encode_tuple_nowrap"
QED

Resume well_typed_type_builtin_success_type[extract32]:
  gvs[LENGTH_EQ_NUM_compute, evaluate_type_builtin_def] >>
  Cases_on`tvs` >>
  gvs[] >>
  qmatch_asmsub_rename_tac`evaluate_type_builtin _ _ _ [v1; v2]` >>
  Cases_on`v1` >> Cases_on`v2` >> gvs[evaluate_type_builtin_def] >>
  drule_at Any evaluate_extract32_well_typed >>
  disch_then drule >>
  simp[]
QED

Resume well_typed_type_builtin_success_type[abi_decode]:
  gvs[LENGTH_EQ_NUM_compute, evaluate_type_builtin_def,
      type_builtin_result_ok_def, well_typed_type_builtin_args_def] >>
  qmatch_asmsub_rename_tac`evaluate_type_builtin _ _ _ [v1]` >>
  Cases_on`v1` >> gvs[evaluate_type_builtin_def] >>
  gvs[AllCaseEqs(),evaluate_type_def,value_has_type_def] >>
  drule evaluate_abi_decode_well_typed >>
  simp[evaluate_type_def, value_has_type_def, type_slot_size_def] >>
  disch_then irule >>
  drule evaluate_type_well_formed_type_value >> strip_tac >>
  drule well_formed_type_value_slot_size >> simp[]
QED

(* TODO: these 3 cheats: type system needs to be fixed to constrain
encoding bound, possibly adding a condition to
type_builtin_result_ok involving a new
abi_encoded_bound definition *)

Resume well_typed_type_builtin_success_type[abi_encode]:
  cheat
QED

Resume well_typed_type_builtin_success_type[encode_tuple]:
  cheat
QED

Resume well_typed_type_builtin_success_type[encode_tuple_nowrap]:
  cheat
QED

Finalise well_typed_type_builtin_success_type

(* ===== Calls / special targets ===== *)

(* TODO: move *)
Theorem word_size_le:
  0 < n ⇒ word_size n ≤ n
Proof
  strip_tac >>
  simp[vfmConstantsTheory.word_size_def] >>
  `n + 31 ≤ 32 * n` by simp[] >>
  `(n + 31) DIV 32 ≤ (32 * n) DIV 32` by
    (irule DIV_LE_MONOTONE >> simp[]) >>
  `(32 * n) DIV 32 = n` by simp[MULT_TO_DIV] >>
  gvs[]
QED

Theorem raw_call_return_type_well_formed:
  flags.rcf_max_outsize < dimword(:256) ==>
  well_formed_type tenv (raw_call_return_type flags)
Proof
  Cases_on `flags` >>
  rw[raw_call_return_type_def, well_formed_type_def, evaluate_type_def,
     type_slot_size_def] >> rw[] >>
  `word_size n ≤ n` by (irule word_size_le >> rw[]) >>
  Cases_on`word_size n < n` >> gvs[type_slot_size_def] >>
  rw[] >>
  `word_size n = n` by gvs[] >>
  gvs[NOT_LESS_EQUAL] >>
  qmatch_assum_abbrev_tac`n + 1 <= bn` >>
  `n + 1 = bn` by gvs[] >>
  `n = bn - 1` by gvs[Abbr`bn`] >>
  gvs[Abbr`bn`] >>
  gvs[vfmConstantsTheory.word_size_def]
QED

Theorem internal_call_signature_sound:
  fn_sigs_consistent fn_sigs cx /\
  FLOOKUP fn_sigs (src,fn) = SOME sig ==>
  ?ts fm nr params dflts body.
    get_module_code cx src = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts = SOME (fm,nr,params,dflts,sig.ret_ty,body) /\
    sig.param_types = MAP SND params /\ sig.num_defaults = LENGTH dflts
Proof
  rw[fn_sigs_consistent_def]
QED

Theorem ext_call_args_typed:
  well_typed_expr env (Call ty (ExtCall stat fsig) args drv) ==>
  well_typed_exprs env args /\ well_typed_opt env drv
Proof
  Cases_on `fsig` >> Cases_on `r` >> rw[well_typed_expr_def]
QED

