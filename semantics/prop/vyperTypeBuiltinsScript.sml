(*
 * Builtin, type-builtin, binop, account/env, and call-target typing lemmas.
 *)

Theory vyperTypeBuiltins
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair
  words byte integer keccak vyperAST vyperValue vyperValueOperation vyperMisc
  vyperABI vyperInterpreter vyperState vyperContext vyperStorage
  vyperTyping vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeValues
  vyperTypeBytesCrypto vyperTypeDefaults vyperTypeConversions vyperTypeABI
Libs
  wordsLib
  intLib

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

Theorem modexp_lt:
  !b e m a. 0 < m ==> vfmExecution$modexp b e m a < m
Proof
  simp[vfmExecutionTheory.modexp_exp]
QED

Theorem int_type_Num_bound:
  !tyv i. value_has_type tyv (IntV i) /\ well_formed_type_value tyv ==>
          Num i < 2 ** 256
Proof
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `_ < bound` >>
  qpat_x_assum `value_has_type _ _` mp_tac >>
  simp[value_has_type_inv] >> strip_tac >> gvs[well_formed_type_value_def]
  >- (irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** n` >>
      unabbrev_all_tac >> simp[] >>
      irule (iffRL EXP_BASE_LE_MONO) >> simp[]) >>
  Cases_on `n = 0` >- (unabbrev_all_tac >> gvs[within_int_bound_def]) >>
  gvs[within_int_bound_def, LET_THM, Num_neg] >>
  Cases_on `i < 0` >> gvs[] >>
  irule LESS_EQ_LESS_TRANS >>
  qexists_tac `2 ** (n - 1)` >>
  unabbrev_all_tac >> simp[]
QED

Theorem uint2str_strlen_bound:
  !tyv i. value_has_type tyv (IntV i) /\ well_formed_type_value tyv ==>
          STRLEN (toString (Num i)) <= 78
Proof
  rpt strip_tac >>
  imp_res_tac int_type_Num_bound >>
  qmatch_asmsub_abbrev_tac `Num i < bound` >>
  simp[ASCIInumbersTheory.LENGTH_num_to_dec_string] >>
  Cases_on `i = 0` >> gvs[] >>
  `0 < Num i` by intLib.ARITH_TAC >>
  `Num i <= bound - 1` by decide_tac >>
  `LOG 10 (Num i) <= LOG 10 (bound - 1)` by
    (irule logrootTheory.LOG_LE_MONO >> simp[]) >>
  `LOG 10 (bound - 1) = 77` by
    (unabbrev_all_tac >> EVAL_TAC) >>
  decide_tac
QED

Theorem floor_decimal_in_int256_bounds:
  within_int_bound (Signed 168) i ==>
  -(&(2 ** 255)) <= i / 10000000000 /\
  i / 10000000000 < &(2 ** 255)
Proof
  rw[within_int_bound_def] >>
  `10000000000:int <> 0` by intLib.ARITH_TAC >>
  drule INT_DIVISION >>
  disch_then (qspec_then `i` strip_assume_tac) >>
  intLib.ARITH_TAC
QED

Theorem ceil_decimal_in_int256_bounds:
  within_int_bound (Signed 168) i ==>
  -(&(2 ** 255)) <= (i + 9999999999) / 10000000000 /\
  (i + 9999999999) / 10000000000 < &(2 ** 255)
Proof
  rw[within_int_bound_def] >>
  `10000000000:int <> 0` by intLib.ARITH_TAC >>
  drule INT_DIVISION >>
  disch_then (qspec_then `i + 9999999999` strip_assume_tac) >>
  intLib.ARITH_TAC
QED

Theorem low_mask_eq:
  !m. m <= 256 ==>
    ~(~(0w:bytes32) << m) = n2w (2 ** m - 1)
Proof
  rpt strip_tac >>
  rewrite_tac[wordsTheory.WORD_NOT_0, wordsTheory.LSL_UINT_MAX,
              wordsTheory.word_1comp_n2w] >>
  AP_TERM_TAC >>
  rewrite_tac[wordsTheory.dimword_def] >>
  `dimindex(:256) = 256` by EVAL_TAC >>
  asm_rewrite_tac[] >>
  `2 ** m <= 2 ** 256` by (irule (iffRL EXP_BASE_LE_MONO) >> simp[]) >>
  `(2 ** 256 - 2 ** m) MOD 2 ** 256 = 2 ** 256 - 2 ** m` by simp[LESS_MOD] >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem w2n_and_mask_mod:
  !m (w:bytes32). w2n (w && n2w (2 ** m - 1)) = w2n w MOD 2 ** m
Proof
  rpt strip_tac >>
  CONV_TAC (LHS_CONV (RAND_CONV (RATOR_CONV (RAND_CONV
    (REWR_CONV (GSYM wordsTheory.n2w_w2n)))))) >>
  rewrite_tac[wordsTheory.WORD_AND_EXP_SUB1, wordsTheory.w2n_n2w] >>
  irule LESS_MOD >>
  irule LESS_EQ_LESS_TRANS >>
  qexists `w2n w` >>
  simp[MOD_LESS_EQ, wordsTheory.w2n_lt]
QED

Theorem w2n_and_low_mask_lt:
  !m (w:bytes32). m <= 256 ==>
    w2n (w && ~(~0w << m)) < 2 ** m
Proof
  rpt strip_tac >>
  imp_res_tac low_mask_eq >> pop_assum (fn th => rewrite_tac[th]) >>
  simp[w2n_and_mask_mod, MOD_LESS]
QED

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
  strip_tac >> Cases_on `blt` >>
  gvs[well_typed_builtin_app_def, evaluate_builtin_def, AllCaseEqs(), LET_THM,
      LENGTH_EQ_NUM_compute, evaluate_type_def]
  >- (rename1`Not` >> suspend "Not_bool")
  >- (rename1`Not` >> suspend "Not_int")
  >- (rename1`Not` >> suspend "Not_flag")
  >- (rename1`Neg` >> suspend "Neg_int")
  >- (rename1`Neg` >> suspend "Neg_decimal")
  >- suspend "Keccak256"
  >- suspend "Sha256"
  >- suspend "AsWeiValue_int"
  >- suspend "AsWeiValue_decimal"
  >- suspend "Concat_bytes"
  >- suspend "Concat_string"
  >- suspend "Slice_bytes"
  >- suspend "Slice_string"
  >- suspend "Uint2Str"
  >- suspend "MakeArray_tuple"
  >- suspend "MakeArray"
  >- suspend "Ceil"
  >- suspend "Floor"
  >- suspend "AddMod"
  >- suspend "MulMod"
  >- (rename1`Bop` >> suspend "Bop")
  >- suspend "BlockHash"
  >- suspend "BlobHash"
  >- suspend "Env"
  >- suspend "Acc"
  >- suspend "Isqrt"
  >- suspend "MethodId"
  >> TRY (
    rename1`evaluate_ecrecover` >>
    Cases_on`tvs` >> gvs[] >>
    cheat )
  >- suspend "ECAdd"
  >- suspend "ECMul"
  >- suspend "PowMod256"
QED

Resume well_typed_builtin_app_success_type[Bop]:
  TRY(Cases_on`tvs` >> gvs[]) >>
  rename1`evaluate_builtin _ _ _ _ [v1; v2]` >>
  gvs[evaluate_builtin_def] >>
  irule well_typed_binop_success_type >>
  goal_assum (drule_at(Pat`well_typed_binop`)) >>
  goal_assum (drule_at(Pat`evaluate_binop`)) >>
  simp[] >>
  goal_assum drule >> simp[]
QED

Resume well_typed_builtin_app_success_type[Not_bool]:
  rename1`evaluate_builtin _ _ _ _ [v1]` >>
  rename1`is_bool_type bt` >> Cases_on`bt` >>
  Cases_on`v1` >>
  gvs[evaluate_builtin_def, value_has_type_def,
      evaluate_type_def, is_bool_type_def, AllCaseEqs()]
QED

Resume well_typed_builtin_app_success_type[Not_int]:
  rename1`evaluate_builtin _ _ _ _ [v1]` >>
  rename1`is_int_type bt` >> Cases_on`bt` >>
  Cases_on`v1` >>
  gvs[evaluate_builtin_def, evaluate_type_def,
      value_has_type_def, AllCaseEqs(), type_to_int_bound_def] >>
  qmatch_goalsub_abbrev_tac `Num rr < NN` >>
  `0 < NN` by simp[Abbr`NN`] >>
  `Num i <= NN - 1` by simp[] >>
  `i = &Num i` by simp[integerTheory.INT_OF_NUM] >>
  `&(NN - 1) = &NN - 1i` by simp[integerTheory.INT_SUB] >>
  gvs[Abbr`rr`] >>
  conj_tac >- intLib.ARITH_TAC >>
  `0 <= &(NN - 1) - &Num i` by intLib.ARITH_TAC >>
  `Num (&(NN - 1) - i) <= NN - 1` by
    (simp[integerTheory.INT_OF_NUM] >> intLib.ARITH_TAC) >>
  gvs[]
QED

Resume well_typed_builtin_app_success_type[Not_flag]:
  rename1`evaluate_builtin _ _ _ _ [v1]` >>
  rename1`is_flag_type bt` >> Cases_on`bt` >>
  Cases_on`v1` >>
  gvs[evaluate_builtin_def, value_has_type_def, AllCaseEqs(),
      evaluate_type_def] >>
 rewrite_tac[wordsTheory.WORD_NEG_1, GSYM wordsTheory.WORD_NOT_0] >>
 qspec_then `m` (qspec_then `~(n2w n:bytes32)` mp_tac) w2n_and_low_mask_lt >>
 simp[]
QED

Resume well_typed_builtin_app_success_type[Neg_int]:
  rename1`evaluate_builtin _ _ _ _ [v1]` >>
  rename1`is_int_type bt` >> Cases_on`bt` >>
  Cases_on`v1` >>
  gvs[evaluate_builtin_def, value_has_type_def, AllCaseEqs(),
      evaluate_type_def, bounded_int_op_def, type_to_int_bound_def,
      within_int_bound_def ]
QED

Resume well_typed_builtin_app_success_type[Neg_decimal]:
  rename1`evaluate_builtin _ _ _ _ [v1]` >>
  Cases_on`v1` >>
  gvs[evaluate_builtin_def, value_has_type_def, bounded_decimal_op_def]
QED

Resume well_typed_builtin_app_success_type[Keccak256]:
  rename1`evaluate_builtin _ _ _ _ [v1]` >>
  Cases_on`v1` >>
  gvs[evaluate_builtin_def, value_has_type_def, LENGTH_Keccak_256_w64]
QED

Resume well_typed_builtin_app_success_type[Sha256]:
  rename1`evaluate_builtin _ _ _ _ [v1]` >>
  Cases_on`v1` >>
  gvs[evaluate_builtin_def, value_has_type_def, LENGTH_word_to_bytes]
QED

Resume well_typed_builtin_app_success_type[AsWeiValue_int]:
  cheat
QED

Resume well_typed_builtin_app_success_type[AsWeiValue_decimal]:
  cheat
QED

Resume well_typed_builtin_app_success_type[Concat_bytes]:
  cheat
QED

Resume well_typed_builtin_app_success_type[Concat_string]:
  cheat
QED

Resume well_typed_builtin_app_success_type[Slice_bytes]:
  cheat
QED

Resume well_typed_builtin_app_success_type[Slice_string]:
  cheat
QED

Resume well_typed_builtin_app_success_type[Uint2Str]:
  rename1`evaluate_builtin _ _ _ _ [v1]` >>
  Cases_on`v1` >>
  gvs[evaluate_builtin_def, value_has_type_def, type_slot_size_def] >>
  irule LESS_EQ_TRANS >> qexists`78` >> simp[] >>
  irule uint2str_strlen_bound >>
  qexists_tac`BaseTV (UintT 256)` >>
  simp[value_has_type_def, well_formed_type_value_def] >>
  irule LESS_LESS_EQ_TRANS >>
  goal_assum $ drule_at Any >>
  qspecl_then[`k`,`256`]mp_tac bitTheory.TWOEXP_MONO2 >>
  simp[]
QED

Resume well_typed_builtin_app_success_type[MakeArray_tuple]:
  cheat
QED

Resume well_typed_builtin_app_success_type[MakeArray]:
  cheat
QED

Resume well_typed_builtin_app_success_type[Ceil]:
  rename1`evaluate_builtin _ _ _ _ [v1]` >>
  Cases_on`v1` >>
  gvs[evaluate_builtin_def, value_has_type_def] >>
  drule ceil_decimal_in_int256_bounds >>
  gvs[within_int_bound_def] >> rw[] >> gvs[Num_neg] >>
  intLib.ARITH_TAC
QED

Resume well_typed_builtin_app_success_type[Floor]:
  rename1`evaluate_builtin _ _ _ _ [v1]` >>
  Cases_on`v1` >>
  gvs[evaluate_builtin_def, value_has_type_def] >>
  drule floor_decimal_in_int256_bounds >>
  gvs[within_int_bound_def] >> intLib.ARITH_TAC
QED

Resume well_typed_builtin_app_success_type[AddMod]:
  Cases_on `tvs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  rename1`evaluate_builtin _ _ _ _ [v1;v2;v3]` >>
  Cases_on`v1` >> gvs[value_has_type_def] >>
  Cases_on`v2` >> gvs[value_has_type_def] >>
  Cases_on`v3` >> gvs[value_has_type_def] >>
  gvs[evaluate_builtin_def,value_has_type_def] >>
     irule LESS_TRANS >>
     qexists `Num i''` >>
     conj_tac >- (
       irule MOD_LESS >>
       imp_res_tac ratTheory.NUM_NZERO >>
       simp[]
     ) >>
  simp[]
QED

Resume well_typed_builtin_app_success_type[MulMod]:
  Cases_on `tvs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  rename1`evaluate_builtin _ _ _ _ [v1;v2;v3]` >>
  Cases_on`v1` >> gvs[value_has_type_def] >>
  Cases_on`v2` >> gvs[value_has_type_def] >>
  Cases_on`v3` >>
  gvs[evaluate_builtin_def,value_has_type_def] >>
     irule LESS_TRANS >>
     qexists `Num i''` >>
     conj_tac >- (
       irule MOD_LESS >>
       imp_res_tac ratTheory.NUM_NZERO >>
       simp[]
     ) >>
  simp[]
QED

Resume well_typed_builtin_app_success_type[Env]:
  drule_at(Pat`evaluate_builtin`)Env_builtin_success_type >>
  disch_then irule >> simp[] >>
  goal_assum drule
QED

Resume well_typed_builtin_app_success_type[BlockHash]:
  rename1`evaluate_builtin _ _ _ _ [v1]` >>
  Cases_on`v1` >>
  gvs[evaluate_builtin_def, value_has_type_def, evaluate_block_hash_def] >>
  gvs[LENGTH_word_to_bytes, word_to_bytes_be_def]
QED

Resume well_typed_builtin_app_success_type[BlobHash]:
  rename1`evaluate_builtin _ _ _ _ [v1]` >>
  Cases_on`v1` >>
  gvs[evaluate_builtin_def, value_has_type_def, evaluate_blob_hash_def] >>
  gvs[LENGTH_word_to_bytes, word_to_bytes_be_def]
QED

Resume well_typed_builtin_app_success_type[Acc]:
  drule_all Acc_builtin_sound >> simp[] >>
  disch_then(qspec_then`cx`strip_assume_tac) >> gvs[]
QED

Resume well_typed_builtin_app_success_type[Isqrt]:
  rename1`evaluate_builtin _ _ _ _ [v1]` >>
  Cases_on`v1` >>
  gvs[evaluate_builtin_def, value_has_type_def, AllCaseEqs()] >>
  cheat (* num_sqrt bound (but also isn't Isqrt supposed to be gone on main?) *)
QED

Resume well_typed_builtin_app_success_type[MethodId]:
  rename1`evaluate_builtin _ _ _ _ [v1]` >>
  Cases_on`v1` >>
  gvs[evaluate_builtin_def, value_has_type_def,
      LENGTH_TAKE, LENGTH_Keccak_256_w64]
QED

Resume well_typed_builtin_app_success_type[ECAdd]:
  cheat
QED

Resume well_typed_builtin_app_success_type[ECMul]:
  cheat
QED

Resume well_typed_builtin_app_success_type[PowMod256]:
  Cases_on`tvs` >> gvs[] >>
  rename1`evaluate_builtin _ _ _ _ [v1; v2]` >>
  Cases_on`v1` >> Cases_on`v2` >>
  gvs[evaluate_builtin_def, value_has_type_def, within_int_bound_def] >>
  irule modexp_lt >>
  rewrite_tac[bitTheory.ZERO_LT_TWOEXP] >>
  simp[]
QED

Finalise well_typed_builtin_app_success_type

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

