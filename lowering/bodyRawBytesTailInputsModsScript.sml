(* Decode the reached byte-expression request before generated GAS/outbuf. *)
Theory bodyRawBytesTailInputsMods
Ancestors
  bodyFullRawCallRequestGas exprSimRawCall exprSimSend exprSimPrecompiles
  exprSafeOperand allocLimits compileEnv loweringPosts ptrDiscipline
  vyperTypeExtCallSoundness vyperTypeSystem vyperInterpreter vyperValue
  valueEncoding words list arithmetic vyperTyping venomMemProps vyperState
  loweringStateRelDefs venomState
Libs monadsyntax

Triviality bytes_tail_address:
  value_has_type (BaseTV AddressT) av /\
  expr_val_rel cx (BaseT AddressT) av addr tk ==>
  ?target. dest_AddressV av = SOME target /\
    eval_operand addr tk = SOME (w2w target)
Proof
  Cases_on `av` >> simp[value_has_type_def,dest_AddressV_def] >>
  strip_tac >> fs[expr_val_rel_def,evaluate_type_def,is_word_type_def] >>
  simp[typed_val_to_w256_def] >>
  qspec_then `l` mp_tac
    (INST_TYPE [alpha |-> ``:160``, beta |-> ``:256``]
      w2w_word_of_bytes_be_pad_left) >>
  simp[dividesTheory.compute_divides,fcpLib.INDEX_CONV ``dimindex(:160)``,EQ_SYM_EQ]
QED

Triviality bytes_tail_uint_words:
  EVERY (\e. expr_type e = BaseT (UintT 256)) kws /\
  LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                      value_has_type tv v) kws kvs /\
  typed_args_post H ctx func cenv cx esD s4 t4 esK kws xs kvs tk ==>
  LENGTH kvs = LENGTH kws /\
  EVERY (value_has_type (BaseTV (UintT 256))) kvs /\
  LIST_REL (\x v. eval_operand x tk = SOME
    (typed_val_to_w256 (BaseTV (UintT 256)) v)) xs kvs
Proof
  simp[typed_args_post_def] >> strip_tac >> simp[] >> conj_tac
  >- (fs[EVERY_EL,LIST_REL_EL_EQN] >> rpt strip_tac >>
      `expr_type (EL n kws) = BaseT (UintT 256)` by simp[] >>
      qpat_assum `!j. _ ==> ?tv. evaluate_type _ _ = SOME tv /\ _`
        (qspec_then `n` mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >> gvs[evaluate_type_def]) >>
  fs[EVERY_EL,LIST_REL_EL_EQN,LENGTH_ZIP] >> rpt strip_tac >>
  `n < LENGTH kws /\ n < LENGTH kvs /\ n < LENGTH xs` by gvs[] >>
  `expr_type (EL n kws) = BaseT (UintT 256)` by fs[] >>
  qpat_assum `!j. _ ==> eval_operand _ _ = _` (qspec_then `n` mp_tac) >>
  (impl_tac >- simp[]) >> disch_tac >> fs[EL_ZIP,evaluate_type_def]
QED

Triviality bytes_tail_absent_gas:
  !ks xs vs. LENGTH xs = LENGTH vs /\ ext_call_kwarg EKGas ks vs = NONE ==>
    ext_call_kwarg EKGas ks xs = NONE
Proof
  Induct >> Cases_on `xs` >> Cases_on `vs` >> simp[ext_call_kwarg_def] >>
  rpt strip_tac >> first_x_assum irule >> goal_assum drule >> gvs[AllCaseEqs()]
QED

Triviality bytes_tail_gas:
  LIST_REL (\x v. eval_operand x tk = SOME
    (typed_val_to_w256 (BaseTV (UintT 256)) v)) xs kvs /\
  EVERY (value_has_type (BaseTV (UintT 256))) kvs /\
  EVERY (\x. op_taint tnK x = {}) xs /\
  go = ext_call_kwarg EKGas ks xs ==>
  (case ext_call_kwarg EKGas ks kvs of NONE => go = NONE
   | SOME gv => ?opr w. go = SOME opr /\ eval_operand opr tk = SOME w /\
       dest_NumV gv = SOME (w2n w) /\ op_taint tnK opr = {})
Proof
  strip_tac >> Cases_on `ext_call_kwarg EKGas ks kvs` >> simp[]
  >- metis_tac[bytes_tail_absent_gas,LIST_REL_LENGTH] >>
  `LIST_REL (\op v. ?w. eval_operand op tk = SOME w /\
       dest_NumV v = SOME (w2n w)) xs kvs` by
    (fs[LIST_REL_EL_EQN,EVERY_EL] >> rpt strip_tac >> simp[uint256_typed_dest]) >>
  drule_all raw_call_selected_gas_word >> strip_tac >> gvs[] >>
  drule raw_call_kwarg_mem >> fs[EVERY_MEM]
QED

Triviality bytes_tail_payload_bound:
  type_alloc_ok cenv (raw_call_return_type flags) ==>
  (if flags.rcf_max_outsize = 0 then 0
   else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32) < dimword (:256)
Proof
  Cases_on `flags.rcf_max_outsize = 0` >> simp[] >>
  Cases_on `flags.rcf_revert_on_failure` >>
  simp[raw_call_return_type_def,type_alloc_ok_def,is_word_type_def,type_memory_bytes_def] >>
  qabbrev_tac `rounded = 32 * ((flags.rcf_max_outsize + 31) DIV 32)` >>
  strip_tac >> irule LESS_TRANS >> qexists_tac `2 ** 64` >>
  simp[dimword_def] >> decide_tac
QED

Triviality bytes_tail_restricted_amount:
  raw_call_kws_ok flags kws /\ raw_call_value flags.rcf_kws kvs = SOME amount ==>
  (flags.rcf_is_delegate \/ flags.rcf_is_static ==> amount = 0)
Proof
  strip_tac >> strip_tac >> fs[raw_call_kws_ok_def,raw_call_value_def] >>
  `ext_call_kwarg EKValue flags.rcf_kws kvs = NONE` by
    (irule ext_call_kwarg_not_mem >> simp[]) >> fs[]
QED

val checked_bytes_tail = ``\cx flags av dv kvs. do
  type_check (LENGTH (av::dv::kvs) = 2 + LENGTH flags.rcf_kws) "raw_call args";
  target <- lift_option_type (dest_AddressV av) "raw_call target";
  data <- lift_option_type (dest_BytesV dv) "raw_call data";
  amount <- lift_option_type (raw_call_value flags.rcf_kws kvs) "raw_call value";
  eval_raw_call cx flags target data amount (ext_call_kwarg EKGas flags.rcf_kws kvs)
  od``;

Triviality bytes_tail_checks:
  LENGTH kvs = LENGTH flags.rcf_kws /\ dest_AddressV av = SOME target /\
  raw_call_value flags.rcf_kws kvs = SOME amount ==>
  (^checked_bytes_tail) cx flags av (BytesV bs) kvs =
  eval_raw_call cx flags target bs amount (ext_call_kwarg EKGas flags.rcf_kws kvs)
Proof
  strip_tac >> simp[dest_BytesV_def,type_check_def,lift_option_type_def,ignore_bind_def,
    assert_def,FUN_EQ_THM,bind_def,return_def]
QED

val value_operand = ``case vo of NONE => Lit 0w | SOME p => p``;

Theorem raw_bytes_reached_tail_inputs_mods:
  LENGTH kws = LENGTH flags.rcf_kws /\ raw_call_kws_ok flags kws /\
  EVERY (\e. expr_type e = BaseT (UintT 256)) kws /\
  type_alloc_ok cenv (raw_call_return_type flags) /\
  value_has_type (BaseTV AddressT) av /\ expr_val_rel cx (BaseT AddressT) av addr tk /\
  typed_args_post H ctx func cenv cx esD s4 t4 esK kws xs kvs tk /\
  LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                      value_has_type tv v) kws kvs /\
  EVERY (\p. op_prov GK p = NONE /\ op_taint tnK p = {}) xs /\
  EVERY (\op. (!l. op <> Label l) /\ (!z. op = Var z ==> not_fresh_at s5 z)) xs /\
  vo = ext_call_kwarg EKValue flags.rcf_kws xs /\ go = ext_call_kwarg EKGas flags.rcf_kws xs ==>
  ?target amount.
    dest_AddressV av = SOME target /\ raw_call_value flags.rcf_kws kvs = SOME amount /\
    eval_operand addr tk = SOME (w2w target) /\
    eval_operand ^value_operand tk = SOME (n2w amount) /\
    safe_operand s5 ^value_operand /\ op_taint tnK ^value_operand = {} /\
    amount < dimword (:256) /\ (flags.rcf_is_delegate ==> amount = 0) /\
    (flags.rcf_is_static ==> amount = 0) /\
    (case ext_call_kwarg EKGas flags.rcf_kws kvs of NONE => go = NONE
     | SOME gv => ?opr w. go = SOME opr /\ eval_operand opr tk = SOME w /\
          dest_NumV gv = SOME (w2n w) /\ op_taint tnK opr = {}) /\
    (!x. go = SOME (Var x) ==> not_fresh_at s5 x) /\
    (if flags.rcf_max_outsize = 0 then 0
     else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32) < dimword (:256) /\
    (^checked_bytes_tail) cx flags av (BytesV bs) kvs =
      eval_raw_call cx flags target bs amount (ext_call_kwarg EKGas flags.rcf_kws kvs)
Proof
  strip_tac >> drule_all_then strip_assume_tac bytes_tail_address >>
  drule_all_then strip_assume_tac bytes_tail_uint_words >>
  drule_all raw_call_value_operand >> disch_then (qspec_then `flags.rcf_kws` strip_assume_tac) >>
  `EVERY (safe_operand s5) xs` by (fs[EVERY_MEM,safe_operand_def] >> metis_tac[]) >>
  `EVERY (\p. op_taint tnK p = {}) xs` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `safe_operand s5 ^value_operand /\ op_taint tnK ^value_operand = {}` by
    (Cases_on `vo` >- simp[safe_operand_def,op_taint_def] >>
     rename1 `SOME p = ext_call_kwarg EKValue _ xs` >>
     `MEM p xs` by metis_tac[raw_call_kwarg_mem] >> fs[EVERY_MEM]) >>
  `!x. go = SOME (Var x) ==> not_fresh_at s5 x` by
    (rpt strip_tac >> `MEM (Var x) xs` by metis_tac[raw_call_kwarg_mem] >>
     fs[EVERY_MEM,safe_operand_def]) >>
  drule_all_then assume_tac bytes_tail_gas >>
  drule_then assume_tac bytes_tail_payload_bound >>
  `flags.rcf_is_delegate \/ flags.rcf_is_static ==> amount = 0` by
    (disch_tac >> irule bytes_tail_restricted_amount >>
     qexistsl_tac [`flags`,`kvs`,`kws`] >> simp[]) >>
  `(^checked_bytes_tail) cx flags av (BytesV bs) kvs =
     eval_raw_call cx flags target bs amount (ext_call_kwarg EKGas flags.rcf_kws kvs)` by
    (BETA_TAC >> irule (BETA_RULE bytes_tail_checks) >> simp[]) >>
  qexistsl_tac [`target`,`amount`] >> gvs[]
QED
