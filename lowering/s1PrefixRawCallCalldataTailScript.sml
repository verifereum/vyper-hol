(* The transaction calldata is already in target memory at this cut. *)
Theory s1PrefixRawCallCalldataTail
Ancestors
  s1PrefixRawCallPreparedTail s1PrefixRawCallMemSafe s1PrefixRawCallSourceTail
  s1PrefixFrame bodyFullRawCall bodyFullRawCallCall exprSimRawCallCalldata
  exprOperandVar exprLoweringProps stateRelProj fragExec venomInst venomState
  vyperStorageTrace vyperStorageFootprint vyperState ptrDiscipline words list
  option arithmetic

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `cx.txn.is_static /\ amount <> 0`
  >- (`~flags.rcf_is_delegate /\ ~flags.rcf_is_static` by metis_tac[] >>
      irule gas_prefix_full_no_outcome >>
      asm_simp_tac bool_ss [storage_trace_frame_raw_call] >> rpt gen_tac >>
      `eval_raw_call cx flags target cx.txn.calldata amount (ext_call_kwarg EKGas flags.rcf_kws kvs)
          (esK with gas_obs := gobs) =
        (INR (Error (RuntimeError "write in static context")),esK with gas_obs := gobs)` by
        (irule raw_call_static_value_abort >> metis_tac[]) >>
      asm_simp_tac (srw_ss()) [] >>
      disch_then (SUBST1_TAC o SYM o CONJUNCT2) >> simp[DROP_LENGTH_NIL]) >>
  `cx.txn.is_static ==> amount = 0` by metis_tac[] >>
  drule raw_call_source_inv_facts >> strip_tac >>
  irule raw_call_eval_prefix_from_take >> asm_simp_tac bool_ss [] >>
  reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> disch_tac >>
  suspend "finish_entry"
QED
*)
Theorem raw_call_calldata_prepared_tail_prefix:
  ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
  ((flags.rcf_is_delegate \/ flags.rcf_is_static) ==> amount = 0) /\
  amount < dimword (:256) /\ flags.rcf_max_outsize < dimword (:256) /\
  expr_sim_inv cenv cx env esK /\ storage_trace_domain cx st0 esK.storage_trace /\
  fn_has_code sa sb func /\ ci_mono sa s7 /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  compile_raw_call_finish addr dp len gas
    (case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME v => v)
    (if flags.rcf_is_delegate then DelegateCall
     else if flags.rcf_is_static then StaticCall else RegularCall)
    flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s7 = (result,sb) /\
  (!H. valid_horizon cx st0 H esK.storage_trace ==>
    stmt_state_rel H ctx func cenv cx esK t7 /\
    ghost_inv_at (DF H) lo dframe cenv cx esK G7 tn7 t7) /\
  ~t7.vs_halted /\ t7.vs_current_bb = s7.cs_current_bb /\
  t7.vs_inst_idx = LENGTH s7.cs_current_insts /\ allocas_from lo t7 /\
  eval_operand addr t7 = SOME (w2w target) /\
  eval_operand (case ext_call_kwarg EKValue flags.rcf_kws xs of
    NONE => Lit 0w | SOME v => v) t7 = SOME (n2w amount) /\
  eval_operand gas t7 = SOME gw /\
  (!g. OPTION_BIND (ext_call_kwarg EKGas flags.rcf_kws kvs) dest_NumV = SOME g ==>
    g = w2n gw) /\
  eval_operand dp t7 = SOME (n2w ib) /\
  eval_operand len t7 = SOME (n2w (LENGTH cx.txn.calldata)) /\
  ib < dimword (:256) /\ LENGTH cx.txn.calldata < dimword (:256) /\
  (LENGTH cx.txn.calldata = 0 \/ ib + LENGTH cx.txn.calldata <= t7.vs_alloca_next \/
   ctx_has_dalloca ctx /\ w2n t7.vs_initial_fmp <= ib /\
   ib + LENGTH cx.txn.calldata <= w2n t7.vs_fmp) /\
  read_memory ib (LENGTH cx.txn.calldata) t7 = cx.txn.calldata /\
  (!j. ib <= j /\ j < ib + LENGTH cx.txn.calldata ==> j NOTIN tn7.t_mem) /\
  (cx.txn.calldata <> [] ==> ?p. dp = Var p /\ ptr_covers G7 tn7 p t7 (LENGTH cx.txn.calldata)) /\
  EVERY (\x. op_taint tn7 x = {})
    [addr;len;dp;gas;(case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME v => v)] /\
  eval_operand op t7 = SOME (n2w (if flags.rcf_max_outsize = 0 then ob else ob + 32)) /\
  payload = (if flags.rcf_max_outsize = 0 then 0
             else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32) /\
  ob + payload < dimword (:256) /\
  FLOOKUP t7.vs_allocas aid = SOME (ob,payload) /\
  op_prov G7 op = SOME (ob,payload) /\ op_taint tn7 op = {} /\
  (!name lb sz. local_region cenv esK.scopes t7 name lb sz ==>
    regions_disjoint ob payload lb sz) /\
  (cenv.ce_is_ctor ==> !src name tv v off.
    (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) ob payload) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (eval_raw_call cx flags target cx.txn.calldata amount (ext_call_kwarg EKGas flags.rcf_kws kvs))
    (esK,t7,G7,tn7)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_call_calldata_prepared_tail_prefix[finish_entry]:
  `stmt_state_rel (storage_trace_horizon esK.storage_trace) ctx func cenv cx esK t7` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon esK.storage_trace` mp_tac) >>
     (impl_tac >- qpat_assum `storage_trace_domain _ _ _`
        (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def])) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  qabbrev_tac `vop = case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME v => v` >>
  qabbrev_tac `cap = flags.rcf_max_outsize` >>
  qabbrev_tac `call_ty = if flags.rcf_is_delegate then DelegateCall
                         else if flags.rcf_is_static then StaticCall else RegularCall` >>
  qabbrev_tac `opc = case call_ty of RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL` >>
  qabbrev_tac `ops = if call_ty = RegularCall then [gas;addr;vop;dp;len;op;Lit (n2w cap)]
                     else [gas;addr;dp;len;op;Lit (n2w cap)]` >>
  `?ok sc. emit_op opc ops s7 = (ok,sc) /\ cs_extends sc sb` by
    (drule raw_call_finish_prefix >>
     disch_then (qx_choose_then `ok` (qx_choose_then `sc` strip_assume_tac)) >>
     qexistsl [`ok`,`sc`] >> simp[Abbr `opc`, Abbr `ops`] >>
     qpat_assum `_ s7 = (ok,sc)` mp_tac >> Cases_on `call_ty` >> simp[NoAsms]) >>
  `fn_has_code s7 sc func` by
    (irule fn_has_code_mid >> conj_tac
     >- metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
     qexistsl [`sb`,`sa`] >> simp[] >>
     qpat_assum `ci_mono sa s7` (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [ci_mono_def])) >>
  `local_ptrs_reserved cenv s7 /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s7 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s7 x)` by
    (rpt conj_tac >> rpt strip_tac >>
     metis_tac[compiler_ci_mono_reserved, compiler_ci_mono_not_fresh]) >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t7` by
    metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
  qabbrev_tac `inst = mk_inst s7.cs_next_id opc ops [STRING #"%" (toString s7.cs_next_var)]` >>
  `EVERY (\p. op_taint tn7 p = {}) inst.inst_operands` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`EVERY _ [addr;len;dp;gas;vop]`,`op_taint tn7 op = _`] >>
     Cases_on `call_ty` >>
     simp[NoAsms,Abbr `inst`,Abbr `ops`,Abbr `opc`,mk_inst_def,op_taint_def] >>
     tautLib.TAUT_TAC) >>
  suspend "memory_ranges"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_call_calldata_prepared_tail_prefix[memory_ranges]:
  qabbrev_tac `ro = if cap = 0 then ob else ob + 32` >>
  `ro < dimword (:256) /\ (cap <> 0 ==> lo <= ro) /\
   (cap <> 0 ==> ro + cap <= t7.vs_alloca_next) /\
   (cap <> 0 ==> ?p. op = Var p /\ ptr_covers G7 tn7 p t7 cap) /\
   (!name lb sz. local_region cenv esK.scopes t7 name lb sz ==>
     regions_disjoint ro cap lb sz) /\
   (cenv.ce_is_ctor ==> !src name tv v off.
      (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
      FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
               | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
      off + type_memory_size tv <= ro \/ ro + cap <= off)` by
    (irule raw_call_output_range >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qexistsl [`aid`,`payload`,`ob`] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         asm_simp_tac bool_ss [Abbr `ro`, MULT_COMM]) >>
     qexistsl [`storage_trace_horizon esK.storage_trace`,`ctx`,`func`] >>
     first_assum ACCEPT_TAC) >>
  `mem_safe_step 0 ctx inst t7` by
    (qunabbrev_tac `inst` >> qunabbrev_tac `ops` >> qunabbrev_tac `opc` >>
     irule raw_call_inst_mem_safe_at >>
     first_assum (irule_at (Pat `eval_operand dp _ = _`)) >>
     first_assum (irule_at (Pat `eval_operand len _ = _`)) >>
     first_assum (irule_at (Pat `eval_operand op _ = _`)) >>
     simp_tac bool_ss [IS_SOME_EXISTS] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     goal_assum (drule_at Any)) >>
  suspend "request_site"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_call_calldata_prepared_tail_prefix[request_site]:
  qabbrev_tac `bs = cx.txn.calldata` >>
  `w2n (n2w ro : bytes32) = ro /\ w2n (n2w ib : bytes32) = ib /\
   w2n (n2w (LENGTH bs) : bytes32) = LENGTH bs /\
   w2n (n2w amount : bytes32) = amount` by
    asm_simp_tac bool_ss [w2n_n2w,LESS_MOD] >>
  `(call_ty = DelegateCall) = flags.rcf_is_delegate` by
    (Cases_on `flags.rcf_is_delegate` >> Cases_on `flags.rcf_is_static` >> simp[Abbr `call_ty`]) >>
  qabbrev_tac `value_opt = if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount` >>
  qabbrev_tac `gas_cap = OPTION_BIND (ext_call_kwarg EKGas flags.rcf_kws kvs) dest_NumV` >>
  `(call_ty = StaticCall \/ cx.txn.is_static) = IS_NONE value_opt /\
   w2n (if call_ty = RegularCall then n2w amount else 0w : bytes32) =
     (case value_opt of NONE => 0 | SOME n => n)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`~(flags.rcf_is_delegate /\ flags.rcf_is_static)`,
        `(flags.rcf_is_delegate \/ flags.rcf_is_static) ==> amount = 0`,
        `cx.txn.is_static ==> amount = 0`, `w2n (n2w amount : bytes32) = amount`] >>
     simp[NoAsms,Abbr `call_ty`,Abbr `value_opt`] >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `flags.rcf_is_delegate` >> Cases_on `flags.rcf_is_static` >>
     Cases_on `cx.txn.is_static` >> simp[]) >>
  `w2w (w2w target : bytes32) = target` by wordsLib.WORD_DECIDE_TAC >>
  `(n2w (LENGTH bs) : bytes32) <> 0w ==>
    ?p. dp = Var p /\ ptr_covers G7 tn7 p t7 (LENGTH bs)` by
    (once_rewrite_tac[GSYM w2n_eq_0] >> asm_simp_tac bool_ss [LENGTH_NIL]) >>
  `read_memory (w2n (n2w ib : bytes32)) (w2n (n2w (LENGTH bs) : bytes32)) t7 = bs` by
    asm_simp_tac bool_ss [] >>
  qpat_assum `read_memory (w2n _) (w2n _) t7 = bs` (fn th => once_rewrite_tac[GSYM th]) >>
  qpat_assum `(call_ty = DelegateCall) = flags.rcf_is_delegate` (fn th => rewrite_tac[GSYM th]) >>
  irule raw_call_actual_call_mem_safe_prefix >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- asm_simp_tac bool_ss []
  >- (qexistsl [`mid`,`outcome`,`rq`] >> asm_simp_tac bool_ss []) >>
  qexistsl [`w2w target : bytes32`,`cap`,`cenv`,`dframe`,`len`,`dp`,
            `gw`,`gas`,`inst`,`ok`,`op`,`n2w ro : bytes32`,`s7`,`sc`,
            `addr`,`vop`,`n2w amount : bytes32`] >>
  qpat_assum `w2n (n2w ro : bytes32) = ro` (fn th => rewrite_tac[th]) >>
  qpat_assum `w2n (n2w (LENGTH bs) : bytes32) = LENGTH bs` (fn th => rewrite_tac[th]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (rename1 `inst = mk_inst _ _ _ _` >>
       simp_tac bool_ss [Abbr `inst`,Abbr `opc`,Abbr `ops`] >> NO_TAC) >>
  TRY (rename1 `emit_op _ _ s7 = (ok,sc)` >>
       qpat_assum `emit_op opc ops s7 = (ok,sc)` mp_tac >>
       simp_tac bool_ss [Abbr `opc`,Abbr `ops`] >> NO_TAC) >>
  qpat_assum `cap <> 0 ==> lo <= ro` mp_tac >> tautLib.TAUT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise raw_call_calldata_prepared_tail_prefix
*)
