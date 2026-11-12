Theory fmpStageTermSimSelfdestruct
Ancestors
  fmpStageOpBase fmpStageRel ptrStaticDiscipline ptrDiscipline
  o1PassContract frameViewFacts unitShapeDefs passSimulationDefs
  o1LowerDloadRelocationKernel o1LowerDloadShared venomExecSemantics venomState venomInst
  frameRelocationGuardedValues pointerConfinedDefs memLocDefs finite_map pred_set list
  contextCodegenRel vfmState memSafeRun

Theorem selfdestruct_operand_clean[local]:
  i.inst_opcode = SELFDESTRUCT /\
  MEM i (fn_insts f) /\ fn_static_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s /\ MEM op i.inst_operands ==>
  op_prov G op = NONE /\ op_taint tn op = {}
Proof
  strip_tac >>
  `ptr_use_static_ok P (fn_pv P f) i` by
    metis_tac[fn_static_ptr_ok_def] >>
  gvs[ptr_use_static_ok_def, is_pointer_preserving_op_def,
      mem_read_ops_def, mem_write_ops_def, taint_ok_def] >>
  Cases_on `op` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem selfdestruct_operand_transport[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = SELFDESTRUCT /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `fn_static_ptr_ok P fn` by metis_tac[EVERY_MEM] >>
  drule_all fmp_stage_prov_support >> strip_tac >>
  `op_prov G op = NONE /\ op_taint tn op = {}` by
    (irule selfdestruct_operand_clean >> metis_tac[]) >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (rpt gen_tac >> disch_tac >> irule ordinary_operand_not_retpc >>
     conj_tac >- gvs[o1_fn_shape_def, fn_shape_ok_def] >>
     qexists_tac `inst` >> gvs[]) >>
  `inst.inst_opcode <> PHI` by simp[] >>
  drule_all fmp_stage_operand >> strip_tac >>
  gvs[fmp_value_rel_def, ld_value_agree_scalar] >>
  metis_tac[word_agree_except_empty]
QED

Theorem shared_selfdestruct_step[local]:
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
  s.vs_call_ctx = t.vs_call_ctx /\ inst.inst_opcode = SELFDESTRUCT /\
  (!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
          eval_operand op t = SOME x) /\
  step_inst fuel C inst s = Halt s1 ==>
  ?t1. step_inst fuel C' inst t = Halt t1 /\
    ld_shared_agree D s1.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1 /\
    s1.vs_returndata = [] /\ t1.vs_returndata = [] /\
    s1.vs_halted = t1.vs_halted
Proof
  strip_tac >>
  `!a. (s.vs_accounts a).balance = (t.vs_accounts a).balance` by
    (gen_tac >> drule ld_shared_accounts_fields >>
     disch_then (qspec_then `a` (SUBST1_TAC o SYM)) >> simp[]) >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_def] >>
  simp[AllCaseEqs()] >> strip_tac >> fs[] >>
  rename1 `inst.inst_operands = [addr_op]` >>
  `!x. eval_operand addr_op s = SOME x ==> eval_operand addr_op t = SOME x` by
    simp[] >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_def] >> simp[] >>
  gvs[halt_state_def, set_returndata_def, step_taint_def, store_taint_def,
      adopt_reset_def, imm_taint_def, lookup_account_def,
      vfmExecutionTheory.transfer_value_def, update_account_def,
      combinTheory.APPLY_UPDATE_THM] >>
  gvs[ld_shared_agree_def, combinTheory.APPLY_UPDATE_THM] >> rpt strip_tac >>
  rpt IF_CASES_TAC >> gvs[] >>
  simp[combinTheory.APPLY_UPDATE_THM] >> rpt IF_CASES_TAC >> gvs[] >>
  qpat_x_assum `!a. _ with storage := _ = _`
    (qspec_then `a` (SUBST1_TAC o SYM)) >> simp[] >>
  gvs[word_agree_except_def] >> metis_tac[]
QED

Theorem selfdestruct_halt_result[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  inst.inst_opcode = SELFDESTRUCT /\ step_inst fuel C inst s = Halt s1 ==>
  ?t1. step_inst fuel C' inst t = Halt t1 /\
       dead_result_rel D (Halt s1) (Halt t1)
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  `final_taint vs C s1 (step_taint inst s s1 tn) (ret_taint tn inst s)` by
    (simp[final_taint_def] >> metis_tac[]) >>
  `taint_within D C vs` by
    fs[fmp_stage_ctx_def, o1_inv_def, o1_static_inv_def] >>
  `(step_taint inst s s1 tn).t_stor SUBSET
      D.d_stor s1.vs_call_ctx.cc_address
        (s1.vs_accounts s1.vs_call_ctx.cc_address).storage /\
   (step_taint inst s s1 tn).t_trans SUBSET
      D.d_trans s1.vs_call_ctx.cc_address
        (s1.vs_transient s1.vs_call_ctx.cc_address) /\
   (step_taint inst s s1 tn).t_imm SUBSET D.d_imm s1.vs_immutables` by
    (fs[taint_within_def] >> metis_tac[]) >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
   s.vs_call_ctx = t.vs_call_ctx` by
    fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  `!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
          eval_operand op t = SOME x` by
    (rpt strip_tac >> irule selfdestruct_operand_transport >> metis_tac[]) >>
  drule_all shared_selfdestruct_step >>
  disch_then (qspec_then `C'` strip_assume_tac) >>
  qexists_tac `t1` >> simp[] >>
  irule ld_shared_halt_result >> gvs[] >>
  conj_tac >- (qexists_tac `{}` >> simp[]) >>
  qexistsl_tac [`s1.vs_call_ctx.cc_address`, `step_taint inst s s1 tn`] >> simp[]
QED

Theorem fmp_stage_selfdestruct_result:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ inst.inst_opcode = SELFDESTRUCT /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?k' r'. step_inst k' C' inst t = r' /\
    case r of
      OK s1 => s1.vs_halted /\
               ?t1. r' = OK t1 /\ t1.vs_halted /\
                    dead_result_rel D (Halt s1) (Halt t1)
    | Halt se => dead_result_rel D r r'
    | Abort ab se => dead_result_rel D r r'
    | _ => F
Proof
  strip_tac >>
  `~t.vs_halted /\ s.vs_call_ctx = t.vs_call_ctx` by
    fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  Cases_on `?s1. r = Halt s1`
  >- (gvs[] >> metis_tac[selfdestruct_halt_result]) >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[terminates_def, dead_result_rel_def] >>
  `!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
          eval_operand op t = SOME x` by
    (rpt strip_tac >> irule selfdestruct_operand_transport >> metis_tac[]) >>
  `IS_SOME (eval_operands inst.inst_operands t)` by
    (fs[eval_operands_IS_SOME_EVERY, EVERY_MEM] >>
     rpt strip_tac >>
     Cases_on `eval_operand op s` >> fs[] >> metis_tac[optionTheory.IS_SOME_DEF]) >>
  simp[]
QED
