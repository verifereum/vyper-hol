Theory fmpStageTermSimBasic
Ancestors
  fmpStageOpBase fmpStageRel ptrDiscipline o1PassContract
  o1LowerDloadShared contextCodegenRel venomExecSemantics venomState venomInst
  pred_set list pointerConfinedDefs memLocDefs unitShapeDefs passSimulationDefs

Theorem basic_stop_sink[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  (inst.inst_opcode = STOP \/ inst.inst_opcode = SINK) /\
  step_inst fuel C inst s = Halt s1 ==>
  ?t1. step_inst fuel C' inst t = Halt t1 /\
       dead_result_rel D (Halt s1) (Halt t1)
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
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
   s.vs_returndata = t.vs_returndata` by fs[fmp_stage_rel_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >> strip_tac >> gvs[] >>
  (simp[step_inst_non_invoke] >>
   asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
   irule (Q.INST [`A` |-> `s.vs_call_ctx.cc_address`,
                  `tn` |-> `tn`, `R` |-> `{}`] ld_shared_halt_result) >>
   gvs[halt_state_def, set_returndata_def, step_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, ret_taint_def, ld_shared_agree_def] >>
   qexists_tac `tn` >> simp[])
QED

Theorem basic_revert_operand[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  inst.inst_opcode = REVERT /\ MEM op inst.inst_operands /\
  eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (rpt strip_tac >>
     `opaque_use_ok fn` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
     gvs[] >> drule_all opaque_use_ok_retpc_use >> simp[retpc_use_ok_def]) >>
  `inst.inst_opcode <> PHI` by simp[] >>
  metis_tac[fmp_stage_operand]
QED

Theorem fmp_stage_basic_result:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ MEM inst.inst_opcode [STOP; SINK; REVERT; INVALID] /\
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
  `~t.vs_halted` by fs[fmp_stage_rel_def] >>
  Cases_on `inst.inst_opcode = STOP \/ inst.inst_opcode = SINK`
  >- (`?s1. r = Halt s1` by
        (fs[] >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
         simp[step_inst_non_invoke] >>
         asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
         metis_tac[]) >>
      gvs[] >> metis_tac[basic_stop_sink]) >>
  `inst.inst_opcode = REVERT ==>
   !op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
     ?y. eval_operand op t = SOME y` by
    (rpt strip_tac >> irule basic_revert_operand >> metis_tac[]) >>
  fs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[terminates_def] >>
  simp[dead_result_rel_def, AllCaseEqs()] >>
  `?a. eval_operand off_op t = SOME a` by metis_tac[] >>
  `?b. eval_operand sz_op t = SOME b` by metis_tac[] >>
  simp[]
QED
