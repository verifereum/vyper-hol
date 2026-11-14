Theory readonlyInvokeCopyFwdStepsControl
Ancestors
  readonlyInvokeCopyFwdStepsCore readonlyInvokeCopyFwdEffects
  readonlyInvokeCopyFwdValues readonlyInvokeCopyFwdRel taintAgree
  venomState venomExecSemantics internalReturnCopyFwdSim o1LowerDloadShared
  finite_map words list pred_set

Theorem ricf_cert_jump_to:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t ==>
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (jump_to lbl s) G0)
    (ricf_effective_taint fn (jump_to lbl s) tn0) fn
    sites maps targets G0 tn0 cur curs (jump_to lbl s) (jump_to lbl t)
Proof
  strip_tac >> irule ricf_cert_reconstruct >>
  fs[ricf_cert_core_def, ricf_live_boundary_core_def] >>
  conj_tac >- (gvs[ircf_cross_def, jump_to_def] >> metis_tac[]) >>
  conj_tac >- (gvs[ricf_cert_crosses_def, ircf_cross_def, jump_to_def] >> metis_tac[]) >>
  conj_tac
  >- (gvs[ricf_frame_agree_def, taint_agree_def, jump_to_def,
          ircf_dead_def, ircf_cross_def, ld_shared_agree_def,
          venom_state_component_equality] >> metis_tac[]) >>
  gvs[ricf_live_stack_agree_def, merge_callee_state_def, jump_to_def]
QED

Theorem ricf_cert_return_boundary:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t ==>
  ricf_cert_return_core D ids stk maps targets curs tn0 s t /\
  ircf_cross tn0 cur s t
Proof
  simp[ricf_cert_core_def, ricf_live_boundary_core_def,
       ricf_cert_return_core_def, ricf_live_return_core_def] >>
  rpt strip_tac >>
  gvs[ricf_frame_agree_def, taint_agree_def, ld_shared_agree_def,
      venom_state_component_equality]
QED

(* Aborted states are intentionally not compared; return values must agree
   as scalars, not as relocated addresses. *)
Definition ricf_control_result_def:
  ricf_control_result D ids stk PG fn sites maps targets H un cur curs r r' <=>
    case r of
      OK u => ?v. r' = OK v /\
        ricf_cert_core D ids stk PG
          (ricf_effective_prov fn u H) (ricf_effective_taint fn u un) fn
          sites maps targets H un cur curs u v
    | Error e => r' = Error e
    | Abort reason u => ?v. r' = Abort reason v
    | Halt u => ?v. r' = Halt v /\
        ricf_cert_return_core D ids stk maps targets curs un u v /\
        ircf_cross un cur u v
    | IntRet ret u => ?v. r' = IntRet ret v /\
        ricf_cert_return_core D ids stk maps targets curs un u v /\
        ircf_cross un cur u v
End

Theorem ricf_cert_control_identity:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t ==>
  ricf_control_result D ids stk PG fn sites maps targets G0 tn0 cur curs
    (OK s) (OK t)
Proof
  simp[ricf_control_result_def, ricf_cert_core_def,
       ricf_live_boundary_core_def, ricf_effective_prov_def,
       ricf_effective_taint_def]
QED

Theorem ricf_cert_control_jump:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t ==>
  ricf_control_result D ids stk PG fn sites maps targets G0 tn0 cur curs
    (OK (jump_to lbl s)) (OK (jump_to lbl t))
Proof
  simp[ricf_control_result_def] >> metis_tac[ricf_cert_jump_to]
QED

Theorem ricf_cert_assert:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) /\
  MEM inst.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE; INVALID; PHI] ==>
  ricf_control_result D ids stk PG fn sites maps targets G0 tn0 cur curs
    (step_inst_base inst s) (step_inst_base inst t)
Proof
  strip_tac >> drule ricf_cert_control_identity >>
  simp[ricf_control_result_def] >> strip_tac >>
  fs[MEM] >> simp[step_inst_base_opcode_eqs, ricf_control_result_def] >>
  namedCases_on `inst.inst_operands` ["", "a ops"] >>
  gvs[ricf_control_result_def] >> Cases_on `ops` >>
  gvs[ricf_control_result_def, MEM] >>
  Cases_on `eval_operand a t` >> gvs[ricf_control_result_def] >>
  IF_CASES_TAC >> simp[ricf_control_result_def] >>
  metis_tac[ricf_cert_control_identity, ricf_control_result_def]
QED

Theorem ricf_cert_jmp:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_opcode = JMP ==>
  ricf_control_result D ids stk PG fn sites maps targets G0 tn0 cur curs
    (step_inst_base inst s) (step_inst_base inst t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `inst.inst_operands` ["", "a ops"] >>
  gvs[ricf_control_result_def] >> Cases_on `a` >>
  gvs[ricf_control_result_def] >> Cases_on `ops` >>
  simp[ricf_control_result_def] >> metis_tac[ricf_cert_jump_to]
QED

Theorem ricf_cert_djmp:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_opcode = DJMP /\
  (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  ricf_control_result D ids stk PG fn sites maps targets G0 tn0 cur curs
    (step_inst_base inst s) (step_inst_base inst t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `inst.inst_operands` ["", "a ops"] >>
  gvs[ricf_control_result_def, MEM] >>
  Cases_on `eval_operand a t` >> gvs[ricf_control_result_def] >>
  Cases_on `extract_labels ops` >> gvs[ricf_control_result_def] >>
  IF_CASES_TAC >> simp[ricf_control_result_def] >> metis_tac[ricf_cert_jump_to]
QED

Theorem ricf_cert_jnz:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_opcode = JNZ /\
  (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  ricf_control_result D ids stk PG fn sites maps targets G0 tn0 cur curs
    (step_inst_base inst s) (step_inst_base inst t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `inst.inst_operands` ["", "a ops"] >>
  gvs[ricf_control_result_def] >>
  namedCases_on `ops` ["", "b rest"] >> gvs[ricf_control_result_def] >>
  Cases_on `b` >> gvs[ricf_control_result_def] >>
  namedCases_on `rest` ["", "c tail"] >> gvs[ricf_control_result_def] >>
  Cases_on `c` >> gvs[ricf_control_result_def] >>
  Cases_on `tail` >> gvs[ricf_control_result_def, MEM] >>
  Cases_on `eval_operand a t` >> gvs[ricf_control_result_def] >>
  IF_CASES_TAC >> simp[ricf_control_result_def] >> metis_tac[ricf_cert_jump_to]
QED

Theorem ricf_cert_ret:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  MEM inst.inst_opcode [RET; RETFMP] /\
  eval_operands inst.inst_operands s = eval_operands inst.inst_operands t ==>
  ricf_control_result D ids stk PG fn sites maps targets G0 tn0 cur curs
    (step_inst_base inst s) (step_inst_base inst t)
Proof
  strip_tac >>
  `s.vs_fmp = t.vs_fmp` by
    gvs[ricf_cert_core_def, ricf_live_boundary_core_def, ricf_frame_agree_def,
        taint_agree_def, venom_state_component_equality] >>
  drule ricf_cert_return_boundary >> strip_tac >>
  fs[MEM] >> simp[step_inst_base_opcode_eqs] >>
  Cases_on `eval_operands inst.inst_operands t` >>
  gvs[ricf_control_result_def] >> Cases_on `x` >>
  simp[ricf_control_result_def]
QED

Theorem ricf_cert_revert:
  inst.inst_opcode = REVERT /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) ==>
  ricf_control_result D ids stk PG fn sites maps targets G0 tn0 cur curs
    (step_inst_base inst s) (step_inst_base inst t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `inst.inst_operands` ["", "a ops"] >>
  gvs[ricf_control_result_def] >>
  namedCases_on `ops` ["", "b tail"] >> gvs[ricf_control_result_def] >>
  Cases_on `tail` >> gvs[ricf_control_result_def, MEM] >>
  Cases_on `eval_operand a s` >> Cases_on `eval_operand a t` >>
  gvs[ricf_control_result_def] >>
  Cases_on `eval_operand b s` >> Cases_on `eval_operand b t` >>
  gvs[ricf_control_result_def] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_cert_halt_boundary:
  ricf_cert_return_core D ids stk maps targets curs un s t /\
  ircf_cross un cur s t ==>
  ricf_cert_return_core D ids stk maps targets curs un
    (halt_state (set_returndata rd s)) (halt_state (set_returndata rd t)) /\
  ircf_cross un cur (halt_state (set_returndata rd s))
    (halt_state (set_returndata rd t))
Proof
  simp[ricf_cert_return_core_def, ricf_live_return_core_def,
       ricf_live_stack_agree_def, ricf_live_frame_decompose,
       halt_state_def, set_returndata_def, ld_shared_agree_def,
       ircf_cross_def, ricf_cert_crosses_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ricf_cert_stop:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_opcode = STOP ==>
  ricf_control_result D ids stk PG fn sites maps targets G0 tn0 cur curs
    (step_inst_base inst s) (step_inst_base inst t)
Proof
  strip_tac >> drule ricf_cert_return_boundary >> strip_tac >>
  drule_all ricf_cert_halt_boundary >>
  disch_then (qspec_then `[]` assume_tac) >>
  gvs[step_inst_base_opcode_eqs, ricf_control_result_def, set_returndata_def]
QED

Theorem ricf_cert_return:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_opcode = RETURN /\ inst.inst_operands = [a;b] /\
  eval_operand a s = SOME off /\ eval_operand a t = SOME off' /\
  eval_operand b s = SOME sz /\ eval_operand b t = SOME sz' /\
  TAKE (w2n sz) (DROP (w2n off) s.vs_memory ++ REPLICATE (w2n sz) 0w) = rd /\
  TAKE (w2n sz') (DROP (w2n off') t.vs_memory ++ REPLICATE (w2n sz') 0w) = rd ==>
  ricf_control_result D ids stk PG fn sites maps targets G0 tn0 cur curs
    (step_inst_base inst s) (step_inst_base inst t)
Proof
  strip_tac >> drule ricf_cert_return_boundary >> strip_tac >>
  drule_all ricf_cert_halt_boundary >>
  disch_then (qspec_then `rd` assume_tac) >>
  gvs[step_inst_base_opcode_eqs, ricf_control_result_def]
QED

Theorem ricf_cert_sink:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_opcode = SINK ==>
  ricf_control_result D ids stk PG fn sites maps targets G0 tn0 cur curs
    (step_inst_base inst s) (step_inst_base inst t)
Proof
  strip_tac >> drule ricf_cert_return_boundary >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, ricf_control_result_def,
      ricf_cert_return_core_def, ricf_live_return_core_def,
      ricf_live_stack_agree_def, ricf_live_frame_decompose,
      halt_state_def, ld_shared_agree_def, ircf_cross_def,
      ricf_cert_crosses_def] >> metis_tac[]
QED

(* These error adapters do not equate pointer values.  Availability in the
   source and target is enough, including evaluation failure with a well
   formed operand/output envelope. *)
Theorem ricf_pure1_error:
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  exec_pure1 f inst s = Error e ==> exec_pure1 g inst t = Error e
Proof
  strip_tac >>
  gvs[exec_pure1_def, AllCaseEqs()] >>
  Cases_on `eval_operand op1 t` >> gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_pure2_error:
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  exec_pure2 f inst s = Error e ==> exec_pure2 g inst t = Error e
Proof
  strip_tac >>
  gvs[exec_pure2_def, AllCaseEqs()] >>
  Cases_on `eval_operand op1 t` >> Cases_on `eval_operand op2 t` >>
  gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED
Theorem ricf_pure3_error:
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  exec_pure3 f inst s = Error e ==> exec_pure3 g inst t = Error e
Proof
  strip_tac >>
  gvs[exec_pure3_def, AllCaseEqs()] >>
  Cases_on `eval_operand op1 t` >> Cases_on `eval_operand op2 t` >>
  Cases_on `eval_operand op3 t` >>
  gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED
Theorem ricf_read0_error:
  exec_read0 f inst s = Error e ==> exec_read0 g inst t = Error e
Proof
  gvs[exec_read0_def, AllCaseEqs()]
QED

Theorem ricf_read1_error:
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  exec_read1 f inst s = Error e ==> exec_read1 g inst t = Error e
Proof
  strip_tac >>
  gvs[exec_read1_def, AllCaseEqs()] >>
  Cases_on `eval_operand op1 t` >> gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_write2_error:
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  exec_write2 f inst s = Error e ==> exec_write2 g inst t = Error e
Proof
  strip_tac >>
  gvs[exec_write2_def, AllCaseEqs()] >>
  Cases_on `eval_operand op1 t` >> Cases_on `eval_operand op2 t` >>
  gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED
