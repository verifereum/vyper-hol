(*
 * FmpLowering's coverage (fmpStageCoverage) across blocks and frames: the
 * invariant fmp_cov is kept by a jump into a block (fmp_stage_jump_step,
 * fmp_stage_block_entry), a call (fmp_stage_invoke_call) and a return
 * (fmp_stage_invoke_return), each on the source step fmpStageCoverBack
 * and fmpStageCoverCall give.  A halting terminator takes no block step:
 * its source counterpart halts too (fmp_stage_halt_step).
 *
 * TOP-LEVEL:
 *   fmp_cov_block - a terminator's step into a block keeps fmp_cov
 *   fmp_cov_call  - an INVOKE's call keeps fmp_cov, pushing the frame
 *   fmp_cov_ret   - a return keeps fmp_cov, popping the frame
 *)
Theory fmpStageCoverFrame
Ancestors
  fmpStageCoverFramePoint fmpStageCoverFrameBlock
  fmpStageCoverFrameCall fmpStageCoverFrameRet
  o1ContractSimplifyCfgSrcFrame venomStepProps fnBlockBodyHelpers
  fmpStageCoverInv fmpStageCoverCall fmpStageCoverBack fmpStageCoverMem
  fmpStageBlockSim fmpStageFmpSteps fmpStageOpSteps fmpStageOpBase
  fmpStageControl fmpStageRel ptrDiscipline contextCodegenRel o1PassContract
  passSimulationDefs venomExecSemantics venomState venomInst finite_map
  words list

Theorem fmp_cov_block:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs' C' stk' PG' G' tn' fn' ti t /\
  fmp_cov D C C' vs vs' fmp eom stk' fn' t /\ active_inst fn' ti t /\
  is_terminator ti.inst_opcode /\ step_inst fuel C' ti t = OK t2 /\
  ~t2.vs_halted /\ enters_block fn' t2 t3 /\ active_inst fn' ti' t3 ==>
  fmp_cov D C C' vs vs' fmp eom stk' fn' t3
Proof
  strip_tac >>
  `MEM ti.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[step_ok_terminator_jump, MEM] >>
  `MEM ti.inst_opcode [JMP; JNZ; DJMP; INVOKE; RET; RETFMP; DRET]` by
    metis_tac[MEM] >>
  drule_all fmp_cov_control_point >> strip_tac >>
  `inst = ti` by (fs[MEM] >> gvs[]) >>
  qpat_x_assum `inst = ti` SUBST_ALL_TAC >>
  drule_all fmp_cov_block_point >> strip_tac >>
  irule fmp_cov_of_point >> metis_tac[]
QED

Theorem fmp_cov_call:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs' C' stk' PG' G' tn' fn' ti t /\
  fmp_cov D C C' vs vs' fmp eom stk' fn' t /\ active_inst fn' ti t /\
  ti.inst_opcode = INVOKE /\ decode_invoke ti = SOME (nm,ops) /\
  lookup_function nm C'.ctx_functions = SOME callee' /\
  eval_operands ops t = SOME args /\ setup_callee callee' args t = SOME cs /\
  enters_block callee' cs t1 /\ active_inst callee' ti1 t1 ==>
  fmp_cov D C C' vs vs' fmp eom
    (<| cf_fn := fn'; cf_inst := ti; cf_state := t; cf_params := PG';
        cf_prov := G'; cf_tvar := tn'.t_var |> :: stk') callee' t1
Proof
  strip_tac >>
  `MEM ti.inst_opcode [JMP; JNZ; DJMP; INVOKE; RET; RETFMP; DRET]` by simp[] >>
  drule_all fmp_cov_control_point >> strip_tac >>
  `inst.inst_opcode = INVOKE` by metis_tac[] >>
  drule_all fmp_cov_call_point >> strip_tac >>
  irule fmp_cov_of_point >> metis_tac[]
QED

Theorem fmp_cov_ret:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs' C' (g::stk') PG' G' tn' fn' ri t /\
  fmp_cov D C C' vs vs' fmp eom (g::stk') fn' t /\ active_inst fn' ri t /\
  step_inst fuel C' ri t = IntRet ret t_end /\
  bind_outputs g.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state g.cf_state t_end)) =
    SOME t' /\
  active_inst g.cf_fn ti' (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx) ==>
  fmp_cov D C C' vs vs' fmp eom stk' g.cf_fn
    (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx)
Proof
  strip_tac >>
  `MEM ri.inst_opcode [RET; RETFMP; DRET]` by
    metis_tac[step_inst_intret_opcodes] >>
  `MEM ri.inst_opcode [JMP; JNZ; DJMP; INVOKE; RET; RETFMP; DRET]` by
    metis_tac[MEM] >>
  drule_all fmp_cov_control_point >> strip_tac >>
  `inst = ri /\ ri.inst_opcode = RET` by
    (fs[MEM, pre_fmp_opcode_def] >> gvs[]) >>
  qpat_x_assum `inst = ri` SUBST_ALL_TAC >>
  drule_all fmp_cov_ret_point >> strip_tac >>
  irule fmp_cov_of_point >> metis_tac[]
QED
