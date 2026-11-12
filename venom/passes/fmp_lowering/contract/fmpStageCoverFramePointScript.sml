(* Shared boundary between coverage and control-transfer simulation.
   Restoring at a control point is a zero-step normalization. *)
Theory fmpStageCoverFramePoint
Ancestors
  fmpStageCoverInv fmpStageCoverMem fmpStageFmpSteps fmpStageOpBase
  fmpStageControl fmpStageRel lowerDloadPtrRawReachable
  o1ContractSimplifyCfgSrcFrame o1PassLift o1PassContract ptrDiscipline
  contextCodegenRel codegenRel fmpStepLayout fmpReclaimDefs
  analysisSimDefs unitTransformDefs venomExecProofs passSimulationDefs venomExecSemantics venomExecProps venomWf venomState
  venomInst finite_map words list

Theorem fmp_cov_of_point:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom F
    stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_cov_stack C' stk ts stk' /\ active_inst fn' ti t ==>
  fmp_cov D C C' vs vs' fmp eom stk' fn' t
Proof
  rpt strip_tac >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
   !nm f. lookup_function nm C.ctx_functions = SOME f ==> wf_function f` by
    (fs[fmp_stage_ctx_def, o1_run_state_ok_def, o1_initial_state_ok_def,
        o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
     metis_tac[lookup_function_MEM]) >>
  drule_all scfg_frame_reachable_entry_root >> strip_tac >>
  `~s.vs_halted` by
    (drule supply_frame_reach_not_halted >> fs[fn_entry_state_def]) >>
  drule_all fmp_cov_target_labels >> strip_tac >>
  drule_all active_inst_block_lookup >> strip_tac >>
  simp[fmp_cov_def] >> disj1_tac >>
  qexistsl [`stk`, `PG`, `G`, `tn`, `fn`, `inst`, `s`, `sm`, `lo`,
            `t`, `ts`, `F`] >>
  fs[fmp_target_run_def, run_insts_def, get_instruction_def]
QED

Theorem fmp_cov_control_raw[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  active_inst fn' ti t /\ fmp_cov D C C' vs vs' fmp eom stk' fn' t /\
  MEM ti.inst_opcode [JMP; JNZ; DJMP; INVOKE; RET; RETFMP; DRET] ==>
  ?stk PG G tn fn inst s sm lo ts restored.
    frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
    ~s.vs_halted /\
    fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom restored
      stk PG G tn fn s lo t ts /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    fmp_cov_stack C' stk ts stk'
Proof
  rpt strip_tac >>
  qpat_x_assum `fmp_cov _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[fmp_cov_def] >> strip_tac
  >- (Cases_on `t.vs_inst_idx = t1.vs_inst_idx`
      >- (`t1 = t` by
            (qpat_x_assum `!k. fmp_target_run _ _ _ _ _ _` (qspec_then `0` mp_tac) >>
             simp[] >> strip_tac >> drule fmp_target_run_zero >> simp[]) >>
          qpat_x_assum `t1 = t` SUBST_ALL_TAC >>
          qexistsl [`stk`, `PG`, `G`, `tn`, `fn`, `inst`, `s`, `sm`, `lo`, `ts`, `restored`] >>
          asm_rewrite_tac[]) >>
      drule_all fmp_cov_target_labels >> strip_tac >>
      drule_all active_inst_block_lookup >> strip_tac >>
      qpat_x_assum `!i. _ <= i /\ _ ==> _` (qspec_then `t.vs_inst_idx` mp_tac) >>
      simp[] >> strip_tac >> gvs[get_instruction_def, fmp_inserted_op_def]) >>
  drule_all active_inst_block_lookup >> strip_tac >>
  gvs[] >>
  Cases_on `t.vs_inst_idx = j` >>
  gvs[revert_forward_pair_def, get_instruction_def] >>
  `ti.inst_opcode = ASSIGN` by
    (first_x_assum irule >> qexists_tac `t.vs_inst_idx` >> simp[get_instruction_def]) >>
  gvs[]
QED

Theorem fmp_cov_control_restore[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\
  fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom restored
    stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  active_inst fn' ti t /\ ti.inst_opcode <> ASSIGN ==>
  ?sm' lo'. fmp_stage_rel D C' sm' (w2n vs'.vs_initial_fmp) (w2n fmp) eom T
    stk PG G tn fn s lo' t ts
Proof
  rpt strip_tac >> Cases_on `restored`
  >- metis_tac[] >>
  drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`) fmp_stage_restore >>
  disch_then (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
  disch_then drule >> simp[] >> strip_tac >>
  drule_all fmp_cov_target_labels >> strip_tac >>
  drule_all active_inst_block_lookup >> strip_tac >>
  `n = 0` by
    (Cases_on `n = 1` >> gvs[get_instruction_def]) >>
  qpat_x_assum `!k. fmp_target_run _ _ _ _ _ _` (qspec_then `0` mp_tac) >>
  simp[] >> strip_tac >> drule fmp_target_run_zero >> strip_tac >>
  metis_tac[]
QED

Theorem fmp_stage_control_inst[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\ MEM fn C.ctx_functions /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\ inst = EL idx bb.bb_instructions /\
  pre_fmp_opcode inst.inst_opcode /\
  lookup_block lbl fn'.fn_blocks = SOME bt /\
  get_instruction bt
    (fmp_stage_tidx (fmp_stage_plan infos ctx fn)
       (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx +
     (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0)) = SOME ti /\
  MEM ti.inst_opcode [JMP; JNZ; DJMP; INVOKE; RET; RETFMP; DRET] ==>
  inst.inst_opcode = ti.inst_opcode /\
  (ti.inst_opcode <> INVOKE ==> inst = ti)
Proof
  strip_tac >>
  Cases_on `MEM inst.inst_opcode [DALLOCA; RETPC_PARAM]`
  >- (mp_tac (Q.INST
         [`i` |-> `fmp_stage_tidx (fmp_stage_plan infos ctx fn)
            (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx +
            (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0)`]
         fmp_stage_inserted_at) >>
      impl_tac >- (simp[fmp_cov_tidx_lt] >> rw[] >> fs[]) >>
      strip_tac >> gvs[get_instruction_def, fmp_inserted_op_def]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (qpat_x_assum `inst = _` SUBST_ALL_TAC >>
      drule_all fmp_stage_invoke_inst >> strip_tac >>
      gvs[get_instruction_def]) >>
  `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by fs[] >>
  drule_all fmp_stage_kept_inst >> strip_tac >>
  gvs[get_instruction_def]
QED

Theorem fmp_cov_control_point:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  active_inst fn' ti t /\ fmp_cov D C C' vs vs' fmp eom stk' fn' t /\
  MEM ti.inst_opcode [JMP; JNZ; DJMP; INVOKE; RET; RETFMP; DRET] ==>
  ?stk PG G tn fn inst s sm lo ts.
    frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
    ~s.vs_halted /\
    fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom T
      stk PG G tn fn s lo t ts /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    fmp_cov_stack C' stk ts stk' /\
    inst.inst_opcode = ti.inst_opcode /\ pre_fmp_opcode inst.inst_opcode /\
    (ti.inst_opcode <> INVOKE ==> inst = ti)
Proof
  strip_tac >> drule_all fmp_cov_control_raw >> strip_tac >>
  `ti.inst_opcode <> ASSIGN` by fs[] >>
  drule_all fmp_cov_control_restore >> strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  drule_all fmp_cov_target_labels >> strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by fs[o1_fn_shape_def, wf_function_def] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst` by
    metis_tac[active_inst_block_lookup] >>
  `?bt. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
        get_instruction bt t.vs_inst_idx = SOME ti` by
    metis_tac[active_inst_block_lookup] >>
  qpat_x_assum `fmp_stage_rel _ _ _ _ _ _ restored _ _ _ _ _ _ _ _ _` kall_tac >>
  drule_all fmp_cov_frame_pos >> strip_tac >>
  qpat_x_assum `!bb. lookup_block _ _ = _ ==> _` drule >> strip_tac >>
  `pre_fmp_opcode inst.inst_opcode` by fs[pre_fmp_ops_def, EVERY_MEM] >>
  `inst.inst_opcode = ti.inst_opcode /\
   (ti.inst_opcode <> INVOKE ==> inst = ti)` by
    (mp_tac (Q.INST [`lbl` |-> `s.vs_current_bb`, `idx` |-> `s.vs_inst_idx`]
       fmp_stage_control_inst) >>
     impl_tac >- fs[get_instruction_def] >> simp[]) >>
  qexistsl [`stk`, `PG`, `G`, `tn`, `fn`, `inst`, `s`, `sm'`, `lo'`, `ts`] >>
  asm_rewrite_tac[]
QED
