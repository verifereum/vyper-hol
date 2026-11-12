(*
 * Target-side facts for FmpLowering's block simulation (fmpStageBlockSim):
 * the lowered function's blocks are well formed with distinct labels, a
 * straight-line run of a block's non-final instructions is skipped by
 * exec_block, a related INVOKE has a target instruction to run, and a
 * related RET returns the source's values.
 *
 * TOP-LEVEL:
 *   fmp_stage_target_shape   - the lowered function is well formed
 *   exec_block_run_prefix    - exec_block skips a run of non-final insts
 *   fmp_target_run_exec_block - likewise for fmp_target_run
 *   fmp_stage_invoke_target  - a related INVOKE has a target instruction
 *   fmp_stage_ret_step       - a related RET returns the same values
 *)
Theory fmpStageBlockSimCode
Ancestors
  fmpStageOpBaseActual fmpStepStructural fmpStepLayout fmpLowerDefs
  fmpStageOpBase fmpStageControl fmpStageRel passSharedProps runInstsProps
  venomWf o1PassContract ptrDiscipline contextCodegenRel analysisSimDefs
  venomExecSemantics venomState venomInst finite_map list

(* Why: the block simulation reads the target's next instruction off the
   lowered block (unique labels) and knows that only its last
   instruction is a terminator. *)
Theorem fmp_stage_target_shape:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\ MEM fn C.ctx_functions /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' ==>
  ALL_DISTINCT (fn_labels fn') /\ EVERY bb_well_formed fn'.fn_blocks
Proof
  strip_tac >>
  drule_all fmp_stage_actual_witness >> strip_tac >>
  `o1_fn_shape C fn` by gvs[fmp_stage_ctx_def, o1_ctx_shape_def, EVERY_MEM] >>
  `wf_function fn /\ first_block_no_phi fn` by gvs[o1_fn_shape_def] >>
  gvs[fmp_stage_lowered_def] >>
  `fmp_lower_function ctx0 sp fn = SOME (fn',sp')` by
    simp[fmp_lower_function_def] >>
  drule_all fmp_lower_function_structure >>
  drule fmp_lower_function_preserves_labels >>
  gvs[wf_function_def]
QED

(* Why: the restores, DALLOCA's expansion and the root run straight-line
   (run_insts); when an instruction of the block follows them, none of
   them is the block's terminator, so exec_block runs them the same way. *)
Theorem exec_block_run_prefix_gen[local]:
  !n fuel ctx bb j s s1.
    bb_well_formed bb /\ j + n < LENGTH bb.bb_instructions /\
    run_insts fuel ctx (TAKE n (DROP j bb.bb_instructions)) s = OK s1 ==>
    exec_block fuel ctx bb (s with vs_inst_idx := j) =
    exec_block fuel ctx bb (s1 with vs_inst_idx := j + n)
Proof
  Induct >- simp[run_insts_def] >>
  rpt strip_tac >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  `DROP j bb.bb_instructions =
   EL j bb.bb_instructions :: DROP (SUC j) bb.bb_instructions` by
    (qspecl_then [`bb.bb_instructions`,`j`] mp_tac
       rich_listTheory.DROP_EL_CONS >>
     impl_tac >- simp[] >> simp[arithmeticTheory.ADD1]) >>
  gvs[run_insts_def, AllCaseEqs()] >>
  rename1 `step_inst _ _ _ s = OK s2` >>
  `~is_terminator (EL j bb.bb_instructions).inst_opcode` by
    (strip_tac >> gvs[bb_well_formed_def] >> res_tac >> simp[]) >>
  drule_then (qspecl_then [`fuel`,`ctx`,`s`,`j`] mp_tac)
    step_inst_non_term_idx >>
  simp[] >> strip_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def] >>
  first_x_assum (qspecl_then [`fuel`,`ctx`,`bb`,`SUC j`,`s2`,`s1`] mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem exec_block_run_prefix:
  !n fuel ctx bb s s1.
    bb_well_formed bb /\ s.vs_inst_idx + n < LENGTH bb.bb_instructions /\
    run_insts fuel ctx (TAKE n (DROP s.vs_inst_idx bb.bb_instructions)) s =
      OK s1 ==>
    exec_block fuel ctx bb s =
    exec_block fuel ctx bb (s1 with vs_inst_idx := s.vs_inst_idx + n)
Proof
  rpt strip_tac >>
  qspecl_then [`n`,`fuel`,`ctx`,`bb`,`s.vs_inst_idx`,`s`,`s1`] mp_tac
    exec_block_run_prefix_gen >>
  simp[]
QED

Theorem fmp_target_run_exec_block:
  fmp_target_run fuel C' name t n t1 /\
  lookup_function name C'.ctx_functions = SOME fn' /\
  EVERY bb_well_formed fn'.fn_blocks /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  t.vs_inst_idx + n < LENGTH bb'.bb_instructions ==>
  exec_block fuel C' bb' t = exec_block fuel C' bb' t1
Proof
  rw[fmp_target_run_def] >> gvs[] >>
  `!lbl bbs bb. lookup_block lbl bbs = SOME bb ==> MEM bb bbs` by
    (Induct_on `bbs` >> rw[lookup_block_def, FIND_thm] >>
     gvs[lookup_block_def] >> res_tac >> simp[]) >>
  `bb_well_formed bb'` by (res_tac >> gvs[EVERY_MEM]) >>
  `t.vs_inst_idx + n < LENGTH bb'.bb_instructions` by simp[] >>
  drule_all exec_block_run_prefix >> simp[]
QED

(* Why: fmp_invoke_sim takes the target INVOKE as given; at a related
   point past the restores the target has an instruction there (the
   lowered INVOKE). *)
Theorem fmp_stage_invoke_target:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = INVOKE /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' ==>
  ?inst'. active_inst fn' inst' t
Proof
  cheat
QED

(* Why: fmp_stage_result's RET case.  RET returns its front operands,
   which carry no provenance (no pointer reaches RET: ptr_use_static_ok)
   and no taint (taint_ok) and aren't the return pc (opaque_use_ok), so
   the relation makes them equal; RET changes no state. *)
Theorem fmp_stage_ret_step:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = RET /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  step_inst k C inst s = IntRet ir s1 ==>
  s1 = s /\ ir.iret_adopt_fmp = NONE /\
  ?jr. (!k'. step_inst k' C' inst t = IntRet jr t) /\
       jr.iret_values = ir.iret_values /\ jr.iret_adopt_fmp = NONE
Proof
  cheat
QED
