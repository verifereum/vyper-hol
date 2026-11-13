(*
 * Backward progress for FmpLowering's coverage (fmpStageCoverage).  The
 * coverage runs over the target's reachable states, but the stage's step
 * lemmas go forward from a source step that terminates.  These lemmas
 * give that source step from the target's: at a related point the source
 * step does not fail, and a jump's target block can be entered.
 * fmpStageCoverCall does calls, returns and the context entry.
 *
 * TOP-LEVEL:
 *   fmp_stage_src_defined      - source operands are defined at a point
 *   fmp_stage_back_kept        - a kept instruction's source step terminates
 *   fmp_stage_back_fmp_ops     - DALLOCA and RETPC_PARAM never fail
 *   fmp_stage_back_block_entry - a jump's target block can be entered
 *)
Theory fmpStageCoverBack
Ancestors
  fmpStageOpBase fmpStageRel o1PassContract ptrDiscipline contextCodegenRel
  unitTransformDefs passSimulationDefs venomExecSemantics venomState venomInst
  simplifyCfgAvailability o1ContractSimplifyCfgSrcFrame
  finite_map words list venomWf venomWfProps
  makeSsaCurrentLockstep makeSsaCurrentPhiBatchRuntime analysisSimProofsBase
  venomExecProofs rich_list
  fmpStageCallArity fmpStageCoverBackParam fmpStageCoverBackKeptOps

Theorem fmp_stage_src_defined:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands ==>
  IS_SOME (lookup_var v s)
Proof
  strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
   !nm f. lookup_function nm C.ctx_functions = SOME f ==> wf_function f` by
    (fs[fmp_stage_ctx_def, o1_run_state_ok_def, o1_initial_state_ok_def,
        o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
     metis_tac[lookup_function_MEM]) >>
  drule_all scfg_frame_reachable_entry_root >> strip_tac >>
  irule scfg_frame_operand_defined >>
  fs[o1_fn_shape_def, make_ssa_input_ok_def] >> metis_tac[]
QED

(* Why it holds: the target steps the same inst, so shape errors match;
   source Var operands are defined (fmp_stage_src_defined) and labels
   agree.  inst_shape_ok bans DJMP; retpc_shape_ok gives RET operands.
   The value-dependent risk is PARAM's index: fmp_params_rel gives only
   LENGTH s <= LENGTH t.  A callee with a root has the pre-root conjunct
   LENGTH s.vs_params = LENGTH (fn_user_param_insts fn); for a root-less
   callee the source frame's params are the call's args, and the caller's
   lowering checked invoke_raw_input_layout_ok (fmpLowerDefsScript). *)
Theorem fmp_stage_back_kept:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  terminates (step_inst k' C' inst t) ==>
  terminates (step_inst k C inst s)
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (`!stk0 PG0 G0 tn0 caller inv st name args callee.
         frame_reachable vs C stk0 PG0 G0 tn0 caller inv st /\
         active_inst caller inv st /\ inv.inst_opcode = INVOKE /\
         inv.inst_operands = Label name::args /\
         lookup_function name C.ctx_functions = SOME callee ==>
         LENGTH (fn_user_param_insts callee) <= LENGTH args` by
        (rpt strip_tac >>
         `MEM caller C.ctx_functions /\ MEM inv (fn_insts caller)` by
           metis_tac[fmp_stage_frame_facts] >>
         `decode_invoke inv = SOME (name,args)` by simp[decode_invoke_def] >>
         `LENGTH args = LENGTH (fn_user_param_insts callee)` by
           metis_tac[fmp_stage_invoke_arity] >>
         simp[]) >>
      drule_all fmp_stage_back_param_conditional >> simp[]) >>
  `!v. MEM (Var v) inst.inst_operands ==> IS_SOME (lookup_var v s)` by
    (rpt strip_tac >> irule fmp_stage_src_defined >>
     metis_tac[MEM]) >>
  drule_all fmp_stage_back_kept_nonparam >> simp[]
QED

(* Why it holds: inst_wf fixes DALLOCA as [size_op],[out] and
   RETPC_PARAM as [Lit idx],[out]; RETPC_PARAM has no bound check, and
   DALLOCA's operand is defined (fmp_stage_src_defined) and not a Label. *)
Theorem fmp_stage_back_fmp_ops:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  MEM inst.inst_opcode [DALLOCA; RETPC_PARAM] ==>
  terminates (step_inst k C inst s)
Proof
  strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `venomWf$inst_wf inst` by
    (fs[o1_fn_shape_def, venomWfTheory.fn_inst_wf_def,
        active_inst_def] >> metis_tac[MEM_EL]) >>
  `unitShapeDefs$inst_shape_ok inst` by
    (fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def, EVERY_MEM] >>
     metis_tac[]) >>
  fs[MEM] >>
  gvs[venomWfTheory.inst_wf_def, LENGTH_EQ_NUM_compute] >>
  simp[step_inst_non_invoke, step_inst_base_def, terminates_def] >>
  rename1 `inst.inst_operands = [size_op]` >>
  Cases_on `size_op` >> simp[eval_operand_def] >>
  gvs[unitShapeDefsTheory.inst_shape_ok_def,
      unitShapeDefsTheory.label_positions_ok_def,
      stackPlanTypesTheory.is_label_operand_def] >>
  rename1 `inst.inst_operands = [Var v]` >>
  `MEM (Var v) inst.inst_operands /\ inst.inst_opcode <> PHI` by simp[] >>
  drule_all fmp_stage_src_defined >>
  Cases_on `lookup_var v s` >> simp[]
QED

(* Why it holds: DJMP is banned by inst_shape_ok.  make_ssa_input_ok
   gives fn_phis_cover_preds (the edge from bi's block is a predecessor)
   and fn_defs_reach_uses for PHI operands: the PHI analogue of
   fmp_stage_src_defined, at the end of the predecessor block. *)
Theorem fmp_stage_back_block_entry:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn bi sb /\ active_inst fn bi sb /\
  MEM bi.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst k C bi sb = OK (jump_to lbl sb) /\
  MEM lbl (MAP (\bb. bb.bb_label) fn.fn_blocks) ==>
  ?s1 inst. enters_block fn (jump_to lbl sb) s1 /\ active_inst fn inst s1
Proof
  strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
   fn_phis_cover_preds fn` by
    fs[o1_fn_shape_def, make_ssa_input_ok_def] >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
   !nm f. lookup_function nm C.ctx_functions = SOME f ==> wf_function f` by
    (fs[fmp_stage_ctx_def, o1_run_state_ok_def, o1_initial_state_ok_def,
        o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
     metis_tac[lookup_function_MEM]) >>
  drule_all scfg_frame_reachable_entry_root >> strip_tac >>
  `is_terminator bi.inst_opcode` by
    (fs[is_terminator_def] >> metis_tac[]) >>
  `~sb.vs_halted` by
    (drule o1PassLiftTheory.supply_frame_reach_not_halted >>
     fs[o1PassLiftTheory.fn_entry_state_def]) >>
  `~(jump_to lbl sb).vs_halted` by simp[jump_to_def] >>
  drule_all lockstep_active_terminator_edge >> strip_tac >>
  drule_all scfg_frame_path_endpoint >> strip_tac >>
  rename1 `scfg_path_defined fn path pred_bb (LENGTH pred_bb.bb_instructions) _` >>
  `?bb. lookup_block lbl fn.fn_blocks = SOME bb` by
    metis_tac[dfAnalyzeProofsTheory.lookup_block_exists] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `?s_phi. eval_phis (jump_to lbl sb) bb.bb_instructions = OK s_phi` by
    (irule current_phi_batch_success_all >> rpt strip_tac >>
     rename1 `MEM phiinst bb.bb_instructions` >>
     `inst_wf phiinst` by
       (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
     `phi_well_formed phiinst.inst_operands /\ LENGTH phiinst.inst_outputs = 1` by
       (qpat_x_assum `inst_wf phiinst` mp_tac >> simp[inst_wf_def]) >>
     `?v. MEM (sb.vs_current_bb,v) (phi_pairs phiinst.inst_operands)` by
       (fs[fn_phis_cover_preds_def, jump_to_def] >> metis_tac[]) >>
     drule phi_pairs_resolve_phi_some >> strip_tac >>
     drule_all resolve_phi_well_formed >> strip_tac >>
     qpat_x_assum `op = Var var` SUBST_ALL_TAC >>
     `IS_SOME (lookup_var var (jump_to lbl sb))` by
       (irule scfg_phi_edge_defined >>
        qexistsl_tac [`bb`, `fn`, `phiinst`, `path`, `pred_bb`] >>
        simp[] >>
        `MEM pred_bb fn.fn_blocks /\ pred_bb.bb_label = sb.vs_current_bb` by
          metis_tac[lookup_block_MEM, lookup_block_label] >>
        fs[jump_to_def] >> metis_tac[resolve_phi_pair]) >>
     Cases_on `phiinst.inst_outputs` >> gvs[] >>
     fs[eval_one_phi_def, jump_to_def, eval_operand_def] >>
     qmatch_goalsub_abbrev_tac `lookup_var var state` >>
     Cases_on `lookup_var var state` >> gvs[]) >>
  `enters_block fn (jump_to lbl sb)
     (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (simp[enters_block_def, jump_to_def] >>
     qexists_tac `s_phi` >> fs[jump_to_def]) >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by
    (spose_not_then assume_tac >>
     `phi_prefix_length bb.bb_instructions = LENGTH bb.bb_instructions` by
       (mp_tac (Q.SPEC `bb.bb_instructions` phi_prefix_length_le) >> decide_tac) >>
     mp_tac (Q.SPEC `bb.bb_instructions` phi_prefix_no_terminator) >>
     gvs[bb_well_formed_def, EVERY_MEM] >>
     simp[EXISTS_MEM] >> qexists_tac `LAST bb.bb_instructions` >>
     Cases_on `bb.bb_instructions` >> gvs[MEM_LAST]) >>
  `s_phi.vs_current_bb = lbl` by
    (drule eval_phis_only_updates_vs_vars >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[jump_to_def]) >>
  qexistsl_tac [`s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`,
    `EL (phi_prefix_length bb.bb_instructions) bb.bb_instructions`] >>
  simp[active_inst_def] >> qexists_tac `bb` >>
  simp[get_instruction_def]
QED
