(*
 * A related RET in FmpLowering's stage simulation returns the source's
 * values: RET is kept, its front operands are untainted and carry no
 * provenance, so they evaluate equally on both sides, and neither side
 * adopts an FMP.
 *
 * TOP-LEVEL:
 *   fmp_stage_ret_step  - a related RET returns the same values
 *)
Theory fmpStageRetStep
Ancestors
  o1LowerDloadOpaque ptrStaticDiscipline pointerConfinedDefs memLocDefs pred_set
  fmpStageOpBaseActual fmpStepStructural fmpStepLayout fmpLowerDefs
  fmpStageOpBase fmpStageControl fmpStageRel passSharedProps runInstsProps
  venomWf o1PassContract ptrDiscipline contextCodegenRel analysisSimDefs
  venomExecSemantics venomState venomInst finite_map list rich_list
  fmpLowerProps fmpLowerIndexedProps dftGasToListReachBoundary

Theorem fmp_run_ret_clean[local]:
  ptr_use_static_ok P pv inst /\ inst.inst_opcode = RET /\
  FDOM G SUBSET pv /\ MEM op inst.inst_operands ==>
  op_prov G op = NONE
Proof
  strip_tac >> Cases_on `op` >> simp[op_prov_def] >>
  rename1 `MEM (Var v) inst.inst_operands` >>
  `v NOTIN pv` by
    (strip_tac >> gvs[ptr_use_static_ok_def, is_pointer_preserving_op_def,
       mem_read_ops_def, mem_write_ops_def] >> metis_tac[]) >>
  fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem fmp_run_operand_defined[local]:
  fmp_env_rel sm fn live G tv s t /\ s.vs_labels = t.vs_labels /\
  IS_SOME (eval_operand op s) ==> IS_SOME (eval_operand op t)
Proof
  strip_tac >> Cases_on `op` >>
  gvs[eval_operand_def, lookup_var_def, fmp_env_rel_def] >>
  metis_tac[optionTheory.IS_SOME_EXISTS]
QED

Theorem fmp_run_ret_front_operand[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = RET /\ inst.inst_operands <> [] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM op (FRONT inst.inst_operands) /\ eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `MEM op inst.inst_operands` by metis_tac[rich_listTheory.MEM_FRONT_NOT_NIL] >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (gvs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def] >>
     metis_tac[o1LowerDloadOpaqueTheory.ret_front_non_retpc]) >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by
    (gvs[EVERY_MEM, fn_static_ptr_ok_def] >> metis_tac[]) >>
  drule fmp_stage_prov_support >> disch_then (qspec_then `P` mp_tac) >>
  simp[] >> strip_tac >>
  `op_prov G op = NONE` by metis_tac[fmp_run_ret_clean] >>
  `op_taint tn op = {}` by metis_tac[o1LowerDloadGhostTheory.ret_operand_untainted] >>
  `inst.inst_opcode <> PHI` by simp[] >>
  drule_all fmp_stage_operand >> simp[] >> strip_tac >>
  gvs[fmp_value_rel_def, o1LowerDloadRelocationKernelTheory.ld_value_agree_def,
      word_agree_except_bits] >>
  simp[fcpTheory.CART_EQ]
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
  strip_tac >>
  `step_inst_base inst s = IntRet ir s1` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> gvs[step_inst_non_invoke]) >>
  `?vals. eval_operands inst.inst_operands s = SOME vals /\ vals <> []` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_def] >>
     Cases_on `eval_operands inst.inst_operands s` >> simp[] >>
     rename1 `SOME vals` >> Cases_on `vals` >> simp[]) >>
  `inst.inst_operands <> []` by (strip_tac >> gvs[eval_operands_def]) >>
  `!op. MEM op inst.inst_operands ==> IS_SOME (eval_operand op s)` by
    (`IS_SOME (eval_operands inst.inst_operands s)` by simp[] >>
     fs[eval_operands_IS_SOME_EVERY, EVERY_MEM]) >>
  `fmp_env_rel sm fn
     (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
     G tn.t_var s t /\ s.vs_labels = t.vs_labels` by
    (gvs[fmp_stage_rel_def, fmp_frame_rel_def] >> metis_tac[]) >>
  `!op. MEM op inst.inst_operands ==>
     (IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t))` by
    metis_tac[fmp_run_operand_defined] >>
  `!op. MEM op (FRONT inst.inst_operands) ==>
     eval_operand op s = eval_operand op t` by
    (rpt strip_tac >>
     `IS_SOME (eval_operand op s)` by metis_tac[rich_listTheory.MEM_FRONT_NOT_NIL] >>
     Cases_on `eval_operand op s` >> gvs[] >>
     metis_tac[fmp_run_ret_front_operand]) >>
  drule_all o1LowerDloadOpaqueTheory.ret_front_transfer >> strip_tac >>
  gvs[] >> qexists `jr` >> gvs[step_inst_non_invoke]
QED
