Theory fmpStageOpFrameForwardScalars
Ancestors
  fmpStageOpBase fmpStageRel ptrStaticDiscipline ptrDiscipline
  o1PassContract frameViewFacts venomExecSemantics venomInst
  list pred_set finite_map pointerConfinedDefs memLocDefs
  unitShapeDefs o1LowerDloadRelocationKernel frameRelocationGuardedValues

Theorem fmp_copy_static_nonpointer[local]:
  fn_static_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dst;src;sz] /\ MEM op [src;sz] /\ op = Var v ==>
  v NOTIN fn_pv P fn
Proof
  strip_tac >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by
    metis_tac[fn_static_ptr_ok_def] >>
  qpat_x_assum `ptr_use_static_ok _ _ _` mp_tac >>
  simp[ptr_use_static_ok_def, is_pointer_preserving_op_def,
       mem_read_ops_def, mem_write_ops_def] >>
  strip_tac >> spose_not_then assume_tac >>
  first_x_assum (qspec_then `v` mp_tac) >> gvs[] >>
  Cases_on `dst = Var v` >> gvs[FILTER] >>
  Cases_on `Var v = src` >> gvs[]
QED

Theorem fmp_forward_copy_scalar[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dst;src;sz] /\ MEM op [src;sz] /\
  eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  drule_all fmp_stage_prov_support >> strip_tac >>
  `fn_static_ptr_ok P fn` by metis_tac[EVERY_MEM] >>
  `!v. op = Var v ==> v NOTIN fn_pv P fn` by
    metis_tac[fmp_copy_static_nonpointer] >>
  `op_prov G op = NONE` by
    (Cases_on `op` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]) >>
  `MEM op inst.inst_operands` by gvs[] >>
  `op_taint tn op = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (rpt gen_tac >> disch_tac >> irule ordinary_operand_not_retpc >>
     conj_tac >- gvs[o1_fn_shape_def, fn_shape_ok_def] >>
     qexists_tac `inst` >> gvs[]) >>
  `inst.inst_opcode <> PHI` by simp[] >>
  drule_all fmp_stage_operand >> strip_tac >>
  gvs[fmp_value_rel_def, ld_value_agree_def] >>
  metis_tac[word_agree_except_empty]
QED

Theorem fmp_forward_copy_scalars:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ in_revert_forward fn s /\
  inst.inst_opcode = RETURNDATACOPY /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  inst.inst_operands = [dst;src;sz] ==>
  (!x. eval_operand src s = SOME x ==> eval_operand src t = SOME x) /\
  (!x. eval_operand sz s = SOME x ==> eval_operand sz t = SOME x)
Proof
  strip_tac >> conj_tac >> gen_tac >> disch_tac >>
  irule fmp_forward_copy_scalar >> metis_tac[MEM]
QED
