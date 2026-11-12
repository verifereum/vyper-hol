(* Affine arithmetic at the FMP stage boundary. *)
Theory fmpStageOpSimPureAffine
Ancestors
  fmpStageOpBase fmpStageRel o1LowerDloadRelocationKernel
  ptrStaticDiscipline ptrDiscipline o1PassContract contextCodegenRel
  venomExecSemantics venomState venomInst pointerConfinedDefs
  finite_map list pred_set words

Theorem fmp_value_rel_add[local]:
  fmp_value_rel sm h1 {} x1 y1 /\ fmp_value_rel sm h2 {} x2 y2 /\
  (h1 = NONE \/ h2 = NONE) /\
  h = (case h1 of NONE => h2 | SOME id => h1) ==>
  fmp_value_rel sm h {} (x1 + x2) (y1 + y2)
Proof
  Cases_on `h1` >> Cases_on `h2` >>
  simp[fmp_value_rel_def] >> rpt strip_tac >>
  imp_res_tac ld_value_agree_clean >> gvs[] >>
  gvs[ld_value_agree_pointer, ld_value_agree_scalar, word_agree_except_def] >>
  qexistsl [`b`,`c`,`z`] >> simp[] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem fmp_value_rel_sub[local]:
  fmp_value_rel sm h {} x1 y1 /\ fmp_value_rel sm NONE {} x2 y2 ==>
  fmp_value_rel sm h {} (x1 - x2) (y1 - y2)
Proof
  Cases_on `h` >> simp[fmp_value_rel_def] >> rpt strip_tac >>
  imp_res_tac ld_value_agree_clean >> gvs[] >>
  gvs[ld_value_agree_pointer, ld_value_agree_scalar, word_agree_except_def] >>
  qexistsl [`b`,`c`,`z`] >> simp[] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem fmp_affine_provenance[local]:
  FDOM G SUBSET fn_pv P fn /\ fn_static_ptr_ok P fn /\
  MEM inst (fn_insts fn) /\ MEM inst.inst_opcode [ADD; SUB] /\
  inst.inst_operands = [op1;op2] ==>
  (op_prov G op1 = NONE \/ op_prov G op2 = NONE) /\
  (inst.inst_opcode = SUB ==> op_prov G op2 = NONE)
Proof
  strip_tac >>
  `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
    (gvs[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `affine_pointer_ops fn (ptr_roots P fn)` by
    gvs[fn_static_ptr_ok_def] >>
  qpat_x_assum `affine_pointer_ops _ _`
    (mp_tac o SRULE [affine_pointer_ops_def, LET_THM]) >>
  disch_then (qspecl_then [`bb`,`inst`,`op1`,`op2`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[op_prov_def, fn_pv_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem fmp_affine_operand[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [ADD; SUB] /\ MEM op inst.inst_operands /\
  eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\
      fmp_value_rel sm (op_prov G op) {} x y
Proof
  strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `op_taint tn op = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (rpt strip_tac >>
     `opaque_use_ok fn` by
       gvs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def] >>
     gvs[] >> drule_all unitShapeDefsTheory.opaque_use_ok_retpc_use >>
     gvs[unitShapeDefsTheory.retpc_use_ok_def]) >>
  `inst.inst_opcode <> PHI` by gvs[] >>
  drule_all fmp_stage_operand >> simp[]
QED


Theorem fmp_affine_step[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [ADD; SUB] /\ step_inst k C inst s = OK s1 ==>
  ?out x y. inst.inst_outputs = [out] /\ s1 = update_var out x s /\
    step_inst k C' inst t = OK (update_var out y t) /\
    fmp_value_rel sm (out_prov PG G inst s1) {} x y
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  drule fmp_stage_prov_support >>
  disch_then (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  `fn_static_ptr_ok P fn` by metis_tac[EVERY_MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> fs[MEM] >>
  (gvs[step_inst_non_invoke, step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
   strip_tac >> gvs[] >>
   rename1 `eval_operand op1 s = SOME x1` >>
   rename1 `eval_operand op2 s = SOME x2` >>
   `?y1. eval_operand op1 t = SOME y1 /\
     fmp_value_rel sm (op_prov G op1) {} x1 y1` by
     metis_tac[fmp_affine_operand, MEM] >>
   `?y2. eval_operand op2 t = SOME y2 /\
     fmp_value_rel sm (op_prov G op2) {} x2 y2` by
     metis_tac[fmp_affine_operand, MEM] >>
   `(op_prov G op1 = NONE \/ op_prov G op2 = NONE) /\
    (inst.inst_opcode = SUB ==> op_prov G op2 = NONE)` by
     metis_tac[fmp_affine_provenance, MEM] >>
   qmatch_goalsub_abbrev_tac `update_var out value s` >>
   qexistsl [`value`,
     `if inst.inst_opcode = ADD then y1 + y2 else y1 - y2`] >>
   simp[out_prov_def, first_prov_def, Abbr `value`]) >>
  (Cases_on `inst.inst_opcode = ADD`
   >- (irule fmp_value_rel_add >>
       qexistsl [`op_prov G op1`,`op_prov G op2`] >>
       Cases_on `op_prov G op1` >> Cases_on `op_prov G op2` >> gvs[]) >>
   gvs[] >> Cases_on `op_prov G op1` >> gvs[] >>
   rewrite_tac[WORD_SUB_INTRO] >> irule fmp_value_rel_sub >> simp[])
QED

Theorem fmp_affine_terminating_result[local]:
  MEM inst.inst_opcode [ADD; SUB] /\
  step_inst k C inst s = r /\ terminates r ==>
  ?s1. r = OK s1
Proof
  strip_tac >> fs[MEM] >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_pure2_def,
      AllCaseEqs(), passSimulationDefsTheory.terminates_def]
QED
