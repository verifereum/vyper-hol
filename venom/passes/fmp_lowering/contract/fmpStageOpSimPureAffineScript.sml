(* Affine arithmetic at the FMP stage boundary. *)
Theory fmpStageOpSimPureAffine
Ancestors
  fmpStageOpBase fmpStageRel o1LowerDloadRelocationKernel
  ptrStaticDiscipline ptrDiscipline o1PassContract contextCodegenRel
  venomExecSemantics venomState venomInst pointerConfinedDefs
  finite_map list pred_set words

Theorem fmp_value_rel_add[local]:
  fmp_value_rel sm h1 {} x1 y1 /\ fmp_value_rel sm h2 {} x2 y2 /\
  (h1 = NONE \/ h2 = NONE) ==>
  fmp_value_rel sm (case h1 of NONE => h2 | SOME id => h1) {}
    (x1 + x2) (y1 + y2)
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

