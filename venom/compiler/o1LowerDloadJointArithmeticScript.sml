(* Affine ADD/SUB operands at the joint semantic boundary. *)
Theory o1LowerDloadJointArithmetic
Ancestors
  o1LowerDloadJointScalar o1LowerDloadJointRelation o1LowerDloadOccurrence
  o1LowerDloadGhost o1LowerDloadOpaque o1LowerDloadEnvironment
  ptrDiscipline pointerConfinedDefs unitShapeDefs o1PassContract
  venomExecSemantics venomInst finite_map list pred_set contextCodegenRel

Theorem ld_joint_arithmetic_operand_taint:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  MEM inst.inst_opcode [ADD; SUB] /\ MEM op inst.inst_operands ==>
  op_taint tn op = {}
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  gvs[taint_ok_def] >> metis_tac[]
QED

Theorem ld_joint_arithmetic_operand_value:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [ADD; SUB] /\ MEM op inst.inst_operands /\
  eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\ ld_value_agree sites (op_prov H op) {} x y
Proof
  strip_tac >>
  `op_taint tn op = {}` by metis_tac[ld_joint_arithmetic_operand_taint] >>
  `!v. op = Var v ==> MEM v (fn_ir_vars fn)` by
    metis_tac[ld_active_operand_ir_var] >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (rpt gen_tac >> disch_tac >> irule ld_active_operand_non_retpc >>
     simp[] >> qexistsl_tac [`inst`,`s`] >> gvs[retpc_use_ok_def] >> metis_tac[]) >>
  drule_all ld_joint_operand_value >> simp[]
QED

Theorem ld_joint_arithmetic_affine:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  active_inst fn inst s /\ MEM inst.inst_opcode [ADD; SUB] /\
  inst.inst_operands = [op1;op2] ==>
  (op_prov H op1 = NONE \/ op_prov H op2 = NONE) /\
  (inst.inst_opcode = SUB ==> op_prov H op2 = NONE)
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  qpat_x_assum `ptr_discipline _ _ _`
    (strip_assume_tac o REWRITE_RULE [ptr_discipline_def]) >>
  drule frame_reachable_prov_support >>
  disch_then (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  `affine_pointer_ops fn (ptr_roots P fn)` by
    (gvs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G` by
    fs[ld_joint_boundary_def, occurrence_annotation_ok_def] >>
  drule occurrence_op_erasure >> disch_then (qspec_then `op1` assume_tac) >>
  drule occurrence_op_erasure >> disch_then (qspec_then `op2` assume_tac) >>
  `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
    (fs[active_inst_def] >> metis_tac[MEM_EL]) >>
  qpat_x_assum `affine_pointer_ops _ _`
    (mp_tac o SRULE [affine_pointer_ops_def, LET_THM]) >>
  disch_then (qspecl_then [`bb`,`inst`,`op1`,`op2`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[op_prov_def, occurrence_param_ok_def, fn_pv_def] >>
  gvs[FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED
