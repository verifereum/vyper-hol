(* Clean unary scalar operands at a joint boundary. *)
Theory o1LowerDloadJointScalar
Ancestors
  o1LowerDloadJointAssign o1LowerDloadGhost o1LowerDloadOpaque
  o1LowerDloadJointRelation o1LowerDloadOccurrence ptrDiscipline
  pointerConfinedDefs memLocDefs unitShapeDefs o1PassContract
  venomInst finite_map list pred_set contextCodegenRel irSupply

Theorem ld_unary_no_provenance:
  ptr_use_ok P pv inst /\ FDOM G SUBSET pv /\
  MEM inst.inst_opcode [ISZERO; NOT] /\ MEM op inst.inst_operands ==>
  op_prov G op = NONE
Proof
  strip_tac >> Cases_on `op` >> simp[op_prov_def] >>
  rename1 `FLOOKUP G v` >>
  Cases_on `FLOOKUP G v` >> simp[] >>
  `v IN pv` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
      mem_read_ops_def, mem_write_ops_def] >> metis_tac[]
QED

Theorem ld_joint_unary_operands_clean:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [ISZERO; NOT] ==>
  !op. MEM op inst.inst_operands ==>
    op_prov H op = NONE /\ op_taint tn op = {} /\
    eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  qpat_x_assum `ptr_discipline _ _ _`
    (strip_assume_tac o REWRITE_RULE [ptr_discipline_def]) >>
  drule frame_reachable_prov_support >>
  disch_then (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (gvs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `taint_ok fn tn inst s` by metis_tac[] >>
  `occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G` by
    fs[ld_joint_boundary_def, occurrence_annotation_ok_def] >>
  rpt strip_tac >>
  `op_prov G op = NONE` by (irule ld_unary_no_provenance >> metis_tac[]) >>
  `op_prov H op = NONE` by
    (drule occurrence_op_erasure >> disch_then (qspec_then `op` mp_tac) >>
     simp[occurrence_param_ok_def]) >>
  `op_taint tn op = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     gvs[taint_ok_def] >> metis_tac[]) >>
  `!v. op = Var v ==> MEM v (fn_ir_vars fn)` by
    (rpt strip_tac >>
      `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
        (fs[fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[]) >>
      simp[NoAsms, fn_ir_vars_def, block_ir_vars_def, MEM_FLAT, MEM_MAP] >>
      qexists_tac `FLAT (MAP inst_ir_vars bb.bb_instructions)` >>
      conj_tac >- (qexists_tac `bb` >> simp[]) >>
      simp[NoAsms, MEM_FLAT, MEM_MAP] >> qexists_tac `inst_ir_vars inst` >>
      conj_tac >- (qexists_tac `inst` >> simp[]) >>
      simp[inst_ir_vars_def, inst_uses_def] >> disj2_tac >>
      `MEM (Var v) inst.inst_operands` by metis_tac[] >>
      qpat_x_assum `MEM (Var v) _` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
      simp[operand_vars_APPEND, operand_vars_def, operand_var_def]) >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (rpt strip_tac >> gvs[] >>
     drule_all opaque_use_ok_retpc_use >>
     gvs[retpc_use_ok_def]) >>
  simp[] >> irule ld_joint_operand_clean >> metis_tac[]
QED
