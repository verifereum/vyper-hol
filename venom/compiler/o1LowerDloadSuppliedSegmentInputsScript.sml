Theory o1LowerDloadSuppliedSegmentInputs
Ancestors
  o1LowerDloadPtrDiscipline o1LowerDloadJointScalar o1LowerDloadJointRelation o1LowerDloadOccurrence
  o1LowerDloadGhost o1LowerDloadOpaque o1LowerDloadJointAssign
  ptrDiscipline pointerConfinedDefs memLocDefs unitShapeDefs o1PassContract
  venomInst finite_map list pred_set irSupply venomExecSemantics contextCodegenRel

Theorem ld_data_load_inputs_untainted:
  taint_ok fn tn inst s /\ MEM inst.inst_opcode [DLOAD;DLOADBYTES] ==>
  !op. MEM op inst.inst_operands ==> op_taint tn op = {}
Proof
  strip_tac >> gvs[taint_ok_def] >> metis_tac[]
QED

Theorem ld_joint_dload_inputs_clean:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ inst.inst_opcode = DLOAD ==>
  !op. MEM op inst.inst_operands ==>
    op_prov H op = NONE /\ op_taint tn op = {} /\
    eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule ld_joint_scalar_operands_clean >>
  gvs[is_pointer_preserving_op_def, mem_read_ops_def,
      mem_write_ops_def, retpc_use_ok_def] >>
  metis_tac[ld_data_load_inputs_untainted, MEM]
QED

Theorem ld_joint_dloadbytes_inputs_clean:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;src;sz] ==>
  !op. MEM op [src;sz] ==>
    op_prov H op = NONE /\ op_taint tn op = {} /\
    eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  qpat_x_assum `ptr_discipline _ _ _`
    (strip_assume_tac o MATCH_MP ptr_discipline_fn_ptr_ok) >>
  drule frame_reachable_prov_support >>
  disch_then (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (gvs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G` by
    fs[ld_joint_boundary_def, occurrence_annotation_ok_def] >>
  `!op. MEM op [src;sz] ==> op_prov G op = NONE` by
    (rpt strip_tac >> Cases_on `op` >> simp[op_prov_def] >>
     rename1 `FLOOKUP G v` >> Cases_on `FLOOKUP G v` >> simp[] >>
     `v IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
     gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_read_ops_def, mem_write_ops_def] >>
     first_x_assum (qspec_then `v` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (CONJUNCTS_THEN assume_tac) >> gvs[] >>
     qpat_x_assum `(if _ then _ else _) = []` mp_tac >>
     IF_CASES_TAC >> simp[]) >>
  rpt strip_tac >>
  `MEM op inst.inst_operands` by simp[] >>
  `op_prov H op = NONE` by
    (drule occurrence_op_erasure >> disch_then (qspec_then `op` mp_tac) >>
     simp[occurrence_param_ok_def]) >>
  `op_taint tn op = {}` by metis_tac[ld_data_load_inputs_untainted, MEM] >>
  `!v. ~retpc_use_ok inst v` by simp[retpc_use_ok_def] >>
  `!v. op = Var v ==> MEM v (fn_ir_vars fn)` by
    metis_tac[ld_active_operand_ir_var] >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    metis_tac[ld_active_operand_non_retpc] >>
  gvs[] >>
  drule ld_joint_operand_clean >>
  disch_then irule >> simp[]
QED
