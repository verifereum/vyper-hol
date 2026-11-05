Theory lowerDloadAffineProducer
Ancestors
  lowerDloadProvenanceSupport lowerDloadOrdinaryExecution lowerDloadOwnership
  lowerDloadReachableDiscipline ptrDiscipline pointerConfinedDefs
  contextCodegenRel memLocDefs venomInst list pred_set

Theorem ld_annotated_affine_prov:
  (!f. MEM f ctx.ctx_functions ==> fn_ptr_ok P f) /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn i s /\
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\
  i.inst_operands = [a;b] ==>
  ld_op_prov AG b = NONE \/
    (i.inst_opcode = ADD /\ ld_op_prov AG a = NONE)
Proof
  strip_tac >>
  `MEM fn ctx.ctx_functions` by metis_tac[ld_annotated_fn_member] >>
  `fn_ptr_ok P fn` by metis_tac[] >>
  `?bb. MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def] >> metis_tac[EL_MEM]) >>
  `(~(?u v. a = Var u /\ b = Var v /\
       u IN fn_pv P fn /\ v IN fn_pv P fn)) /\
    (i.inst_opcode = SUB ==> !v. b = Var v ==> v NOTIN fn_pv P fn)` by
    (fs[fn_ptr_ok_def, affine_pointer_ops_def, fn_pv_def] >> metis_tac[]) >>
  (Cases_on `!v. b = Var v ==> v NOTIN fn_pv P fn`
  >- (disj1_tac >> irule ld_annotated_scalar_prov >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  disj2_tac >>
  `i.inst_opcode = ADD` by metis_tac[] >> simp[] >>
  irule ld_annotated_scalar_prov >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[])
QED

Theorem ld_annotated_affine_backward:
  (!f. MEM f ctx.ctx_functions ==> fn_ptr_ok P f) /\
  ptr_discipline lo ctx vs0 /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn i s /\
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\
  i.inst_operands = [a;b] /\ i.inst_outputs = [out] /\
  ld_owned_vars V E AG BH tn un s t /\
  (!v. a = Var v \/ b = Var v ==> v IN V) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS ctx i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `taint_ok fn tn i s` by metis_tac[ld_annotated_taint_ok] >>
  `!op. MEM op i.inst_operands ==> op_taint tn op = {}` by
    (rpt strip_tac >> irule ld_taint_operand_clean >>
     qexistsl [`fn`, `i`, `s`] >> simp[]) >>
  `op_taint tn a = {} /\ op_taint tn b = {}` by metis_tac[MEM] >>
  `ld_op_prov AG b = NONE \/
    (i.inst_opcode = ADD /\ ld_op_prov AG a = NONE)` by
    metis_tac[ld_annotated_affine_prov] >>
  irule ld_owned_offset_cases_backward >> simp[] >> metis_tac[]
QED
