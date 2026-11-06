Theory augAssignPtrScalarRun
Ancestors augAssignPtrScalarCertificate augAssignPtrScalarProbe
  augAssignPtrScalarJoin augAssignPtrInterfaces fragGasSeqPtr
  ptrDiscipline ptrSafeRun venomInst venomState venomExecSemantics
  finite_map pred_set list

Theorem scalar_available_clean:
  scalar_available A op /\
  (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) ==>
  op_prov G op = NONE /\ op_taint tn op = {}
Proof
  simp[scalar_available_def] >> rpt strip_tac >>
  gvs[op_prov_def, op_taint_def]
QED

Theorem scalar_out_metadata:
  scalar_shape i /\
  EVERY (\op. op_prov G op = NONE /\ op_taint tn op = {}) i.inst_operands ==>
  out_prov PG G i u = NONE /\ out_taint tn i s = {}
Proof
  simp[scalar_shape_def, scalar_binary_def, scalar_unary_def,
       LENGTH_EQ_NUM_compute] >>
  rpt strip_tac >> gvs[] >>
  simp[out_prov_def, first_prov_def, out_taint_def, AllCaseEqs(),
       shift_taint_def] >> metis_tac[optionTheory.option_nchotomy]
QED

Theorem scalar_step_prov:
  scalar_shape i /\
  EVERY (\op. op_prov G op = NONE /\ op_taint tn op = {}) i.inst_operands ==>
  (!v. MEM v i.inst_outputs ==>
    op_prov (step_prov PG G i u) (Var v) = NONE) /\
  (!v. ~MEM v i.inst_outputs ==>
    FLOOKUP (step_prov PG G i u) v = FLOOKUP G v)
Proof
  strip_tac >> drule_all scalar_out_metadata >> strip_tac >>
  Cases_on `i.inst_outputs` >>
  simp[step_prov_def, set_prov_def, op_prov_def, FLOOKUP_DRESTRICT]
QED

Theorem scalar_step_var_taint:
  scalar_shape i /\
  EVERY (\op. op_prov G op = NONE /\ op_taint tn op = {}) i.inst_operands ==>
  (!v. MEM v i.inst_outputs ==>
    op_taint (step_taint i s u tn) (Var v) = {}) /\
  (!v. ~MEM v i.inst_outputs ==>
    op_taint (step_taint i s u tn) (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule_all scalar_out_metadata >> strip_tac >>
  gvs[scalar_shape_def, LENGTH_EQ_NUM_compute] >>
  simp[step_taint_def, set_var_taint_def, op_taint_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >> rpt strip_tac >> gvs[]
QED

