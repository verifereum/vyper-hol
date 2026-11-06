Theory augAssignPtrScalarRun
Ancestors augAssignPtrScalarSafety augAssignPtrScalarCertificate augAssignPtrScalarProbe
  augAssignPtrScalarJoin augAssignPtrInterfaces fragGasSeqPtr
  ptrDiscipline ptrSafeRun venomInst venomState venomExecSemantics
  finite_map pred_set list fragExec exprLoweringProps venomInstProofs instIdxIndep

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

Theorem scalar_step_clean:
  scalar_shape i /\
  EVERY (scalar_available A) i.inst_operands /\
  (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) ==>
  !v. v IN A UNION set i.inst_outputs ==>
    op_prov (step_prov PG G i u) (Var v) = NONE /\
    op_taint (step_taint i s u tn) (Var v) = {}
Proof
  strip_tac >>
  `EVERY (\op. op_prov G op = NONE /\ op_taint tn op = {}) i.inst_operands`
    by (gvs[EVERY_MEM] >> metis_tac[scalar_available_clean]) >>
  drule_all scalar_step_prov >> strip_tac >>
  drule_all scalar_step_var_taint >> strip_tac >>
  rpt strip_tac >> Cases_on `MEM v i.inst_outputs` >>
  gvs[op_prov_def] >> metis_tac[]
QED

Theorem scalar_code_inst_seq_ptr:
  !code A G tn s.
    scalar_code A code /\
    (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
    ~ctx_has_dalloca ctx ==>
    ?H tm. inst_seq_ptr D 0 ctx fn PG G tn code s H tm
Proof
  Induct >- simp[inst_seq_ptr_def] >>
  rpt gen_tac >> simp[scalar_code_def] >> strip_tac >>
  `EVERY (\op. op_prov G op = NONE /\ op_taint tn op = {}) h.inst_operands`
    by (gvs[EVERY_MEM] >> metis_tac[scalar_available_clean]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn h s` by metis_tac[scalar_ptr_inst_ok] >>
  Cases_on `step_inst_base h s` >> simp[inst_seq_ptr_def] >>
  first_x_assum irule >> simp[] >> qexists `A UNION set h.inst_outputs` >>
  reverse conj_tac >- simp[] >>
  ho_match_mp_tac scalar_step_clean >> simp[]
QED

Theorem scalar_seq_metadata_frame:
  !code A G tn s H tm.
    scalar_code A code /\
    (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
    inst_seq_ptr D 0 ctx fn PG G tn code s H tm ==>
    (!v. ~MEM v (FLAT (MAP (\i. i.inst_outputs) code)) ==>
       FLOOKUP H v = FLOOKUP G v /\
       op_taint tm (Var v) = op_taint tn (Var v)) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm
Proof
  Induct >- simp[inst_seq_ptr_def] >>
  rpt gen_tac >> simp[scalar_code_def, inst_seq_ptr_def] >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  `EVERY (\op. op_prov G op = NONE /\ op_taint tn op = {}) h.inst_operands`
    by (gvs[EVERY_MEM] >> metis_tac[scalar_available_clean]) >>
  `!w. w IN A UNION set h.inst_outputs ==>
    op_prov (step_prov PG G h v) (Var w) = NONE /\
    op_taint (step_taint h s v tn) (Var w) = {}`
    by (ho_match_mp_tac scalar_step_clean >> simp[]) >>
  first_x_assum drule >> disch_then drule >> simp[] >>
  disch_then drule >> strip_tac >>
  drule_all scalar_ambient_taint >> strip_tac >>
  drule_all scalar_step_prov >> strip_tac >>
  drule_all scalar_step_var_taint >> strip_tac >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED

Theorem scalar_seq_success_clean:
  !code A G tn s H tm t.
    scalar_code A code /\
    (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
    inst_seq_ptr D 0 ctx fn PG G tn code s H tm /\
    run_inst_seq code s = OK t ==>
    !v. v IN A UNION BIGUNION (set (MAP (\i. set i.inst_outputs) code)) ==>
      op_prov H (Var v) = NONE /\ op_taint tm (Var v) = {}
Proof
  Induct >- simp[inst_seq_ptr_def, run_inst_seq_def] >>
  rpt gen_tac >> simp[scalar_code_def, inst_seq_ptr_def, run_inst_seq_def] >>
  strip_tac >> Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK u` >>
  `!w. w IN A UNION set h.inst_outputs ==>
    op_prov (step_prov PG G h u) (Var w) = NONE /\
    op_taint (step_taint h s u tn) (Var w) = {}`
    by (ho_match_mp_tac scalar_step_clean >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code`
    by metis_tac[scalar_code_nonterminators] >>
  `run_inst_seq code (u with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (t with vs_inst_idx := SUC s.vs_inst_idx)`
    by simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  first_x_assum drule >> disch_then drule >> simp[] >>
  disch_then drule >> disch_then drule >>
  simp[UNION_ASSOC] >> metis_tac[]
QED
