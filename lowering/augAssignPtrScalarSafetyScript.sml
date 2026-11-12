Theory augAssignPtrScalarSafety
Ancestors augAssignPtrScalarExec augAssignPtrScalarCertificate codegenRel contextCodegenRel
  ptrDiscipline ptrSafeRun
  venomExecSemantics venomInst venomState finite_map pred_set list

Theorem scalar_access_taint_ok:
  scalar_shape i /\
  EVERY (\op. op_prov G op = NONE /\ op_taint tn op = {}) i.inst_operands ==>
  access_ok 0 G fn i s /\ taint_ok fn tn i s
Proof
  simp[scalar_shape_def, scalar_binary_def, scalar_unary_def,
       LENGTH_EQ_NUM_compute] >> strip_tac >> gvs[] >>
  simp[access_ok_def, taint_ok_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem scalar_ptr_inst_ok:
  scalar_shape i /\
  EVERY (\op. op_prov G op = NONE /\ op_taint tn op = {}) i.inst_operands /\
  ~ctx_has_dalloca ctx ==> ptr_inst_ok D 0 fuel ctx fn G tn i s
Proof
  strip_tac >> drule_all scalar_access_taint_ok >> strip_tac >>
  drule scalar_shape_control >> strip_tac >>
  drule scalar_step_shape >> strip_tac >>
  simp[ptr_inst_ok_def, allocas_from_def, step_inst_non_invoke] >>
  rpt strip_tac >> drule_all (cj 1 scalar_exec_result) >>
  strip_tac >> gvs[update_var_def]
QED

Theorem scalar_ambient_taint:
  scalar_shape i /\ step_inst_base i s = OK u ==>
  (step_taint i s u tn).t_mem = tn.t_mem /\
  (step_taint i s u tn).t_stor = tn.t_stor /\
  (step_taint i s u tn).t_trans = tn.t_trans /\
  (step_taint i s u tn).t_imm = tn.t_imm
Proof
  strip_tac >> drule scalar_step_shape >> strip_tac >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp` by metis_tac[] >>
  `new_site_bytes s u = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  `i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
   i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> SSTORE /\
   i.inst_opcode <> TSTORE /\ i.inst_opcode <> ISTORE` by
    gvs[scalar_shape_def, scalar_binary_def, scalar_unary_def] >>
  `source_memory_write_ranges i s = [] /\ written_taint tn i s = {}` by
    (gvs[scalar_shape_def, scalar_binary_def, scalar_unary_def,
         LENGTH_EQ_NUM_compute] >>
     simp[source_memory_write_ranges_def, written_taint_def]) >>
  simp[step_taint_def, mem_taint_def, store_taint_def, imm_taint_def,
       adopt_reset_def, step_writes_def, range_bytes_def]
QED
