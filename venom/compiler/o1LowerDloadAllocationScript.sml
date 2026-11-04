(* Semantic allocation/taint boundaries for LowerDload relocation. *)
Theory o1LowerDloadAllocation
Ancestors
  ptrDiscipline venomExecSemantics venomState finite_map pred_set list

Theorem fresh_allocation_byte_tainted:
  aid NOTIN FDOM s.vs_allocas /\
  FLOOKUP s'.vs_allocas aid = SOME (b,z) /\ i < z /\
  b+i NOTIN range_bytes (step_writes inst s s') ==>
  b+i IN (step_taint inst s s' tn).t_mem
Proof
  rpt strip_tac >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def] >>
  disj1_tac >> disj2_tac >> disj1_tac >> qexistsl_tac [`aid`, `b`, `z`] >> simp[]
QED

Theorem alloca_fresh_byte_tainted:
  inst.inst_opcode = ALLOCA /\ step_inst fuel C inst s = OK s' /\
  aid NOTIN FDOM s.vs_allocas /\
  FLOOKUP s'.vs_allocas aid = SOME (b,z) /\ i < z ==>
  b+i IN (step_taint inst s s' tn).t_mem
Proof
  rpt strip_tac >> irule fresh_allocation_byte_tainted >>
  simp[step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       range_bytes_def] >> metis_tac[]
QED

Theorem alloca_repeated_mem_taint:
  inst.inst_opcode = ALLOCA /\ step_inst fuel C inst s = OK s' /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,z) ==>
  (step_taint inst s s' tn).t_mem = tn.t_mem
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_alloca_def,
      AllCaseEqs()] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, update_var_def, range_bytes_def] >>
  simp[FLOOKUP_DEF, EXTENSION] >> metis_tac[]
QED

Theorem positive_interval_identity:
  !S p q (b:num) (c:num) (d:num) (z:num). (!p q b c z b' c' z'.
    FLOOKUP S p = SOME (b,c,z) /\ FLOOKUP S q = SOME (b',c',z') /\
    p <> q /\ 0 < z /\ 0 < z' ==> b+z <= b' \/ b'+z' <= b) /\
  FLOOKUP S p = SOME (b,c,z) /\ FLOOKUP S q = SOME (b,d,z) /\
  0 < z ==> p = q
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  first_x_assum (qspecl_then [`p`, `q`] mp_tac) >>
  simp[] >> decide_tac
QED

