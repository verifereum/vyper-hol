Theory frameRelocationMemory
Ancestors ptrDiscipline regularCallEmitSim venomMemProps codegenRel
  venomExecSemantics venomState venomInst list rich_list finite_map

(* Allocation is a cache operation, not a memory initialization. *)
Theorem exec_alloca_memory:
  exec_alloca inst s sz = OK s' ==> s'.vs_memory = s.vs_memory
Proof
  simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def]
QED

Theorem assign_memory:
  inst.inst_opcode = ASSIGN /\ step_inst_base inst s = OK s' ==>
  s'.vs_memory = s.vs_memory
Proof
  simp[step_inst_base_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def]
QED

(* The source is read in the pre-state, including its implicit zero tail.
   No disjointness premise is needed, even when destination overlaps source. *)
Theorem read_byte_mcopy:
  read_byte i (mcopy dst src n s).vs_memory =
  if dst <= i /\ i < dst + n then read_byte (src + (i - dst)) s.vs_memory
  else read_byte i s.vs_memory
Proof
  simp[mcopy_def, read_byte_write_memory_with_expansion, LENGTH_TAKE_EQ] >>
  IF_CASES_TAC >> simp[] >>
  `i - dst < n` by decide_tac >>
  simp[EL_TAKE, EL_APPEND_EQN, LENGTH_DROP, EL_DROP, EL_REPLICATE,
       read_byte_def] >>
  Cases_on `src + (i - dst) < LENGTH s.vs_memory` >> simp[]
QED

Theorem new_site_bytes_unchanged:
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  new_site_bytes s s' = {}
Proof
  rw[new_site_bytes_def, pred_setTheory.EXTENSION] >>
  fs[FLOOKUP_DEF, AllCaseEqs()]
QED

Theorem new_site_bytes_fresh:
  aid NOTIN FDOM s.vs_allocas /\
  s'.vs_allocas = s.vs_allocas |+ (aid, (b,sz)) /\
  s'.vs_fmp = s.vs_fmp ==>
  new_site_bytes s s' = {i | b <= i /\ i < b + sz}
Proof
  rw[new_site_bytes_def, pred_setTheory.EXTENSION, FLOOKUP_UPDATE] >>
  fs[FLOOKUP_DEF, AllCaseEqs()] >> metis_tac[]
QED

Theorem exec_alloca_cached_fields:
  exec_alloca inst s sz = OK s' /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME site ==>
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp
Proof
  simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def]
QED

Theorem exec_alloca_fresh_fields:
  exec_alloca inst s sz = OK s' /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
  s'.vs_allocas = s.vs_allocas |+
    (inst.inst_id, (s.vs_alloca_next, w2n sz)) /\
  s'.vs_fmp = s.vs_fmp
Proof
  simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def]
QED

Theorem allocation_mem_taint:
  inst.inst_opcode = ALLOCA ==>
  mem_taint tn inst s s' = tn.t_mem UNION new_site_bytes s s'
Proof
  strip_tac >>
  simp[mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       range_bytes_def] >>
  simp[written_taint_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[])
QED

Theorem exec_alloca_cached_taint:
  inst.inst_opcode = ALLOCA /\ exec_alloca inst s sz = OK s' /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME site ==>
  mem_taint tn inst s s' = tn.t_mem
Proof
  strip_tac >> drule_all exec_alloca_cached_fields >> strip_tac >>
  simp[allocation_mem_taint, new_site_bytes_unchanged]
QED

Theorem exec_alloca_fresh_taint:
  inst.inst_opcode = ALLOCA /\ exec_alloca inst s sz = OK s' /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
  mem_taint tn inst s s' = tn.t_mem UNION
    {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next + w2n sz}
Proof
  strip_tac >> drule_all exec_alloca_fresh_fields >> strip_tac >>
  `inst.inst_id NOTIN FDOM s.vs_allocas` by
    fs[FLOOKUP_DEF, AllCaseEqs()] >>
  simp[allocation_mem_taint] >>
  AP_TERM_TAC >> irule new_site_bytes_fresh >> simp[] >>
  qexists_tac `inst.inst_id` >> simp[]
QED
