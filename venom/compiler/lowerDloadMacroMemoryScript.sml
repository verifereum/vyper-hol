Theory lowerDloadMacroMemory
Ancestors
  lowerDloadMacroBoundary lowerDloadPhaseBoundary lowerDloadRelocation ptrDiscipline
  regularCallEmitSim regularMemorySim codegenRel
  venomState venomExecSemantics finite_map words list pred_set

Theorem ld_read_memory_singleton[local]:
  read_memory b 1 s = [read_byte b s.vs_memory]
Proof
  simp[read_memory_def, venom_returndata_read_byte, GENLIST]
QED

Theorem ld_read_memory_write_outside:
  LENGTH bytes <= sz /\ (b < p \/ p + sz <= b) ==>
  read_memory b 1 (write_memory_with_expansion p bytes s) = read_memory b 1 s
Proof
  strip_tac >> simp[ld_read_memory_singleton, read_byte_write_memory_with_expansion] >>
  `~(p <= b /\ b < p + LENGTH bytes)` by decide_tac >> simp[]
QED

Theorem ld_load_first_outside:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\ p + 32 < dimword (:256) /\
  ((FLOOKUP t0.vs_allocas a.inst_id = NONE /\ p = t0.vs_alloca_next) \/
   FLOOKUP t0.vs_allocas a.inst_id = SOME (p,32)) /\
  ld_target_prefix C [a;b;c;d] t0 un (SUC 0) t u ==>
  eval_operand (Var av) t = SOME (n2w p) /\
  (!k. k < p \/ p + 32 <= k ==>
    read_memory k 1 t = read_memory k 1 t0 /\
    (k IN u.t_mem <=> k IN un.t_mem))
Proof
  strip_tac >> drule_all ld_load_first_prefix >>
  disch_then (fn th => gvs[th]) >>
  simp[ld_macro_operand_pc, eval_operand_def, lookup_var_def, update_var_def,
    FLOOKUP_UPDATE, read_memory_def, step_taint_def, mem_taint_def,
    new_site_bytes_def, step_writes_def, written_taint_def,
    source_memory_write_ranges_def, range_bytes_def] >>
  rpt strip_tac >> gvs[FLOOKUP_UPDATE, FLOOKUP_DEF] >>
  simp[AllCaseEqs(), SF CONJ_ss] >> decide_tac
QED

Theorem ld_load_second_outside:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\ p + 32 < dimword (:256) /\
  ((FLOOKUP t0.vs_allocas a.inst_id = NONE /\ p = t0.vs_alloca_next) \/
   FLOOKUP t0.vs_allocas a.inst_id = SOME (p,32)) /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\
  (!v. off = Var v ==> v <> av) /\
  ld_target_prefix C [a;b;c;d] t0 un (SUC (SUC 0)) t u ==>
  eval_operand (Var av) t = SOME (n2w p) /\
  (!k. k < p \/ p + 32 <= k ==>
    read_memory k 1 t = read_memory k 1 t0 /\
    (k IN u.t_mem <=> k IN un.t_mem))
Proof
  strip_tac >> drule_all ld_load_second_prefix >>
  disch_then (fn th => gvs[th]) >>
  `eval_operand (Var av) (update_var bv (x + y) r) = eval_operand (Var av) r` by
    (gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  qmatch_goalsub_abbrev_tac `SOME (n2w ptr)` >>
  drule_at (Pat `ld_target_prefix _ _ _ _ _ _ _`) (SRULE [] ld_load_first_outside) >>
  disch_then (qspec_then `ptr` mp_tac) >> simp[Abbr `ptr`] >> strip_tac >>
  simp[ld_macro_operand_pc, read_memory_def, update_var_def,
    step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
    written_taint_def, source_memory_write_ranges_def, range_bytes_def,
    FLOOKUP_DEF] >>
  gvs[read_memory_def, SF CONJ_ss] >> first_assum ACCEPT_TAC
QED

Theorem ld_read_memory_pc[local]:
  read_memory k sz (s with vs_inst_idx := n) = read_memory k sz s
Proof
  simp[read_memory_def]
QED

Theorem ld_copy_operand[local]:
  eval_operand op (write_memory_with_expansion p bytes s) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def, write_memory_with_expansion_def]
QED

Theorem ld_load_third_outside:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\ p + 32 < dimword (:256) /\
  ((FLOOKUP t0.vs_allocas a.inst_id = NONE /\ p = t0.vs_alloca_next) \/
   FLOOKUP t0.vs_allocas a.inst_id = SOME (p,32)) /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\
  (!v. off = Var v ==> v <> av) /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  ld_target_prefix C [a;b;c;d] t0 un (SUC (SUC (SUC 0))) t u ==>
  eval_operand (Var av) t = SOME (n2w p) /\
  (!k. k < p \/ p + 32 <= k ==>
    read_memory k 1 t = read_memory k 1 t0 /\
    (k IN u.t_mem <=> k IN un.t_mem))
Proof
  strip_tac >> drule_all ld_load_third_prefix >>
  disch_then (fn th => gvs[th]) >>
  qmatch_goalsub_abbrev_tac `SOME (n2w ptr)` >>
  drule_at (Pat `ld_target_prefix _ _ _ _ _ _ _`) (SRULE [] ld_load_second_outside) >>
  disch_then (qspec_then `ptr` mp_tac) >> simp[Abbr `ptr`] >> strip_tac >>
  gvs[] >>
  simp[ld_macro_operand_pc, ld_copy_operand, ld_read_memory_pc] >>
  (rpt gen_tac >> disch_tac >> conj_tac
  >- (irule EQ_TRANS >> qexists_tac `read_memory k 1 r` >> conj_tac
      >- (irule ld_read_memory_write_outside >> qexists_tac `32` >> simp[] >> decide_tac) >>
      metis_tac[]) >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
    written_taint_def, source_memory_write_ranges_def, sized_source_write_range_def,
    range_bytes_def, write_memory_with_expansion_def, FLOOKUP_DEF, SF CONJ_ss] >>
  simp[eval_operand_def, dimword_def] >>
  qpat_x_assum `k < _ \/ _ <= k` strip_assume_tac >> simp[] >> metis_tac[])
QED

Theorem ld_load_fourth_outside:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\ p + 32 < dimword (:256) /\
  ((FLOOKUP t0.vs_allocas a.inst_id = NONE /\ p = t0.vs_alloca_next) \/
   FLOOKUP t0.vs_allocas a.inst_id = SOME (p,32)) /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\
  (!v. off = Var v ==> v <> av) /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  ld_target_prefix C [a;b;c;d] t0 un (SUC (SUC (SUC (SUC 0)))) t u ==>
  !k. k < p \/ p + 32 <= k ==>
    read_memory k 1 t = read_memory k 1 t0 /\
    (k IN u.t_mem <=> k IN un.t_mem)
Proof
  strip_tac >> drule_all ld_load_fourth_prefix >>
  disch_then (fn th => gvs[th]) >>
  qmatch_asmsub_abbrev_tac `ptr + 32 < dimword (:256)` >>
  drule_at (Pat `ld_target_prefix _ _ _ _ _ _ _`) (SRULE [] ld_load_third_outside) >>
  disch_then (qspec_then `ptr` mp_tac) >> simp[Abbr `ptr`] >> strip_tac >>
  simp[ld_read_memory_pc, read_memory_def, update_var_def,
    step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
    written_taint_def, source_memory_write_ranges_def, range_bytes_def,
    FLOOKUP_DEF, SF CONJ_ss] >>
  gvs[read_memory_def] >> first_assum ACCEPT_TAC
QED

Theorem ld_load_prefix_outside:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\ p + 32 < dimword (:256) /\
  ((FLOOKUP t0.vs_allocas a.inst_id = NONE /\ p = t0.vs_alloca_next) \/
   FLOOKUP t0.vs_allocas a.inst_id = SOME (p,32)) /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\
  (!v. off = Var v ==> v <> av) /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  n <= 4 /\ ld_target_prefix C [a;b;c;d] t0 un n t u ==>
  !k. k < p \/ p + 32 <= k ==>
    read_memory k 1 t = read_memory k 1 t0 /\
    (k IN u.t_mem <=> k IN un.t_mem)
Proof
  strip_tac >>
  (Cases_on `n = 0` >- gvs[ld_target_prefix_empty] >>
   Cases_on `n = 1` >- (gvs[] >> metis_tac[SRULE [] ld_load_first_outside]) >>
   Cases_on `n = 2` >- (gvs[] >> metis_tac[SRULE [] ld_load_second_outside]) >>
   Cases_on `n = 3` >- (gvs[] >> metis_tac[SRULE [] ld_load_third_outside]) >>
   `n = 4` by decide_tac >> gvs[] >>
   metis_tac[SRULE [] ld_load_fourth_outside])
QED

Theorem ld_load_prefix_byte_rel:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\ p + 32 < dimword (:256) /\
  ((FLOOKUP t0.vs_allocas a.inst_id = NONE /\ p = t0.vs_alloca_next) \/
   FLOOKUP t0.vs_allocas a.inst_id = SOME (p,32)) /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\
  (!v. off = Var v ==> v <> av) /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  n <= 4 /\ ld_target_prefix C [a;b;c;d] t0 un n t u /\
  ld_byte_rel R tn.t_mem un.t_mem (\j. read_memory j 1 s) (\k. read_memory k 1 t0) /\
  (!j k. R j k ==> k < p \/ p + 32 <= k) ==>
  ld_byte_rel R tn.t_mem u.t_mem (\j. read_memory j 1 s) (\k. read_memory k 1 t)
Proof
  strip_tac >> qmatch_asmsub_abbrev_tac `ptr + 32 < dimword (:256)` >>
  drule_at (Pat `ld_target_prefix _ _ _ _ _ _ _`) ld_load_prefix_outside >>
  disch_then (qspec_then `ptr` mp_tac) >> simp[Abbr `ptr`] >> strip_tac >>
  fs[ld_byte_rel_def] >> metis_tac[]
QED

Theorem ld_dload_memory:
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\
  inst.inst_outputs = [out] /\ step_inst fuel C inst s = OK z ==>
  z.vs_memory = s.vs_memory /\ (step_taint inst s z tn).t_mem = tn.t_mem
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_read1_def, AllCaseEqs()] >>
  simp[update_var_def, step_taint_def, mem_taint_def, new_site_bytes_def,
    step_writes_def, source_memory_write_ranges_def, range_bytes_def,
    written_taint_def, FLOOKUP_DEF, SF CONJ_ss, EXTENSION]
QED

Theorem ld_load_completed_byte_rel:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\ p + 32 < dimword (:256) /\
  ((FLOOKUP t0.vs_allocas a.inst_id = NONE /\ p = t0.vs_alloca_next) \/
   FLOOKUP t0.vs_allocas a.inst_id = SOME (p,32)) /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\
  (!v. off = Var v ==> v <> av) /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  ld_target_prefix C' [a;b;c;d] t0 un (SUC (SUC (SUC (SUC 0)))) t u /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\ inst.inst_outputs = [out] /\
  ld_owned_vars V E AG AH tn un s t0 /\ (!v. off = Var v ==> v IN V) /\
  ld_byte_rel R tn.t_mem un.t_mem (\j. read_memory j 1 s) (\k. read_memory k 1 t0) /\
  (!j k. R j k ==> k < p \/ p + 32 <= k) ==>
  ?z. step_inst fuel C inst s = OK z /\
    ld_byte_rel R (step_taint inst s z tn).t_mem u.t_mem
      (\j. read_memory j 1 z) (\k. read_memory k 1 t)
Proof
  strip_tac >> drule_all ld_load_completed_source_success >>
  disch_then (qspecl_then [`fuel`,`C`] strip_assume_tac) >>
  (drule_all ld_dload_memory >>
   disch_then (qspec_then `tn` strip_assume_tac) >> qexists_tac `z` >> simp[] >>
   `ld_byte_rel R tn.t_mem u.t_mem (\j. read_memory j 1 s) (\k. read_memory k 1 t)`
     suffices_by (simp[ld_byte_rel_def, read_memory_def] >> metis_tac[]) >>
   metis_tac[ld_load_prefix_byte_rel, DECIDE ``SUC (SUC (SUC (SUC 0))) <= 4``])
QED
