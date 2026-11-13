(* Local masked-memory boundaries for paired LowerDload steps. *)
Theory lowerDloadPairing
Ancestors
  lowerDloadLifetime lowerDloadOwnership ptrDiscipline
  venomExecSemantics venomState codegenRel finite_map pred_set list words

Theorem ld_alloca_memory:
  i.inst_outputs = [out] /\ exec_alloca i s n = OK s' ==>
  s'.vs_memory = s.vs_memory
Proof
  strip_tac >>
  gvs[exec_alloca_def, AllCaseEqs(), update_var_def]
QED

Theorem ld_alloca_mask:
  i.inst_opcode = ALLOCA ==>
  mem_taint tn i s s' = tn.t_mem UNION new_site_bytes s s'
Proof
  strip_tac >>
  simp[mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       range_bytes_def, written_taint_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  Cases_on `t` >> simp[]
QED

Theorem ld_alloca_fresh_byte_rel:
  i.inst_opcode = ALLOCA /\ j.inst_opcode = ALLOCA /\
  i.inst_outputs = [out] /\ j.inst_outputs = [out'] /\
  FLOOKUP s.vs_allocas i.inst_id = NONE /\
  FLOOKUP t.vs_allocas j.inst_id = NONE /\
  exec_alloca i s n = OK s' /\ exec_alloca j t n = OK t' /\
  ld_byte_rel R tn.t_mem un.t_mem
    (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  (!a b. R a b ==> b NOTIN new_site_bytes t t') ==>
  ld_byte_rel
    (\a b. R a b \/ ?d. d < w2n n /\
       a = s.vs_alloca_next+d /\ b = t.vs_alloca_next+d)
    (mem_taint tn i s s') (mem_taint un j t t')
    (\a. read_memory a 1 s') (\b. read_memory b 1 t')
Proof
  strip_tac >>
  `s'.vs_memory = s.vs_memory /\ t'.vs_memory = t.vs_memory` by
    metis_tac[ld_alloca_memory] >>
  simp[ld_alloca_mask, read_memory_def] >>
  ho_match_mp_tac ld_byte_rel_fresh_extension >>
  conj_tac >- gvs[read_memory_def] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> gvs[] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule (ld_new_site_fresh_range |> Q.INST [`b` |-> `s.vs_alloca_next`, `k` |-> `d`]) >>
  qexistsl [`i.inst_id`, `w2n n`] >>
  gvs[FLOOKUP_DEF, exec_alloca_def, update_var_def, FLOOKUP_UPDATE]
QED
