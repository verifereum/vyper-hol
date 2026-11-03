Theory nonreentrantExit
Ancestors
  list rich_list
  loweringHalt fragExecMem instMemFrontier
  context compileEnv exprLoweringProps venomState venomInst venomExecSemantics

Theorem literal_tstore_mem_safe[local]:
  !id key s.
    inst_mem_below_frontier (mk_inst id TSTORE [Lit key; Lit 0w] []) s
Proof
  rpt gen_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem literal_tstore_step[local]:
  !id key s.
    step_inst_base (mk_inst id TSTORE [Lit key; Lit 0w] []) s =
    OK (tstore key 0w s)
Proof
  rpt gen_tac >> simp[mk_inst_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[exec_write2_def, eval_operand_def]
QED

Theorem empty_frag_mem_indexed[local]:
  !ctx st P Q R.
    (!s. P s ==> Q (s with vs_inst_idx := LENGTH st.cs_current_insts)) ==>
    frag_exec_mem ctx st st P Q R
Proof
  rw[frag_exec_mem_def] >> disj1_tac >> qexists_tac `s` >> simp[] >>
  conj_tac
  >- (qpat_x_assum `!s. P s ==> _` (qspec_then `s` mp_tac) >>
      qpat_x_assum `s.vs_inst_idx = _`
        (fn th => pure_once_rewrite_tac[GSYM th]) >> simp[]) >>
  rpt strip_tac >> qexists_tac `fuel` >> simp[]
QED

Theorem optional_unlock_frag_mem:
  !ctx nr nkey ut iv st st' P Q R.
    (if nr then compile_nonreentrant_unlock nkey ut iv else comp_return ())
      st = ((), st') /\
    (nr /\ ~iv ==> ut) /\
    (!s. P s ==>
         Q ((if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
              vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rpt strip_tac >> drule_all optional_unlock_code >> strip_tac >>
  Cases_on `nr /\ ~iv`
  >- (gvs[] >> irule frag_exec_mem_step >> simp[] >>
      simp[literal_tstore_mem_safe, literal_tstore_step, is_terminator_def]) >>
  gvs[] >> irule empty_frag_mem_indexed >> simp[]
QED
