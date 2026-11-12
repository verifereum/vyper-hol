Theory fmpStageOpFrameForwardAbort
Ancestors
  venomExecSemantics venomExecProps venomState
  venomInst contextCodegenRel finite_map list

Theorem fmp_forward_operand[local]:
  s.vs_labels = t.vs_labels /\
  (!v x. FLOOKUP s.vs_vars v = SOME x ==>
         ?y. FLOOKUP t.vs_vars v = SOME y) /\
  eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def] >> metis_tac[]
QED

Theorem fmp_forward_revert[local]:
  s.vs_labels = t.vs_labels /\
  (!v x. FLOOKUP s.vs_vars v = SOME x ==>
         ?y. FLOOKUP t.vs_vars v = SOME y) /\
  get_instruction bb s.vs_inst_idx = SOME ri /\
  get_instruction bb' t.vs_inst_idx = SOME ri /\
  ri.inst_opcode = REVERT /\
  exec_block fuel C bb s = Abort reason s1 ==>
  ?t1. exec_block fuel C' bb' t = Abort reason t1
Proof
  strip_tac >>
  qpat_x_assum `exec_block fuel C bb s = _` mp_tac >>
  simp[Once exec_block_def, step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  `?a. eval_operand off_op t = SOME a` by metis_tac[fmp_forward_operand] >>
  `?b. eval_operand sz_op t = SOME b` by metis_tac[fmp_forward_operand] >>
  simp[Once exec_block_def, step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >> simp[]
QED

Theorem fmp_forward_assign[local]:
  s.vs_labels = t.vs_labels /\
  (!v x. FLOOKUP s.vs_vars v = SOME x ==>
         ?y. FLOOKUP t.vs_vars v = SOME y) /\
  get_instruction bb s.vs_inst_idx = SOME cur /\
  get_instruction bb' t.vs_inst_idx = SOME cur /\
  cur.inst_opcode = ASSIGN /\
  exec_block fuel C bb s = Abort reason s1 ==>
  ?s2 t2.
    exec_block fuel C bb s2 = Abort reason s1 /\
    s2.vs_inst_idx = SUC s.vs_inst_idx /\
    t2.vs_inst_idx = SUC t.vs_inst_idx /\
    s2.vs_labels = t2.vs_labels /\
    (!v x. FLOOKUP s2.vs_vars v = SOME x ==>
           ?y. FLOOKUP t2.vs_vars v = SOME y) /\
    (!u. exec_block fuel C' bb' t2 = Abort reason u ==>
         exec_block fuel C' bb' t = Abort reason u)
Proof
  strip_tac >>
  qpat_x_assum `exec_block fuel C bb s = _` mp_tac >>
  simp[Once exec_block_def, step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs(), is_terminator_def] >> strip_tac >>
  `?w. eval_operand op1 t = SOME w` by metis_tac[fmp_forward_operand] >>
  qpat_x_assum `update_var out v s = s''` (SUBST_ALL_TAC o SYM) >>
  qexistsl_tac [`(update_var out v s) with vs_inst_idx := SUC s.vs_inst_idx`,
                `(update_var out w t) with vs_inst_idx := SUC t.vs_inst_idx`] >>
  simp[update_var_def] >> conj_tac
  >- (rpt strip_tac >> Cases_on `out = v'` >> gvs[FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  rpt strip_tac >> simp[Once exec_block_def, step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  gvs[is_terminator_def, update_var_def]
QED

Theorem fmp_forward_suffix_abort:
  !d s t bb bb' ri fuel C C' reason s1.
  s.vs_labels = t.vs_labels /\
  (!v x. FLOOKUP s.vs_vars v = SOME x ==>
         ?y. FLOOKUP t.vs_vars v = SOME y) /\
  (!k. k <= d ==> get_instruction bb (s.vs_inst_idx + k) =
                  get_instruction bb' (t.vs_inst_idx + k)) /\
  get_instruction bb (s.vs_inst_idx + d) = SOME ri /\
  ri.inst_opcode = REVERT /\
  (!k ii. k < d /\ get_instruction bb (s.vs_inst_idx + k) = SOME ii ==>
          ii.inst_opcode = ASSIGN) /\
  exec_block fuel C bb s = Abort reason s1 ==>
  ?t1. exec_block fuel C' bb' t = Abort reason t1
Proof
  Induct_on `d`
  >- (rpt gen_tac >> simp[] >> strip_tac >>
      irule fmp_forward_revert >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `exec_block fuel C bb s = _` mp_tac >>
      simp[Once exec_block_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME cur` >>
  `get_instruction bb' t.vs_inst_idx = SOME cur` by
    (qpat_x_assum `!k. k <= _ ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  `cur.inst_opcode = ASSIGN` by
    (qpat_x_assum `!k ii. _` (qspec_then `0` mp_tac) >> simp[]) >>
  drule_all fmp_forward_assign >>
  disch_then (qspec_then `C'` strip_assume_tac) >>
  `?u. exec_block fuel C' bb' t2 = Abort reason u` suffices_by metis_tac[] >>
  first_x_assum irule >>
  qexistsl_tac [`C`, `bb`, `ri`, `s2`, `s1`] >>
  simp[arithmeticTheory.ADD_CLAUSES] >>
  conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!k ii. _` (qspec_then `SUC k` mp_tac) >>
      simp[NoAsms, arithmeticTheory.ADD_CLAUSES] >>
      disch_then (qspec_then `ii` mp_tac) >>
      impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!k. k <= _ ==> _` (qspec_then `SUC k` mp_tac) >>
      simp[arithmeticTheory.ADD_CLAUSES]) >>
  gvs[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_COMM]
QED

Theorem fmp_forward_after_copy[local]:
  revert_forward_pair bb p j /\
  (!k. k <= j - p ==> get_instruction bb (p+k) = get_instruction bb' (q+k)) /\
  s.vs_inst_idx = SUC p /\ t.vs_inst_idx = SUC q /\
  s.vs_labels = t.vs_labels /\
  (!v x. FLOOKUP s.vs_vars v = SOME x ==>
         ?y. FLOOKUP t.vs_vars v = SOME y) /\
  exec_block fuel C bb s = Abort reason s1 ==>
  ?t1. exec_block fuel C' bb' t = Abort reason t1
Proof
  strip_tac >> irule fmp_forward_suffix_abort >>
  qpat_x_assum `revert_forward_pair _ _ _`
    (strip_assume_tac o REWRITE_RULE [revert_forward_pair_def]) >>
  qexistsl_tac [`C`, `bb`, `j - SUC p`, `inst2`, `s`, `s1`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `p < k + SUC p /\ k + SUC p < j` by decide_tac >> metis_tac[]) >>
  rpt strip_tac >>
  `SUC k <= j - p` by decide_tac >>
  qpat_x_assum `!k. k <= _ ==> _` (qspec_then `SUC k` mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem fmp_forward_available_abort:
  s.vs_labels = t.vs_labels /\
  (!v x. FLOOKUP s.vs_vars v = SOME x ==>
         ?y. FLOOKUP t.vs_vars v = SOME y) /\
  revert_forward_pair bb s.vs_inst_idx j /\
  (!k. k <= j - s.vs_inst_idx ==>
    get_instruction bb (s.vs_inst_idx+k) =
    get_instruction bb' (t.vs_inst_idx+k)) /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dst;src;sz] /\
  (!x. eval_operand src s = SOME x ==> eval_operand src t = SOME x) /\
  (!x. eval_operand sz s = SOME x ==> eval_operand sz t = SOME x) /\
  s.vs_returndata = t.vs_returndata /\
  exec_block fuel C bb s = Abort reason s1 ==>
  ?t1. exec_block fuel C' bb' t = Abort reason t1
Proof
  strip_tac >>
  `get_instruction bb' t.vs_inst_idx = SOME inst` by
    (qpat_x_assum `!k. k <= _ ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  qpat_x_assum `exec_block fuel C bb s = _` mp_tac >>
  simp[Once exec_block_def, step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs(), is_terminator_def] >> strip_tac >>
  `?w. eval_operand dst t = SOME w` by metis_tac[fmp_forward_operand] >>
  `eval_operand src t = SOME offset /\ eval_operand sz t = SOME size_val` by metis_tac[] >>
  pure_once_rewrite_tac[exec_block_def] >> pure_asm_rewrite_tac[] >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[is_terminator_def] >>
  qpat_x_assum `write_memory_with_expansion _ _ s = s''` (SUBST_ALL_TAC o SYM) >>
  irule fmp_forward_after_copy >>
  qexistsl_tac [`C`, `bb`, `j`, `s.vs_inst_idx`, `t.vs_inst_idx`,
    `(write_memory_with_expansion (w2n destOffset) (TAKE (w2n size_val) (DROP (w2n offset) t.vs_returndata)) s) with vs_inst_idx := SUC s.vs_inst_idx`, `s1`] >>
  simp[write_memory_with_expansion_def, write_memory_def]
QED
