Theory staticAbortOptPruneJumpsStopped
Ancestors
  staticAbortOptMergeIszeroSync staticAbortOptMergeIszeroOutside
  staticAbortProtectedTraceCoverage asmSplice asmSymPc asmSymSem
  codegenSymRel asmOptimizer asmWf asmSem arithmetic list

Theorem prune_jump_site_stopped_prefix:
  !p. p = pre ++ [AsmPushLabel x; AsmOp "JUMP"; AsmLabel x] ++ tail ==>
  !q. q = pre ++ [AsmLabel x] ++ tail ==>
  !b. b = LENGTH pre ==>
  !c. c = ss.sym_base.as_pc ==>
  asm_static_wf p /\ s.as_pc = 0 /\
  sym_steps p env n (sym_init s) = SymOK ss ==>
  if c = b+1 then
    ?h j u. n = h+1 /\ sym_steps p env h (sym_init s) = SymOK u /\
      u.sym_base.as_pc = b /\ sym_steps p env 1 u = SymOK ss /\
      sym_steps q env j (sym_init s) = SymOK u /\
      ss = (sym_with_pc (b+1) u with sym_stack := Lab x 0 :: u.sym_stack)
  else
    ?j. sym_steps q env j (sym_init s) = SymOK (sym_with_pc (splice_pc b 2 0 c) ss)
Proof
  CONV_TAC (REPEATC Unwind.UNWIND_FORALL_CONV) >> strip_tac >>
  qabbrev_tac `b = LENGTH pre` >>
  qabbrev_tac `p = pre ++ [AsmPushLabel x; AsmOp "JUMP"; AsmLabel x] ++ tail` >>
  qabbrev_tac `q = pre ++ [AsmLabel x] ++ tail` >>
  `b+1 < LENGTH p /\ EL b p = AsmPushLabel x /\ EL (b+1) p = AsmOp "JUMP"` by
    simp[Abbr `p`, Abbr `b`, EL_APPEND_EQN] >>
  `~MEM (AsmLabel x) pre` by (
    irule asm_labels_unique_append_not_mem >>
    qexists_tac `AsmPushLabel x :: AsmOp "JUMP" :: AsmLabel x :: tail` >>
    simp[] >>
    `asm_labels_unique p` by fs[asm_static_wf_def] >>
    qpat_x_assum `asm_labels_unique p` mp_tac >>
    simp[Abbr `p`, rich_listTheory.APPEND_ASSOC_CONS]) >>
  `INDEX_OF (AsmLabel x) p = SOME (b+2)` by
    simp[Abbr `p`, Abbr `b`, INDEX_OF_APPEND, INDEX_OF_CONS] >>
  `!u. u.sym_base.as_pc = b ==>
      sym_steps p env 1 u =
      SymOK (sym_with_pc (b+1) u with sym_stack := Lab x 0 :: u.sym_stack)` by (
    rpt strip_tac >> simp[Once sym_steps_pos, sym_step_push_label, sym_steps_def,
                          asm_next_def, sym_with_pc_def]) >>
  `!u. u.sym_base.as_pc = b ==>
      sym_steps p env 2 u = SymOK (sym_with_pc (b+2) u)` by (
    rpt strip_tac >>
    qspecl_then [`1`, `1`, `u`] mp_tac
      (Q.INST [`p` |-> `p`, `env` |-> `env`] sym_steps_add) >>
    simp[] >> disch_then (once_rewrite_tac o single) >>
    simp[Once sym_steps_pos, sym_with_pc_def, sym_steps_def,
         sym_step_def, sym_step_op_def, sym_jump_def, sym_jump_dest_def]) >>
  `!h u. sym_steps p env h (sym_init s) = SymOK u /\
         ~(b < u.sym_base.as_pc /\ u.sym_base.as_pc < b+2) ==>
         ?j. sym_steps q env j (sym_init s) =
             SymOK (sym_with_pc (splice_pc b 2 0 u.sym_base.as_pc) u)` by
    (suspend "replay") >>
  reverse IF_CASES_TAC
  >- (`~(b < ss.sym_base.as_pc /\ ss.sym_base.as_pc < b+2)` by decide_tac >>
      first_x_assum (qspecl_then [`n`, `ss`] mp_tac) >> simp[]) >>
  suspend "interior"
QED

Resume prune_jump_site_stopped_prefix[replay]:
  mp_tac (Q.INST [`pat` |-> `[AsmPushLabel x; AsmOp "JUMP"]`,
                  `repl` |-> `[]`, `tail` |-> `AsmLabel x :: tail`]
    (CONV_RULE (REPEATC (FIRST_CONV
       [Unwind.UNWIND_FORALL_CONV, REWR_CONV LET_THM THENC BETA_CONV]))
       merge_iszero_synchronized_replay)) >>
  unabbrev_all_tac >>
  rule_assum_tac (REWRITE_RULE[rich_listTheory.APPEND_ASSOC_CONS, APPEND]) >>
  simp[rich_listTheory.APPEND_ASSOC_CONS] >>
  (impl_tac >- (
    conj_tac >- (
      rpt strip_tac >> `i = LENGTH pre + 1` by decide_tac >>
      gvs[asm_reachable_marker_def]) >>
    conj_tac >- (
      rpt strip_tac >> `i = LENGTH pre` by decide_tac >> gvs[]) >>
    conj_tac >- (
      rpt strip_tac >>
      irule (SRULE [] (Q.SPECL [`pre`, `[AsmPushLabel x; AsmOp "JUMP"]`, `[]`,
                                `AsmLabel x :: tail`]
        (CONV_RULE (REDEPTH_CONV (FIRST_CONV [Unwind.UNWIND_FORALL_CONV,
                                               REWR_CONV LET_THM, BETA_CONV]))
          merge_iszero_outside_fetch_ok))) >>
      simp[rich_listTheory.APPEND_ASSOC_CONS]) >>
    rpt strip_tac >>
    `v = sym_with_pc (LENGTH pre + 2) u` by (
      qpat_x_assum `!u. _ ==> sym_steps _ _ 2 u = _`
        (qspec_then `u` mp_tac) >> simp[]) >>
    qexists_tac `0` >>
    simp[sym_steps_def, splice_pc_def, sym_with_pc_def,
         sym_state_component_equality, asm_state_component_equality])) >>
  simp[]
QED

Resume prune_jump_site_stopped_prefix[interior]:
  `1 <= n /\ ?u. sym_steps p env (n-1) (sym_init s) = SymOK u /\
         u.sym_base.as_pc = b /\ sym_steps p env 1 u = SymOK ss` by (
    qspecl_then [`n`, `b`, `b+1`, `s`, `ss`] mp_tac
      (Q.INST [`p` |-> `p`, `env` |-> `env`] protected_prefix_window_entry) >>
    simp[] >> disch_then irule >> rpt strip_tac >>
    `j = b+1` by decide_tac >> gvs[asm_reachable_marker_def]) >>
  `sym_with_pc (splice_pc b 2 0 u.sym_base.as_pc) u = u` by
    simp[splice_pc_def, sym_with_pc_def, sym_state_component_equality,
         asm_state_component_equality] >>
  qpat_x_assum `!h u. sym_steps p env h _ = _ /\ _ ==> _`
    (qspecl_then [`n-1`, `u`] mp_tac) >>
  simp[] >> strip_tac >>
  `n-1+1 = n` by decide_tac >>
  qexistsl_tac [`n-1`, `j`, `u`] >> simp[] >>
  qpat_x_assum `!u. _ ==> sym_steps p env 1 u = _`
    (qspec_then `u` mp_tac) >> simp[]
QED

Finalise prune_jump_site_stopped_prefix
