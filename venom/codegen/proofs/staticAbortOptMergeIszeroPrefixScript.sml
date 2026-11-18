Theory staticAbortOptMergeIszeroPrefix
Ancestors
  staticAbortOptMergeIszeroVisits staticAbortOptMergeIszeroOutside
  staticAbortOptMergeIszeroSync staticAbortProtectedTraceCoverage
  codegenSymRel asmSplice asmSymPc asmSymSem asmOptimizer asmSem arithmetic list

Theorem merge_iszero_one_stopped_prefix:
  let b = LENGTH pre; m = LENGTH pat; c = ss.sym_base.as_pc in
  let r = splice_pc b m (LENGTH repl) in
  p = pre ++ pat ++ tail /\ q = pre ++ repl ++ tail /\
  ((?x. asm_returns_zero_or_one x /\
        pat = [x; AsmOp "ISZERO"; AsmOp "ISZERO"] /\ repl = [x]) \/
   (?l. pat = [AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"] /\
        repl = [AsmPushLabel l; AsmOp "JUMPI"])) /\
  s.as_pc = 0 /\ sym_steps p env n (sym_init s) = SymOK ss ==>
  ?h j u. h <= n /\ sym_steps p env h (sym_init s) = SymOK u /\
    sym_steps p env (n-h) u = SymOK ss /\
    (if b < c /\ c < b+m then
       n-h = c-b /\ u.sym_base.as_pc = b /\
       sym_steps q env j (sym_init s) = SymOK u /\
       (m = 3 ==> ?v w stk.
          sym_step p env (HD pat) u = SymOK v /\
          sym_step q env (HD pat) u = SymOK v /\
          v.sym_base.as_pc = b+1 /\ v.sym_stack = Val w::stk /\
          (w=0w \/ w=1w) /\ sym_steps q env (j+1) (sym_init s) = SymOK v /\
          sym_steps p env (n-h-1) v = SymOK ss)
     else h=n /\ u=ss /\
          sym_steps q env j (sym_init s) = SymOK (sym_with_pc (r c) ss))
Proof
  rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!i. LENGTH pre <= i /\ i < LENGTH pre + LENGTH pat ==>
       i < LENGTH p /\ ~asm_reachable_marker (EL i p) /\
       (i+1 < LENGTH pre + LENGTH pat ==>
        EL i p <> AsmOp "JUMP" /\ EL i p <> AsmOp "JUMPI")` by (
    qx_gen_tac `i` >> strip_tac >>
    qabbrev_tac `d = i - LENGTH pre` >>
    `d < LENGTH pat /\ i = LENGTH pre + d` by (simp[Abbr `d`] >> decide_tac) >>
    `EL i p = EL d pat` by simp[EL_APPEND_EQN] >>
    `i < LENGTH p` by (simp[] >> decide_tac) >>
    asm_rewrite_tac[] >>
    qpat_x_assum `Abbrev (d = _)` kall_tac >>
    qpat_x_assum `(?x. asm_returns_zero_or_one x /\ _) \/ _` strip_assume_tac
    >- (`d = 0 \/ d = 1 \/ d = 2` by (fs[] >> decide_tac) >>
        simp[asm_reachable_marker_def] >>
        qpat_x_assum `asm_returns_zero_or_one x` mp_tac >>
        simp[asm_returns_zero_or_one_def] >>
        strip_tac >> simp[asm_reachable_marker_def]) >>
    `d = 0 \/ d = 1 \/ d = 2 \/ d = 3` by (fs[] >> decide_tac) >>
    simp[asm_reachable_marker_def]) >>
  `!k t. sym_steps p env k (sym_init s) = SymOK t /\
      ~(LENGTH pre < t.sym_base.as_pc /\ t.sym_base.as_pc < LENGTH pre + LENGTH pat) ==>
      ?j. sym_steps q env j (sym_init s) = SymOK
        (sym_with_pc (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) t.sym_base.as_pc) t)` by
    suspend "replay" >>
  Cases_on `LENGTH pre < ss.sym_base.as_pc /\
            ss.sym_base.as_pc < LENGTH pre + LENGTH pat`
  >- suspend "interior" >>
  `?j. sym_steps q env j (sym_init s) = SymOK
     (sym_with_pc (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) ss.sym_base.as_pc) ss)`
    by metis_tac[] >>
  qexistsl_tac [`n`, `j`, `ss`] >> simp[sym_steps_def]
QED

Resume merge_iszero_one_stopped_prefix[replay]:
  mp_tac (BETA_RULE (REWRITE_RULE [LET_THM] merge_iszero_synchronized_replay)) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (qpat_assum `(?x. asm_returns_zero_or_one x /\ _) \/ _` strip_assume_tac >> simp[])
      >- (qx_gen_tac `i` >> strip_tac >> `LENGTH pre <= i` by decide_tac >>
          qpat_assum `!i. LENGTH pre <= i /\ _ ==> _` (qspec_then `i` mp_tac) >> simp[])
      >- (qx_gen_tac `i` >> strip_tac >> `i < LENGTH pre + LENGTH pat` by decide_tac >>
          qpat_assum `!i. LENGTH pre <= i /\ _ ==> _` (qspec_then `i` mp_tac) >> simp[])
      >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
          qpat_x_assum `p = pre ++ pat ++ tail` SUBST_ALL_TAC >>
          qpat_x_assum `q = pre ++ repl ++ tail` SUBST_ALL_TAC >>
          irule (BETA_RULE (REWRITE_RULE [LET_THM] merge_iszero_outside_fetch_ok)) >>
          simp[] >>
          qpat_x_assum `(?x. asm_returns_zero_or_one x /\ _) \/ _` strip_assume_tac >>
          simp[] >> qpat_x_assum `asm_returns_zero_or_one x` mp_tac >>
          simp[asm_returns_zero_or_one_def] >> strip_tac >> simp[]) >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `(?x. asm_returns_zero_or_one x /\ _) \/ _` strip_assume_tac >> gvs[]
      >- (qexists_tac `1` >> irule iszero_pair_complete_visit >> simp[]) >>
      qexists_tac `2` >> irule iszero_branch_complete_visit >> simp[]) >>
  disch_then ACCEPT_TAC
QED

Resume merge_iszero_one_stopped_prefix[interior]:
  qabbrev_tac `b = LENGTH pre` >>
  qabbrev_tac `c = ss.sym_base.as_pc` >>
  `c-b <= n /\ ?u. sym_steps p env (n-(c-b)) (sym_init s) = SymOK u /\
     u.sym_base.as_pc = b /\ sym_steps p env (c-b) u = SymOK ss` by (
    irule protected_prefix_window_entry >>
    `LENGTH pre + LENGTH pat <= LENGTH p` by simp[] >>
    `0 < LENGTH pat` by decide_tac >>
    simp[] >> rpt strip_tac >>
    `j < LENGTH pre + LENGTH pat` by decide_tac >> metis_tac[LESS_OR_EQ]) >>
  qabbrev_tac `h = n-(c-b)` >>
  `h <= n /\ n-h = c-b /\ 0 < c-b /\ n-(h+1) = c-b-1`
    by (simp[Abbr `h`] >> decide_tac) >>
  `sym_with_pc (splice_pc b (LENGTH pat) (LENGTH repl) u.sym_base.as_pc) u = u`
    by simp[splice_pc_def, sym_with_pc_def, sym_state_component_equality,
            asm_state_component_equality] >>
  qpat_x_assum `!k t. _ ==> ?j. _` (qspecl_then [`h`, `u`] mp_tac) >>
  impl_tac >- simp[] >>
  qpat_assum `sym_with_pc _ u = u` (pure_rewrite_tac o single) >>
  strip_tac >>
  qexistsl_tac [`h`, `j`, `u`] >> gvs[] >>
  `u.sym_base.as_stack = []` by metis_tac[sym_init_prefix_base_stack] >>
  `u.sym_base.as_pc = LENGTH pre` by metis_tac[] >>
  drule_all (Q.INST [`k` |-> `c-u.sym_base.as_pc`] iszero_pair_after_producer) >>
  disch_then (qx_choose_then `v` (qx_choose_then `w` (qx_choose_then `stk`
    (map_every assume_tac o CONJUNCTS)))) >>
  qexistsl_tac [`v`, `w`, `stk`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `u.sym_base.as_pc = LENGTH pre` SUBST1_TAC >>
      first_assum ACCEPT_TAC)
  >- (once_rewrite_tac[sym_steps_add] >>
      qpat_assum `sym_steps _ _ j (sym_init s) = SymOK u`
        (pure_rewrite_tac o single) >>
      simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[SUB_PLUS] >> first_assum ACCEPT_TAC
QED

Finalise merge_iszero_one_stopped_prefix
