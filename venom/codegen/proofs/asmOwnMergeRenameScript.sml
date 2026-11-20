(* One global label rename preserves refinement with fixed own-code bytes. *)
Theory asmOwnMergeRename
Ancestors
  asmOwnMergeCodecopy asmOwnMergeStep asmOwnMergeSkip asmOwnMergeRun
  asmOptMergeJumpdests asmSymOwnCode asmSplice asmSpliceOwn asmSymPcOwn asmSymSem asmOptimizer
  asmWf asmSem list rich_list

Theorem rename_refines_own:
  (next = AsmLabel y /\ y <> x \/
   next = AsmPushLabel y /\ third = AsmOp "JUMP") ==>
  asm_refines_own (pre ++ AsmLabel x :: next :: third :: more)
    (MAP (rename_push_label x y)
      (pre ++ AsmLabel x :: next :: third :: more))
Proof
  disch_tac >>
  qabbrev_tac `P = pre ++ AsmLabel x :: next :: third :: more` >>
  simp[asm_refines_own_def, rename_filter_data] >> strip_tac >>
  `asm_static_wf (MAP (rename_push_label x y) P)`
    by (irule rename_static_wf >>
        qpat_x_assum `next = _ /\ _ \/ _` strip_assume_tac >>
        simp[Abbr `P`, asm_label_refs_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
        metis_tac[MEM, MEM_APPEND]) >>
  pop_assum (fn th => rewrite_tac [th]) >> rpt strip_tac >>
  `asm_labels_unique P` by fs[asm_static_wf_def] >>
  `INDEX_OF (AsmLabel x) P = SOME (LENGTH pre)`
    by (`~MEM (AsmLabel x) pre`
          by (irule asm_labels_unique_append_not_mem >>
              qexists_tac `AsmLabel x :: next :: third :: more` >>
              fs[Abbr `P`]) >>
        simp[Abbr `P`, INDEX_OF_APPEND, INDEX_OF_CONS]) >>
  irule rename_run_own_under >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule rename_step_own_under >>
      simp[] >> metis_tac[codecopy_rel_own]) >>
  simp[] >> reverse conj_tac
  >- simp[rn_rel_def, sym_init_def, ml_rel_def, mem_blocks_ok_def] >>
  rpt strip_tac >>
  irule rename_skip_own >> simp[] >>
  qexistsl_tac [`next`, `pre`, `third :: more`, `x`] >>
  fs[Abbr `P`]
QED

Theorem rename_prefix_one_step_own[local]:
  !p x y env own n ss ss' a.
    asm_static_wf p /\ MEM (AsmLabel x) p /\ 0 < n /\
    rn_rel x y ss ss' /\ sym_steps_own p env own n ss = SymOK a ==>
      ?t. t.sym_base.as_stack = [] /\ sym_steps_own p env own (n-1) t = SymOK a /\
        ((?t'. sym_steps_own (MAP (rename_push_label x y) p) env own 1 ss' = SymOK t' /\
             rn_rel x y t t') \/
         (INDEX_OF (AsmLabel x) p = SOME t.sym_base.as_pc /\
          !j. INDEX_OF (AsmLabel y) p = SOME j ==>
            ?t'. sym_steps_own (MAP (rename_push_label x y) p) env own 1 ss' = SymOK t' /\
                 rn_rel x y (t with sym_base := t.sym_base with as_pc := j) t'))
Proof
  rpt gen_tac >> strip_tac >>
  `ss.sym_base.as_pc < LENGTH p`
    by (spose_not_then assume_tac >>
        qpat_x_assum `sym_steps_own _ _ _ _ _ = _` mp_tac >>
        Cases_on `n` >- gvs[] >> simp[Once sym_steps_own_def]) >>
  `~sym_data_label p env x`
    by metis_tac[asm_static_wf_def, sym_data_label_def] >>
  `ss'.sym_base = ss.sym_base` by metis_tac[rn_rel_def] >>
  qpat_x_assum `sym_steps_own _ _ _ _ _ = _` mp_tac >>
  simp[sym_steps_own_pos] >>
  Cases_on `sym_step_own p env own (EL ss.sym_base.as_pc p) ss` >> simp[] >>
  rename1 `sym_step_own p env own _ ss = SymOK t` >> disch_tac >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (irule sym_step_own_base_stack >> metis_tac[rn_rel_def]) >>
  mp_tac (Q.INST [`p` |-> `p`, `x` |-> `x`, `y` |-> `y`,
    `env` |-> `env`, `own` |-> `own`] rename_step_own_under) >>
  (impl_tac >- metis_tac[codecopy_rel_own]) >>
  disch_then (qspecl_then [`ss`,`ss'`,`EL ss.sym_base.as_pc p`] mp_tac) >>
  simp[] >> disch_tac >>
  qpat_x_assum `(?t'. _) \/ _` strip_assume_tac
  >- (disj1_tac >> qexists_tac `t'` >> rewrite_tac[Once arithmeticTheory.ONE, sym_steps_own_def] >> simp[EL_MAP]) >>
  disj2_tac >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `t'` >> rewrite_tac[Once arithmeticTheory.ONE, sym_steps_own_def] >> simp[EL_MAP]
QED

Theorem rename_prefix_skip_own[local]:
  !pre x y next third more env own t n a.
    (next = AsmLabel y /\ y <> x \/
     next = AsmPushLabel y /\ third = AsmOp "JUMP") /\
    asm_labels_unique (pre ++ AsmLabel x::next::third::more) /\
    t.sym_base.as_pc = LENGTH pre /\ t.sym_base.as_stack = [] /\
    sym_steps_own (pre ++ AsmLabel x::next::third::more) env own n t = SymOK a ==>
    (n <= 2 /\ a.sym_base.as_pc < LENGTH (pre ++ AsmLabel x::next::third::more) /\
      !op. op IN {"GAS"; "CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"} ==>
        EL a.sym_base.as_pc (pre ++ AsmLabel x::next::third::more) <> AsmOp op) \/
    (?k j. 0 < k /\ k <= 3 /\ k <= n /\
      INDEX_OF (AsmLabel y) (pre ++ AsmLabel x::next::third::more) = SOME j /\
      sym_steps_own (pre ++ AsmLabel x::next::third::more) env own (n-k)
        (t with sym_base := t.sym_base with as_pc := j) = SymOK a)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `p = pre ++ AsmLabel x::next::third::more` >>
  Cases_on `n = 0` >- gvs[sym_steps_own_def, Abbr `p`, EL_APPEND_EQN] >>
  qpat_x_assum `_ \/ _` strip_assume_tac
  >- (gvs[] >>
      `sym_steps_own p env own 1 t = sym_steps p env 1 t` by
        (irule sym_steps_own_agree_on_window >>
         qexists_tac `LENGTH pre` >> simp[Abbr `p`, EL_APPEND_EQN]) >>
      mp_tac (Q.INST [`p` |-> `p`, `sfx` |-> `third::more`]
        rename_adjacent_label_steps) >>
      (impl_tac >- simp[Abbr `p`]) >>
      disch_then (CONJUNCTS_THEN2 assume_tac (mp_tac o Q.SPEC `0`)) >>
      disch_then (assume_tac o
        CONV_RULE (RAND_CONV (REWRITE_CONV [sym_steps_def])) o
        PURE_REWRITE_RULE [GSYM arithmeticTheory.ONE]) >>
      `n = 1 + (n-1)` by decide_tac >>
      qpat_x_assum `sym_steps_own p env own n t = _` mp_tac >>
      pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
      rewrite_tac[sym_steps_own_add] >> simp[] >> strip_tac >>
      disj2_tac >> qexists_tac `1` >> simp[]) >>
  qpat_x_assum `next = AsmPushLabel y` SUBST_ALL_TAC >>
  qpat_x_assum `third = AsmOp "JUMP"` SUBST_ALL_TAC >>
  `!i. i <= 3 ==> sym_steps_own p env own i t = sym_steps p env i t` by
    (rpt strip_tac >> irule sym_steps_own_agree_on_window >>
     qexists_tac `LENGTH pre` >> simp[Abbr `p`] >> rpt strip_tac >>
     `i' = 0 \/ i' = 1 \/ i' = 2` by decide_tac >>
     gvs[EL_APPEND_EQN] >> decide_tac) >>
  Cases_on `n < 3`
  >- (`sym_steps p env n t = SymOK a` by
        (first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
      qpat_x_assum `sym_steps_own _ _ _ _ _ = _` kall_tac >>
      `n = 1 \/ n = 2` by decide_tac >>
      disj1_tac >>
      gvs[Abbr `p`, EL_APPEND_EQN, sym_steps_pos, sym_steps_def,
          sym_step_label_skip, sym_step_push_label, asm_next_def]) >>
  mp_tac (Q.INST [`p` |-> `p`] rename_jump_steps) >>
  (impl_tac >- simp[Abbr `p`]) >>
  disch_then (mp_tac o Q.SPEC `0` o CONJUNCT1) >>
  disch_then (assume_tac o
    CONV_RULE (RAND_CONV (REWRITE_CONV [sym_steps_def])) o
    PURE_REWRITE_RULE [EVAL ``SUC (SUC (SUC 0))``]) >>
  qpat_assum `!i. i <= 3 ==> _` (qspec_then `3` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `n = 3 + (n-3)` by decide_tac >>
  qpat_x_assum `sym_steps_own p env own n t = _` mp_tac >>
  pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  rewrite_tac[sym_steps_own_add] >>
  Cases_on `INDEX_OF (AsmLabel y) p` >> fs[] >>
  strip_tac >> qexists_tac `3` >> simp[]
QED

Theorem rename_prefix_boundaries_own[local]:
  !p pre x y next third more env own.
    p = pre ++ AsmLabel x::next::third::more /\
    (next = AsmLabel y /\ y <> x \/
     next = AsmPushLabel y /\ third = AsmOp "JUMP") /\
    asm_static_wf p ==>
    !n ss ss' a.
      rn_rel x y ss ss' /\ sym_steps_own p env own n ss = SymOK a ==>
      (?m b. sym_steps_own (MAP (rename_push_label x y) p) env own m ss' = SymOK b /\
        n <= 4 * (m+1)) /\
      (!op. op IN {"GAS"; "CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"} /\
         a.sym_base.as_pc < LENGTH p /\ EL a.sym_base.as_pc p = AsmOp op ==>
       ?m b. sym_steps_own (MAP (rename_push_label x y) p) env own m ss' = SymOK b /\
         b.sym_base.as_pc < LENGTH p /\
         EL b.sym_base.as_pc (MAP (rename_push_label x y) p) = AsmOp op /\
         rn_rel x y a b)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.SPECL [`p`, `pre`, `x`, `y`, `next`, `third`, `more`,
    `sym_steps_own p env own`,
    `sym_steps_own (MAP (rename_push_label x y) p) env own`]
    rename_prefix_boundaries_by_steps) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY (simp_tac bool_ss [sym_steps_own_def] >> NO_TAC)
    >- (rpt gen_tac >> strip_tac >>
        `SUC m = 1 + m` by decide_tac >>
        pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
        rewrite_tac[sym_steps_own_add] >>
        qpat_x_assum `p = _` kall_tac >> simp[])
    >- (rpt gen_tac >> strip_tac >> irule rename_prefix_one_step_own >>
        simp[] >> metis_tac[MEM_APPEND, MEM]) >>
    qpat_x_assum `p = _` SUBST_ALL_TAC >>
    rpt gen_tac >> strip_tac >>
    `asm_labels_unique (pre ++ AsmLabel x::next::third::more)`
      by metis_tac[asm_static_wf_def] >>
    mp_tac (Q.SPECL [`pre`,`x`,`y`,`next`,`third`,`more`,`env`,`own`,`t`,`n`,`a`]
      rename_prefix_skip_own) >> simp[])) >>
  simp[]
QED

Theorem rename_site_prefix_transport_own:
  !pre x y next third more.
    (next = AsmLabel y /\ y <> x \/
     next = AsmPushLabel y /\ third = AsmOp "JUMP") /\
    asm_static_wf (pre ++ AsmLabel x::next::third::more) ==>
    ?K. 0 < K /\ !env own s n a.
      s.as_pc = 0 /\
      sym_steps_own (pre ++ AsmLabel x::next::third::more) env own n (sym_init s) = SymOK a ==>
      (?m b. sym_steps_own (MAP (rename_push_label x y)
        (pre ++ AsmLabel x::next::third::more)) env own m (sym_init s) = SymOK b /\
        n <= K * (m+1)) /\
      (!op. op IN {"GAS"; "CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"} /\
         a.sym_base.as_pc < LENGTH (pre ++ AsmLabel x::next::third::more) /\
         EL a.sym_base.as_pc (pre ++ AsmLabel x::next::third::more) = AsmOp op ==>
       ?m b. sym_steps_own (MAP (rename_push_label x y)
         (pre ++ AsmLabel x::next::third::more)) env own m (sym_init s) = SymOK b /\
         b.sym_base.as_pc < LENGTH (MAP (rename_push_label x y)
           (pre ++ AsmLabel x::next::third::more)) /\
         EL b.sym_base.as_pc (MAP (rename_push_label x y)
           (pre ++ AsmLabel x::next::third::more)) = AsmOp op /\
         (b.sym_base with as_pc := 0) = (a.sym_base with as_pc := 0) /\
         MAP sval_val b.sym_stack = MAP sval_val a.sym_stack /\
         FDOM b.sym_mem_labels = FDOM a.sym_mem_labels)
Proof
  rpt gen_tac >> disch_tac >> qexists_tac `4` >>
  conj_tac >- decide_tac >>
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[LENGTH_MAP] >>
  qspecl_then [`pre ++ AsmLabel x::next::third::more`, `pre`, `x`, `y`, `next`,
    `third`, `more`, `env`, `own`] mp_tac rename_prefix_boundaries_own >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qspecl_then [`n`, `sym_init s`, `sym_init s`, `a`] mp_tac) >>
  (impl_tac >- simp[rn_rel_def, sym_init_def, ml_rel_def, mem_blocks_ok_def]) >>
  strip_tac >> conj_tac >- metis_tac[] >>
  rpt strip_tac >> first_x_assum drule_all >>
  disch_then (qx_choosel_then [`m2`, `b2`] strip_assume_tac) >>
  qexistsl_tac [`m2`, `b2`] >> fs[rn_rel_def] >>
  metis_tac[sv_rel_list_vals, ml_rel_fdom]
QED
