Theory staticAbortOptConditionalJumpsStopped
Ancestors asmSymBridge[qualified,ignore_grammar] option[qualified,ignore_grammar]
  staticAbortOptMergeIszeroOutside staticAbortOptMergeIszeroSync
  staticAbortProtectedTraceCoverage staticAbortProtectedFetch asmSymPcOwn codegenSymRel asmSplice asmSymPc
  asmSymSem asmOptimizer asmWf asmSem arithmetic list words

(* A complete visit leaves the four replaced instructions, not necessarily
   via the retained label. The predecessor PC distinguishes a visit from a
   longer execution that has already left the window. *)
Theorem conditional_jump_visit_mode[local]:
  !b. b = LENGTH pre ==>
  p = pre ++ [AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x;
              AsmOp "JUMP"] ++ AsmLabel c::tail /\
  q = pre ++ [AsmOp "ISZERO"; AsmPushLabel x; AsmOp "JUMPI"] ++
              AsmLabel c::tail /\
  asm_static_wf p /\ u.sym_base.as_pc = b /\ u.sym_base.as_stack = [] /\
  d < 4 /\ sym_steps_mode allow_own p env own d u = SymOK mid /\ mid.sym_base.as_pc = b+d /\
  sym_steps_mode allow_own p env own 1 mid = SymOK v /\
  ~(b < v.sym_base.as_pc /\ v.sym_base.as_pc < b+4) ==>
  sym_steps_mode allow_own q env own 3 u =
    SymOK (sym_with_pc (splice_pc b 4 3 v.sym_base.as_pc) v)
Proof
  CONV_TAC (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2) THENC
            REDEPTH_CONV BETA_CONV) >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `~MEM (AsmLabel c) pre` by (
    qpat_x_assum `asm_static_wf p` mp_tac >> simp[asm_static_wf_def] >>
    disch_then (mp_tac o CONJUNCT1) >>
    qpat_assum `p = _` SUBST1_TAC >>
    disch_then (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                    asm_labels_unique_append_not_mem)) >>
    disch_then (qspec_then `c` mp_tac) >> simp[]) >>
  qabbrev_tac `b = LENGTH (pre:asm_inst list)` >>
  `b+4 < LENGTH p /\ EL b p = AsmPushLabel c /\ EL (b+1) p = AsmOp "JUMPI" /\
   EL (b+2) p = AsmPushLabel x /\ EL (b+3) p = AsmOp "JUMP" /\
   EL (b+4) p = AsmLabel c /\ INDEX_OF (AsmLabel c) p = SOME (b+4) /\
   b+2 < LENGTH q /\ EL b q = AsmOp "ISZERO" /\
   EL (b+1) q = AsmPushLabel x /\ EL (b+2) q = AsmOp "JUMPI"` by
    simp[Abbr `b`, EL_APPEND_EQN, INDEX_OF_APPEND, INDEX_OF_CONS] >>
  `INDEX_OF (AsmLabel x) q = OPTION_MAP (splice_pc b 4 3) (INDEX_OF (AsmLabel x) p)` by
    (qpat_assum `q = _` SUBST1_TAC >> qpat_assum `p = _` SUBST1_TAC >>
     simp[Abbr `b`] >>
     mp_tac (Q.INST [`pat` |-> `[AsmPushLabel c; AsmOp "JUMPI";
                                  AsmPushLabel x; AsmOp "JUMP"]`,
                     `repl` |-> `[AsmOp "ISZERO"; AsmPushLabel x; AsmOp "JUMPI"]`,
                     `pfx` |-> `pre`, `sfx` |-> `AsmLabel c::tail`, `l` |-> `x`]
              splice_index_of_label) >> simp[]) >>
  qpat_x_assum `p = _` kall_tac >> qpat_x_assum `q = _` kall_tac >>
  qpat_x_assum `Abbrev (b = _)` kall_tac >>
  `b < LENGTH p /\ b+1 < LENGTH p /\ b+2 < LENGTH p /\ b+3 < LENGTH p /\
   b < LENGTH q /\ b+1 < LENGTH q` by decide_tac >>
  Cases_on `d=0` >- gvs[protected_mode_fetch_one, sym_steps_mode_zero, sym_step_push_label, asm_next_def] >>
  `sym_steps_mode allow_own p env own (2+(d-1)) u = SymOK v` by (
    `2+(d-1)=d+1` by decide_tac >>
     qpat_assum `2+(d-1)=d+1` (pure_rewrite_tac o single) >>
     once_rewrite_tac[sym_steps_mode_add] >> asm_simp_tac bool_ss [sym_result_case_def] >>
     first_assum ACCEPT_TAC) >>
  qabbrev_tac `u1 = u with <| sym_base := asm_next u.sym_base;
                              sym_stack := Lab c 0::u.sym_stack |>` >>
  `u1.sym_base.as_pc=b+1 /\ u1.sym_stack=Lab c 0::u.sym_stack` by
     simp[Abbr `u1`, asm_next_def] >>
  `!k. sym_steps_mode allow_own p env own (SUC k) u = sym_steps_mode allow_own p env own k u1` by
     simp[Once sym_steps_mode_suc, sym_step_own_eq, sym_step_push_label, Abbr `u1`] >>
  `sym_steps_mode allow_own p env own (SUC (d-1)) u1 = SymOK v` by (
    qpat_assum `sym_steps_mode allow_own p env own (2+(d-1)) u = _` mp_tac >>
    `2+(d-1)=SUC (SUC (d-1))` by decide_tac >>
    pop_assum SUBST1_TAC >>
    qpat_assum `!k. sym_steps_mode allow_own p env own (SUC k) u = _`
      (qspec_then `SUC (d-1)` SUBST1_TAC) >> simp[]) >>
  `?w stk. u.sym_stack=Val w::stk` by (
    qpat_x_assum `sym_steps_mode allow_own p env own (SUC (d-1)) u1 = _` mp_tac >>
    once_rewrite_tac[sym_steps_mode_suc] >>
    simp[sym_step_own_eq] >>
    Cases_on `u.sym_stack` >- simp[sym_step_def, sym_step_op_def, sym_jumpi_def] >>
    rename1 `u.sym_stack=z::stk` >> Cases_on `z` >>
    simp[sym_step_def, sym_step_op_def, sym_jumpi_def]) >>
  `u1.sym_stack = Lab c 0::Val w::stk` by simp[] >>
  drule_then (qspecl_then [`p`, `env`] assume_tac) sym_step_jumpi_label >>
  qabbrev_tac `postpop = u with sym_stack := stk` >>
  `sym_steps_mode allow_own p env own 2 u =
     SymOK (sym_with_pc (if w=0w then b+2 else b+4) postpop)` by (
    `SUC 1 = 2` by simp[] >>
    pop_assum (SUBST1_TAC o SYM) >>
    qpat_assum `!k. sym_steps_mode allow_own p env own (SUC k) u = _`
      (qspec_then `1` SUBST1_TAC) >>
    Cases_on `w=0w` >> simp[protected_mode_fetch_one, protected_mode_fetch_two, protected_mode_fetch_three, sym_steps_mode_zero] >>
    simp[Abbr `u1`, Abbr `postpop`, sym_with_pc_def, asm_next_def]) >>
  `sym_steps_mode allow_own q env own 3 u =
     if w=0w then
       case INDEX_OF (AsmLabel x) q of
         NONE => SymBad "jumpi target"
       | SOME i => SymOK (sym_with_pc i postpop)
     else SymOK (sym_with_pc (b+3) postpop)` by (
    qpat_x_assum `INDEX_OF (AsmLabel x) q = OPTION_MAP _ _` kall_tac >>
    drule_then (qspecl_then [`q`, `env`] assume_tac) sym_step_iszero_val >>
    qmatch_asmsub_abbrev_tac `sym_step q env (AsmOp "ISZERO") u = SymOK t1` >>
    qabbrev_tac `t2 = t1 with <| sym_base := asm_next t1.sym_base;
                                 sym_stack := Lab x 0::t1.sym_stack |>` >>
    `t1.sym_base.as_pc = b+1 /\ t2.sym_base.as_pc = b+2 /\
     t2.sym_stack = Lab x 0::Val (b2w (w=0w))::stk /\
     sym_step q env (AsmPushLabel x) t1 = SymOK t2` by
      simp[Abbr `t2`, Abbr `t1`, asm_next_def, sym_step_push_label] >>
    drule_then (qspecl_then [`q`, `env`] assume_tac) sym_step_jumpi_label >>
    `(1w:bytes32) <> 0w` by simp[n2w_11, ONE_LT_dimword] >>
    Cases_on `w=0w` >>
    simp[protected_mode_fetch_one, protected_mode_fetch_two, protected_mode_fetch_three, sym_steps_mode_zero] >>
    Cases_on `INDEX_OF (AsmLabel x) q` >>
    simp[Abbr `t2`, Abbr `t1`, Abbr `postpop`, asm_next_def, sym_with_pc_def,
         sym_state_component_equality, asm_state_component_equality]) >>
  qpat_x_assum `!k. sym_steps_mode allow_own p env own (SUC k) u = _` kall_tac >>
  qpat_x_assum `sym_steps_mode allow_own p env own (SUC (d-1)) u1 = _` kall_tac >>
  qpat_x_assum `sym_step p env (AsmOp "JUMPI") u1 = _` kall_tac >>
  qpat_x_assum `Abbrev (u1 = _)` kall_tac >>
  reverse (Cases_on `w=0w`)
  >- (`sym_steps_mode allow_own p env own (2+1) u = SymOK (sym_with_pc (b+5) postpop)` by (
        rewrite_tac[sym_steps_mode_add] >>
        simp[protected_mode_fetch_one, protected_mode_fetch_two, protected_mode_fetch_three, sym_steps_mode_zero, Abbr `postpop`, sym_with_pc_def,
             sym_step_def, asm_step_def, sym_lift_def, asm_next_def,
             sym_state_component_equality, asm_state_component_equality]) >>
      `d=1` by (
        `d=1 \/ d=2 \/ d=3` by decide_tac >>
        gvs[sym_with_pc_def] >> decide_tac) >>
      gvs[sym_with_pc_def, splice_pc_def]) >>
  qabbrev_tac `u3 = (sym_with_pc (b+3) postpop) with sym_stack := Lab x 0::stk` >>
  `sym_steps_mode allow_own p env own (2+1) u = SymOK u3` by (
    rewrite_tac[sym_steps_mode_add] >>
    simp[protected_mode_fetch_one, protected_mode_fetch_two, protected_mode_fetch_three, sym_steps_mode_zero, sym_step_push_label,
         Abbr `postpop`, Abbr `u3`, sym_with_pc_def, asm_next_def]) >>
  `u3.sym_base.as_pc = b+3 /\ u3.sym_stack = Lab x 0::stk` by
    simp[Abbr `u3`, sym_with_pc_def] >>
  `d=3` by (
    `d=1 \/ d=2 \/ d=3` by decide_tac >>
    gvs[sym_with_pc_def] >> decide_tac) >>
  `mid=u3` by gvs[] >>
  qpat_x_assum `sym_steps_mode allow_own p env own 1 mid = _` mp_tac >>
  asm_rewrite_tac[] >>
  simp[protected_mode_fetch_one, protected_mode_fetch_two, protected_mode_fetch_three, sym_steps_mode_zero, sym_step_def, sym_step_op_def,
       sym_jump_def, sym_jump_dest_def] >>
  Cases_on `INDEX_OF (AsmLabel x) p` >>
  simp[Abbr `u3`, sym_with_pc_def] >>
  strip_tac >> gvs[sym_with_pc_def, Abbr `postpop`]
QED

Theorem conditional_jump_one_stopped_prefix_mode:
  !b. b = LENGTH pre ==>
  p = pre ++ [AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x;
              AsmOp "JUMP"] ++ AsmLabel c::tail /\
  q = pre ++ [AsmOp "ISZERO"; AsmPushLabel x; AsmOp "JUMPI"] ++
              AsmLabel c::tail /\
  asm_static_wf p /\ s.as_pc = 0 ==>
  !n ss. sym_steps_mode allow_own p env own n (sym_init s) = SymOK ss ==>
    if b < ss.sym_base.as_pc /\ ss.sym_base.as_pc < b+4 then
      !d. d = ss.sym_base.as_pc - b ==>
      d <= n /\ ?h j.
        sym_steps_mode allow_own p env own (n-d) (sym_init s) = SymOK h /\
        h.sym_base.as_pc = b /\ sym_steps_mode allow_own p env own d h = SymOK ss /\
        sym_steps_mode allow_own q env own j (sym_init s) = SymOK h
    else
      ?j. sym_steps_mode allow_own q env own j (sym_init s) =
          SymOK (sym_with_pc (splice_pc b 4 3 ss.sym_base.as_pc) ss)
Proof
  CONV_TAC (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2) THENC
            REDEPTH_CONV BETA_CONV) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `b = LENGTH (pre:asm_inst list)` >>
  `b < LENGTH p /\
   (!i. b < i /\ i < b+4 ==> i < LENGTH p /\ ~asm_reachable_marker (EL i p))` by (
    simp[Abbr `b`] >> rpt strip_tac >>
    `i=LENGTH pre+1 \/ i=LENGTH pre+2 \/ i=LENGTH pre+3` by decide_tac >>
    gvs[EL_APPEND_EQN, asm_reachable_marker_def]) >>
  `!m t. sym_steps_mode allow_own p env own m (sym_init s) = SymOK t /\
         b <= t.sym_base.as_pc /\ t.sym_base.as_pc < b+4 ==>
    let d = t.sym_base.as_pc-b in
      d<=m /\ ?h. sym_steps_mode allow_own p env own (m-d) (sym_init s)=SymOK h /\
                  h.sym_base.as_pc=b /\ sym_steps_mode allow_own p env own d h=SymOK t` by (
    rpt gen_tac >> rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
    irule protected_prefix_window_entry_mode >> simp[] >> rpt strip_tac >>
    `j < b+4` by decide_tac >> metis_tac[]) >>
  `!t. t.sym_base.as_pc=b ==> sym_with_pc (splice_pc b 4 3 t.sym_base.as_pc) t = t`
    by (rpt strip_tac >>
        simp[sym_with_pc_def, splice_pc_def, sym_state_component_equality,
             asm_state_component_equality]) >>
  completeInduct_on `n` >> Cases_on `n`
  >- (rpt strip_tac >> gvs[sym_steps_mode_zero, sym_init_def, splice_pc_def, sym_with_pc_def] >>
      qexists_tac `0` >> simp[sym_steps_mode_zero]) >>
  qx_gen_tac `ss` >> strip_tac >>
  Cases_on `b < ss.sym_base.as_pc /\ ss.sym_base.as_pc < b+4`
  >- suspend "interior" >>
  qpat_x_assum `sym_steps_mode allow_own p env own (SUC _) _ = _` mp_tac >>
  rewrite_tac[ADD1, sym_steps_mode_add] >>
  Cases_on `sym_steps_mode allow_own p env own n' (sym_init s)` >> simp[NoAsms] >>
  rename1 `sym_steps_mode allow_own p env own n' (sym_init s) = SymOK mid` >>
  strip_tac >>
  Cases_on `mid.sym_base.as_pc < b \/ b+4 <= mid.sym_base.as_pc`
  >- suspend "outside" >>
  suspend "completed"
QED

Resume conditional_jump_one_stopped_prefix_mode[interior]:
  `ss.sym_base.as_pc-b <= SUC n' /\
   ?h. sym_steps_mode allow_own p env own (SUC n'-(ss.sym_base.as_pc-b)) (sym_init s)=SymOK h /\
       h.sym_base.as_pc=b /\ sym_steps_mode allow_own p env own (ss.sym_base.as_pc-b) h=SymOK ss` by (
    qpat_assum `!m t. sym_steps_mode allow_own p env own m _ = _ /\ _ ==> _`
      (qspecl_then [`SUC n'`, `ss`] mp_tac) >>
    (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac)) >>
    simp[LET_THM, NoAsms]) >>
  qabbrev_tac `d = ss.sym_base.as_pc-b` >>
  `SUC n'-d < SUC n'` by (simp[Abbr `d`] >> decide_tac) >>
  `?j. sym_steps_mode allow_own q env own j (sym_init s) = SymOK h` by (
    qpat_x_assum `!m. m < SUC n' ==> _` (qspec_then `SUC n'-d` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (qspec_then `h` mp_tac) >> simp[]) >>
  simp[] >> qexists_tac `j` >> simp[]
  >> (metis_tac[])
QED

Resume conditional_jump_one_stopped_prefix_mode[outside]:
  `~(b < mid.sym_base.as_pc /\ mid.sym_base.as_pc < b+4)` by decide_tac >>
  `?j. sym_steps_mode allow_own q env own j (sym_init s) =
       SymOK (sym_with_pc (splice_pc b 4 3 mid.sym_base.as_pc) mid)` by (
    qpat_x_assum `!m. m < SUC n' ==> _` (qspec_then `n'` mp_tac) >>
    simp[NoAsms] >> disch_then (qspec_then `mid` mp_tac) >>
    simp[IgnAsm `p = _`, IgnAsm `q = _`]) >>
  `sym_steps_mode allow_own q env own 1 (sym_with_pc (splice_pc b 4 3 mid.sym_base.as_pc) mid) =
    SymOK (sym_with_pc (splice_pc b 4 3 ss.sym_base.as_pc) ss)` by (
    mp_tac (Q.SPECL [`pre`, `[AsmPushLabel c; AsmOp "JUMPI";
                               AsmPushLabel x; AsmOp "JUMP"]`,
                     `[AsmOp "ISZERO"; AsmPushLabel x; AsmOp "JUMPI"]`,
                     `AsmLabel c::tail`] merge_iszero_outside_fetch_ok_mode) >>
    simp[Abbr `b`] >> disch_then irule >> reverse conj_tac
    >- first_assum ACCEPT_TAC >>
    qpat_assum `sym_steps_mode allow_own p env own 1 mid = _` mp_tac >>
    qpat_assum `p = _` SUBST1_TAC >> rewrite_tac[APPEND]) >>
  simp[IgnAsm `q = _`] >> qexists_tac `j+1` >>
  pure_rewrite_tac[sym_steps_mode_add] >> simp[IgnAsm `q = _`]
QED

Resume conditional_jump_one_stopped_prefix_mode[completed]:
  qabbrev_tac `d = mid.sym_base.as_pc-b` >>
  `d < 4 /\ mid.sym_base.as_pc=b+d` by (simp[Abbr `d`] >> decide_tac) >>
  `d <= n' /\
   ?h. sym_steps_mode allow_own p env own (n'-d) (sym_init s)=SymOK h /\
       h.sym_base.as_pc=b /\ sym_steps_mode allow_own p env own d h=SymOK mid` by (
    qpat_x_assum `!m t. sym_steps_mode allow_own p env own m _ = _ /\ _ ==> _`
      (qspecl_then [`n'`, `mid`] mp_tac) >>
    (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac)) >>
    simp[Abbr `d`, NoAsms]) >>
  `n'-d < SUC n'` by decide_tac >>
  `?j. sym_steps_mode allow_own q env own j (sym_init s) = SymOK h` by (
    qpat_x_assum `!m. m < SUC n' ==> _` (qspec_then `n'-d` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (qspec_then `h` mp_tac) >>
    simp[IgnAsm `p = _`, IgnAsm `q = _`]) >>
  `h.sym_base.as_stack = []` by metis_tac[sym_init_prefix_base_stack_mode] >>
  `sym_steps_mode allow_own q env own 3 h = SymOK (sym_with_pc (splice_pc b 4 3 ss.sym_base.as_pc) ss)` by (
    qpat_x_assum `!m. m < SUC n' ==> _` kall_tac >>
    metis_tac[CONV_RULE (HO_REWR_CONV UNWIND_FORALL_THM2)
                conditional_jump_visit_mode, Abbr `b`]) >>
  simp[IgnAsm `q = _`] >> qexists_tac `j+3` >>
  pure_rewrite_tac[sym_steps_mode_add] >> simp[IgnAsm `q = _`]
QED

Finalise conditional_jump_one_stopped_prefix_mode

Theorem conditional_jump_one_stopped_prefix:
  !b. b = LENGTH pre ==>
  p = pre ++ [AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x;
              AsmOp "JUMP"] ++ AsmLabel c::tail /\
  q = pre ++ [AsmOp "ISZERO"; AsmPushLabel x; AsmOp "JUMPI"] ++
              AsmLabel c::tail /\
  asm_static_wf p /\ s.as_pc = 0 ==>
  !n ss. sym_steps p env n (sym_init s) = SymOK ss ==>
    if b < ss.sym_base.as_pc /\ ss.sym_base.as_pc < b+4 then
      !d. d = ss.sym_base.as_pc - b ==>
      d <= n /\ ?h j.
        sym_steps p env (n-d) (sym_init s) = SymOK h /\
        h.sym_base.as_pc = b /\ sym_steps p env d h = SymOK ss /\
        sym_steps q env j (sym_init s) = SymOK h
    else
      ?j. sym_steps q env j (sym_init s) =
          SymOK (sym_with_pc (splice_pc b 4 3 ss.sym_base.as_pc) ss)
Proof
  MATCH_ACCEPT_TAC (Q.INST [`allow_own` |-> `F`, `own` |-> `[]`]
    conditional_jump_one_stopped_prefix_mode
    |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES])
QED
