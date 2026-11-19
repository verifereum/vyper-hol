Theory staticAbortOptStackStopped
Ancestors stackOpAsmSim[qualified,ignore_grammar] stackOpSim[qualified,ignore_grammar] codegenSymRel[qualified,ignore_grammar]
  staticAbortOptMergeIszeroSync staticAbortOptMergeIszeroOutside
  staticAbortProtectedTraceCoverage asmOptPeephole asmOptimizer asmSplice
  asmSymPc asmSymSem asmSem asmWf list arithmetic

(* Bounded successful visits only; terminal results never need replay here. *)
Theorem literal_stack_dispatch[local]:
  sym_step p env (AsmOp "DUP1") u = sym_dup 0 u /\
  sym_step p env (AsmOp "DUP2") u = sym_dup 1 u /\
  sym_step p env (AsmOp "SWAP1") u = sym_swap 1 u /\
  sym_step p env (AsmOp "SWAP2") u = sym_swap 2 u /\
  sym_step p env (AsmOp "POP") u =
    case u.sym_stack of [] => SymError "pop: stack underflow"
                      | _::stk => sym_set_stack stk u
Proof
  simp[sym_step_def, sym_step_op_def, dup_table_def, swap_table_def]
QED
Theorem literal_stack_visit[local]:
  !b. b = LENGTH pre ==>
  ((pat = [AsmOp "DUP1"; AsmOp "SWAP2"; AsmOp "SWAP1"] /\
      repl = [AsmOp "SWAP1"; AsmOp "DUP2"]) \/
   (pat = [AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "POP"] /\ repl = []) \/
   (pat = [AsmOp "SWAP1"; AsmOp "POP"; AsmOp "POP"] /\
      repl = [AsmOp "POP"; AsmOp "POP"]) \/
   (pat = [AsmOp "DUP1"; AsmOp "SWAP1"] /\ repl = [AsmOp "DUP1"])) /\
  u.sym_base.as_pc = b /\ sym_steps (pre ++ pat ++ tail) env (LENGTH pat) u = SymOK v ==>
  sym_steps (pre ++ repl ++ tail) env (LENGTH repl) u =
    SymOK (sym_with_pc (splice_pc b (LENGTH pat) (LENGTH repl) v.sym_base.as_pc) v)
Proof
  CONV_TAC (HO_REWR_CONV UNWIND_FORALL_THM2) >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `sym_steps _ _ _ _ = _` mp_tac >>
  Cases_on `u.sym_stack` >>
  simp[sym_steps_pos, sym_steps_def, EL_APPEND_EQN, literal_stack_dispatch,
       sym_dup_def, sym_swap_def, sym_set_stack_def, asm_next_def,
       LUPDATE_compute, splice_pc_def, sym_with_pc_def, GSYM ADD_ASSOC] >>
  rename1 `u.sym_stack = _ :: stk` >> Cases_on `stk` >>
  simp[sym_steps_pos, sym_steps_def, EL_APPEND_EQN, literal_stack_dispatch,
       sym_dup_def, sym_swap_def, sym_set_stack_def, asm_next_def,
       LUPDATE_compute, splice_pc_def, sym_with_pc_def, GSYM ADD_ASSOC] >>
  strip_tac >> gvs[sym_with_pc_def, splice_pc_def,
                   sym_state_component_equality, asm_state_component_equality,
                   GSYM ADD_ASSOC]
QED

Theorem equal_swaps_visit[local]:
  !b. b = LENGTH pre ==>
  asm_swap_op (AsmOp name) /\ u.sym_base.as_pc = b /\
  sym_steps (pre ++ [AsmOp name; AsmOp name] ++ tail) env 2 u = SymOK v ==>
  u = sym_with_pc (splice_pc b 2 0 v.sym_base.as_pc) v
Proof
  CONV_TAC (HO_REWR_CONV UNWIND_FORALL_THM2) >> rewrite_tac[APPEND] >> strip_tac >>
  `isPREFIX "SWAP" name` by fs[asm_swap_op_def] >>
  Cases_on `ALOOKUP swap_table name`
  >- (drule_all swap_prefix_unknown >> strip_tac >>
      drule_all sym_step_unknown_op >>
      disch_then (qspecl_then [`u`, `pre ++ [AsmOp name; AsmOp name] ++ tail`,
                              `env`] strip_assume_tac) >>
      gvs[sym_steps_pos, EL_APPEND_EQN]) >>
  drule sym_step_swap_table >> strip_tac >>
  rename1 `ALOOKUP swap_table name = SOME k` >>
  Cases_on `k < LENGTH u.sym_stack /\ 0 < k` >>
  gvs[sym_steps_pos, sym_steps_def, EL_APPEND_EQN, sym_swap_def,
      sym_set_stack_def, asm_next_def, swap_swap_id] >>
  simp[splice_pc_def, sym_with_pc_def, sym_state_component_equality,
       asm_state_component_equality, GSYM ADD_ASSOC]
QED

Theorem commutative_visit[local]:
  !b. b = LENGTH pre ==>
  asm_commutative_op (AsmOp name) /\ u.sym_base.as_pc = b /\
  sym_steps (pre ++ [AsmOp "SWAP1"; AsmOp name] ++ tail) env 2 u = SymOK v ==>
  sym_steps (pre ++ [AsmOp name] ++ tail) env 1 u =
    SymOK (sym_with_pc (splice_pc b 2 1 v.sym_base.as_pc) v)
Proof
  simp[] >> strip_tac >>
  qabbrev_tac `p = pre ++ [AsmOp "SWAP1"; AsmOp name] ++ tail` >>
  qabbrev_tac `q = pre ++ [AsmOp name] ++ tail` >>
  `u.sym_base.as_pc < LENGTH p /\ EL u.sym_base.as_pc p = AsmOp "SWAP1" /\
   u.sym_base.as_pc < LENGTH q /\ EL u.sym_base.as_pc q = AsmOp name`
    by simp[Abbr `p`, Abbr `q`, EL_APPEND_EQN] >>
  `?x y stk. u.sym_stack = x::y::stk` by (
    gvs[] >> Cases_on `u.sym_stack` >>
    gvs[Once sym_steps_pos, literal_stack_dispatch, sym_swap_def] >>
    rename1 `u.sym_stack = _::stk` >> Cases_on `stk` >> gvs[]) >>
  qabbrev_tac `mid = sym_with_pc (u.sym_base.as_pc + 1)
                         (u with sym_stack := y::x::stk)` >>
  `sym_swap 1 u = SymOK mid /\ mid.sym_base.as_pc = LENGTH pre + 1`
    by simp[Abbr `mid`, sym_with_pc_def, sym_swap_def, sym_set_stack_def,
            asm_next_def, LUPDATE_compute] >>
  `mid.sym_base.as_pc < LENGTH p /\ EL mid.sym_base.as_pc p = AsmOp name`
    by simp[Abbr `p`, EL_APPEND_EQN] >>
  `sym_step p env (AsmOp name) mid = SymOK v` by (
    qpat_x_assum `sym_steps p env 2 u = _` mp_tac >>
    simp[sym_steps_pos, sym_steps_def, literal_stack_dispatch, AllCaseEqs()]) >>
  reverse (Cases_on `MEM name ["ADD"; "MUL"; "EQ"; "AND"; "OR"; "XOR"]`)
  >- (drule_all commutative_unknown >> strip_tac >>
      drule_all sym_step_unknown_op >>
      disch_then (qspecl_then [`mid`,`p`,`env`] strip_assume_tac) >> gvs[]) >>
  `AsmOp name <> AsmOp "JUMP" /\ AsmOp name <> AsmOp "JUMPI"` by gvs[] >>
  `sym_step p env (AsmOp name) u = sym_step q env (AsmOp name) u`
    by (irule sym_step_prog_cong >> simp[Abbr `p`, Abbr `q`]) >>
  `sym_step p env (AsmOp name) mid =
   sym_result_pc_add 1 (sym_step q env (AsmOp name) u)` by (
    `mid = sym_with_pc ((u with sym_stack := y::x::stk).sym_base.as_pc + 1)
                         (u with sym_stack := y::x::stk)` by simp[Abbr `mid`] >>
    qpat_x_assum `mid = _` SUBST1_TAC >>
    drule_all sym_step_pc_add >> disch_then (pure_rewrite_tac o single) >>
    drule sym_step_commutative_swap >> disch_then (pure_once_rewrite_tac o single) >>
    `u with sym_stack := x::y::stk = u` by simp[sym_state_component_equality] >>
    simp[]) >>
  Cases_on `sym_step q env (AsmOp name) u` >> fs[sym_result_pc_add_def] >>
  rename1 `sym_step q env (AsmOp name) u = SymOK out` >>
  `out.sym_base.as_pc = LENGTH pre + 1` by (
    qpat_assum `sym_step q env _ u = SymOK out`
      (mp_then (Pos last) mp_tac sym_step_pc_next) >> simp[]) >>
  gvs[] >>
  simp[sym_steps_pos, sym_steps_def, splice_pc_def, sym_with_pc_def,
       sym_state_component_equality, asm_state_component_equality,
       GSYM ADD_ASSOC]
QED

(* The synchronized replay is also usable at the entry of a partial visit. *)
Theorem stack_window_synchronized[local]:
  p = pre ++ pat ++ tail /\ q = pre ++ repl ++ tail /\
  2 <= LENGTH pat /\ LENGTH repl <= LENGTH pat /\
  (!a. MEM a pat ==> ~asm_reachable_marker a /\
                       a <> AsmOp "JUMP" /\ a <> AsmOp "JUMPI") /\
  (!a. MEM a repl ==> ~asm_reachable_marker a) /\
  (!u v. u.sym_base.as_pc = LENGTH pre /\
         sym_steps p env (LENGTH pat) u = SymOK v ==>
     sym_steps q env (LENGTH repl) u = SymOK (sym_with_pc
       (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) v.sym_base.as_pc) v)) /\
  s.as_pc = 0 ==>
  (!i. LENGTH pre <= i /\ i < LENGTH pre + LENGTH pat ==>
       ~asm_reachable_marker (EL i p)) /\
  (!n ss. sym_steps p env n (sym_init s) = SymOK ss /\
          ~(LENGTH pre < ss.sym_base.as_pc /\ ss.sym_base.as_pc < LENGTH pre + LENGTH pat) ==>
    ?j. sym_steps q env j (sym_init s) = SymOK (sym_with_pc
      (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) ss.sym_base.as_pc) ss))
Proof
  strip_tac >>
  `!i. LENGTH pre <= i /\ i < LENGTH pre + LENGTH pat ==> MEM (EL i p) pat` by (
    rpt strip_tac >> simp[EL_APPEND_EQN] >> irule EL_MEM >> decide_tac) >>
  conj_asm1_tac >- metis_tac[] >>
  match_mp_tac (BETA_RULE (CONV_RULE (DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2)) merge_iszero_synchronized_replay)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      `LENGTH pre <= i /\ i < LENGTH pre + LENGTH pat` by decide_tac >> metis_tac[])
  >- (rpt strip_tac >>
      `i < LENGTH pre + LENGTH pat` by decide_tac >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `q = pre ++ repl ++ tail` SUBST_ALL_TAC >>
      irule (BETA_RULE (CONV_RULE (DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2)) merge_iszero_outside_fetch_ok)) >>
      `pat <> []` by (CCONTR_TAC >> gvs[]) >> simp[] >>
      metis_tac[asm_reachable_marker_def]) >>
  rpt strip_tac >> qexists_tac `LENGTH repl` >> metis_tac[]
QED

Theorem stack_peephole_one_stopped_prefix:
  !pre pat repl tail env s n ss.
    !p. p = pre ++ pat ++ tail ==>
    !q. q = pre ++ repl ++ tail ==>
    !b. b = LENGTH pre ==>
    !m. m = LENGTH pat ==>
    !c. c = ss.sym_base.as_pc ==>
    ((pat = [AsmOp "DUP1"; AsmOp "SWAP2"; AsmOp "SWAP1"] /\
        repl = [AsmOp "SWAP1"; AsmOp "DUP2"]) \/
     (pat = [AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "POP"] /\ repl = []) \/
     (pat = [AsmOp "SWAP1"; AsmOp "POP"; AsmOp "POP"] /\
        repl = [AsmOp "POP"; AsmOp "POP"]) \/
     (?a. asm_swap_op a /\ pat = [a;a] /\ repl = []) \/
     (?a. asm_commutative_op a /\ pat = [AsmOp "SWAP1";a] /\ repl = [a]) \/
     (pat = [AsmOp "DUP1"; AsmOp "SWAP1"] /\ repl = [AsmOp "DUP1"])) /\
    asm_static_wf p /\ s.as_pc = 0 /\ sym_steps p env n (sym_init s) = SymOK ss ==>
    if b<c /\ c<b+m then
      c-b<=n /\ ?h j u. h=n-(c-b) /\
        sym_steps p env h (sym_init s)=SymOK u /\ u.sym_base.as_pc=b /\
        sym_steps p env (c-b) u=SymOK ss /\ sym_steps q env j (sym_init s)=SymOK u
    else
      ?j. sym_steps q env j (sym_init s)=SymOK (sym_with_pc (splice_pc b m (LENGTH repl) c) ss)
Proof
  CONV_TAC (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2)) >>
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "rewrite") strip_assume_tac) >>
  qabbrev_tac `p = pre ++ pat ++ tail` >> qabbrev_tac `q = pre ++ repl ++ tail` >>
  `2 <= LENGTH pat /\
   (!i. LENGTH pre <= i /\ i < LENGTH pre + LENGTH pat ==>
        ~asm_reachable_marker (EL i p)) /\
   (!k u. sym_steps p env k (sym_init s) = SymOK u /\
          ~(LENGTH pre < u.sym_base.as_pc /\ u.sym_base.as_pc < LENGTH pre + LENGTH pat) ==>
      ?j. sym_steps q env j (sym_init s) = SymOK (sym_with_pc
        (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) u.sym_base.as_pc) u))` by
    suspend "replay" >>
  IF_CASES_TAC >- suspend "interior" >>
  qpat_assum `!k u. sym_steps p env k _ = _ /\ _ ==> _`
    (qspecl_then [`n`,`ss`] mp_tac) >> simp[]
QED

Resume stack_peephole_one_stopped_prefix[replay]:
  `2 <= LENGTH pat` by (asm "rewrite" strip_assume_tac >> simp[]) >>
  `!a. asm_swap_op a \/ asm_commutative_op a ==>
       ~asm_reachable_marker a /\ a <> AsmOp "JUMP" /\ a <> AsmOp "JUMPI"` by (
    gen_tac >> Cases_on `a` >>
    simp[asm_reachable_marker_def, asm_swap_op_def, asm_commutative_op_def] >>
    rpt strip_tac >> gvs[]) >>
  `!u v. u.sym_base.as_pc = LENGTH pre /\
         sym_steps p env (LENGTH pat) u = SymOK v ==>
     sym_steps q env (LENGTH repl) u = SymOK (sym_with_pc
       (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) v.sym_base.as_pc) v)` by (
    rpt gen_tac >> strip_tac >>
    Cases_on `?a. asm_swap_op a /\ pat = [a;a] /\ repl = []`
    >- (gvs[] >> rename1 `asm_swap_op a` >> Cases_on `a` >>
        fs[asm_swap_op_def] >> simp[sym_steps_def] >>
        (metis_tac[SRULE [asm_swap_op_def] equal_swaps_visit])) >>
    Cases_on `?a. asm_commutative_op a /\ pat = [AsmOp "SWAP1";a] /\ repl = [a]`
    >- (gvs[] >> rename1 `asm_commutative_op a` >> Cases_on `a` >>
        fs[asm_commutative_op_def] >> gvs[Abbr `p`, Abbr `q`] >>
        irule (SRULE [LET_THM, asm_commutative_op_def] commutative_visit) >> simp[]) >>
    simp[Abbr `q`] >> irule (SRULE [LET_THM] literal_stack_visit) >>
    asm_x "rewrite" mp_tac >> gvs[Abbr `p`] >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule stack_window_synchronized >> simp[Abbr `p`, Abbr `q`] >>
  asm "rewrite" strip_assume_tac >> gvs[] >>
  rpt strip_tac >> gvs[asm_reachable_marker_def] >> metis_tac[]
QED

Resume stack_peephole_one_stopped_prefix[interior]:
  qabbrev_tac `b = LENGTH pre` >> qabbrev_tac `c = ss.sym_base.as_pc` >>
  `c-b<=n /\ ?u. sym_steps p env (n-(c-b)) (sym_init s) = SymOK u /\
                 u.sym_base.as_pc=b /\ sym_steps p env (c-b) u = SymOK ss` by (
    irule protected_prefix_window_entry >>
    `b + LENGTH pat <= LENGTH p` by simp[Abbr `p`, Abbr `b`] >>
    `!j. b < j /\ j <= c ==> j < LENGTH p /\ ~asm_reachable_marker (EL j p)` by
      (gen_tac >> strip_tac >> conj_tac >- decide_tac >>
       qpat_assum `!i. b <= i /\ _ ==> _` (qspec_then `j` irule) >>
       decide_tac) >>
    simp[Abbr `c`] >> decide_tac) >>
  `sym_with_pc (splice_pc b (LENGTH pat) (LENGTH repl) u.sym_base.as_pc) u = u`
    by simp[sym_with_pc_def, splice_pc_def, sym_state_component_equality,
            asm_state_component_equality] >>
  qpat_x_assum `!k u. sym_steps p env k _ = _ /\ _ ==> _`
    (qspecl_then [`n-(c-b)`,`u`] mp_tac) >>
  (impl_tac >- simp[Abbr `b`]) >>
  qpat_assum `Abbrev (b = _)` (SUBST1_TAC o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  qpat_assum `sym_with_pc _ u = u` (pure_rewrite_tac o single) >>
  strip_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`n-(c-b)`,`j`,`u`] >> simp[]
QED

Finalise stack_peephole_one_stopped_prefix
