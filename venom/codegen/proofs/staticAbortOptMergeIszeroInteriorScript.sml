Theory staticAbortOptMergeIszeroInterior
Ancestors
  staticAbortOptMergeIszeroPrefix staticAbortOptMergeIszeroLayout
  staticAbortProtectedActualPrefix staticAbortProtectedTraceCoverage
  codegenSymRel asmSymPcOwn asmSymOwnCode asmSplice asmSymSem asmSem asmDataEnv
  asmOptimizer words arithmetic list

Theorem merge_iszero_actual_interior_cut_mode:
  !b. b = LENGTH pre ==>
  !m. m = LENGTH pat ==>
  !c. c = ss.sym_base.as_pc ==>
  !d. d = c-b ==>
  !B. B = (\w:bytes32. (b2w (w=0w):bytes32)) ==>
  !eq. eq = (if allow_own then asm_data_env orig s.as_code else asm_data_env q (assemble q ++ data)) ==>
  !sq. sq = (if allow_own then s else (s with as_code := assemble q ++ data)) ==>
  p = pre ++ pat ++ tail /\ q = pre ++ repl ++ tail /\
  ((?x. asm_returns_zero_or_one x /\
        pat = [x; AsmOp "ISZERO"; AsmOp "ISZERO"] /\ repl = [x]) \/
   (?l. pat = [AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"] /\
        repl = [AsmPushLabel l; AsmOp "JUMPI"])) /\
  s.as_pc = 0 /\ s.as_code = assemble orig ++ data /\ asm_static_wf orig /\ asm_static_wf p /\
  FILTER is_data_inst p = FILTER is_data_inst orig /\
  sym_steps_mode allow_own p (asm_data_env orig (assemble orig ++ data)) s.as_code n (sym_init s) = SymOK ss /\
  b < c /\ c < b+m ==>
  asm_static_wf q /\ ?k u t.
    sym_steps_mode allow_own q eq s.as_code k (sym_init sq) = SymOK u /\
    asm_steps (if allow_own then lo_reloc q orig else SND (compute_label_offsets q)) (build_offset_to_pc q) q k sq = AsmOK t /\
    (if allow_own then asm_sym_rel_own (lo_reloc q orig) q eq s.as_code else asm_sym_rel q eq) t u /\ t.as_pc = u.sym_base.as_pc /\
    LENGTH t.as_stack = LENGTH u.sym_stack /\
    t.as_call_ctx = u.sym_base.as_call_ctx /\ u.sym_base.as_call_ctx = ss.sym_base.as_call_ctx /\
    t.as_requests = u.sym_base.as_requests /\ u.sym_base.as_requests = ss.sym_base.as_requests /\
    (if m=3 then u.sym_base.as_pc=b+1 /\ ?w stk.
       (w=0w \/ w=1w) /\ u.sym_stack=Val w::stk /\
       ss.sym_stack=Val (FUNPOW B (d-1) w)::stk
     else u.sym_base.as_pc=b /\ ?l w stk.
       repl=[AsmPushLabel l; AsmOp "JUMPI"] /\ u.sym_stack=Val w::stk /\
       ss.sym_stack=(if d=3 then [Lab l 0] else []) ++ (Val (FUNPOW B (MIN d 2) w)::stk))
Proof
  CONV_TAC (REPEATC (HO_REWR_CONV UNWIND_FORALL_THM2)) >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (cj 1 (BETA_RULE (CONV_RULE (REPEATC (HO_REWR_CONV UNWIND_FORALL_THM2)) merge_iszero_one_canonical_layout))) >>
  disch_then assume_tac >>
  drule_all (cj 2 (BETA_RULE (CONV_RULE (REPEATC (HO_REWR_CONV UNWIND_FORALL_THM2)) merge_iszero_one_canonical_layout))) >>
  disch_then assume_tac >>
  qmatch_asmsub_abbrev_tac `sym_steps_mode allow_own p ep s.as_code n (sym_init s) = SymOK ss` >>
  `?k u. sym_steps_mode allow_own q ep s.as_code k (sym_init s) = SymOK u /\
    u.sym_base.as_call_ctx = ss.sym_base.as_call_ctx /\
    u.sym_base.as_requests = ss.sym_base.as_requests /\
    (if LENGTH pat=3 then u.sym_base.as_pc=LENGTH pre+1 /\ ?w stk.
       (w=0w \/ w=1w) /\ u.sym_stack=Val w::stk /\
       ss.sym_stack=Val (FUNPOW (\z:bytes32. (b2w (z=0w):bytes32))
                                (ss.sym_base.as_pc-LENGTH pre-1) w)::stk
     else u.sym_base.as_pc=LENGTH pre /\ ?l w stk.
       repl=[AsmPushLabel l; AsmOp "JUMPI"] /\ u.sym_stack=Val w::stk /\
       ss.sym_stack=(if ss.sym_base.as_pc-LENGTH pre=3 then [Lab l 0] else []) ++
         (Val (FUNPOW (\z:bytes32. (b2w (z=0w):bytes32))
                      (MIN (ss.sym_base.as_pc-LENGTH pre) 2) w)::stk))` by (
    drule_all (BETA_RULE (CONV_RULE (REPEATC (HO_REWR_CONV UNWIND_FORALL_THM2)) merge_iszero_one_stopped_prefix_mode)) >>
    simp[] >>
    disch_then (qx_choose_then `h` (qx_choose_then `j` (qx_choose_then `entry`
      (map_every assume_tac o CONJUNCTS)))) >>
    qpat_x_assum `(?x. asm_returns_zero_or_one x /\ _) \/ _` strip_assume_tac
    >- suspend "pair" >> suspend "branch") >>
  rename1 `sym_steps_mode allow_own q ep s.as_code k (sym_init s) = SymOK u` >>
  `sym_steps_mode allow_own q (asm_data_env orig (assemble orig ++ data)) s.as_code k (sym_init s) = SymOK u` by
    (qpat_assum `sym_steps_mode allow_own q ep s.as_code k (sym_init s) = SymOK u` mp_tac >> simp[Abbr `ep`]) >>
  `FILTER is_data_inst q = FILTER is_data_inst orig` by metis_tac[] >>
  mp_tac (Q.INST [`p` |-> `orig`, `q` |-> `q`, `ss` |-> `u`, `n` |-> `k`]
     stopped_symbolic_prefix_mode) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)) >>
  `(if allow_own then asm_data_env orig s.as_code else asm_data_env q (assemble q ++ data)) = ep` by
    (Cases_on `allow_own` >> simp[Abbr `ep`] >>
     metis_tac[asm_data_env_agree]) >>
  `sym_init (if allow_own then s else (s with as_code := assemble q ++ data)) = sym_init s` by
    (Cases_on `allow_own` >> simp[sym_init_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`k`, `u`, `t`] >> asm_rewrite_tac[]
  >> (Cases_on `allow_own` >> fs[] >> gvs[])
QED

Resume merge_iszero_actual_interior_cut_mode[pair]:
  `LENGTH pat = 3` by simp[] >>
  qpat_x_assum `LENGTH pat = 3 ==> _`
    (fn th => mp_tac th >> simp[NoAsms, ASSUME ``LENGTH (pat:asm_inst list) = 3``]) >>
  disch_then (qx_choose_then `v` (qx_choose_then `w` (qx_choose_then `stk`
    (map_every assume_tac o CONJUNCTS)))) >>
  `v.sym_base.as_pc < LENGTH p /\ EL v.sym_base.as_pc p = AsmOp "ISZERO"` by
    simp[EL_APPEND_EQN] >>
  `n-(h+1) = ss.sym_base.as_pc-(LENGTH pre+1)` by decide_tac >>
  `ss.sym_base.as_pc-(LENGTH pre+1) < 2` by decide_tac >>
  qexistsl_tac [`j+1`, `v`] >>
  qpat_x_assum `sym_steps_mode allow_own _ ep _ (n-(h+1)) v = SymOK ss` mp_tac >>
  Cases_on `ss.sym_base.as_pc-(LENGTH pre+1) = 0`
  >- (simp[sym_steps_mode_zero] >> disch_then (SUBST1_TAC o GSYM) >>
      simp[] >> qexistsl_tac [`w`, `stk`] >> simp[]) >>
  `ss.sym_base.as_pc-(LENGTH pre+1) = 1` by decide_tac >>
  `sym_step (pre ++ pat ++ tail) ep (AsmOp "ISZERO") v =
     SymOK (v with <|sym_base := asm_next (v.sym_base with as_stack := []);
                     sym_stack := Val (b2w (w=0w))::stk|>)` by
    (irule sym_step_iszero_val >> simp[]) >>
  simp[Once sym_steps_mode_pos] >> Cases_on `allow_own` >> simp[EL_APPEND_EQN, sym_steps_mode_zero, sym_step_own_eq] >>
  disch_tac >> gvs[asm_next_def]
QED

Resume merge_iszero_actual_interior_cut_mode[branch]:
  `LENGTH pat = 4` by simp[] >>
  `0 < n-h /\ ss.sym_base.as_pc-LENGTH pre < 4` by decide_tac >>
  `entry.sym_base.as_pc < LENGTH (pre ++ pat ++ tail)` by simp[] >>
  `?w stk. entry.sym_stack = Val w::stk` by (
    qpat_x_assum `sym_steps_mode allow_own _ ep _ (n-h) entry = SymOK ss` mp_tac >>
    simp[Once sym_steps_mode_pos] >> Cases_on `allow_own` >> simp[EL_APPEND_EQN, sym_step_own_eq] >> disch_tac >>
    mp_tac (Q.INST [`ss` |-> `entry`, `p` |-> `pre ++ pat ++ tail`,
                    `env` |-> `ep`] sym_step_iszero_cases) >>
    strip_tac >> gvs[] >> metis_tac[]) >>
  rename1 `entry.sym_stack = Val w::stk` >>
  qabbrev_tac `mid = entry with <|
    sym_base := asm_next (entry.sym_base with as_stack := []);
    sym_stack := Val (b2w (w=0w))::stk|>` >>
  `sym_step (pre ++ pat ++ tail) ep (AsmOp "ISZERO") entry = SymOK mid` by
    (simp[Abbr `mid`] >> irule sym_step_iszero_val >> simp[]) >>
  `mid.sym_base.as_pc = LENGTH pre+1 /\ mid.sym_stack = Val (b2w (w=0w))::stk`
    by simp[Abbr `mid`, asm_next_def] >>
  qabbrev_tac `last = mid with <|
    sym_base := asm_next (mid.sym_base with as_stack := []);
    sym_stack := Val (b2w ((b2w (w=0w):bytes32)=0w))::stk|>` >>
  `sym_step (pre ++ pat ++ tail) ep (AsmOp "ISZERO") mid = SymOK last` by
    (simp[Abbr `last`] >> irule sym_step_iszero_val >> simp[]) >>
  `last.sym_base.as_pc = LENGTH pre+2` by simp[Abbr `last`, asm_next_def] >>
  `mid.sym_base.as_pc < LENGTH (pre ++ pat ++ tail) /\
   last.sym_base.as_pc < LENGTH (pre ++ pat ++ tail)` by simp[] >>
  `!f. 0 < f ==>
     sym_steps_mode allow_own (pre ++ pat ++ tail) ep s.as_code f entry =
       sym_steps_mode allow_own (pre ++ pat ++ tail) ep s.as_code (f-1) mid` by
    (gen_tac >> disch_tac >> simp[Once sym_steps_mode_pos] >> Cases_on `allow_own` >> gvs[EL_APPEND_EQN, sym_step_own_eq]) >>
  `!f. 0 < f ==>
     sym_steps_mode allow_own (pre ++ pat ++ tail) ep s.as_code f mid =
       sym_steps_mode allow_own (pre ++ pat ++ tail) ep s.as_code (f-1) last` by
    (gen_tac >> disch_tac >> simp[Once sym_steps_mode_pos] >> Cases_on `allow_own` >> gvs[EL_APPEND_EQN, sym_step_own_eq]) >>
  `sym_steps_mode allow_own (pre ++ pat ++ tail) ep s.as_code 1 last =
     SymOK (last with <|sym_base := asm_next last.sym_base;
                        sym_stack := Lab l 0::last.sym_stack|>)` by
    (simp[Once sym_steps_mode_pos] >> Cases_on `allow_own` >> simp[EL_APPEND_EQN, sym_step_push_label, sym_steps_mode_zero, sym_step_own_eq]) >>
  `ss.sym_base.as_pc-LENGTH pre = 1 \/ ss.sym_base.as_pc-LENGTH pre = 2 \/
   ss.sym_base.as_pc-LENGTH pre = 3` by decide_tac >>
  qexistsl_tac [`j`, `entry`] >>
  qpat_x_assum `sym_steps_mode allow_own _ ep _ (n-h) entry = SymOK ss` mp_tac >>
  simp[sym_steps_mode_zero] >>
  disch_tac >> gvs[Abbr `last`, Abbr `mid`, asm_next_def, MIN_DEF, FUNPOW_2, sym_steps_mode_zero]
QED

Finalise merge_iszero_actual_interior_cut_mode

Theorem merge_iszero_actual_interior_cut:
  !b. b = LENGTH pre ==>
  !m. m = LENGTH pat ==>
  !c. c = ss.sym_base.as_pc ==>
  !d. d = c-b ==>
  !B. B = (\w:bytes32. (b2w (w=0w):bytes32)) ==>
  !eq. eq = asm_data_env q (assemble q ++ data) ==>
  !sq. sq = (s with as_code := assemble q ++ data) ==>
  p = pre ++ pat ++ tail /\ q = pre ++ repl ++ tail /\
  ((?x. asm_returns_zero_or_one x /\
        pat = [x; AsmOp "ISZERO"; AsmOp "ISZERO"] /\ repl = [x]) \/
   (?l. pat = [AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"] /\
        repl = [AsmPushLabel l; AsmOp "JUMPI"])) /\
  s.as_pc = 0 /\ s.as_code = assemble p ++ data /\ asm_static_wf p /\
  sym_steps p (asm_data_env p (assemble p ++ data)) n (sym_init s) = SymOK ss /\
  b < c /\ c < b+m ==>
  asm_static_wf q /\ ?k u t.
    sym_steps q eq k (sym_init sq) = SymOK u /\
    asm_steps (SND (compute_label_offsets q)) (build_offset_to_pc q) q k sq = AsmOK t /\
    asm_sym_rel q eq t u /\ t.as_pc = u.sym_base.as_pc /\
    LENGTH t.as_stack = LENGTH u.sym_stack /\
    t.as_call_ctx = u.sym_base.as_call_ctx /\ u.sym_base.as_call_ctx = ss.sym_base.as_call_ctx /\
    t.as_requests = u.sym_base.as_requests /\ u.sym_base.as_requests = ss.sym_base.as_requests /\
    (if m=3 then u.sym_base.as_pc=b+1 /\ ?w stk.
       (w=0w \/ w=1w) /\ u.sym_stack=Val w::stk /\
       ss.sym_stack=Val (FUNPOW B (d-1) w)::stk
     else u.sym_base.as_pc=b /\ ?l w stk.
       repl=[AsmPushLabel l; AsmOp "JUMPI"] /\ u.sym_stack=Val w::stk /\
       ss.sym_stack=(if d=3 then [Lab l 0] else []) ++ (Val (FUNPOW B (MIN d 2) w)::stk))
Proof
  CONV_TAC (REPEATC (HO_REWR_CONV UNWIND_FORALL_THM2)) >> BETA_TAC >>
  mp_tac (Q.INST [`allow_own` |-> `F`, `orig` |-> `p`]
    merge_iszero_actual_interior_cut_mode
    |> CONV_RULE (REPEATC (HO_REWR_CONV UNWIND_FORALL_THM2))
    |> BETA_RULE
    |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES, REFL_CLAUSE, AND_CLAUSES]) >>
  metis_tac[]
QED
