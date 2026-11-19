Theory staticAbortOptMergeIszeroVisits
Ancestors
  asmOptMergeIszero codegenSymRel asmSymPc asmSplice asmOptimizer asmSymSem
  asmSem list arithmetic words

Theorem iszero_prefix_one_iff[local]:
  sym_steps p env 1 u = SymOK v <=>
    u.sym_base.as_pc < LENGTH p /\
    sym_step p env (EL u.sym_base.as_pc p) u = SymOK v
Proof
  rewrite_tac[ONE, sym_steps_def] >> simp[AllCaseEqs(), NOT_LESS_EQUAL, GREATER_EQ] >> decide_tac
QED

Theorem iszero_prefix_split[local]:
  sym_steps p env (h+k) u = SymOK v <=>
  ?mid. sym_steps p env h u = SymOK mid /\ sym_steps p env k mid = SymOK v
Proof
  simp[sym_steps_add, AllCaseEqs()]
QED

Theorem iszero_pair_after_producer:
  u.sym_base.as_pc = LENGTH pre /\ u.sym_base.as_stack = [] /\
  asm_returns_zero_or_one x /\
  sym_steps (pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ tail) env k u = SymOK ss /\
  0 < k ==> ?v w stk.
    sym_step (pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ tail) env x u = SymOK v /\
    sym_step (pre ++ [x] ++ tail) env x u = SymOK v /\
    sym_steps (pre ++ [x] ++ tail) env 1 u = SymOK v /\
    v.sym_base.as_pc = LENGTH pre+1 /\ v.sym_base.as_stack = [] /\
    v.sym_stack = Val w::stk /\ (w=0w \/ w=1w) /\
    sym_steps (pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ tail) env (k-1) v = SymOK ss
Proof
  strip_tac >>
  `x <> AsmOp "JUMP" /\ x <> AsmOp "JUMPI" /\ (!l. x <> AsmDataHeader l)`
    by gvs[asm_returns_zero_or_one_def] >>
  qabbrev_tac `p = pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ tail` >>
  qabbrev_tac `q = pre ++ [x] ++ tail` >>
  `u.sym_base.as_pc < LENGTH p /\ EL u.sym_base.as_pc p = x /\
   u.sym_base.as_pc < LENGTH q /\ EL u.sym_base.as_pc q = x`
    by simp[Abbr `p`, Abbr `q`, EL_APPEND_EQN] >>
  `k = 1+(k-1)` by decide_tac >>
  `?v. sym_steps p env 1 u = SymOK v /\ sym_steps p env (k-1) v = SymOK ss`
    by metis_tac[iszero_prefix_split] >>
  `sym_step p env x u = SymOK v`
    by (qpat_assum `sym_steps p env 1 u = SymOK v`
          (mp_tac o REWRITE_RULE[iszero_prefix_one_iff]) >>
        asm_rewrite_tac[]) >>
  `sym_step p env x u = sym_step q env x u`
    by (irule sym_step_prog_cong >> simp[Abbr `p`, Abbr `q`] >> metis_tac[]) >>
  drule_all sym_step_zero_or_one >> strip_tac >>
  qexistsl_tac [`v`,`w`,`stk`] >> simp[iszero_prefix_one_iff] >>
  metis_tac[sym_step_pc_next,sym_step_base_stack]
QED

Theorem iszero_prefix_double_test[local]:
  u.sym_base.as_stack = [] /\ u.sym_stack = Val w::stk /\
  u.sym_base.as_pc + 1 < LENGTH p /\
  EL u.sym_base.as_pc p = AsmOp "ISZERO" /\
  EL (u.sym_base.as_pc+1) p = AsmOp "ISZERO" ==>
  sym_steps p env 2 u = SymOK
    (sym_with_pc (u.sym_base.as_pc + 2)
      (u with sym_stack := Val (b2w (b2w (w=0w) = (0w:bytes32)))::stk))
Proof
  strip_tac >>
  drule_then (qspecl_then [`p`, `env`] assume_tac) sym_step_iszero_val >>
  qmatch_asmsub_abbrev_tac `sym_step p env (AsmOp "ISZERO") u = SymOK mid` >>
  `mid.sym_stack = Val (b2w (w=0w))::stk` by simp[Abbr `mid`] >>
  drule_then (qspecl_then [`p`, `env`] assume_tac) sym_step_iszero_val >>
  `mid.sym_base.as_pc = u.sym_base.as_pc+1` by simp[Abbr `mid`, asm_next_def] >>
  simp[sym_steps_pos, iszero_prefix_one_iff] >>
  simp[Abbr `mid`, sym_steps_def, asm_next_def, sym_with_pc_def, sym_state_component_equality,
       asm_state_component_equality]
QED

Theorem iszero_pair_complete_visit:
  u.sym_base.as_pc = LENGTH pre /\ u.sym_base.as_stack = [] /\
  asm_returns_zero_or_one x /\
  sym_steps (pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ tail) env 3 u = SymOK ss ==>
  sym_steps (pre ++ [x] ++ tail) env 1 u =
    SymOK (sym_with_pc (splice_pc (LENGTH pre) 3 1 ss.sym_base.as_pc) ss)
Proof
  strip_tac >>
  drule_all (SRULE [] (Q.INST [`k` |-> `3`] iszero_pair_after_producer)) >> strip_tac >>
  qabbrev_tac `p = pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ tail` >>
  `v.sym_base.as_pc+1 < LENGTH p /\ EL v.sym_base.as_pc p = AsmOp "ISZERO" /\
   EL (v.sym_base.as_pc+1) p = AsmOp "ISZERO"`
    by simp[Abbr `p`, EL_APPEND_EQN] >>
  drule_all iszero_prefix_double_test >>
  `b2w (b2w (w=0w) = (0w:bytes32)) = w` by metis_tac[b2w_b2w_zero_or_one] >>
  simp[] >> disch_then (qspecl_then [`env`] mp_tac) >>
  simp[sym_with_pc_def, splice_pc_def, sym_state_component_equality,
       asm_state_component_equality]
QED

Theorem iszero_prefix_push_branch[local]:
  u.sym_stack = Val w::stk /\ u.sym_base.as_pc+1 < LENGTH p /\
  EL u.sym_base.as_pc p = AsmPushLabel l /\
  EL (u.sym_base.as_pc+1) p = AsmOp "JUMPI" ==>
  sym_steps p env 2 u =
    if w=0w then SymOK (sym_with_pc (u.sym_base.as_pc+2) (u with sym_stack := stk))
    else case INDEX_OF (AsmLabel l) p of
       NONE => SymBad "jumpi target"
     | SOME i => SymOK (sym_with_pc i (u with sym_stack := stk))
Proof
  strip_tac >>
  qabbrev_tac `mid = u with <|sym_base := asm_next u.sym_base;
                               sym_stack := Lab l 0::u.sym_stack|>` >>
  `sym_step p env (AsmPushLabel l) u = SymOK mid` by simp[Abbr `mid`,sym_step_push_label] >>
  `mid.sym_base.as_pc = u.sym_base.as_pc+1 /\ mid.sym_stack = Lab l 0::Val w::stk`
    by simp[Abbr `mid`,asm_next_def] >>
  drule_then (qspecl_then [`p`, `env`] assume_tac) sym_step_jumpi_label >>
  simp[sym_steps_pos, sym_steps_def] >>
  Cases_on `w=0w` >> Cases_on `INDEX_OF (AsmLabel l) p` >>
  simp[sym_steps_def, Abbr `mid`, sym_with_pc_def, asm_next_def,
       sym_state_component_equality, asm_state_component_equality]
QED

Theorem iszero_branch_complete_visit:
  u.sym_base.as_pc = LENGTH pre /\ u.sym_base.as_stack = [] /\
  sym_steps (pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"] ++ tail)
    env 4 u = SymOK ss ==>
  sym_steps (pre ++ [AsmPushLabel l; AsmOp "JUMPI"] ++ tail) env 2 u =
    SymOK (sym_with_pc (splice_pc (LENGTH pre) 4 2 ss.sym_base.as_pc) ss)
Proof
  strip_tac >>
  qabbrev_tac `p = pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"] ++ tail` >>
  qabbrev_tac `q = pre ++ [AsmPushLabel l; AsmOp "JUMPI"] ++ tail` >>
  `u.sym_base.as_pc+1 < LENGTH p /\ EL u.sym_base.as_pc p = AsmOp "ISZERO" /\
    EL (u.sym_base.as_pc+1) p = AsmOp "ISZERO"`
    by simp[Abbr `p`,EL_APPEND_EQN] >>
  `?w stk. u.sym_stack = Val w::stk` by
    (`?v. sym_steps p env 1 u = SymOK v /\ sym_steps p env 3 v = SymOK ss`
       by metis_tac[SRULE [] (Q.INST [`h` |-> `1`,`k` |-> `3`] iszero_prefix_split)] >>
     qpat_x_assum `sym_steps p env 1 u = SymOK v`
       (strip_assume_tac o REWRITE_RULE[iszero_prefix_one_iff]) >>
     metis_tac[sym_step_iszero_cases, sym_result_distinct]) >>
  `?mid. sym_steps p env 2 u = SymOK mid /\ sym_steps p env 2 mid = SymOK ss`
    by metis_tac[SRULE [] (Q.INST [`h` |-> `2`,`k` |-> `2`] iszero_prefix_split)] >>
  `mid = sym_with_pc (LENGTH pre+2)
     (u with sym_stack := Val (b2w (b2w (w=0w) = (0w:bytes32)))::stk)`
    by (drule_all iszero_prefix_double_test >> disch_then (qspec_then `env` mp_tac) >> simp[]) >>
  `INDEX_OF (AsmLabel l) q = OPTION_MAP (splice_pc (LENGTH pre) 4 2) (INDEX_OF (AsmLabel l) p)`
    by (mp_tac (Q.INST [`pat` |-> `[AsmOp "ISZERO";AsmOp "ISZERO";AsmPushLabel l;AsmOp "JUMPI"]`,
                        `repl` |-> `[AsmPushLabel l;AsmOp "JUMPI"]`,
                        `pfx` |-> `pre`, `sfx` |-> `tail`] splice_index_of_label) >>
        simp[Abbr `p`,Abbr `q`]) >>
  `?v:bytes32. mid.sym_stack = Val v::stk /\ (v=0w <=> w=0w)`
    by (qexists `b2w (b2w (w=0w) = (0w:bytes32))` >> simp[sym_with_pc_def,b2w_b2w_eq_zero]) >>
  `sym_steps p env 2 mid =
     if v=0w then SymOK (sym_with_pc (mid.sym_base.as_pc+2) (mid with sym_stack := stk))
     else case INDEX_OF (AsmLabel l) p of
            NONE => SymBad "jumpi target"
          | SOME i => SymOK (sym_with_pc i (mid with sym_stack := stk))`
    by (irule iszero_prefix_push_branch >> simp[sym_with_pc_def,Abbr `p`,EL_APPEND_EQN]) >>
  `sym_steps q env 2 u =
     if w=0w then SymOK (sym_with_pc (u.sym_base.as_pc+2) (u with sym_stack := stk))
     else case INDEX_OF (AsmLabel l) q of
            NONE => SymBad "jumpi target"
          | SOME i => SymOK (sym_with_pc i (u with sym_stack := stk))`
    by (irule iszero_prefix_push_branch >> simp[Abbr `q`,EL_APPEND_EQN]) >>
  Cases_on `w=0w`
  >- gvs[splice_pc_def,sym_with_pc_def,sym_state_component_equality,asm_state_component_equality] >>
  Cases_on `INDEX_OF (AsmLabel l) p` >>
  gvs[sym_with_pc_def,sym_state_component_equality,asm_state_component_equality]
QED
