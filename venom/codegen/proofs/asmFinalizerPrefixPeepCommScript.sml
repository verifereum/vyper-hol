Theory asmFinalizerPrefixPeepComm
Ancestors
  asmSplice asmSymPc asmSymSem asmOptimizer asmWf asmOptPeephole asmSem list

(* Quotation only: no new logical constant. *)
val window = ``\pre pat repl post D.
  !env u. u.sym_base.as_pc = LENGTH pre /\ u.sym_base.as_stack = [] /\
    sym_state_labels_in (asm_label_refs (pre ++ pat ++ post)) u ==>
    ?d. 0 < d /\ d <= D /\
      (!i a. i < d /\ sym_steps (pre ++ pat ++ post) env i u = SymOK a ==>
        ~(a.sym_base.as_pc < LENGTH (pre ++ pat ++ post) /\
          EL a.sym_base.as_pc (pre ++ pat ++ post) = AsmOp "GAS")) /\
      (!a. sym_steps (pre ++ pat ++ post) env d u = SymOK a ==>
        ?e. sym_steps (pre ++ repl ++ post) env e u =
          SymOK (sym_with_pc
            (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) a.sym_base.as_pc) a) /\
          (a.sym_base.as_pc <= LENGTH pre \/ LENGTH pre + LENGTH pat <= a.sym_base.as_pc) /\
          (e = 0 ==> LENGTH pre + LENGTH pat <= a.sym_base.as_pc))``;

Theorem swap1_commutative_bounded_window:
  !pre post y. asm_commutative_op y ==>
    ^window pre [AsmOp "SWAP1"; y] [y] post 2
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  `?name. y = AsmOp name` by (Cases_on `y` >> gvs[asm_commutative_op_def]) >>
  gvs[] >> rpt gen_tac >> strip_tac >> qexists_tac `2` >> simp[] >>
  `name <> "GAS"` by
    (strip_tac >> gvs[] >> qpat_x_assum `asm_commutative_op _` mp_tac >> EVAL_TAC) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> `i = 0 \/ i = 1` by decide_tac >>
      gvs[sym_steps_pos, sym_steps_def, EL_APPEND_EQN, sym_step_def, sym_step_op_def,
          dup_table_def, swap_table_def, sym_swap_def, sym_set_stack_def,
          asm_next_def, AllCaseEqs()]) >>
  gen_tac >> strip_tac >> qexists_tac `1` >>
  qabbrev_tac `p = pre ++ [AsmOp "SWAP1"; AsmOp name] ++ post` >>
  qabbrev_tac `q = pre ++ [AsmOp name] ++ post` >>
  `LENGTH pre < LENGTH p /\ EL (LENGTH pre) p = AsmOp "SWAP1" /\
   LENGTH pre + 1 < LENGTH p /\ EL (LENGTH pre + 1) p = AsmOp name /\
   LENGTH pre < LENGTH q /\ EL (LENGTH pre) q = AsmOp name`
    by simp[Abbr `p`, Abbr `q`, EL_APPEND_EQN] >>
  `sym_step p env (AsmOp "SWAP1") u = sym_swap 1 u`
    by (irule sym_step_swap_table >> simp[swap_table_def]) >>
  Cases_on `u.sym_stack`
  >- gvs[sym_steps_pos, sym_steps_def, sym_swap_def] >>
  rename1 `u.sym_stack = x::t` >> Cases_on `t`
  >- gvs[sym_steps_pos, sym_steps_def, sym_swap_def] >>
  rename1 `u.sym_stack = x::y::stk` >>
  qabbrev_tac `s1 = u with <|sym_base := asm_next u.sym_base;
                            sym_stack := y::x::stk|>` >>
  `sym_swap 1 u = SymOK s1`
    by simp[Abbr `s1`, sym_swap_def, sym_set_stack_def, LUPDATE_compute] >>
  `s1.sym_base.as_pc = LENGTH pre + 1`
    by simp[Abbr `s1`, asm_next_def] >>
  reverse (Cases_on `MEM name ["ADD"; "MUL"; "EQ"; "AND"; "OR"; "XOR"]`)
  >- (`~MEM name (MAP FST asm_op_arity_table) /\
       ALOOKUP dup_table name = NONE /\ ALOOKUP swap_table name = NONE` by
        (gvs[asm_op_arity_table_def, dup_table_def, swap_table_def,
             alistTheory.ALOOKUP_NONE] >>
         rpt strip_tac >> qpat_x_assum `name = _` SUBST_ALL_TAC >>
         qpat_x_assum `asm_commutative_op _` mp_tac >> EVAL_TAC) >>
      drule_all sym_step_unknown_op >>
      disch_then (qspecl_then [`s1`, `p`, `env`] strip_assume_tac) >>
      gvs[sym_steps_pos, sym_steps_def]) >>
  `s1 = sym_with_pc (u.sym_base.as_pc + 1)
          (u with sym_stack := y::x::stk)`
    by simp[Abbr `s1`, sym_with_pc_def, asm_next_def] >>
  `AsmOp name <> AsmOp "JUMP" /\ AsmOp name <> AsmOp "JUMPI"` by gvs[] >>
  `sym_step p env (AsmOp name) s1 =
   sym_result_pc_add 1 (sym_step q env (AsmOp name) u)` by
    (qpat_x_assum `s1 = _` SUBST1_TAC >>
     mp_tac (Q.INST [`inst` |-> `AsmOp name`, `n` |-> `1`,
                     `ss` |-> `u with sym_stack := y::x::stk`] sym_step_pc_add) >>
     (impl_tac >- simp[]) >>
     disch_then (SUBST1_TAC o SIMP_RULE (srw_ss()) []) >>
     drule sym_step_commutative_swap >>
     disch_then (fn th => once_rewrite_tac[th]) >>
     `u with sym_stack := x::y::stk = u`
       by simp[sym_state_component_equality] >>
     pop_assum SUBST1_TAC >> AP_TERM_TAC >>
     irule sym_step_prog_cong >> simp[Abbr `p`, Abbr `q`]) >>
  qpat_x_assum `s1 = sym_with_pc _ _` kall_tac >>
  qpat_x_assum `sym_steps p env 2 u = _` mp_tac >>
  simp[sym_steps_pos, sym_steps_def] >> strip_tac >>
  qpat_x_assum `MEM name _` kall_tac >>
  Cases_on `sym_step q env (AsmOp name) u` >>
  gvs[sym_result_pc_add_def] >>
  rename1 `sym_step q env (AsmOp name) u = SymOK s2` >>
  `s2.sym_base.as_pc = LENGTH pre + 1`
    by (drule_at (Pos last) sym_step_pc_next >> simp[]) >>
  simp[splice_pc_def, sym_with_pc_def, sym_state_component_equality,
       asm_state_component_equality]

QED
