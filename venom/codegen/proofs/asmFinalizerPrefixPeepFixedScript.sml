Theory asmFinalizerPrefixPeepFixed
Ancestors
  asmSplice asmSymPc asmSymSem asmOptimizer asmWf asmOptPeephole asmSem list

(* Quotation only; the exported statements expand the bounded-window schema. *)
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

Theorem dup1_swap1_bounded_window:
  !pre post. ^window pre [AsmOp "DUP1"; AsmOp "SWAP1"] [AsmOp "DUP1"] post 2
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >> qexists_tac `2` >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> `i = 0 \/ i = 1` by decide_tac >>
      gvs[sym_steps_pos, sym_steps_def, EL_APPEND_EQN, sym_step_def, sym_step_op_def,
          dup_table_def, swap_table_def, sym_dup_def, sym_set_stack_def,
          asm_next_def, AllCaseEqs()]) >>
  gen_tac >> strip_tac >> qexists_tac `1` >>
  Cases_on `u.sym_stack` >>
  gvs[sym_steps_pos, sym_steps_def, EL_APPEND_EQN, sym_step_def, sym_step_op_def,
      dup_table_def, swap_table_def, sym_dup_def, sym_swap_def,
      sym_set_stack_def, asm_next_def, LUPDATE_compute,
      splice_pc_def, sym_with_pc_def, sym_state_component_equality,
      asm_state_component_equality]
QED

Theorem dup1_swap1_pop_bounded_window:
  !pre post. ^window pre [AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "POP"] [] post 3
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >> qexists_tac `3` >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> `i = 0 \/ i = 1 \/ i = 2` by decide_tac >>
      Cases_on `u.sym_stack` >>
      gvs[sym_steps_pos, sym_steps_def, EL_APPEND_EQN, sym_step_def, sym_step_op_def,
          dup_table_def, swap_table_def, sym_dup_def, sym_swap_def, sym_set_stack_def,
          asm_next_def, LUPDATE_compute, AllCaseEqs()]) >>
  gen_tac >> strip_tac >> qexists_tac `0` >>
  Cases_on `u.sym_stack` >>
  gvs[sym_steps_pos, sym_steps_def, EL_APPEND_EQN, sym_step_def, sym_step_op_def,
      dup_table_def, swap_table_def, sym_dup_def, sym_swap_def,
      sym_set_stack_def, asm_next_def, LUPDATE_compute,
      splice_pc_def, sym_with_pc_def, sym_state_component_equality,
      asm_state_component_equality]
QED

Theorem dup1_swap2_swap1_bounded_window:
  !pre post. ^window pre [AsmOp "DUP1"; AsmOp "SWAP2"; AsmOp "SWAP1"]
    [AsmOp "SWAP1"; AsmOp "DUP2"] post 3
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >> qexists_tac `3` >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> `i = 0 \/ i = 1 \/ i = 2` by decide_tac >>
      Cases_on `u.sym_stack` >>
      gvs[sym_steps_pos, sym_steps_def, EL_APPEND_EQN, sym_step_def, sym_step_op_def,
          dup_table_def, swap_table_def, sym_dup_def, sym_swap_def, sym_set_stack_def,
          asm_next_def, LUPDATE_compute, AllCaseEqs()]) >>
  gen_tac >> strip_tac >> qexists_tac `2` >>
  Cases_on `u.sym_stack`
  >- gvs[sym_steps_pos, sym_steps_def, EL_APPEND_EQN, sym_step_def, sym_step_op_def,
         dup_table_def, swap_table_def, sym_dup_def] >>
  rename1 `u.sym_stack = h::t` >> Cases_on `t` >>
  gvs[sym_steps_pos, sym_steps_def, EL_APPEND_EQN, sym_step_def, sym_step_op_def,
      dup_table_def, swap_table_def, sym_dup_def, sym_swap_def,
      sym_set_stack_def, asm_next_def, LUPDATE_compute,
      splice_pc_def, sym_with_pc_def, sym_state_component_equality,
      asm_state_component_equality]
QED

Theorem swap1_pop_pop_bounded_window:
  !pre post. ^window pre [AsmOp "SWAP1"; AsmOp "POP"; AsmOp "POP"]
    [AsmOp "POP"; AsmOp "POP"] post 3
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >> qexists_tac `3` >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> `i = 0 \/ i = 1 \/ i = 2` by decide_tac >>
      Cases_on `u.sym_stack` >>
      gvs[sym_steps_pos, sym_steps_def, EL_APPEND_EQN, sym_step_def, sym_step_op_def,
          dup_table_def, swap_table_def, sym_dup_def, sym_swap_def,
          sym_set_stack_def, asm_next_def, LUPDATE_compute, AllCaseEqs()]) >>
  gen_tac >> strip_tac >> qexists_tac `2` >>
  Cases_on `u.sym_stack`
  >- gvs[sym_steps_pos, sym_steps_def, EL_APPEND_EQN, sym_step_def, sym_step_op_def,
         dup_table_def, swap_table_def, sym_swap_def] >>
  rename1 `u.sym_stack = h::t` >> Cases_on `t` >>
  gvs[sym_steps_pos, sym_steps_def, EL_APPEND_EQN, sym_step_def, sym_step_op_def,
      dup_table_def, swap_table_def, sym_dup_def, sym_swap_def,
      sym_set_stack_def, asm_next_def, LUPDATE_compute,
      splice_pc_def, sym_with_pc_def, sym_state_component_equality,
      asm_state_component_equality]
QED
