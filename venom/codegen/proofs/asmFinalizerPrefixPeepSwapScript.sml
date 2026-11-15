Theory asmFinalizerPrefixPeepSwap
Ancestors
  asmSplice asmSymPc asmSymSem asmOptimizer asmWf asmOptPeephole asmSem list

(* Quotation only; no new logical constant is introduced. *)
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

Theorem swap_pair_bounded_window:
  !pre post name. isPREFIX "SWAP" name ==>
    ^window pre [AsmOp name; AsmOp name] [] post 2
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `name <> "GAS"` by (strip_tac >> gvs[]) >>
  qexists_tac `2` >> simp[] >>
  Cases_on `ALOOKUP swap_table name`
  >- (drule_all swap_prefix_unknown >> strip_tac >>
      drule_all sym_step_unknown_op >>
      disch_then (qspecl_then [`u`, `pre ++ [AsmOp name; AsmOp name] ++ post`, `env`]
        strip_assume_tac) >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >> `i = 0 \/ i = 1` by decide_tac >>
          gvs[sym_steps_pos, sym_steps_def, EL_APPEND_EQN, sym_terminal_def]) >>
      simp[sym_steps_pos, EL_APPEND_EQN, sym_terminal_def]) >>
  rename1 `ALOOKUP swap_table name = SOME n` >>
  drule sym_step_swap_table >> strip_tac >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> `i = 0 \/ i = 1` by decide_tac >>
      qpat_x_assum `sym_steps _ _ _ _ = SymOK a` mp_tac >>
      simp[sym_steps_pos, sym_steps_def, EL_APPEND_EQN, sym_swap_def,
          sym_set_stack_def, asm_next_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[EL_APPEND_EQN]) >>
  gen_tac >>
  simp[sym_steps_pos, sym_steps_def, EL_APPEND_EQN, sym_swap_def,
      sym_set_stack_def, asm_next_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[swap_swap_id] >> qexists_tac `0` >>
  simp[sym_steps_def, splice_pc_def, sym_with_pc_def,
      sym_state_component_equality, asm_state_component_equality,
      asm_next_def]
QED
