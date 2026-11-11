(*
 * stack_peephole_opts refines its input.
 *
 * Each rewrite is a splice whose window only shuffles the stack:
 *   DUP1 SWAP2 SWAP1 -> SWAP1 DUP2
 *   DUP1 SWAP1 POP   -> nothing
 *   SWAP1 POP POP    -> POP POP
 *   SWAPn SWAPn      -> nothing
 *   SWAP1 op         -> op, for a commutative op
 *   DUP1 SWAP1       -> DUP1
 * A stack too short for the pattern makes the original run fail, which
 * constrains nothing. The rule matches some names that aren't opcodes
 * (SWAP followed by anything, commutative op names in any case, and NE);
 * running one fails, so those windows hold too.
 *
 * TOP-LEVEL:
 *   stack_peephole_opts_refines — the rule's obligation in
 *                                 asm_opt_finalizer_correct
 *)

Theory asmOptPeephole
Ancestors
  asmSplice asmSymPc finalizerContract asmSymSem asmOptimizer asmWf
  asmSem symbolResolve list

(* ===== Names that aren't opcodes ===== *)

Theorem sym_step_unknown_op:
  ¬MEM name (MAP FST asm_op_arity_table) ∧ ALOOKUP dup_table name = NONE ∧
  ALOOKUP swap_table name = NONE ⇒
  ∃e. sym_step p env (AsmOp name) ss = SymError e
Proof
  simp[asm_op_arity_table_def, dup_table_def, swap_table_def] >>
  strip_tac >>
  simp[sym_step_def, sym_step_op_def, dup_table_def, swap_table_def,
       sym_step_concrete_def, asm_op_arity_def, asm_op_arity_table_def,
       asm_op_mem_reads_def, log_table_def, mem_labels_hit_def,
       sym_lift_def, asm_step_op_def, asm_step_arith_def,
       asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
       asm_step_control_def, asm_step_extcall_def, asm_step_copy_def,
       asm_step_context_def]
QED

Theorem swap_prefix_names[local]:
  EVERY (λn. isPREFIX "SWAP" n ⇒ IS_SOME (ALOOKUP swap_table n))
    (MAP FST asm_op_arity_table ++ MAP FST dup_table ++ MAP FST swap_table)
Proof
  EVAL_TAC
QED

Theorem swap_prefix_unknown[local]:
  isPREFIX "SWAP" name ∧ ALOOKUP swap_table name = NONE ⇒
  ¬MEM name (MAP FST asm_op_arity_table) ∧ ALOOKUP dup_table name = NONE
Proof
  strip_tac >>
  `¬IS_SOME (ALOOKUP swap_table name)` by simp[] >>
  `∀n. MEM n (MAP FST asm_op_arity_table ++ MAP FST dup_table ++
              MAP FST swap_table) ⇒
       isPREFIX "SWAP" n ⇒ IS_SOME (ALOOKUP swap_table n)`
    by (mp_tac swap_prefix_names >> REWRITE_TAC [EVERY_MEM] >>
        BETA_TAC >> REWRITE_TAC []) >>
  `¬MEM name (MAP FST asm_op_arity_table ++ MAP FST dup_table ++
              MAP FST swap_table)` by metis_tac[] >>
  gvs[alistTheory.ALOOKUP_NONE]
QED

Theorem commutative_names[local]:
  EVERY (λn. asm_commutative_op (AsmOp n) ⇒
             MEM n ["ADD"; "MUL"; "EQ"; "AND"; "OR"; "XOR"])
    (MAP FST asm_op_arity_table ++ MAP FST dup_table ++ MAP FST swap_table)
Proof
  EVAL_TAC
QED

Theorem commutative_unknown[local]:
  asm_commutative_op (AsmOp name) ∧
  ¬MEM name ["ADD"; "MUL"; "EQ"; "AND"; "OR"; "XOR"] ⇒
  ¬MEM name (MAP FST asm_op_arity_table) ∧ ALOOKUP dup_table name = NONE ∧
  ALOOKUP swap_table name = NONE
Proof
  strip_tac >>
  `∀n. MEM n (MAP FST asm_op_arity_table ++ MAP FST dup_table ++
              MAP FST swap_table) ⇒
       asm_commutative_op (AsmOp n) ⇒
       MEM n ["ADD"; "MUL"; "EQ"; "AND"; "OR"; "XOR"]`
    by (mp_tac commutative_names >> REWRITE_TAC [EVERY_MEM] >>
        BETA_TAC >> REWRITE_TAC []) >>
  `¬MEM name (MAP FST asm_op_arity_table ++ MAP FST dup_table ++
              MAP FST swap_table)` by metis_tac[] >>
  gvs[alistTheory.ALOOKUP_NONE]
QED

(* ===== Stack shuffles ===== *)

Theorem sym_step_swap_table:
  ALOOKUP swap_table name = SOME n ⇒
  sym_step p env (AsmOp name) ss = sym_swap n ss
Proof
  simp[swap_table_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[sym_step_def, sym_step_op_def, dup_table_def, swap_table_def]
QED

Theorem swap_swap_id[local]:
  n < LENGTH stk ∧ 0 < n ⇒
  LUPDATE (HD (LUPDATE (HD stk) n (LUPDATE (EL n stk) 0 stk))) n
    (LUPDATE (EL n (LUPDATE (HD stk) n (LUPDATE (EL n stk) 0 stk))) 0
       (LUPDATE (HD stk) n (LUPDATE (EL n stk) 0 stk))) = stk
Proof
  Cases_on `stk` >> Cases_on `n` >> simp[LUPDATE_def] >> strip_tac >>
  simp[EL_LUPDATE, LUPDATE_SAME] >>
  rw[LIST_EQ_REWRITE, EL_LUPDATE] >> rw[]
QED

(* ADD, MUL, EQ, AND, OR and XOR don't see their operands' order. *)
Theorem sym_lift_commutative[local]:
  MEM name ["ADD"; "MUL"; "EQ"; "AND"; "OR"; "XOR"] ⇒
  sym_lift 2 labs (ss with sym_stack := Val x :: Val y :: stk)
    (asm_step_op FEMPTY name (s0 with as_stack := [x; y])) =
  sym_lift 2 labs (ss with sym_stack := Val y :: Val x :: stk)
    (asm_step_op FEMPTY name (s0 with as_stack := [y; x]))
Proof
  rw[] >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_binop_def, sym_lift_def] >>
  simp[wordsTheory.WORD_ADD_COMM, wordsTheory.WORD_MULT_COMM,
       wordsTheory.WORD_AND_COMM, wordsTheory.WORD_OR_COMM,
       wordsTheory.WORD_XOR_COMM, EQ_SYM_EQ]
QED

Theorem sym_step_concrete_commutative[local]:
  MEM name ["ADD"; "MUL"; "EQ"; "AND"; "OR"; "XOR"] ⇒
  sym_step_concrete name (ss with sym_stack := b :: a :: stk) =
  sym_step_concrete name (ss with sym_stack := a :: b :: stk)
Proof
  strip_tac >>
  `asm_op_arity name = 2 ∧ (∀args. asm_op_mem_reads name args = (λi. F)) ∧
   (∀args. asm_op_mem_writes name args = (λi. F))`
    by (gvs[] >>
        simp[asm_op_arity_def, asm_op_arity_table_def, asm_op_mem_reads_def,
             asm_op_mem_writes_def, log_table_def, FUN_EQ_THM]) >>
  Cases_on `a` >> Cases_on `b` >>
  simp[sym_step_concrete_def, sval_val_def, mem_labels_hit_def] >>
  simp[sym_lift_commutative]
QED

Theorem sym_step_commutative_swap:
  MEM name ["ADD"; "MUL"; "EQ"; "AND"; "OR"; "XOR"] ⇒
  sym_step p env (AsmOp name) (ss with sym_stack := b :: a :: stk) =
  sym_step p env (AsmOp name) (ss with sym_stack := a :: b :: stk)
Proof
  rw[]
  >~ [`AsmOp "ADD"`]
  >- (Cases_on `a` >> Cases_on `b` >>
      simp[sym_step_def, sym_step_op_def, sym_add_def, sym_push_lab_def,
           sym_set_stack_def, sym_step_concrete_commutative]) >>
  simp[sym_step_def, sym_step_op_def, dup_table_def, swap_table_def,
       sym_step_concrete_commutative]
QED

(* ===== Windows ===== *)

Theorem dup1_swap2_swap1_window[local]:
  asm_window_refines pfx [AsmOp "DUP1"; AsmOp "SWAP2"; AsmOp "SWAP1"]
    [AsmOp "SWAP1"; AsmOp "DUP2"] sfx
Proof
  simp_tac bool_ss [asm_window_refines_def, GSYM APPEND_ASSOC, APPEND] >>
  rpt strip_tac >>
  qabbrev_tac `p = pfx ++ AsmOp "DUP1" :: AsmOp "SWAP2" :: AsmOp "SWAP1" ::
                   sfx` >>
  qabbrev_tac `q = pfx ++ AsmOp "SWAP1" :: AsmOp "DUP2" :: sfx` >>
  `LENGTH pfx < LENGTH p ∧ EL (LENGTH pfx) p = AsmOp "DUP1" ∧
   LENGTH pfx + 1 < LENGTH p ∧ EL (LENGTH pfx + 1) p = AsmOp "SWAP2" ∧
   LENGTH pfx + 2 < LENGTH p ∧ EL (LENGTH pfx + 2) p = AsmOp "SWAP1" ∧
   LENGTH pfx < LENGTH q ∧ EL (LENGTH pfx) q = AsmOp "SWAP1" ∧
   LENGTH pfx + 1 < LENGTH q ∧ EL (LENGTH pfx + 1) q = AsmOp "DUP2"`
    by simp[Abbr `p`, Abbr `q`, EL_APPEND_EQN] >>
  qexistsl_tac [`3`, `2`] >>
  Cases_on `ss.sym_stack` >>
  simp[sym_steps_pos, sym_steps_def, sym_step_def, sym_step_op_def,
       dup_table_def, swap_table_def, sym_dup_def, sym_swap_def,
       sym_set_stack_def, asm_next_def, sym_terminal_def] >>
  rename1 `_ = h :: t` >> Cases_on `t` >>
  simp[sym_steps_pos, sym_steps_def, sym_step_def, sym_step_op_def,
       dup_table_def, swap_table_def, sym_dup_def, sym_swap_def,
       sym_set_stack_def, asm_next_def, sym_terminal_def, LUPDATE_compute,
       splice_pc_def, sym_with_pc_def, sym_state_component_equality,
       asm_state_component_equality]
QED

Theorem dup1_swap1_pop_window[local]:
  asm_window_refines pfx [AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "POP"] [] sfx
Proof
  simp_tac bool_ss [asm_window_refines_def, GSYM APPEND_ASSOC, APPEND] >>
  rpt strip_tac >>
  qabbrev_tac `p = pfx ++ AsmOp "DUP1" :: AsmOp "SWAP1" :: AsmOp "POP" ::
                   sfx` >>
  `LENGTH pfx < LENGTH p ∧ EL (LENGTH pfx) p = AsmOp "DUP1" ∧
   LENGTH pfx + 1 < LENGTH p ∧ EL (LENGTH pfx + 1) p = AsmOp "SWAP1" ∧
   LENGTH pfx + 2 < LENGTH p ∧ EL (LENGTH pfx + 2) p = AsmOp "POP"`
    by simp[Abbr `p`, EL_APPEND_EQN] >>
  qexistsl_tac [`3`, `0`] >>
  Cases_on `ss.sym_stack` >>
  simp[sym_steps_pos, sym_steps_def, sym_step_def, sym_step_op_def,
       dup_table_def, swap_table_def, sym_dup_def, sym_swap_def,
       sym_set_stack_def, asm_next_def, sym_terminal_def, LUPDATE_compute,
       splice_pc_def, sym_with_pc_def, sym_state_component_equality,
       asm_state_component_equality]
QED

Theorem swap1_pop_pop_window[local]:
  asm_window_refines pfx [AsmOp "SWAP1"; AsmOp "POP"; AsmOp "POP"]
    [AsmOp "POP"; AsmOp "POP"] sfx
Proof
  simp_tac bool_ss [asm_window_refines_def, GSYM APPEND_ASSOC, APPEND] >>
  rpt strip_tac >>
  qabbrev_tac `p = pfx ++ AsmOp "SWAP1" :: AsmOp "POP" :: AsmOp "POP" ::
                   sfx` >>
  qabbrev_tac `q = pfx ++ AsmOp "POP" :: AsmOp "POP" :: sfx` >>
  `LENGTH pfx < LENGTH p ∧ EL (LENGTH pfx) p = AsmOp "SWAP1" ∧
   LENGTH pfx + 1 < LENGTH p ∧ EL (LENGTH pfx + 1) p = AsmOp "POP" ∧
   LENGTH pfx + 2 < LENGTH p ∧ EL (LENGTH pfx + 2) p = AsmOp "POP" ∧
   LENGTH pfx < LENGTH q ∧ EL (LENGTH pfx) q = AsmOp "POP" ∧
   LENGTH pfx + 1 < LENGTH q ∧ EL (LENGTH pfx + 1) q = AsmOp "POP"`
    by simp[Abbr `p`, Abbr `q`, EL_APPEND_EQN] >>
  qexistsl_tac [`3`, `2`] >>
  Cases_on `ss.sym_stack` >>
  simp[sym_steps_pos, sym_steps_def, sym_step_def, sym_step_op_def,
       dup_table_def, swap_table_def, sym_swap_def, sym_set_stack_def,
       asm_next_def, sym_terminal_def] >>
  rename1 `_ = h :: t` >> Cases_on `t` >>
  simp[sym_steps_pos, sym_steps_def, sym_step_def, sym_step_op_def,
       dup_table_def, swap_table_def, sym_swap_def, sym_set_stack_def,
       asm_next_def, sym_terminal_def, LUPDATE_compute, splice_pc_def,
       sym_with_pc_def, sym_state_component_equality,
       asm_state_component_equality]
QED

Theorem dup1_swap1_window[local]:
  asm_window_refines pfx [AsmOp "DUP1"; AsmOp "SWAP1"] [AsmOp "DUP1"] sfx
Proof
  simp_tac bool_ss [asm_window_refines_def, GSYM APPEND_ASSOC, APPEND] >>
  rpt strip_tac >>
  qabbrev_tac `p = pfx ++ AsmOp "DUP1" :: AsmOp "SWAP1" :: sfx` >>
  qabbrev_tac `q = pfx ++ AsmOp "DUP1" :: sfx` >>
  `LENGTH pfx < LENGTH p ∧ EL (LENGTH pfx) p = AsmOp "DUP1" ∧
   LENGTH pfx + 1 < LENGTH p ∧ EL (LENGTH pfx + 1) p = AsmOp "SWAP1" ∧
   LENGTH pfx < LENGTH q ∧ EL (LENGTH pfx) q = AsmOp "DUP1"`
    by simp[Abbr `p`, Abbr `q`, EL_APPEND_EQN] >>
  qexistsl_tac [`2`, `1`] >>
  Cases_on `ss.sym_stack` >>
  simp[sym_steps_pos, sym_steps_def, sym_step_def, sym_step_op_def,
       dup_table_def, swap_table_def, sym_dup_def, sym_swap_def,
       sym_set_stack_def, asm_next_def, sym_terminal_def, LUPDATE_compute,
       splice_pc_def, sym_with_pc_def, sym_state_component_equality,
       asm_state_component_equality]
QED

Theorem swap_pair_window[local]:
  isPREFIX "SWAP" name ⇒
  asm_window_refines pfx [AsmOp name; AsmOp name] [] sfx
Proof
  strip_tac >>
  simp_tac bool_ss [asm_window_refines_def, GSYM APPEND_ASSOC, APPEND] >>
  rpt strip_tac >>
  qabbrev_tac `p = pfx ++ AsmOp name :: AsmOp name :: sfx` >>
  `LENGTH pfx < LENGTH p ∧ EL (LENGTH pfx) p = AsmOp name ∧
   LENGTH pfx + 1 < LENGTH p ∧ EL (LENGTH pfx + 1) p = AsmOp name`
    by simp[Abbr `p`, EL_APPEND_EQN] >>
  qexistsl_tac [`2`, `0`] >>
  Cases_on `ALOOKUP swap_table name`
  >- (drule_all swap_prefix_unknown >> strip_tac >>
      drule_all sym_step_unknown_op >>
      disch_then (qspecl_then [`ss`, `p`, `env`] strip_assume_tac) >>
      simp[sym_steps_pos, sym_terminal_def]) >>
  rename1 `ALOOKUP swap_table name = SOME n` >>
  drule sym_step_swap_table >> strip_tac >>
  simp[sym_steps_pos, sym_steps_def, sym_swap_def] >>
  IF_CASES_TAC >> simp[sym_terminal_def, sym_set_stack_def] >>
  simp[asm_next_def, sym_steps_pos, sym_steps_def, sym_swap_def,
       sym_set_stack_def, swap_swap_id, sym_terminal_def, splice_pc_def,
       sym_with_pc_def, sym_state_component_equality,
       asm_state_component_equality]
QED

Theorem swap1_commutative_window[local]:
  asm_commutative_op (AsmOp name) ⇒
  asm_window_refines pfx [AsmOp "SWAP1"; AsmOp name] [AsmOp name] sfx
Proof
  strip_tac >>
  simp_tac bool_ss [asm_window_refines_def, GSYM APPEND_ASSOC, APPEND] >>
  rpt strip_tac >>
  qabbrev_tac `p = pfx ++ AsmOp "SWAP1" :: AsmOp name :: sfx` >>
  qabbrev_tac `q = pfx ++ AsmOp name :: sfx` >>
  `LENGTH pfx < LENGTH p ∧ EL (LENGTH pfx) p = AsmOp "SWAP1" ∧
   LENGTH pfx + 1 < LENGTH p ∧ EL (LENGTH pfx + 1) p = AsmOp name ∧
   LENGTH pfx < LENGTH q ∧ EL (LENGTH pfx) q = AsmOp name`
    by simp[Abbr `p`, Abbr `q`, EL_APPEND_EQN] >>
  `sym_step p env (AsmOp "SWAP1") ss = sym_swap 1 ss`
    by (irule sym_step_swap_table >> simp[swap_table_def]) >>
  qexistsl_tac [`2`, `1`] >>
  `(∃e. sym_swap 1 ss = SymError e) ∨ ∃a b stk. ss.sym_stack = a :: b :: stk`
    by (Cases_on `ss.sym_stack` >> simp[sym_swap_def] >>
        rename1 `_ = _ :: t` >> Cases_on `t` >> simp[]) >>
  gvs[sym_steps_pos, sym_terminal_def] >>
  qabbrev_tac `s1 = ss with <| sym_base := asm_next ss.sym_base;
                               sym_stack := b :: a :: stk |>` >>
  `sym_swap 1 ss = SymOK s1`
    by simp[Abbr `s1`, sym_swap_def, sym_set_stack_def, LUPDATE_compute] >>
  `s1.sym_base.as_pc = LENGTH pfx + 1`
    by simp[Abbr `s1`, asm_next_def] >>
  reverse (Cases_on `MEM name ["ADD"; "MUL"; "EQ"; "AND"; "OR"; "XOR"]`)
  >- (drule_all commutative_unknown >> strip_tac >>
      drule_all sym_step_unknown_op >>
      disch_then (qspecl_then [`s1`, `p`, `env`] strip_assume_tac) >>
      simp[sym_steps_pos, sym_terminal_def]) >>
  `s1 = sym_with_pc (ss.sym_base.as_pc + 1)
          (ss with sym_stack := b :: a :: stk)`
    by simp[Abbr `s1`, sym_with_pc_def, asm_next_def] >>
  `AsmOp name ≠ AsmOp "JUMP" ∧ AsmOp name ≠ AsmOp "JUMPI"` by gvs[] >>
  `sym_step p env (AsmOp name) s1 =
   sym_result_pc_add 1 (sym_step q env (AsmOp name) ss)`
    by (qpat_x_assum `s1 = _` SUBST1_TAC >>
        mp_tac (Q.INST [`inst` |-> `AsmOp name`, `n` |-> `1`,
                        `ss` |-> `ss with sym_stack := b :: a :: stk`]
                  sym_step_pc_add) >>
        impl_tac >- simp[] >>
        disch_then (SUBST1_TAC o SIMP_RULE (srw_ss()) []) >>
        mp_tac sym_step_commutative_swap >>
        impl_tac >- simp[] >>
        disch_then SUBST1_TAC >>
        `(ss with sym_stack := a :: b :: stk) = ss`
          by simp[sym_state_component_equality] >>
        pop_assum SUBST1_TAC >> AP_TERM_TAC >>
        irule sym_step_prog_cong >> simp[Abbr `p`, Abbr `q`]) >>
  qpat_x_assum `s1 = sym_with_pc _ _` kall_tac >>
  Cases_on `sym_step q env (AsmOp name) ss` >>
  simp[sym_steps_pos, sym_steps_def, sym_result_pc_add_def, sym_terminal_def,
       sym_result_rel_def, sym_obs_def, sym_with_pc_def] >>
  rename1 `sym_step q env (AsmOp name) ss = SymOK s2` >>
  `s2.sym_base.as_pc = LENGTH pfx + 1`
    by (drule_at (Pos last) sym_step_pc_next >> simp[]) >>
  simp[splice_pc_def, sym_state_component_equality,
       asm_state_component_equality]
QED

(* ===== Splices ===== *)

Theorem dup2_opcode[local]:
  IS_SOME (evm_opcode_byte "DUP2")
Proof
  EVAL_TAC
QED

Theorem dup1_swap2_swap1_refines[local]:
  asm_refines (pfx ++ AsmOp "DUP1" :: AsmOp "SWAP2" :: AsmOp "SWAP1" :: rest)
              (pfx ++ AsmOp "SWAP1" :: AsmOp "DUP2" :: rest)
Proof
  mp_tac (Q.INST [`pat` |-> `[AsmOp "DUP1"; AsmOp "SWAP2"; AsmOp "SWAP1"]`,
                  `repl` |-> `[AsmOp "SWAP1"; AsmOp "DUP2"]`,
                  `sfx` |-> `rest`] asm_splice_window_refines) >>
  impl_tac
  >- (rpt conj_tac
      >- simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
              asm_inst_size_def, dup2_opcode, DISJ_IMP_THM, FORALL_AND_THM]
      >- simp[]
      >- simp[dup1_swap2_swap1_window]) >>
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> disch_then ACCEPT_TAC
QED

Theorem dup1_swap1_pop_refines[local]:
  asm_refines (pfx ++ AsmOp "DUP1" :: AsmOp "SWAP1" :: AsmOp "POP" :: rest)
              (pfx ++ rest)
Proof
  mp_tac (Q.INST [`pat` |-> `[AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "POP"]`,
                  `repl` |-> `[]`, `sfx` |-> `rest`]
            asm_splice_window_refines) >>
  impl_tac
  >- (rpt conj_tac
      >- simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
              asm_inst_size_def, dup2_opcode, DISJ_IMP_THM, FORALL_AND_THM]
      >- simp[]
      >- simp[dup1_swap1_pop_window]) >>
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> disch_then ACCEPT_TAC
QED

Theorem swap1_pop_pop_refines[local]:
  asm_refines (pfx ++ AsmOp "SWAP1" :: AsmOp "POP" :: AsmOp "POP" :: rest)
              (pfx ++ AsmOp "POP" :: AsmOp "POP" :: rest)
Proof
  mp_tac (Q.INST [`pat` |-> `[AsmOp "SWAP1"; AsmOp "POP"; AsmOp "POP"]`,
                  `repl` |-> `[AsmOp "POP"; AsmOp "POP"]`, `sfx` |-> `rest`]
            asm_splice_window_refines) >>
  impl_tac
  >- (rpt conj_tac
      >- simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
              asm_inst_size_def, dup2_opcode, DISJ_IMP_THM, FORALL_AND_THM]
      >- simp[]
      >- simp[swap1_pop_pop_window]) >>
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> disch_then ACCEPT_TAC
QED

Theorem swap_pair_refines[local]:
  isPREFIX "SWAP" name ⇒
  asm_refines (pfx ++ AsmOp name :: AsmOp name :: rest) (pfx ++ rest)
Proof
  strip_tac >>
  mp_tac (Q.INST [`pat` |-> `[AsmOp name; AsmOp name]`,
                  `repl` |-> `[]`, `sfx` |-> `rest`]
            asm_splice_window_refines) >>
  impl_tac
  >- (rpt conj_tac
      >- simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
              asm_inst_size_def, dup2_opcode, DISJ_IMP_THM, FORALL_AND_THM]
      >- simp[]
      >- simp[swap_pair_window]) >>
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> disch_then ACCEPT_TAC
QED

Theorem swap1_commutative_refines[local]:
  asm_commutative_op y ⇒
  asm_refines (pfx ++ AsmOp "SWAP1" :: y :: rest) (pfx ++ y :: rest)
Proof
  strip_tac >>
  `∃name. y = AsmOp name` by (Cases_on `y` >> gvs[asm_commutative_op_def]) >>
  gvs[] >>
  mp_tac (Q.INST [`pat` |-> `[AsmOp "SWAP1"; AsmOp name]`,
                  `repl` |-> `[AsmOp name]`, `sfx` |-> `rest`]
            asm_splice_window_refines) >>
  impl_tac
  >- (rpt conj_tac
      >- simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
              asm_inst_size_def, dup2_opcode, DISJ_IMP_THM, FORALL_AND_THM]
      >- simp[]
      >- simp[swap1_commutative_window]) >>
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> disch_then ACCEPT_TAC
QED

Theorem dup1_swap1_refines[local]:
  asm_refines (pfx ++ AsmOp "DUP1" :: AsmOp "SWAP1" :: rest)
              (pfx ++ AsmOp "DUP1" :: rest)
Proof
  mp_tac (Q.INST [`pat` |-> `[AsmOp "DUP1"; AsmOp "SWAP1"]`,
                  `repl` |-> `[AsmOp "DUP1"]`, `sfx` |-> `rest`]
            asm_splice_window_refines) >>
  impl_tac
  >- (rpt conj_tac
      >- simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
              asm_inst_size_def, dup2_opcode, DISJ_IMP_THM, FORALL_AND_THM]
      >- simp[]
      >- simp[dup1_swap1_window]) >>
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> disch_then ACCEPT_TAC
QED

(* ===== The three rules at one index ===== *)

Theorem peep_swap_pair_refines[local]:
  peep_swap_pair a b c rest = (l, ch) ⇒
  asm_refines (pfx ++ a :: b :: c :: rest) (pfx ++ l)
Proof
  rw[peep_swap_pair_def] >> simp[asm_refines_refl] >>
  Cases_on `a` >> gvs[asm_swap_op_def] >>
  irule swap_pair_refines >> simp[]
QED

Theorem peep_swap_comm_refines[local]:
  peep_swap_comm l = SOME (l', ch) ⇒ asm_refines (pfx ++ l) (pfx ++ l')
Proof
  rw[peep_swap_comm_def, AllCaseEqs()] >> simp[asm_refines_refl] >>
  irule swap1_commutative_refines >> simp[]
QED

Theorem peep_dup_swap_refines[local]:
  peep_dup_swap l = SOME (l', ch) ⇒ asm_refines (pfx ++ l) (pfx ++ l')
Proof
  rw[peep_dup_swap_def, AllCaseEqs()] >>
  simp[asm_refines_refl, dup1_swap1_refines]
QED

(* ===== The rule ===== *)

Theorem stack_peephole_opts_cons3[local]:
  stack_peephole_opts (a :: b :: c :: rest) = SOME (out, ch) ⇒
  (a = AsmOp "DUP1" ∧ b = AsmOp "SWAP2" ∧ c = AsmOp "SWAP1" ∧
   ∃ch'. stack_peephole_opts (AsmOp "SWAP1" :: AsmOp "DUP2" :: rest) =
         SOME (out, ch')) ∨
  (a = AsmOp "DUP1" ∧ b = AsmOp "SWAP1" ∧ c = AsmOp "POP" ∧
   ∃ch'. stack_peephole_opts rest = SOME (out, ch')) ∨
  (a = AsmOp "SWAP1" ∧ b = AsmOp "POP" ∧ c = AsmOp "POP" ∧
   ∃ch'. stack_peephole_opts (AsmOp "POP" :: AsmOp "POP" :: rest) =
         SOME (out, ch')) ∨
  ∃l1 ch1 l2 ch2 h t ch3 out' ch'.
    peep_swap_pair a b c rest = (l1, ch1) ∧
    peep_swap_comm l1 = SOME (l2, ch2) ∧
    peep_dup_swap l2 = SOME (h :: t, ch3) ∧
    stack_peephole_opts t = SOME (out', ch') ∧ out = h :: out'
Proof
  simp[Once stack_peephole_opts_def] >>
  rw[] >> gvs[optionTheory.OPTION_MAP_EQ_SOME, pairTheory.EXISTS_PROD] >>
  pairarg_tac >> gvs[AllCaseEqs(), optionTheory.OPTION_MAP_EQ_SOME,
                     pairTheory.EXISTS_PROD] >>
  imp_res_tac peep_dup_swap_length >>
  rename1 `peep_dup_swap _ = SOME (l3, _)` >> Cases_on `l3` >> gvs[]
QED

Theorem stack_peephole_opts_refines_under[local]:
  ∀asm pfx out c.
    stack_peephole_opts asm = SOME (out, c) ⇒
    asm_refines (pfx ++ asm) (pfx ++ out)
Proof
  measureInduct_on `LENGTH asm` >>
  Cases_on `asm` >- simp[Once stack_peephole_opts_def, asm_refines_refl] >>
  rename1 `a :: t1` >> Cases_on `t1`
  >- simp[Once stack_peephole_opts_def, asm_refines_refl] >>
  rename1 `a :: b :: t2` >> Cases_on `t2`
  >- simp[Once stack_peephole_opts_def, asm_refines_refl] >>
  rename1 `a :: b :: c1 :: rest` >> rpt gen_tac >> strip_tac >>
  drule stack_peephole_opts_cons3 >> strip_tac >> gvs[]
  >~ [`stack_peephole_opts (AsmOp "SWAP1" :: AsmOp "DUP2" :: _)`]
  >- (irule asm_refines_trans >>
      qexists_tac `pfx ++ AsmOp "SWAP1" :: AsmOp "DUP2" :: rest` >>
      simp[dup1_swap2_swap1_refines] >>
      first_x_assum irule >> simp[] >> first_assum (irule_at Any))
  >~ [`stack_peephole_opts rest = SOME _`]
  >- (irule asm_refines_trans >> qexists_tac `pfx ++ rest` >>
      simp[dup1_swap1_pop_refines] >>
      first_x_assum irule >> simp[] >> first_assum (irule_at Any))
  >~ [`stack_peephole_opts (AsmOp "POP" :: AsmOp "POP" :: _)`]
  >- (irule asm_refines_trans >>
      qexists_tac `pfx ++ AsmOp "POP" :: AsmOp "POP" :: rest` >>
      simp[swap1_pop_pop_refines] >>
      first_x_assum irule >> simp[] >> first_assum (irule_at Any)) >>
  imp_res_tac peep_swap_pair_length >>
  imp_res_tac peep_swap_comm_length >>
  imp_res_tac peep_dup_swap_length >>
  irule asm_refines_trans >> qexists_tac `pfx ++ l1` >> conj_tac
  >- (drule peep_swap_pair_refines >> simp[]) >>
  irule asm_refines_trans >> qexists_tac `pfx ++ l2` >> conj_tac
  >- (drule peep_swap_comm_refines >> simp[]) >>
  irule asm_refines_trans >> qexists_tac `pfx ++ h :: t` >> conj_tac
  >- (drule peep_dup_swap_refines >> simp[]) >>
  irule asm_refines_cons >> gen_tac >>
  first_x_assum irule >> gvs[] >> first_assum (irule_at Any)
QED

Theorem stack_peephole_opts_refines:
  ∀p p' c. stack_peephole_opts p = SOME (p', c) ⇒ asm_refines p p'
Proof
  rpt strip_tac >> drule stack_peephole_opts_refines_under >>
  disch_then (qspec_then `[]` mp_tac) >> simp[]
QED
