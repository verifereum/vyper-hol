(* Stack peepholes preserve symbolic execution with fixed own-code bytes. *)
Theory asmOptOwnPeephole
Ancestors
  asmOptPeephole asmSpliceOwn asmSymPcOwn finalizerContractOwn
  asmSymOwnCode asmSplice asmSymPc asmSymSem asmOptimizer asmWf
  asmSem symbolResolve list

Theorem sym_steps_own_pos:
  0 < n ∧ ss.sym_base.as_pc < LENGTH p ⇒
  sym_steps_own p env own n ss =
    case sym_step_own p env own (EL ss.sym_base.as_pc p) ss of
      SymOK ss' => sym_steps_own p env own (n - 1) ss'
    | r => r
Proof
  Cases_on `n` >> rw[sym_steps_own_def]
QED

Theorem sym_step_unknown_op_own:
  ¬MEM name (MAP FST asm_op_arity_table) ∧ ALOOKUP dup_table name = NONE ∧
  ALOOKUP swap_table name = NONE ⇒
  ∀ss p env own. ∃e. sym_step_own p env own (AsmOp name) ss = SymError e
Proof
  strip_tac >>
  `name ≠ "CODESIZE" ∧ name ≠ "CODECOPY"`
    by (conj_tac >> strip_tac >> gvs[asm_op_arity_table_def]) >>
  simp[sym_step_own_eq] >> rpt gen_tac >>
  irule sym_step_unknown_op >> simp[]
QED

Theorem sym_step_swap_table_own:
  ALOOKUP swap_table name = SOME n ⇒
  sym_step_own p env own (AsmOp name) ss = sym_swap n ss
Proof
  simp[swap_table_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[sym_step_own_eq, sym_step_swap_table, swap_table_def]
QED

Theorem sym_step_commutative_swap_own:
  MEM name ["ADD"; "MUL"; "EQ"; "AND"; "OR"; "XOR"] ⇒
  sym_step_own p env own (AsmOp name) (ss with sym_stack := b :: a :: stk) =
  sym_step_own p env own (AsmOp name) (ss with sym_stack := a :: b :: stk)
Proof
  strip_tac >> `name ≠ "CODESIZE" ∧ name ≠ "CODECOPY"` by gvs[] >>
  simp[sym_step_own_eq, sym_step_commutative_swap]
QED

Theorem dup1_swap2_swap1_window_own[local]:
  asm_window_refines_own pfx [AsmOp "DUP1"; AsmOp "SWAP2"; AsmOp "SWAP1"]
    [AsmOp "SWAP1"; AsmOp "DUP2"] sfx
Proof
  simp_tac bool_ss [asm_window_refines_own_def, GSYM APPEND_ASSOC, APPEND] >>
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
  simp[sym_steps_own_pos, sym_steps_own_def, sym_step_own_eq, sym_step_def, sym_step_op_def,
       dup_table_def, swap_table_def, sym_dup_def, sym_swap_def,
       sym_set_stack_def, asm_next_def, sym_terminal_def] >>
  rename1 `_ = h :: t` >> Cases_on `t` >>
  simp[sym_steps_own_pos, sym_steps_own_def, sym_step_own_eq, sym_step_def, sym_step_op_def,
       dup_table_def, swap_table_def, sym_dup_def, sym_swap_def,
       sym_set_stack_def, asm_next_def, sym_terminal_def, LUPDATE_compute,
       splice_pc_def, sym_with_pc_def, sym_state_component_equality,
       asm_state_component_equality]
QED

Theorem dup1_swap1_pop_window_own[local]:
  asm_window_refines_own pfx [AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "POP"] [] sfx
Proof
  simp_tac bool_ss [asm_window_refines_own_def, GSYM APPEND_ASSOC, APPEND] >>
  rpt strip_tac >>
  qabbrev_tac `p = pfx ++ AsmOp "DUP1" :: AsmOp "SWAP1" :: AsmOp "POP" ::
                   sfx` >>
  `LENGTH pfx < LENGTH p ∧ EL (LENGTH pfx) p = AsmOp "DUP1" ∧
   LENGTH pfx + 1 < LENGTH p ∧ EL (LENGTH pfx + 1) p = AsmOp "SWAP1" ∧
   LENGTH pfx + 2 < LENGTH p ∧ EL (LENGTH pfx + 2) p = AsmOp "POP"`
    by simp[Abbr `p`, EL_APPEND_EQN] >>
  qexistsl_tac [`3`, `0`] >>
  Cases_on `ss.sym_stack` >>
  simp[sym_steps_own_pos, sym_steps_own_def, sym_step_own_eq, sym_step_def, sym_step_op_def,
       dup_table_def, swap_table_def, sym_dup_def, sym_swap_def,
       sym_set_stack_def, asm_next_def, sym_terminal_def, LUPDATE_compute,
       splice_pc_def, sym_with_pc_def, sym_state_component_equality,
       asm_state_component_equality]
QED

Theorem swap1_pop_pop_window_own[local]:
  asm_window_refines_own pfx [AsmOp "SWAP1"; AsmOp "POP"; AsmOp "POP"]
    [AsmOp "POP"; AsmOp "POP"] sfx
Proof
  simp_tac bool_ss [asm_window_refines_own_def, GSYM APPEND_ASSOC, APPEND] >>
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
  simp[sym_steps_own_pos, sym_steps_own_def, sym_step_own_eq, sym_step_def, sym_step_op_def,
       dup_table_def, swap_table_def, sym_swap_def, sym_set_stack_def,
       asm_next_def, sym_terminal_def] >>
  rename1 `_ = h :: t` >> Cases_on `t` >>
  simp[sym_steps_own_pos, sym_steps_own_def, sym_step_own_eq, sym_step_def, sym_step_op_def,
       dup_table_def, swap_table_def, sym_swap_def, sym_set_stack_def,
       asm_next_def, sym_terminal_def, LUPDATE_compute, splice_pc_def,
       sym_with_pc_def, sym_state_component_equality,
       asm_state_component_equality]
QED

Theorem dup1_swap1_window_own[local]:
  asm_window_refines_own pfx [AsmOp "DUP1"; AsmOp "SWAP1"] [AsmOp "DUP1"] sfx
Proof
  simp_tac bool_ss [asm_window_refines_own_def, GSYM APPEND_ASSOC, APPEND] >>
  rpt strip_tac >>
  qabbrev_tac `p = pfx ++ AsmOp "DUP1" :: AsmOp "SWAP1" :: sfx` >>
  qabbrev_tac `q = pfx ++ AsmOp "DUP1" :: sfx` >>
  `LENGTH pfx < LENGTH p ∧ EL (LENGTH pfx) p = AsmOp "DUP1" ∧
   LENGTH pfx + 1 < LENGTH p ∧ EL (LENGTH pfx + 1) p = AsmOp "SWAP1" ∧
   LENGTH pfx < LENGTH q ∧ EL (LENGTH pfx) q = AsmOp "DUP1"`
    by simp[Abbr `p`, Abbr `q`, EL_APPEND_EQN] >>
  qexistsl_tac [`2`, `1`] >>
  Cases_on `ss.sym_stack` >>
  simp[sym_steps_own_pos, sym_steps_own_def, sym_step_own_eq, sym_step_def, sym_step_op_def,
       dup_table_def, swap_table_def, sym_dup_def, sym_swap_def,
       sym_set_stack_def, asm_next_def, sym_terminal_def, LUPDATE_compute,
       splice_pc_def, sym_with_pc_def, sym_state_component_equality,
       asm_state_component_equality]
QED

Theorem swap_pair_window_own[local]:
  isPREFIX "SWAP" name ⇒
  asm_window_refines_own pfx [AsmOp name; AsmOp name] [] sfx
Proof
  strip_tac >>
  simp_tac bool_ss [asm_window_refines_own_def, GSYM APPEND_ASSOC, APPEND] >>
  rpt strip_tac >>
  qabbrev_tac `p = pfx ++ AsmOp name :: AsmOp name :: sfx` >>
  `LENGTH pfx < LENGTH p ∧ EL (LENGTH pfx) p = AsmOp name ∧
   LENGTH pfx + 1 < LENGTH p ∧ EL (LENGTH pfx + 1) p = AsmOp name`
    by simp[Abbr `p`, EL_APPEND_EQN] >>
  qexistsl_tac [`2`, `0`] >>
  Cases_on `ALOOKUP swap_table name`
  >- (drule_all swap_prefix_unknown >> strip_tac >>
      drule_all sym_step_unknown_op_own >>
      disch_then (qspecl_then [`ss`, `p`, `env`, `own`] strip_assume_tac) >>
      simp[sym_steps_own_pos, sym_terminal_def]) >>
  rename1 `ALOOKUP swap_table name = SOME n` >>
  drule sym_step_swap_table_own >> strip_tac >>
  simp[sym_steps_own_pos, sym_steps_own_def, sym_swap_def] >>
  IF_CASES_TAC >> simp[sym_terminal_def, sym_set_stack_def] >>
  simp[asm_next_def, sym_steps_own_pos, sym_steps_own_def, sym_swap_def,
       sym_set_stack_def, swap_swap_id, sym_terminal_def, splice_pc_def,
       sym_with_pc_def, sym_state_component_equality,
       asm_state_component_equality]
QED

Theorem swap1_commutative_window_own[local]:
  asm_commutative_op (AsmOp name) ⇒
  asm_window_refines_own pfx [AsmOp "SWAP1"; AsmOp name] [AsmOp name] sfx
Proof
  strip_tac >>
  simp_tac bool_ss [asm_window_refines_own_def, GSYM APPEND_ASSOC, APPEND] >>
  rpt strip_tac >>
  qabbrev_tac `p = pfx ++ AsmOp "SWAP1" :: AsmOp name :: sfx` >>
  qabbrev_tac `q = pfx ++ AsmOp name :: sfx` >>
  `LENGTH pfx < LENGTH p ∧ EL (LENGTH pfx) p = AsmOp "SWAP1" ∧
   LENGTH pfx + 1 < LENGTH p ∧ EL (LENGTH pfx + 1) p = AsmOp name ∧
   LENGTH pfx < LENGTH q ∧ EL (LENGTH pfx) q = AsmOp name`
    by simp[Abbr `p`, Abbr `q`, EL_APPEND_EQN] >>
  `sym_step_own p env own (AsmOp "SWAP1") ss = sym_swap 1 ss`
    by (irule sym_step_swap_table_own >> simp[swap_table_def]) >>
  qexistsl_tac [`2`, `1`] >>
  `(∃e. sym_swap 1 ss = SymError e) ∨ ∃a b stk. ss.sym_stack = a :: b :: stk`
    by (Cases_on `ss.sym_stack` >> simp[sym_swap_def] >>
        rename1 `_ = _ :: t` >> Cases_on `t` >> simp[]) >>
  gvs[sym_steps_own_pos, sym_terminal_def] >>
  qabbrev_tac `s1 = ss with <| sym_base := asm_next ss.sym_base;
                               sym_stack := b :: a :: stk |>` >>
  `sym_swap 1 ss = SymOK s1`
    by simp[Abbr `s1`, sym_swap_def, sym_set_stack_def, LUPDATE_compute] >>
  `s1.sym_base.as_pc = LENGTH pfx + 1`
    by simp[Abbr `s1`, asm_next_def] >>
  reverse (Cases_on `MEM name ["ADD"; "MUL"; "EQ"; "AND"; "OR"; "XOR"]`)
  >- (drule_all commutative_unknown >> strip_tac >>
      drule_all sym_step_unknown_op_own >>
      disch_then (qspecl_then [`s1`, `p`, `env`, `own`] strip_assume_tac) >>
      simp[sym_steps_own_pos, sym_terminal_def]) >>
  `s1 = sym_with_pc (ss.sym_base.as_pc + 1)
          (ss with sym_stack := b :: a :: stk)`
    by simp[Abbr `s1`, sym_with_pc_def, asm_next_def] >>
  `AsmOp name ≠ AsmOp "JUMP" ∧ AsmOp name ≠ AsmOp "JUMPI"` by gvs[] >>
  `sym_step_own p env own (AsmOp name) s1 =
   sym_result_pc_add 1 (sym_step_own q env own (AsmOp name) ss)`
    by (qpat_x_assum `s1 = _` SUBST1_TAC >>
        mp_tac (Q.INST [`inst` |-> `AsmOp name`, `n` |-> `1`,
                        `ss` |-> `ss with sym_stack := b :: a :: stk`]
                  sym_step_own_pc_add) >>
        impl_tac >- simp[] >>
        disch_then (SUBST1_TAC o SIMP_RULE (srw_ss()) []) >>
        mp_tac sym_step_commutative_swap_own >>
        impl_tac >- simp[] >>
        disch_then SUBST1_TAC >>
        `(ss with sym_stack := a :: b :: stk) = ss`
          by simp[sym_state_component_equality] >>
        pop_assum SUBST1_TAC >> AP_TERM_TAC >>
        irule sym_step_own_prog_cong >> simp[Abbr `p`, Abbr `q`]) >>
  qpat_x_assum `s1 = sym_with_pc _ _` kall_tac >>
  Cases_on `sym_step_own q env own (AsmOp name) ss` >>
  simp[sym_steps_own_pos, sym_steps_own_def, sym_result_pc_add_def, sym_terminal_def,
       sym_result_rel_def, sym_obs_def, sym_with_pc_def] >>
  rename1 `sym_step_own q env own (AsmOp name) ss = SymOK s2` >>
  `s2.sym_base.as_pc = LENGTH pfx + 1`
    by (drule_at (Pos last) sym_step_own_pc_next >> simp[]) >>
  simp[splice_pc_def, sym_state_component_equality,
       asm_state_component_equality]
QED

(* ===== Splices ===== *)

Theorem dup1_swap2_swap1_refines_own[local]:
  asm_refines_own (pfx ++ AsmOp "DUP1" :: AsmOp "SWAP2" :: AsmOp "SWAP1" :: rest)
              (pfx ++ AsmOp "SWAP1" :: AsmOp "DUP2" :: rest)
Proof
  mp_tac (Q.INST [`pat` |-> `[AsmOp "DUP1"; AsmOp "SWAP2"; AsmOp "SWAP1"]`,
                  `repl` |-> `[AsmOp "SWAP1"; AsmOp "DUP2"]`,
                  `sfx` |-> `rest`] asm_splice_window_refines_own) >>
  impl_tac
  >- (rpt conj_tac
      >- simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
              asm_inst_size_def, dup2_opcode, DISJ_IMP_THM, FORALL_AND_THM]
      >- simp[]
      >- simp[dup1_swap2_swap1_window_own]) >>
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> disch_then ACCEPT_TAC
QED

Theorem dup1_swap1_pop_refines_own[local]:
  asm_refines_own (pfx ++ AsmOp "DUP1" :: AsmOp "SWAP1" :: AsmOp "POP" :: rest)
              (pfx ++ rest)
Proof
  mp_tac (Q.INST [`pat` |-> `[AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "POP"]`,
                  `repl` |-> `[]`, `sfx` |-> `rest`]
            asm_splice_window_refines_own) >>
  impl_tac
  >- (rpt conj_tac
      >- simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
              asm_inst_size_def, dup2_opcode, DISJ_IMP_THM, FORALL_AND_THM]
      >- simp[]
      >- simp[dup1_swap1_pop_window_own]) >>
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> disch_then ACCEPT_TAC
QED

Theorem swap1_pop_pop_refines_own[local]:
  asm_refines_own (pfx ++ AsmOp "SWAP1" :: AsmOp "POP" :: AsmOp "POP" :: rest)
              (pfx ++ AsmOp "POP" :: AsmOp "POP" :: rest)
Proof
  mp_tac (Q.INST [`pat` |-> `[AsmOp "SWAP1"; AsmOp "POP"; AsmOp "POP"]`,
                  `repl` |-> `[AsmOp "POP"; AsmOp "POP"]`, `sfx` |-> `rest`]
            asm_splice_window_refines_own) >>
  impl_tac
  >- (rpt conj_tac
      >- simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
              asm_inst_size_def, dup2_opcode, DISJ_IMP_THM, FORALL_AND_THM]
      >- simp[]
      >- simp[swap1_pop_pop_window_own]) >>
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> disch_then ACCEPT_TAC
QED

Theorem swap_pair_refines_own[local]:
  isPREFIX "SWAP" name ⇒
  asm_refines_own (pfx ++ AsmOp name :: AsmOp name :: rest) (pfx ++ rest)
Proof
  strip_tac >>
  mp_tac (Q.INST [`pat` |-> `[AsmOp name; AsmOp name]`,
                  `repl` |-> `[]`, `sfx` |-> `rest`]
            asm_splice_window_refines_own) >>
  impl_tac
  >- (rpt conj_tac
      >- simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
              asm_inst_size_def, dup2_opcode, DISJ_IMP_THM, FORALL_AND_THM]
      >- simp[]
      >- simp[swap_pair_window_own]) >>
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> disch_then ACCEPT_TAC
QED

Theorem swap1_commutative_refines_own[local]:
  asm_commutative_op y ⇒
  asm_refines_own (pfx ++ AsmOp "SWAP1" :: y :: rest) (pfx ++ y :: rest)
Proof
  strip_tac >>
  `∃name. y = AsmOp name` by (Cases_on `y` >> gvs[asm_commutative_op_def]) >>
  gvs[] >>
  mp_tac (Q.INST [`pat` |-> `[AsmOp "SWAP1"; AsmOp name]`,
                  `repl` |-> `[AsmOp name]`, `sfx` |-> `rest`]
            asm_splice_window_refines_own) >>
  impl_tac
  >- (rpt conj_tac
      >- simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
              asm_inst_size_def, dup2_opcode, DISJ_IMP_THM, FORALL_AND_THM]
      >- simp[]
      >- simp[swap1_commutative_window_own]) >>
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> disch_then ACCEPT_TAC
QED

Theorem dup1_swap1_refines_own[local]:
  asm_refines_own (pfx ++ AsmOp "DUP1" :: AsmOp "SWAP1" :: rest)
              (pfx ++ AsmOp "DUP1" :: rest)
Proof
  mp_tac (Q.INST [`pat` |-> `[AsmOp "DUP1"; AsmOp "SWAP1"]`,
                  `repl` |-> `[AsmOp "DUP1"]`, `sfx` |-> `rest`]
            asm_splice_window_refines_own) >>
  impl_tac
  >- (rpt conj_tac
      >- simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
              asm_inst_size_def, dup2_opcode, DISJ_IMP_THM, FORALL_AND_THM]
      >- simp[]
      >- simp[dup1_swap1_window_own]) >>
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> disch_then ACCEPT_TAC
QED

(* ===== The three rules at one index ===== *)

Theorem peep_swap_pair_refines_own[local]:
  peep_swap_pair a b c rest = (l, ch) ⇒
  asm_refines_own (pfx ++ a :: b :: c :: rest) (pfx ++ l)
Proof
  rw[peep_swap_pair_def] >> simp[asm_refines_own_refl] >>
  Cases_on `a` >> gvs[asm_swap_op_def] >>
  irule swap_pair_refines_own >> simp[]
QED

Theorem peep_swap_comm_refines_own[local]:
  peep_swap_comm l = SOME (l', ch) ⇒ asm_refines_own (pfx ++ l) (pfx ++ l')
Proof
  rw[peep_swap_comm_def, AllCaseEqs()] >> simp[asm_refines_own_refl] >>
  irule swap1_commutative_refines_own >> simp[]
QED

Theorem peep_dup_swap_refines_own[local]:
  peep_dup_swap l = SOME (l', ch) ⇒ asm_refines_own (pfx ++ l) (pfx ++ l')
Proof
  rw[peep_dup_swap_def, AllCaseEqs()] >>
  simp[asm_refines_own_refl, dup1_swap1_refines_own]
QED

(* ===== The rule ===== *)

Theorem stack_peephole_opts_refines_under_own[local]:
  ∀asm pfx out c.
    stack_peephole_opts asm = SOME (out, c) ⇒
    asm_refines_own (pfx ++ asm) (pfx ++ out)
Proof
  measureInduct_on `LENGTH asm` >>
  Cases_on `asm` >- simp[Once stack_peephole_opts_def, asm_refines_own_refl] >>
  rename1 `a :: t1` >> Cases_on `t1`
  >- simp[Once stack_peephole_opts_def, asm_refines_own_refl] >>
  rename1 `a :: b :: t2` >> Cases_on `t2`
  >- simp[Once stack_peephole_opts_def, asm_refines_own_refl] >>
  rename1 `a :: b :: c1 :: rest` >> rpt gen_tac >> strip_tac >>
  drule stack_peephole_opts_cons3 >> strip_tac >> gvs[]
  >~ [`stack_peephole_opts (AsmOp "SWAP1" :: AsmOp "DUP2" :: _)`]
  >- (irule asm_refines_own_trans >>
      qexists_tac `pfx ++ AsmOp "SWAP1" :: AsmOp "DUP2" :: rest` >>
      simp[dup1_swap2_swap1_refines_own] >>
      first_x_assum irule >> simp[] >> first_assum (irule_at Any))
  >~ [`stack_peephole_opts rest = SOME _`]
  >- (irule asm_refines_own_trans >> qexists_tac `pfx ++ rest` >>
      simp[dup1_swap1_pop_refines_own] >>
      first_x_assum irule >> simp[] >> first_assum (irule_at Any))
  >~ [`stack_peephole_opts (AsmOp "POP" :: AsmOp "POP" :: _)`]
  >- (irule asm_refines_own_trans >>
      qexists_tac `pfx ++ AsmOp "POP" :: AsmOp "POP" :: rest` >>
      simp[swap1_pop_pop_refines_own] >>
      first_x_assum irule >> simp[] >> first_assum (irule_at Any)) >>
  imp_res_tac peep_swap_pair_length >>
  imp_res_tac peep_swap_comm_length >>
  imp_res_tac peep_dup_swap_length >>
  irule asm_refines_own_trans >> qexists_tac `pfx ++ l1` >> conj_tac
  >- (drule peep_swap_pair_refines_own >> simp[]) >>
  irule asm_refines_own_trans >> qexists_tac `pfx ++ l2` >> conj_tac
  >- (drule peep_swap_comm_refines_own >> simp[]) >>
  irule asm_refines_own_trans >> qexists_tac `pfx ++ h :: t` >> conj_tac
  >- (drule peep_dup_swap_refines_own >> simp[]) >>
  first_x_assum (qspec_then `t` mp_tac) >>
  impl_tac >- gvs[] >>
  disch_then (qspecl_then [`pfx ++ [h]`, `out'`, `ch'`] mp_tac) >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem stack_peephole_opts_refines_own:
  ∀p p' c. stack_peephole_opts p = SOME (p', c) ⇒ asm_refines_own p p'
Proof
  rpt strip_tac >> drule stack_peephole_opts_refines_under_own >>
  disch_then (qspec_then `[]` mp_tac) >> simp[]
QED
