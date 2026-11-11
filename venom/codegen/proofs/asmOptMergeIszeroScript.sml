(*
 * merge_iszero refines its input.
 *
 * Its two walks are splices:
 *   X ISZERO ISZERO -> X, where X leaves 0 or 1 on the stack, so two
 *     ISZEROs give back what X left;
 *   ISZERO ISZERO before PUSHLABEL l JUMPI -> nothing, since JUMPI only
 *     asks whether its condition is zero.
 *
 * TOP-LEVEL:
 *   merge_iszero_refines — asm_refines p (FST (merge_iszero p))
 *)

Theory asmOptMergeIszero
Ancestors
  asmSplice asmSymPc finalizerContract asmSymSem asmOptimizer asmWf
  asmSem vfmExecution list

(* ===== X ISZERO ISZERO ===== *)

Theorem compare_zero_or_one[local]:
  MEM name ["LT"; "GT"; "SLT"; "SGT"; "EQ"; "ISZERO"] /\
  asm_step_op FEMPTY name s = AsmOK s' ==>
  ?w stk. s'.as_stack = w :: stk /\ (w = 0w \/ w = 1w)
Proof
  simp[MEM] >> strip_tac >>
  gvs[asm_step_op_def, asm_step_arith_def, asm_step_compare_def] >>
  gvs[asm_binop_def, asm_unop_def, AllCaseEqs()] >>
  gvs[asm_next_def] >>
  qmatch_goalsub_abbrev_tac `b2w b` >> Cases_on `b` >>
  simp[vfmExecutionTheory.b2w_def]
QED

Theorem consume_zero_or_one[local]:
  asm_consume_call_outcome rq ro rs stk s = AsmOK t ==>
  ?w tail. t.as_stack = w :: tail /\ (w = 0w \/ w = 1w)
Proof
  simp[asm_consume_call_outcome_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  simp[asm_next_def] >> strip_tac >> gvs[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem call_zero_or_one[local]:
  MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"] /\
  asm_step_op FEMPTY name s = AsmOK t ==>
  ?w stk. t.as_stack = w :: stk /\ (w = 0w \/ w = 1w)
Proof
  simp[MEM] >> strip_tac >>
  gvs[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
      asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
      asm_step_extcall_def] >>
  gvs[asm_exec_call_def, asm_exec_staticcall_def, asm_exec_delegatecall_def,
      AllCaseEqs()] >>
  drule consume_zero_or_one >> simp[]
QED

Theorem callcode_not_ok[local]:
  asm_step_op FEMPTY "CALLCODE" s <> AsmOK t
Proof
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
       asm_step_extcall_def, asm_step_copy_def, asm_step_context_def,
       asmSemTheory.dup_table_def, asmSemTheory.swap_table_def,
       asmSemTheory.log_table_def]
QED

Theorem concrete_zero_or_one_lift[local]:
  (!s t. asm_step_op FEMPTY name s = AsmOK t ==>
     ?w stk. t.as_stack = w :: stk /\ (w = 0w \/ w = 1w)) /\
  sym_step_concrete name ss = SymOK ss' ==>
  ?w stk. ss'.sym_stack = Val w :: stk /\ (w = 0w \/ w = 1w)
Proof
  strip_tac >>
  gvs[sym_step_concrete_def, AllCaseEqs()] >>
  qpat_x_assum `sym_lift _ _ _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `sym_lift k labs ss r` >>
  Cases_on `r` >> simp[sym_lift_def] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem sym_step_zero_or_one:
  asm_returns_zero_or_one inst ∧ sym_step p env inst ss = SymOK ss' ⇒
  ∃w stk. ss'.sym_stack = Val w :: stk ∧ (w = 0w ∨ w = 1w)
Proof
  simp[asm_returns_zero_or_one_def, MEM] >> strip_tac >>
  gvs[sym_step_def, sym_step_op_def, dup_table_def, swap_table_def] >>
  irule concrete_zero_or_one_lift >>
  goal_assum (drule_at Any) >> rpt strip_tac >>
  metis_tac[compare_zero_or_one, call_zero_or_one,
            callcode_not_ok, MEM]
QED

Theorem one_ne_zero_bytes32[local]:
  (1w:bytes32) ≠ 0w
Proof
  simp[wordsTheory.n2w_11, wordsTheory.ONE_LT_dimword,
       arithmeticTheory.LESS_MOD]
QED

Theorem b2w_b2w_zero_or_one[local]:
  w = 0w ∨ w = 1w ⇒ b2w (b2w (w = 0w) = (0w:bytes32)) = (w:bytes32)
Proof
  rw[] >> simp[one_ne_zero_bytes32]
QED

Theorem iszero_pair_window_refines:
  asm_returns_zero_or_one x ⇒
  asm_window_refines pfx [x; AsmOp "ISZERO"; AsmOp "ISZERO"] [x] rest
Proof
  rw[asm_window_refines_def] >>
  `x ≠ AsmOp "JUMP" ∧ x ≠ AsmOp "JUMPI"`
    by gvs[asm_returns_zero_or_one_def] >>
  qabbrev_tac `p = pfx ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ rest` >>
  qabbrev_tac `q = pfx ++ [x] ++ rest` >>
  `sym_step p env x ss = sym_step q env x ss`
    by (irule sym_step_prog_cong >> simp[Abbr `p`, Abbr `q`] >>
        metis_tac[]) >>
  `LENGTH pfx < LENGTH p ∧ EL (LENGTH pfx) p = x ∧
   LENGTH pfx + 1 < LENGTH p ∧ EL (LENGTH pfx + 1) p = AsmOp "ISZERO" ∧
   LENGTH pfx + 2 < LENGTH p ∧ EL (LENGTH pfx + 2) p = AsmOp "ISZERO" ∧
   LENGTH pfx < LENGTH q ∧ EL (LENGTH pfx) q = x`
    by simp[Abbr `p`, Abbr `q`, listTheory.EL_APPEND_EQN] >>
  qexistsl_tac [`3`, `1`] >> simp[sym_steps_pos] >>
  Cases_on `sym_step q env x ss` >>
  simp[sym_terminal_def, sym_result_rel_refl] >>
  rename1 `sym_step q env x ss = SymOK s1` >>
  `sym_step p env x ss = SymOK s1` by simp[] >>
  drule_all sym_step_zero_or_one >>
  disch_then (qx_choosel_then [`w`, `stk`] (CONJUNCTS_THEN assume_tac)) >>
  `s1.sym_base.as_pc = LENGTH pfx + 1`
    by (drule_at (Pos last) sym_step_pc_next >> simp[]) >>
  `s1.sym_base.as_stack = []`
    by (drule_at (Pos last) sym_step_base_stack >> simp[]) >>
  drule_then (qspecl_then [`p`, `env`] assume_tac) sym_step_iszero_val >>
  qmatch_asmsub_abbrev_tac `sym_step p env (AsmOp "ISZERO") s1 = SymOK s2` >>
  `s2.sym_stack = Val (b2w (w = 0w)) :: stk ∧
   s2.sym_base.as_pc = LENGTH pfx + 2`
    by simp[Abbr `s2`, asmSemTheory.asm_next_def] >>
  drule_then (qspecl_then [`p`, `env`] assume_tac) sym_step_iszero_val >>
  `b2w (b2w (w = 0w) = (0w:bytes32)) = w`
    by (irule b2w_b2w_zero_or_one >> first_assum ACCEPT_TAC) >>
  simp[sym_steps_pos, sym_steps_def, sym_terminal_def] >>
  simp[Abbr `s2`, asmSemTheory.asm_next_def,
       splice_pc_def, sym_with_pc_def, sym_state_component_equality,
       asmSemTheory.asm_state_component_equality]
QED

Theorem merge_iszero_pairs_fst[local]:
  FST (merge_iszero_pairs (x :: y :: z :: rest)) =
  if asm_returns_zero_or_one x ∧ y = AsmOp "ISZERO" ∧ z = AsmOp "ISZERO"
  then FST (merge_iszero_pairs (x :: rest))
  else x :: FST (merge_iszero_pairs (y :: z :: rest))
Proof
  simp[Once merge_iszero_pairs_def] >> rw[] >> pairarg_tac >> simp[]
QED

Theorem merge_iszero_pairs_refines_under:
  ∀sfx pfx. asm_refines (pfx ++ sfx) (pfx ++ FST (merge_iszero_pairs sfx))
Proof
  ho_match_mp_tac merge_iszero_pairs_ind >>
  reverse (rpt conj_tac)
  >- simp[merge_iszero_pairs_def, asm_refines_refl]
  >- simp[merge_iszero_pairs_def, asm_refines_refl]
  >- simp[merge_iszero_pairs_def, asm_refines_refl] >>
  rpt gen_tac >> strip_tac >> simp[merge_iszero_pairs_fst] >>
  reverse IF_CASES_TAC >- (gvs[] >> irule asm_refines_cons >> simp[]) >>
  gvs[] >> gen_tac >>
  `∃name. x = AsmOp name` by gvs[asm_returns_zero_or_one_def] >>
  gvs[] >>
  irule asm_refines_trans >>
  qexists_tac `pfx ++ AsmOp name :: rest` >> simp[] >>
  `asm_splice_ok [AsmOp name; AsmOp "ISZERO"; AsmOp "ISZERO"] [AsmOp name]`
    by simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
            symbolResolveTheory.asm_inst_size_def] >>
  drule iszero_pair_window_refines >> strip_tac >>
  mp_tac (Q.INST [`pat` |-> `[AsmOp name; AsmOp "ISZERO"; AsmOp "ISZERO"]`,
                  `repl` |-> `[AsmOp name]`, `sfx` |-> `rest`]
            asm_splice_window_refines) >>
  impl_tac >- simp[] >>
  REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  disch_then ACCEPT_TAC
QED

(* ===== ISZERO ISZERO PUSHLABEL l JUMPI ===== *)

Theorem b2w_b2w_eq_zero[local]:
  (b2w (b2w (w = 0w) = (0w:bytes32)) = (0w:bytes32)) ⇔ (w = (0w:bytes32))
Proof
  Cases_on `w = 0w` >> simp[one_ne_zero_bytes32, GSYM one_ne_zero_bytes32]
QED

Theorem iszero_jumpi_window_refines:
  asm_window_refines pfx [AsmOp "ISZERO"; AsmOp "ISZERO"] []
    (AsmPushLabel l :: AsmOp "JUMPI" :: rest)
Proof
  rw[asm_window_refines_def] >>
  qabbrev_tac `p = pfx ++ [AsmOp "ISZERO"; AsmOp "ISZERO"] ++
                   AsmPushLabel l :: AsmOp "JUMPI" :: rest` >>
  qabbrev_tac `q = pfx ++ AsmPushLabel l :: AsmOp "JUMPI" :: rest` >>
  `LENGTH pfx < LENGTH p ∧ EL (LENGTH pfx) p = AsmOp "ISZERO" ∧
   LENGTH pfx + 1 < LENGTH p ∧ EL (LENGTH pfx + 1) p = AsmOp "ISZERO" ∧
   LENGTH pfx + 2 < LENGTH p ∧ EL (LENGTH pfx + 2) p = AsmPushLabel l ∧
   LENGTH pfx + 3 < LENGTH p ∧ EL (LENGTH pfx + 3) p = AsmOp "JUMPI" ∧
   LENGTH pfx < LENGTH q ∧ EL (LENGTH pfx) q = AsmPushLabel l ∧
   LENGTH pfx + 1 < LENGTH q ∧ EL (LENGTH pfx + 1) q = AsmOp "JUMPI"`
    by simp[Abbr `p`, Abbr `q`, listTheory.EL_APPEND_EQN] >>
  `INDEX_OF (AsmLabel l) q =
     OPTION_MAP (splice_pc (LENGTH pfx) 2 0) (INDEX_OF (AsmLabel l) p) ∧
   ∀i. INDEX_OF (AsmLabel l) p = SOME i ⇒
       i < LENGTH pfx ∨ LENGTH pfx + 2 ≤ i`
    by (mp_tac (Q.INST [`pat` |-> `[AsmOp "ISZERO"; AsmOp "ISZERO"]`,
                        `repl` |-> `[]`,
                        `sfx` |-> `AsmPushLabel l :: AsmOp "JUMPI" :: rest`]
                  splice_index_of_label) >>
        simp[Abbr `p`, Abbr `q`]) >>
  qexistsl_tac [`4`, `2`] >> simp[] >>
  qspecl_then [`ss`, `p`, `env`] strip_assume_tac
    (GEN_ALL sym_step_iszero_cases)
  >~ [`SymError`] >- simp[sym_steps_pos, sym_terminal_def]
  >~ [`SymBad`] >- simp[sym_steps_pos, sym_terminal_def] >>
  drule_then (qspecl_then [`p`, `env`] assume_tac) sym_step_iszero_val >>
  qmatch_asmsub_abbrev_tac `sym_step p env (AsmOp "ISZERO") ss = SymOK s1` >>
  `s1.sym_stack = Val (b2w (w = 0w)) :: stk ∧
   s1.sym_base.as_pc = LENGTH pfx + 1`
    by simp[Abbr `s1`, asmSemTheory.asm_next_def] >>
  drule_then (qspecl_then [`p`, `env`] assume_tac) sym_step_iszero_val >>
  qmatch_asmsub_abbrev_tac `sym_step p env (AsmOp "ISZERO") s1 = SymOK s2` >>
  `s2.sym_stack = Val (b2w (b2w (w = 0w) = (0w:bytes32))) :: stk ∧
   s2.sym_base.as_pc = LENGTH pfx + 2`
    by simp[Abbr `s2`, asmSemTheory.asm_next_def] >>
  qabbrev_tac `s3 = s2 with <| sym_base := asm_next s2.sym_base;
                               sym_stack := Lab l 0 :: s2.sym_stack |>` >>
  `sym_step p env (AsmPushLabel l) s2 = SymOK s3`
    by simp[Abbr `s3`, sym_step_push_label] >>
  `s3.sym_stack =
     Lab l 0 :: Val (b2w (b2w (w = 0w) = (0w:bytes32))) :: stk ∧
   s3.sym_base.as_pc = LENGTH pfx + 3`
    by simp[Abbr `s3`, asmSemTheory.asm_next_def] >>
  drule_then (qspecl_then [`p`, `env`] assume_tac) sym_step_jumpi_label >>
  qabbrev_tac `t1 = ss with <| sym_base := asm_next ss.sym_base;
                               sym_stack := Lab l 0 :: ss.sym_stack |>` >>
  `sym_step q env (AsmPushLabel l) ss = SymOK t1`
    by simp[Abbr `t1`, sym_step_push_label] >>
  `t1.sym_stack = Lab l 0 :: Val w :: stk ∧
   t1.sym_base.as_pc = LENGTH pfx + 1`
    by simp[Abbr `t1`, asmSemTheory.asm_next_def] >>
  drule_then (qspecl_then [`q`, `env`] assume_tac) sym_step_jumpi_label >>
  simp[sym_steps_pos, sym_steps_def, b2w_b2w_eq_zero] >>
  IF_CASES_TAC >> simp[sym_terminal_def]
  >- simp[Abbr `s1`, Abbr `s2`, Abbr `s3`, Abbr `t1`,
          asmSemTheory.asm_next_def, splice_pc_def, sym_with_pc_def,
          sym_state_component_equality,
          asmSemTheory.asm_state_component_equality] >>
  Cases_on `INDEX_OF (AsmLabel l) p` >> gvs[sym_terminal_def] >>
  simp[Abbr `s1`, Abbr `s2`, Abbr `s3`, Abbr `t1`, splice_pc_def,
       asmSemTheory.asm_next_def, sym_with_pc_def, sym_state_component_equality,
       asmSemTheory.asm_state_component_equality]
QED

Theorem merge_iszero_jumpi_fst[local]:
  FST (merge_iszero_jumpi (a :: b :: c :: d :: rest)) =
  if a = AsmOp "ISZERO" ∧ b = AsmOp "ISZERO" ∧ asm_is_push_label c ∧
     d = AsmOp "JUMPI"
  then FST (merge_iszero_jumpi (c :: d :: rest))
  else a :: FST (merge_iszero_jumpi (b :: c :: d :: rest))
Proof
  simp[Once merge_iszero_jumpi_def] >> rw[] >> pairarg_tac >> simp[]
QED

Theorem merge_iszero_jumpi_refines_under:
  ∀sfx pfx. asm_refines (pfx ++ sfx) (pfx ++ FST (merge_iszero_jumpi sfx))
Proof
  ho_match_mp_tac merge_iszero_jumpi_ind >>
  reverse (rpt conj_tac)
  >- simp[merge_iszero_jumpi_def, asm_refines_refl]
  >- simp[merge_iszero_jumpi_def, asm_refines_refl]
  >- simp[merge_iszero_jumpi_def, asm_refines_refl]
  >- simp[merge_iszero_jumpi_def, asm_refines_refl] >>
  rpt gen_tac >> strip_tac >> simp[merge_iszero_jumpi_fst] >>
  reverse IF_CASES_TAC >- (gvs[] >> irule asm_refines_cons >> simp[]) >>
  Cases_on `c` >> gvs[asm_is_push_label_def] >> gen_tac >>
  qmatch_goalsub_rename_tac `AsmPushLabel lbl` >>
  irule asm_refines_trans >>
  qexists_tac `pfx ++ AsmPushLabel lbl :: AsmOp "JUMPI" :: rest` >> simp[] >>
  mp_tac (Q.INST [`pat` |-> `[AsmOp "ISZERO"; AsmOp "ISZERO"]`,
                  `repl` |-> `[]`,
                  `sfx` |-> `AsmPushLabel lbl :: AsmOp "JUMPI" :: rest`]
            asm_splice_window_refines) >>
  impl_tac
  >- simp[asm_splice_ok_def, iszero_jumpi_window_refines, is_data_inst_def,
          asm_label_refs_def, symbolResolveTheory.asm_inst_size_def] >>
  REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  disch_then ACCEPT_TAC
QED

(* ===== The rule ===== *)

Theorem merge_iszero_fst[local]:
  FST (merge_iszero p) =
  FST (merge_iszero_jumpi (FST (merge_iszero_pairs p)))
Proof
  simp[merge_iszero_def] >> rpt (pairarg_tac >> simp[])
QED

Theorem merge_iszero_refines:
  ∀p. asm_refines p (FST (merge_iszero p))
Proof
  gen_tac >> simp[merge_iszero_fst] >>
  irule asm_refines_trans >>
  qexists_tac `FST (merge_iszero_pairs p)` >>
  qspecl_then [`p`, `[]`] mp_tac merge_iszero_pairs_refines_under >>
  qspecl_then [`FST (merge_iszero_pairs p)`, `[]`] mp_tac
    merge_iszero_jumpi_refines_under >>
  simp[]
QED
