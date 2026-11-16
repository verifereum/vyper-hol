(* The two merge-iszero windows read the same fixed own-code bytes. *)
Theory asmOptOwnMergeIszero
Ancestors
  asmSpliceOwn asmSymPcOwn finalizerContractOwn asmSymOwnCode
  asmOptMergeIszero asmSplice asmSymPc finalizerContract asmSymSem
  asmOptimizer asmWf asmSem vfmExecution list

Theorem iszero_pair_window_refines_own:
  asm_returns_zero_or_one x ⇒
  asm_window_refines_own pfx [x; AsmOp "ISZERO"; AsmOp "ISZERO"] [x] rest
Proof
  rw[asm_window_refines_own_def] >>
  `x ≠ AsmOp "JUMP" ∧ x ≠ AsmOp "JUMPI" ∧
   x ≠ AsmOp "CODESIZE" ∧ x ≠ AsmOp "CODECOPY"`
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
  qexistsl_tac [`3`, `1`] >>
  rewrite_tac[numLib.num_CONV ``3:num``, numLib.num_CONV ``1:num``,
              sym_steps_own_def] >> simp[sym_step_own_eq] >>
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
  rewrite_tac[numLib.num_CONV ``2:num``, numLib.num_CONV ``1:num``,
              sym_steps_own_def] >>
  simp[sym_step_own_eq, sym_terminal_def] >>
  simp[Abbr `s2`, asmSemTheory.asm_next_def,
       splice_pc_def, sym_with_pc_def, sym_state_component_equality,
       asmSemTheory.asm_state_component_equality]
QED

Theorem merge_iszero_pairs_refines_own_under:
  ∀sfx pfx. asm_refines_own (pfx ++ sfx) (pfx ++ FST (merge_iszero_pairs sfx))
Proof
  ho_match_mp_tac merge_iszero_pairs_ind >>
  reverse (rpt conj_tac)
  >- simp[merge_iszero_pairs_def, asm_refines_own_refl]
  >- simp[merge_iszero_pairs_def, asm_refines_own_refl]
  >- simp[merge_iszero_pairs_def, asm_refines_own_refl] >>
  rpt gen_tac >> strip_tac >> simp[merge_iszero_pairs_fst] >>
  reverse IF_CASES_TAC
  >- (gvs[] >> gen_tac >>
      first_x_assum (qspec_then `pfx ++ [x]` mp_tac) >>
      REWRITE_TAC[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
  gvs[] >> gen_tac >>
  `∃name. x = AsmOp name` by gvs[asm_returns_zero_or_one_def] >>
  gvs[] >>
  irule asm_refines_own_trans >>
  qexists_tac `pfx ++ AsmOp name :: rest` >> simp[] >>
  `asm_splice_ok [AsmOp name; AsmOp "ISZERO"; AsmOp "ISZERO"] [AsmOp name]`
    by simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
            symbolResolveTheory.asm_inst_size_def] >>
  drule iszero_pair_window_refines_own >> strip_tac >>
  mp_tac (Q.INST [`pat` |-> `[AsmOp name; AsmOp "ISZERO"; AsmOp "ISZERO"]`,
                  `repl` |-> `[AsmOp name]`, `sfx` |-> `rest`]
            asm_splice_window_refines_own) >>
  impl_tac >- simp[] >>
  REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  disch_then ACCEPT_TAC
QED

Theorem iszero_jumpi_window_refines_own:
  asm_window_refines_own pfx [AsmOp "ISZERO"; AsmOp "ISZERO"] []
    (AsmPushLabel l :: AsmOp "JUMPI" :: rest)
Proof
  rw[asm_window_refines_own_def] >>
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
  >~ [`SymError`]
  >- (rewrite_tac[numLib.num_CONV ``4:num``, sym_steps_own_def] >>
      simp[sym_step_own_eq, sym_terminal_def])
  >~ [`SymBad`]
  >- (rewrite_tac[numLib.num_CONV ``4:num``, sym_steps_own_def] >>
      simp[sym_step_own_eq, sym_terminal_def]) >>
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
  rewrite_tac[numLib.num_CONV ``4:num``, numLib.num_CONV ``3:num``,
              numLib.num_CONV ``2:num``, numLib.num_CONV ``1:num``,
              sym_steps_own_def] >>
  simp[sym_step_own_eq, b2w_b2w_eq_zero] >>
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

Theorem merge_iszero_jumpi_refines_own_under:
  ∀sfx pfx. asm_refines_own (pfx ++ sfx) (pfx ++ FST (merge_iszero_jumpi sfx))
Proof
  ho_match_mp_tac merge_iszero_jumpi_ind >>
  reverse (rpt conj_tac)
  >- simp[merge_iszero_jumpi_def, asm_refines_own_refl]
  >- simp[merge_iszero_jumpi_def, asm_refines_own_refl]
  >- simp[merge_iszero_jumpi_def, asm_refines_own_refl]
  >- simp[merge_iszero_jumpi_def, asm_refines_own_refl] >>
  rpt gen_tac >> strip_tac >> simp[merge_iszero_jumpi_fst] >>
  reverse IF_CASES_TAC
  >- (gvs[] >> gen_tac >>
      first_x_assum (qspec_then `pfx ++ [a]` mp_tac) >>
      REWRITE_TAC[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
  Cases_on `c` >> gvs[asm_is_push_label_def] >> gen_tac >>
  qmatch_goalsub_rename_tac `AsmPushLabel lbl` >>
  irule asm_refines_own_trans >>
  qexists_tac `pfx ++ AsmPushLabel lbl :: AsmOp "JUMPI" :: rest` >> simp[] >>
  mp_tac (Q.INST [`pat` |-> `[AsmOp "ISZERO"; AsmOp "ISZERO"]`,
                  `repl` |-> `[]`,
                  `sfx` |-> `AsmPushLabel lbl :: AsmOp "JUMPI" :: rest`]
            asm_splice_window_refines_own) >>
  impl_tac
  >- simp[asm_splice_ok_def, iszero_jumpi_window_refines_own, is_data_inst_def,
          asm_label_refs_def, symbolResolveTheory.asm_inst_size_def] >>
  REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  disch_then ACCEPT_TAC
QED

Theorem merge_iszero_refines_own:
  ∀p. asm_refines_own p (FST (merge_iszero p))
Proof
  gen_tac >> simp[merge_iszero_fst] >>
  irule asm_refines_own_trans >>
  qexists_tac `FST (merge_iszero_pairs p)` >>
  qspecl_then [`p`, `[]`] mp_tac merge_iszero_pairs_refines_own_under >>
  qspecl_then [`FST (merge_iszero_pairs p)`, `[]`] mp_tac
    merge_iszero_jumpi_refines_own_under >>
  simp[]
QED
