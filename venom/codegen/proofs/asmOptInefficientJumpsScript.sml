(*
 * optimize_inefficient_jumps refines its input.
 *
 * The rule turns PUSHLABEL x JUMPI PUSHLABEL y JUMP right before LABEL x
 * into ISZERO PUSHLABEL y JUMPI. Each rewrite is a splice with LABEL x
 * kept at the head of the suffix: a nonzero condition goes to LABEL x
 * either way (by the jump, or by falling through), and a zero condition
 * goes to LABEL y either way.
 *
 * TOP-LEVEL:
 *   optimize_inefficient_jumps_refines — asm_refines p (FST (rule p))
 *)

Theory asmOptInefficientJumps
Ancestors
  asmSplice asmSymPc finalizerContract asmSymSem asmOptimizer asmWf

Theorem jumpi_over_jump_window_refines:
  asm_window_refines pfx
    [AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"]
    [AsmOp "ISZERO"; AsmPushLabel y; AsmOp "JUMPI"]
    (AsmLabel x :: rest)
Proof
  rw[asm_window_refines_def, asm_static_wf_def] >>
  `¬MEM (AsmLabel x) pfx`
    by (qpat_x_assum `asm_labels_unique _`
          (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                asm_labels_unique_append_not_mem)) >>
        disch_then (qspec_then `x` mp_tac) >> simp[]) >>
  qabbrev_tac `p = pfx ++
                   [AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y;
                    AsmOp "JUMP"] ++ AsmLabel x :: rest` >>
  qabbrev_tac `q = pfx ++ [AsmOp "ISZERO"; AsmPushLabel y; AsmOp "JUMPI"] ++
                   AsmLabel x :: rest` >>
  `LENGTH pfx < LENGTH p ∧ EL (LENGTH pfx) p = AsmPushLabel x ∧
   LENGTH pfx + 1 < LENGTH p ∧ EL (LENGTH pfx + 1) p = AsmOp "JUMPI" ∧
   LENGTH pfx + 2 < LENGTH p ∧ EL (LENGTH pfx + 2) p = AsmPushLabel y ∧
   LENGTH pfx + 3 < LENGTH p ∧ EL (LENGTH pfx + 3) p = AsmOp "JUMP" ∧
   INDEX_OF (AsmLabel x) p = SOME (LENGTH pfx + 4) ∧
   LENGTH pfx < LENGTH q ∧ EL (LENGTH pfx) q = AsmOp "ISZERO" ∧
   LENGTH pfx + 1 < LENGTH q ∧ EL (LENGTH pfx + 1) q = AsmPushLabel y ∧
   LENGTH pfx + 2 < LENGTH q ∧ EL (LENGTH pfx + 2) q = AsmOp "JUMPI"`
    by simp[Abbr `p`, Abbr `q`, listTheory.EL_APPEND_EQN, INDEX_OF_APPEND,
            INDEX_OF_CONS] >>
  `INDEX_OF (AsmLabel y) q =
     OPTION_MAP (splice_pc (LENGTH pfx) 4 3) (INDEX_OF (AsmLabel y) p) ∧
   ∀i. INDEX_OF (AsmLabel y) p = SOME i ⇒
       i ≤ LENGTH pfx ∨ LENGTH pfx + 4 ≤ i`
    by (mp_tac (Q.INST [`pat` |-> `[AsmPushLabel x; AsmOp "JUMPI";
                                    AsmPushLabel y; AsmOp "JUMP"]`,
                        `repl` |-> `[AsmOp "ISZERO"; AsmPushLabel y;
                                     AsmOp "JUMPI"]`,
                        `sfx` |-> `AsmLabel x :: rest`, `l` |-> `y`]
                  splice_index_of_label) >>
        simp[Abbr `p`, Abbr `q`] >> strip_tac >> simp[] >>
        rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[]) >>
  qabbrev_tac `s1 = ss with <| sym_base := asm_next ss.sym_base;
                               sym_stack := Lab x 0 :: ss.sym_stack |>` >>
  `sym_step p env (AsmPushLabel x) ss = SymOK s1`
    by simp[Abbr `s1`, sym_step_push_label] >>
  `s1.sym_base.as_pc = LENGTH pfx + 1 ∧
   s1.sym_stack = Lab x 0 :: ss.sym_stack`
    by simp[Abbr `s1`, asmSemTheory.asm_next_def] >>
  reverse (Cases_on `∃c stk. ss.sym_stack = Val c :: stk`)
  >- ((* a Lab condition, or too few items: p's JUMPI misuses its stack *)
      `∃e. sym_step p env (AsmOp "JUMPI") s1 = SymError e ∨
           sym_step p env (AsmOp "JUMPI") s1 = SymBad e`
        by (Cases_on `ss.sym_stack` >> gvs[]
            >- simp[sym_step_def, sym_step_op_def, sym_jumpi_def] >>
            rename1 `ss.sym_stack = v :: _` >> Cases_on `v` >>
            gvs[sym_step_def, sym_step_op_def, sym_jumpi_def]) >>
      qexistsl_tac [`2`, `0`] >>
      pop_assum strip_assume_tac >>
      simp[sym_steps_pos, sym_terminal_def]) >>
  gvs[] >>
  `sym_step p env (AsmOp "JUMPI") s1 =
   if c = 0w then
     SymOK (s1 with <| sym_base := asm_next s1.sym_base; sym_stack := stk |>)
   else
     case INDEX_OF (AsmLabel x) p of
       SOME i => SymOK (s1 with <| sym_base := s1.sym_base with as_pc := i;
                                   sym_stack := stk |>)
     | NONE => SymBad "jumpi target"`
    by (irule sym_step_jumpi_label >> simp[]) >>
  drule_then (qspecl_then [`q`, `env`] assume_tac) sym_step_iszero_val >>
  qmatch_asmsub_abbrev_tac `sym_step q env (AsmOp "ISZERO") ss = SymOK t1` >>
  qabbrev_tac `t2 = t1 with <| sym_base := asm_next t1.sym_base;
                               sym_stack := Lab y 0 :: t1.sym_stack |>` >>
  `sym_step q env (AsmPushLabel y) t1 = SymOK t2`
    by simp[Abbr `t2`, sym_step_push_label] >>
  `t1.sym_base.as_pc = LENGTH pfx + 1 ∧
   t2.sym_stack = Lab y 0 :: Val (b2w (c = 0w)) :: stk ∧
   t2.sym_base.as_pc = LENGTH pfx + 2`
    by simp[Abbr `t1`, Abbr `t2`, asmSemTheory.asm_next_def] >>
  `sym_step q env (AsmOp "JUMPI") t2 =
   if b2w (c = 0w) = (0w:bytes32) then
     SymOK (t2 with <| sym_base := asm_next t2.sym_base; sym_stack := stk |>)
   else
     case INDEX_OF (AsmLabel y) q of
       SOME i => SymOK (t2 with <| sym_base := t2.sym_base with as_pc := i;
                                   sym_stack := stk |>)
     | NONE => SymBad "jumpi target"`
    by (irule sym_step_jumpi_label >> simp[]) >>
  `(1w:bytes32) ≠ 0w`
    by simp[wordsTheory.n2w_11, wordsTheory.ONE_LT_dimword] >>
  reverse (Cases_on `c = 0w`)
  >- ((* nonzero: p jumps to LABEL x, q falls through onto it *)
      qexistsl_tac [`2`, `3`] >>
      simp[sym_steps_pos, sym_steps_def, sym_terminal_def] >>
      simp[Abbr `s1`, Abbr `t1`, Abbr `t2`, splice_pc_def,
           asmSemTheory.asm_next_def, sym_with_pc_def,
           sym_state_component_equality,
           asmSemTheory.asm_state_component_equality]) >>
  (* zero: p falls through to its JUMP, q takes its JUMPI, both to y *)
  pop_assum SUBST_ALL_TAC >>
  qabbrev_tac `s2 = s1 with <| sym_base := asm_next s1.sym_base;
                               sym_stack := stk |>` >>
  qabbrev_tac `s3 = s2 with <| sym_base := asm_next s2.sym_base;
                               sym_stack := Lab y 0 :: stk |>` >>
  `sym_step p env (AsmOp "JUMPI") s1 = SymOK s2 ∧
   s2.sym_base.as_pc = LENGTH pfx + 2 ∧
   sym_step p env (AsmPushLabel y) s2 = SymOK s3 ∧
   s3.sym_base.as_pc = LENGTH pfx + 3`
    by simp[Abbr `s2`, Abbr `s3`, sym_step_push_label,
            asmSemTheory.asm_next_def] >>
  `sym_step p env (AsmOp "JUMP") s3 =
   case INDEX_OF (AsmLabel y) p of
     SOME i => SymOK (s3 with <| sym_base := s3.sym_base with as_pc := i;
                                 sym_stack := stk |>)
   | NONE => SymBad "jump target"`
    by simp[Abbr `s3`, sym_step_def, sym_step_op_def, sym_jump_def,
            sym_jump_dest_def] >>
  qexistsl_tac [`4`, `3`] >>
  Cases_on `INDEX_OF (AsmLabel y) p` >>
  simp[sym_steps_pos, sym_steps_def, sym_terminal_def] >>
  rename1 `INDEX_OF (AsmLabel y) p = SOME i` >>
  qpat_x_assum `∀i'. SOME i = SOME i' ⇒ _` (qspec_then `i` mp_tac) >>
  simp[] >> disch_then kall_tac >>
  simp[Abbr `s1`, Abbr `s2`, Abbr `s3`, Abbr `t1`, Abbr `t2`,
       asmSemTheory.asm_next_def, sym_with_pc_def,
       sym_state_component_equality,
       asmSemTheory.asm_state_component_equality]
QED

Theorem optimize_inefficient_jumps_fst[local]:
  FST (optimize_inefficient_jumps (a :: b :: c :: d :: e :: rest)) =
  if asm_jumpi_over_jump a b c d e then
    FST (optimize_inefficient_jumps
           (AsmOp "ISZERO" :: c :: AsmOp "JUMPI" :: e :: rest))
  else a :: FST (optimize_inefficient_jumps (b :: c :: d :: e :: rest))
Proof
  simp[Once optimize_inefficient_jumps_def] >> rw[] >>
  pairarg_tac >> simp[]
QED

Theorem optimize_inefficient_jumps_refines_under:
  ∀sfx pfx.
    asm_refines (pfx ++ sfx) (pfx ++ FST (optimize_inefficient_jumps sfx))
Proof
  ho_match_mp_tac optimize_inefficient_jumps_ind >>
  reverse (rpt conj_tac)
  >- simp[optimize_inefficient_jumps_def, asm_refines_refl]
  >- simp[optimize_inefficient_jumps_def, asm_refines_refl]
  >- simp[optimize_inefficient_jumps_def, asm_refines_refl]
  >- simp[optimize_inefficient_jumps_def, asm_refines_refl]
  >- simp[optimize_inefficient_jumps_def, asm_refines_refl] >>
  rpt gen_tac >> strip_tac >> simp[optimize_inefficient_jumps_fst] >>
  reverse IF_CASES_TAC >- (gvs[] >> irule asm_refines_cons >> simp[]) >>
  Cases_on `a` >> Cases_on `e` >> gvs[asm_jumpi_over_jump_def] >>
  Cases_on `c` >> gvs[asm_is_push_label_def] >> gen_tac >>
  qmatch_goalsub_rename_tac
    `AsmPushLabel lx :: AsmOp "JUMPI" :: AsmPushLabel ly :: _` >>
  irule asm_refines_trans >>
  qexists_tac `pfx ++ AsmOp "ISZERO" :: AsmPushLabel ly :: AsmOp "JUMPI" ::
               AsmLabel lx :: rest` >>
  simp[] >>
  mp_tac (Q.INST [`pat` |-> `[AsmPushLabel lx; AsmOp "JUMPI";
                              AsmPushLabel ly; AsmOp "JUMP"]`,
                  `repl` |-> `[AsmOp "ISZERO"; AsmPushLabel ly;
                               AsmOp "JUMPI"]`,
                  `sfx` |-> `AsmLabel lx :: rest`] asm_splice_window_refines) >>
  impl_tac
  >- (simp[asm_splice_ok_def, jumpi_over_jump_window_refines,
           is_data_inst_def, asm_label_refs_def,
           symbolResolveTheory.asm_inst_size_def] >>
      rw[] >> EVAL_TAC) >>
  REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  disch_then ACCEPT_TAC
QED

Theorem optimize_inefficient_jumps_refines:
  ∀p. asm_refines p (FST (optimize_inefficient_jumps p))
Proof
  gen_tac >>
  qspecl_then [`p`, `[]`] mp_tac optimize_inefficient_jumps_refines_under >>
  simp[]
QED
