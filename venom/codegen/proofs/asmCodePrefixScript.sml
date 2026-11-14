(*
 * Finalized bytecode never starts with the byte 0xEF, which EIP-3541
 * rejects as deposited code.
 *
 * The code part of an assembly program, everything before its first data
 * header, carries no data and ends in a terminal opcode. Under target
 * safety no non-data instruction encodes to a leading 0xEF, and the
 * terminal opcode encodes to a byte, so the first byte is a code byte.
 * codegen_assembly produces that shape (the plan ends with the revert
 * postamble) and every rule of the final assembly optimizer keeps it.
 *
 * TOP-LEVEL:
 *   finalize_codegen_not_ef — an accepted finalizer's bytecode does not
 *                             start with 0xEF
 *)

Theory asmCodePrefix
Ancestors
  codegen asmIR asmOptimizer asmWf asmTargetSafety symbolResolve planExec
  stackPlanGen asmOptPruneUnreachable asmOptMergeIszero asmOptPruneJumps
  asmOptInefficientJumps asmOptPeephole list rich_list

(* ===== Encoding ===== *)

Theorem evm_opcode_byte_not_ef[local]:
  evm_opcode_byte name = SOME b ⇒ b ≠ 0xEFw
Proof
  rw[evm_opcode_byte_def] >> strip_tac >> gvs[] >>
  drule alistTheory.ALOOKUP_MEM >>
  `EVERY (λp. SND p ≠ 0xEFw) evm_opcode_table`
    by (EVAL_TAC >> simp[wordsTheory.n2w_11, wordsTheory.dimword_8]) >>
  gvs[EVERY_MEM] >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem encode_inst_not_ef[local]:
  asm_inst_target_safe caps inst ∧ ¬is_data_inst inst ∧
  encode_inst offsets inst = b :: bs ⇒ b ≠ 0xEFw
Proof
  Cases_on `inst` >>
  simp[asm_inst_target_safe_def, is_data_inst_def, encode_inst_def]
  >~ [`evm_opcode_byte`]
  >- (CASE_TAC >> rw[] >> metis_tac[evm_opcode_byte_not_ef])
  >~ [`AsmPush bytes`]
  >- (Cases_on `bytes` >> simp[encode_inst_def] >> rw[] >>
      simp[wordsTheory.n2w_11, wordsTheory.dimword_8])
  >> rpt CASE_TAC >> simp[wordsTheory.dimword_8]
QED

Theorem flat_encode_not_ef[local]:
  ∀code rest.
    EVERY (asm_inst_target_safe caps) code ∧
    EVERY (λi. ¬is_data_inst i) code ∧
    EXISTS (λi. encode_inst offsets i ≠ []) code ⇒
    ∀bs. FLAT (MAP (encode_inst offsets) (code ++ rest)) ≠ 0xEFw :: bs
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `encode_inst offsets h` >> gvs[] >>
  drule_all encode_inst_not_ef >> simp[]
QED

Theorem terminal_op_facts[local]:
  asm_terminal_op t ⇒
    ¬is_data_inst t ∧ ¬asm_reachable_marker t ∧ (∀l. t ≠ AsmLabel l) ∧
    (∀l. t ≠ AsmPushLabel l) ∧ (∀h. t ≠ AsmDataHeader h) ∧
    ∀offsets. encode_inst offsets t ≠ []
Proof
  rw[asm_terminal_op_def] >> EVAL_TAC
QED

(* ===== The code part ===== *)

(* Everything before the first data header carries no data and ends in a
   terminal opcode. *)
Definition code_prefix_terminal_def:
  code_prefix_terminal asm ⇔
    ∃code t h rest.
      asm = code ++ t :: AsmDataHeader h :: rest ∧
      EVERY (λi. ¬is_data_inst i) code ∧ asm_terminal_op t
End

Theorem assemble_code_prefix_not_ef:
  code_prefix_terminal asm ∧ assembly_target_safe caps asm ⇒
  ¬∃bs. assemble asm = 0xEFw :: bs
Proof
  rw[code_prefix_terminal_def, assemble_def] >> pairarg_tac >> simp[] >>
  drule terminal_op_facts >> strip_tac >>
  qspecl_then [`code ++ [t]`, `AsmDataHeader h :: rest`] mp_tac
    (Q.GENL [`caps`, `offsets`] flat_encode_not_ef |>
     Q.SPECL [`caps`, `offsets`]) >>
  gvs[assembly_target_safe_def, EVERY_APPEND] >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]
QED

(* Consing a non-data instruction onto a list keeps the shape, in the
   normal form simp gives the equations. *)
Theorem cons_code_prefix[local]:
  (∃c r. Y = c ++ [t; AsmDataHeader lbl] ++ r ∧
         EVERY (λi. ¬is_data_inst i) c) ∧ ¬is_data_inst x ⇒
  ∃c r. x :: Y = c ++ [t; AsmDataHeader lbl] ++ r ∧
        EVERY (λi. ¬is_data_inst i) c
Proof
  rw[] >> qexistsl_tac [`x :: c`, `r`] >> simp[]
QED

Theorem cons_code_prefix_any[local]:
  (∃c t r. Y = c ++ [t; AsmDataHeader lbl] ++ r ∧
           EVERY (λi. ¬is_data_inst i) c ∧ asm_terminal_op t) ∧
  ¬is_data_inst x ⇒
  ∃c t r. x :: Y = c ++ [t; AsmDataHeader lbl] ++ r ∧
          EVERY (λi. ¬is_data_inst i) c ∧ asm_terminal_op t
Proof
  rw[] >> qexistsl_tac [`x :: c`, `t`, `r`] >> simp[]
QED

(* Replacing a window that holds no data header, and holds no terminal op
   unless a label follows it, keeps the shape. *)
Theorem code_prefix_splice_head[local]:
  ∀old code.
    old ++ sfx = code ++ t :: AsmDataHeader lbl :: rest ∧
    EVERY (λi. ¬is_data_inst i) code ∧ asm_terminal_op t ∧ old ≠ [] ∧
    (∀l. ¬MEM (AsmDataHeader l) old) ∧
    (EXISTS asm_terminal_op old ⇒ ∃l r. sfx = AsmLabel l :: r) ∧
    EVERY (λi. ¬is_data_inst i) new ⇒
    ∃code' rest'.
      new ++ sfx = code' ++ t :: AsmDataHeader lbl :: rest' ∧
      EVERY (λi. ¬is_data_inst i) code'
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >> Cases_on `code` >> fs[]
  >- (Cases_on `old` >> gvs[] >> metis_tac[]) >>
  Cases_on `old = []`
  >- (gvs[] >> qexistsl_tac [`new ++ t'`, `rest`] >> simp[EVERY_APPEND]) >>
  metis_tac[]
QED

Theorem code_prefix_splice_aux[local]:
  ∀pfx code.
    pfx ++ old ++ sfx = code ++ t :: AsmDataHeader lbl :: rest ∧
    EVERY (λi. ¬is_data_inst i) code ∧ asm_terminal_op t ∧ old ≠ [] ∧
    (∀l. ¬MEM (AsmDataHeader l) old) ∧
    (EXISTS asm_terminal_op old ⇒ ∃l r. sfx = AsmLabel l :: r) ∧
    EVERY (λi. ¬is_data_inst i) new ⇒
    ∃code' rest'.
      pfx ++ new ++ sfx = code' ++ t :: AsmDataHeader lbl :: rest' ∧
      EVERY (λi. ¬is_data_inst i) code'
Proof
  Induct
  >- (rpt strip_tac >> irule code_prefix_splice_head >> simp[] >>
      qexistsl_tac [`code`, `old`] >> fs[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `code` >> fs[]
  >- (Cases_on `pfx` >> fs[]
      >- (Cases_on `old` >> gvs[] >> metis_tac[]) >>
      qexistsl_tac [`[]`, `t' ++ new ++ sfx`] >> gvs[]) >>
  irule cons_code_prefix >> simp[] >> metis_tac[]
QED

Theorem code_prefix_splice[local]:
  ∀pfx old sfx new.
  code_prefix_terminal (pfx ++ old ++ sfx) ∧ old ≠ [] ∧
  (∀l. ¬MEM (AsmDataHeader l) old) ∧
  (EXISTS asm_terminal_op old ⇒ ∃l r. sfx = AsmLabel l :: r) ∧
  EVERY (λi. ¬is_data_inst i) new ⇒
  code_prefix_terminal (pfx ++ new ++ sfx)
Proof
  rpt gen_tac >> simp[code_prefix_terminal_def] >> strip_tac >>
  qspecl_then [`pfx`, `code`] mp_tac
    (Q.GENL [`old`, `sfx`, `t`, `lbl`, `rest`, `new`]
       code_prefix_splice_aux |>
     Q.SPECL [`old`, `sfx`, `t`, `h`, `rest`, `new`]) >>
  simp[] >> strip_tac >> metis_tac[]
QED

(* ===== _prune_unreachable_code ===== *)

Theorem code_prefix_prune_one_aux[local]:
  ∀pre code.
    pre ++ t0 :: x :: rest0 = code ++ t :: AsmDataHeader lbl :: rest ∧
    EVERY (λi. ¬is_data_inst i) code ∧ asm_terminal_op t ∧
    asm_terminal_op t0 ∧ ¬asm_reachable_marker x ⇒
    ∃code' t' rest'.
      pre ++ t0 :: rest0 = code' ++ t' :: AsmDataHeader lbl :: rest' ∧
      EVERY (λi. ¬is_data_inst i) code' ∧ asm_terminal_op t'
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> Cases_on `code` >>
      full_simp_tac std_ss [APPEND, CONS_11]
      >- gvs[asm_reachable_marker_def] >>
      rename1 `x :: rest0 = code1 ++ _` >> Cases_on `code1` >>
      full_simp_tac std_ss [APPEND, CONS_11] >>
      rpt (qpat_x_assum `_ ∧ _` strip_assume_tac)
      >- (qexistsl_tac [`[]`, `t0`, `rest`] >> gvs[]) >>
      rename1 `rest0 = code2 ++ _` >>
      qexistsl_tac [`t0 :: code2`, `t`, `rest`] >> gvs[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `code` >> fs[]
  >- (Cases_on `pre` >> fs[] >- gvs[asm_terminal_op_def] >>
      qexists_tac `[]` >> simp[]) >>
  irule cons_code_prefix_any >> simp[] >> metis_tac[]
QED

Theorem code_prefix_prune_one[local]:
  code_prefix_terminal (pre ++ t0 :: x :: rest) ∧ asm_terminal_op t0 ∧
  ¬asm_reachable_marker x ⇒
  code_prefix_terminal (pre ++ t0 :: rest)
Proof
  simp[code_prefix_terminal_def] >> strip_tac >>
  qspecl_then [`pre`, `code`] mp_tac
    (Q.GENL [`t0`, `x`, `rest0`, `t`, `lbl`, `rest`]
       code_prefix_prune_one_aux |>
     Q.SPECL [`t0`, `x`, `rest`, `t`, `h`, `rest'`]) >>
  simp[] >> strip_tac >> metis_tac[]
QED

Theorem prune_unreachable_walk_code_prefix[local]:
  ∀sfx d pfx.
    (d ⇒ ∃pre t. pfx = pre ++ [t] ∧ asm_terminal_op t) ∧
    code_prefix_terminal (pfx ++ sfx) ⇒
    code_prefix_terminal (pfx ++ FST (prune_unreachable_walk d sfx))
Proof
  Induct >- simp[prune_unreachable_walk_def] >>
  rpt strip_tac >> simp[prune_unreachable_walk_fst] >>
  IF_CASES_TAC
  >- (gvs[] >>
      first_x_assum (qspecl_then [`T`, `pre ++ [t]`] mp_tac) >>
      impl_tac
      >- (conj_tac >- (strip_tac >> qexistsl_tac [`pre`, `t`] >> simp[]) >>
          REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
          irule code_prefix_prune_one >> simp[] >>
          qexists_tac `h` >> full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]) >>
      REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]) >>
  first_x_assum (qspecl_then [`asm_terminal_op h`, `pfx ++ [h]`] mp_tac) >>
  impl_tac
  >- (conj_tac >- (strip_tac >> qexistsl_tac [`pfx`, `h`] >> simp[]) >>
      REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]
QED

Theorem prune_unreachable_code_prefix[local]:
  code_prefix_terminal p ⇒
  code_prefix_terminal (FST (prune_unreachable_code p))
Proof
  strip_tac >> simp[prune_unreachable_code_def] >>
  qspecl_then [`p`, `F`, `[]`] mp_tac prune_unreachable_walk_code_prefix >>
  simp[]
QED

(* ===== _merge_iszero ===== *)

Theorem returns_zero_or_one_facts[local]:
  asm_returns_zero_or_one x ⇒
  ∃name. x = AsmOp name ∧ ¬asm_terminal_op x
Proof
  rw[asm_returns_zero_or_one_def] >> simp[asm_terminal_op_def]
QED

Theorem merge_iszero_pairs_code_prefix[local]:
  ∀sfx pfx.
    code_prefix_terminal (pfx ++ sfx) ⇒
    code_prefix_terminal (pfx ++ FST (merge_iszero_pairs sfx))
Proof
  ho_match_mp_tac merge_iszero_pairs_ind >>
  reverse (rpt conj_tac) >- simp[merge_iszero_pairs_def]
  >- simp[merge_iszero_pairs_def] >- simp[merge_iszero_pairs_def] >>
  rpt gen_tac >> strip_tac >> simp[merge_iszero_pairs_fst] >>
  reverse IF_CASES_TAC
  >- (gvs[] >> rpt strip_tac >> first_x_assum (qspec_then `pfx ++ [x]` mp_tac) >>
      REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  gvs[] >> rpt strip_tac >> first_x_assum irule >>
  drule returns_zero_or_one_facts >> strip_tac >> gvs[] >>
  qspecl_then [`pfx`, `[AsmOp name; AsmOp "ISZERO"; AsmOp "ISZERO"]`, `rest`,
               `[AsmOp name]`] mp_tac code_prefix_splice >>
  simp[is_data_inst_def, asm_terminal_op_def] >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> gvs[asm_terminal_op_def]
QED

Theorem merge_iszero_jumpi_code_prefix[local]:
  ∀sfx pfx.
    code_prefix_terminal (pfx ++ sfx) ⇒
    code_prefix_terminal (pfx ++ FST (merge_iszero_jumpi sfx))
Proof
  ho_match_mp_tac merge_iszero_jumpi_ind >>
  reverse (rpt conj_tac) >- simp[merge_iszero_jumpi_def]
  >- simp[merge_iszero_jumpi_def] >- simp[merge_iszero_jumpi_def]
  >- simp[merge_iszero_jumpi_def] >>
  rpt gen_tac >> strip_tac >> simp[merge_iszero_jumpi_fst] >>
  reverse IF_CASES_TAC
  >- (gvs[] >> rpt strip_tac >> first_x_assum (qspec_then `pfx ++ [a]` mp_tac) >>
      REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  gvs[] >> rpt strip_tac >> first_x_assum irule >>
  qspecl_then [`pfx`, `[AsmOp "ISZERO"; AsmOp "ISZERO"]`,
               `c :: AsmOp "JUMPI" :: rest`, `[]`] mp_tac
    code_prefix_splice >>
  simp[asm_terminal_op_def] >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem merge_iszero_code_prefix[local]:
  code_prefix_terminal p ⇒ code_prefix_terminal (FST (merge_iszero p))
Proof
  strip_tac >> simp[merge_iszero_fst] >>
  qspecl_then [`FST (merge_iszero_pairs p)`, `[]`] mp_tac
    merge_iszero_jumpi_code_prefix >> simp[] >> disch_then irule >>
  qspecl_then [`p`, `[]`] mp_tac merge_iszero_pairs_code_prefix >> simp[]
QED

(* ===== _merge_jumpdests ===== *)

Theorem rename_code_prefix[local]:
  ∀x y p. code_prefix_terminal p ⇒
  code_prefix_terminal (MAP (rename_push_label x y) p)
Proof
  rw[code_prefix_terminal_def] >> drule terminal_op_facts >> strip_tac >>
  qexistsl_tac [`MAP (rename_push_label x y) code`, `t`, `h`,
                `MAP (rename_push_label x y) rest`] >>
  Cases_on `t` >> gvs[rename_push_label_def, EVERY_MAP] >>
  gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
  rename1 `MEM i code` >> Cases_on `i` >>
  gvs[rename_push_label_def, is_data_inst_def, COND_RAND]
QED

Theorem merge_jumpdests_walk_code_prefix[local]:
  ∀n done rest changed.
    LENGTH rest = n ∧ code_prefix_terminal (REVERSE done ++ rest) ⇒
    code_prefix_terminal (FST (merge_jumpdests_walk done rest changed))
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  `∀d r c. LENGTH r < LENGTH rest ∧ code_prefix_terminal (REVERSE d ++ r) ⇒
           code_prefix_terminal (FST (merge_jumpdests_walk d r c))`
    by metis_tac[] >>
  qpat_x_assum `∀m. m < n ⇒ _` kall_tac >>
  Cases_on `rest` >- gvs[Once merge_jumpdests_walk_def] >>
  rename1 `h :: t` >> Cases_on `t`
  >- (simp[Once merge_jumpdests_walk_def] >> Cases_on `h` >> gvs[]) >>
  rename1 `h :: next :: t` >> Cases_on `t`
  >- (simp[Once merge_jumpdests_walk_def] >> Cases_on `h` >> gvs[]) >>
  rename1 `h :: next :: third :: more` >>
  qpat_x_assum `LENGTH _ = n` kall_tac >>
  Cases_on `∃x. h = AsmLabel x`
  >- (
    pop_assum (qx_choose_then `x` SUBST_ALL_TAC) >>
    Cases_on `∃y. next = AsmLabel y ∧ y ≠ x ∨
                  next = AsmPushLabel y ∧ third = AsmOp "JUMP"`
    >- (
      pop_assum (qx_choose_then `y` assume_tac) >>
      `merge_jumpdests_walk done (AsmLabel x :: next :: third :: more) changed =
       merge_jumpdests_walk
         (AsmLabel x :: MAP (rename_push_label x y) done)
         (MAP (rename_push_label x y) (next :: third :: more))
         (changed ∨
          push_label_used x (REVERSE done ++ AsmLabel x :: next :: third :: more))`
        by (CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [merge_jumpdests_walk_def])) >>
            qpat_x_assum `_ ∨ _` strip_assume_tac >>
            gvs[LET_THM, rename_push_label_def]) >>
      pop_assum SUBST1_TAC >>
      qmatch_goalsub_abbrev_tac `merge_jumpdests_walk _ _ cc` >>
      first_x_assum irule >> simp[MAP_REVERSE] >>
      drule rename_code_prefix >>
      disch_then (qspecl_then [`x`, `y`] mp_tac) >>
      simp[MAP_REVERSE, rename_push_label_def] >>
      REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]) >>
    `merge_jumpdests_walk done (AsmLabel x :: next :: third :: more) changed =
     merge_jumpdests_walk (AsmLabel x :: done) (next :: third :: more) changed`
      by (CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [merge_jumpdests_walk_def])) >>
          Cases_on `next` >> gvs[LET_THM] >> rw[] >> gvs[]) >>
    pop_assum SUBST1_TAC >> first_x_assum irule >> simp[] >>
    REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  `merge_jumpdests_walk done (h :: next :: third :: more) changed =
   merge_jumpdests_walk (h :: done) (next :: third :: more) changed`
    by (CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [merge_jumpdests_walk_def])) >>
        Cases_on `h` >> gvs[]) >>
  pop_assum SUBST1_TAC >> first_x_assum irule >> simp[] >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem merge_jumpdests_code_prefix[local]:
  code_prefix_terminal p ⇒ code_prefix_terminal (FST (merge_jumpdests p))
Proof
  strip_tac >> simp[merge_jumpdests_def] >>
  qspecl_then [`LENGTH p`, `[]`, `p`, `F`] mp_tac
    merge_jumpdests_walk_code_prefix >> simp[]
QED

(* ===== _prune_inefficient_jumps ===== *)

Theorem prune_inefficient_jumps_code_prefix[local]:
  ∀sfx pfx.
    code_prefix_terminal (pfx ++ sfx) ⇒
    code_prefix_terminal (pfx ++ FST (prune_inefficient_jumps sfx))
Proof
  ho_match_mp_tac prune_inefficient_jumps_ind >>
  reverse (rpt conj_tac) >- simp[prune_inefficient_jumps_def]
  >- simp[prune_inefficient_jumps_def] >- simp[prune_inefficient_jumps_def] >>
  rpt gen_tac >> strip_tac >> simp[prune_inefficient_jumps_fst] >>
  reverse IF_CASES_TAC
  >- (gvs[] >> rpt strip_tac >> first_x_assum (qspec_then `pfx ++ [a]` mp_tac) >>
      REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  Cases_on `a` >> gvs[asm_jump_to_next_def] >>
  Cases_on `c` >> gvs[] >> rpt strip_tac >> first_x_assum irule >>
  qmatch_goalsub_rename_tac `AsmLabel lbl :: rest` >>
  qspecl_then [`pfx`, `[AsmPushLabel lbl; AsmOp "JUMP"]`,
               `AsmLabel lbl :: rest`, `[]`] mp_tac
    code_prefix_splice >>
  simp[] >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

(* ===== _optimize_inefficient_jumps ===== *)

Theorem optimize_inefficient_jumps_code_prefix[local]:
  ∀sfx pfx.
    code_prefix_terminal (pfx ++ sfx) ⇒
    code_prefix_terminal (pfx ++ FST (optimize_inefficient_jumps sfx))
Proof
  ho_match_mp_tac optimize_inefficient_jumps_ind >>
  reverse (rpt conj_tac) >- simp[optimize_inefficient_jumps_def]
  >- simp[optimize_inefficient_jumps_def]
  >- simp[optimize_inefficient_jumps_def]
  >- simp[optimize_inefficient_jumps_def]
  >- simp[optimize_inefficient_jumps_def] >>
  rpt gen_tac >> strip_tac >> simp[optimize_inefficient_jumps_fst] >>
  reverse IF_CASES_TAC
  >- (gvs[] >> rpt strip_tac >> first_x_assum (qspec_then `pfx ++ [a]` mp_tac) >>
      REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  Cases_on `a` >> Cases_on `e` >> gvs[asm_jumpi_over_jump_def] >>
  Cases_on `c` >> gvs[asm_is_push_label_def] >> rpt strip_tac >>
  first_x_assum irule >>
  qmatch_goalsub_rename_tac `AsmLabel lx :: rest` >>
  qmatch_goalsub_rename_tac `AsmPushLabel ly :: AsmOp "JUMPI" :: _` >>
  qspecl_then [`pfx`, `[AsmPushLabel lx; AsmOp "JUMPI"; AsmPushLabel ly;
                        AsmOp "JUMP"]`,
               `AsmLabel lx :: rest`,
               `[AsmOp "ISZERO"; AsmPushLabel ly; AsmOp "JUMPI"]`] mp_tac
    code_prefix_splice >>
  simp[is_data_inst_def] >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

(* ===== _prune_unused_jumpdests ===== *)

Theorem filter_unused_code_prefix[local]:
  ∀sfx pfx.
    code_prefix_terminal (pfx ++ sfx) ⇒
    code_prefix_terminal (pfx ++ FILTER ($~ o asm_unused_label used) sfx)
Proof
  Induct >- simp[] >>
  rpt strip_tac >> reverse (Cases_on `asm_unused_label used h`) >> simp[]
  >- (first_x_assum (qspec_then `pfx ++ [h]` mp_tac) >>
      REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> disch_then irule >> simp[]) >>
  Cases_on `h` >> gvs[asm_unused_label_def] >>
  first_x_assum irule >>
  qspecl_then [`pfx`, `[AsmLabel s]`, `sfx`, `[]`] mp_tac
    code_prefix_splice >>
  simp[asm_terminal_op_def] >> disch_then irule >>
  full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]
QED

Theorem prune_unused_jumpdests_code_prefix[local]:
  code_prefix_terminal p ⇒
  code_prefix_terminal (FST (prune_unused_jumpdests p))
Proof
  strip_tac >> simp[prune_unused_jumpdests_def] >>
  qspecl_then [`p`, `[]`] mp_tac
    (Q.INST [`used` |-> `asm_label_refs p`] filter_unused_code_prefix) >>
  simp[]
QED

(* ===== _stack_peephole_opts ===== *)

Theorem peep_swap_pair_code_prefix[local]:
  peep_swap_pair a b c rest = (l, ch) ∧
  code_prefix_terminal (pfx ++ a :: b :: c :: rest) ⇒
  code_prefix_terminal (pfx ++ l)
Proof
  rw[peep_swap_pair_def] >> simp[] >>
  Cases_on `a` >> gvs[asm_swap_op_def] >>
  qspecl_then [`pfx`, `[AsmOp s; AsmOp s]`, `c :: rest`, `[]`] mp_tac
    code_prefix_splice >>
  simp[] >> impl_tac
  >- (full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND] >> rpt strip_tac >> gvs[asm_terminal_op_def]) >>
  simp[]
QED

Theorem peep_swap_comm_code_prefix[local]:
  peep_swap_comm l = SOME (l', ch) ∧ code_prefix_terminal (pfx ++ l) ⇒
  code_prefix_terminal (pfx ++ l')
Proof
  rw[peep_swap_comm_def, AllCaseEqs()] >> simp[] >>
  qmatch_goalsub_rename_tac `pfx ++ rr` >>
  qspecl_then [`pfx`, `[AsmOp "SWAP1"]`, `rr`, `[]`] mp_tac
    code_prefix_splice >>
  simp[asm_terminal_op_def] >> disch_then irule >> full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]
QED

Theorem peep_dup_swap_code_prefix[local]:
  peep_dup_swap l = SOME (l', ch) ∧ code_prefix_terminal (pfx ++ l) ⇒
  code_prefix_terminal (pfx ++ l')
Proof
  rw[peep_dup_swap_def, AllCaseEqs()] >> simp[] >>
  qmatch_goalsub_rename_tac `AsmOp "DUP1" :: rr` >>
  qspecl_then [`pfx ++ [AsmOp "DUP1"]`, `[AsmOp "SWAP1"]`, `rr`, `[]`] mp_tac
    code_prefix_splice >>
  simp[asm_terminal_op_def] >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  simp[]
QED

Theorem stack_peephole_opts_code_prefix[local]:
  ∀asm pfx out c.
    stack_peephole_opts asm = SOME (out, c) ∧
    code_prefix_terminal (pfx ++ asm) ⇒
    code_prefix_terminal (pfx ++ out)
Proof
  measureInduct_on `LENGTH asm` >>
  Cases_on `asm` >- simp[Once stack_peephole_opts_def] >>
  rename1 `a :: t1` >> Cases_on `t1`
  >- simp[Once stack_peephole_opts_def] >>
  rename1 `a :: b :: t2` >> Cases_on `t2`
  >- simp[Once stack_peephole_opts_def] >>
  rename1 `a :: b :: c1 :: rest` >> rpt gen_tac >> strip_tac >>
  drule stack_peephole_opts_cons3 >> strip_tac >> gvs[]
  >~ [`stack_peephole_opts (AsmOp "SWAP1" :: AsmOp "DUP2" :: _)`]
  >- (first_x_assum irule >> simp[] >> first_assum (irule_at Any) >>
      qspecl_then [`pfx`, `[AsmOp "DUP1"; AsmOp "SWAP2"; AsmOp "SWAP1"]`,
                   `rest`, `[AsmOp "SWAP1"; AsmOp "DUP2"]`] mp_tac
        code_prefix_splice >>
      simp[asm_terminal_op_def, is_data_inst_def] >>
      full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND])
  >~ [`stack_peephole_opts rest = SOME _`]
  >- (first_x_assum irule >> simp[] >> first_assum (irule_at Any) >>
      qspecl_then [`pfx`, `[AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "POP"]`,
                   `rest`, `[]`] mp_tac code_prefix_splice >>
      simp[asm_terminal_op_def] >>
      full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND])
  >~ [`stack_peephole_opts (AsmOp "POP" :: AsmOp "POP" :: _)`]
  >- (first_x_assum irule >> simp[] >> first_assum (irule_at Any) >>
      qspecl_then [`pfx`, `[AsmOp "SWAP1"]`, `AsmOp "POP" :: AsmOp "POP" :: rest`,
                   `[]`] mp_tac code_prefix_splice >>
      simp[asm_terminal_op_def] >>
      full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]) >>
  imp_res_tac peep_swap_pair_length >>
  imp_res_tac peep_swap_comm_length >>
  imp_res_tac peep_dup_swap_length >>
  drule_all peep_swap_pair_code_prefix >> strip_tac >>
  drule_all peep_swap_comm_code_prefix >> strip_tac >>
  drule_all peep_dup_swap_code_prefix >> strip_tac >>
  first_x_assum (qspec_then `t` mp_tac) >> impl_tac >- gvs[] >>
  disch_then (qspec_then `pfx ++ [h]` mp_tac) >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> metis_tac[]
QED

(* ===== The optimizer ===== *)

Theorem optimize_round_code_prefix[local]:
  optimize_round p = SOME (p', c) ∧ code_prefix_terminal p ⇒
  code_prefix_terminal p'
Proof
  rw[optimize_round_def] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[optionTheory.OPTION_MAP_EQ_SOME, pairTheory.EXISTS_PROD] >>
  rpt (pairarg_tac >> gvs[]) >>
  qspecl_then [`asm6`, `[]`] mp_tac stack_peephole_opts_code_prefix >>
  simp[] >> disch_then irule >>
  `code_prefix_terminal asm1`
    by (mp_tac prune_unreachable_code_prefix >> gvs[]) >>
  `code_prefix_terminal asm2`
    by (mp_tac (Q.INST [`p` |-> `asm1`] merge_iszero_code_prefix) >> gvs[]) >>
  `code_prefix_terminal asm3`
    by (mp_tac (Q.INST [`p` |-> `asm2`] merge_jumpdests_code_prefix) >> gvs[]) >>
  `code_prefix_terminal asm4`
    by (qspecl_then [`asm3`, `[]`] mp_tac prune_inefficient_jumps_code_prefix >>
        gvs[]) >>
  `code_prefix_terminal asm5`
    by (qspecl_then [`asm4`, `[]`] mp_tac
          optimize_inefficient_jumps_code_prefix >> gvs[]) >>
  mp_tac (Q.INST [`p` |-> `asm5`] prune_unused_jumpdests_code_prefix) >> gvs[]
QED

Theorem optimize_assembly_rounds_code_prefix[local]:
  ∀n p p'.
    optimize_assembly_rounds n p = SOME p' ∧ code_prefix_terminal p ⇒
    code_prefix_terminal p'
Proof
  Induct >> simp[optimize_assembly_rounds_def] >>
  rpt gen_tac >> CASE_TAC >> PairCases_on `x` >> rw[] >>
  metis_tac[optimize_round_code_prefix]
QED

Theorem accepted_finalizer_code_prefix:
  fin ∈ accepted_finalizers ∧ fin rpolicy asm = SOME asm' ∧
  code_prefix_terminal asm ⇒
  code_prefix_terminal asm'
Proof
  rw[accepted_finalizers_def] >> gvs[asm_opt_finalizer_def] >>
  gvs[AllCaseEqs(), optimize_assembly_def] >>
  metis_tac[optimize_assembly_rounds_code_prefix]
QED

(* ===== Code generation ===== *)

Theorem exec_stack_op_not_data[local]:
  EVERY (λi. ¬is_data_inst i) (exec_stack_op fmp op)
Proof
  Cases_on `op` >> TRY (Cases_on `o'`) >>
  simp[exec_stack_op_def, is_data_inst_def]
QED

Theorem codegen_assembly_code_prefix:
  codegen_assembly rpolicy unit = SOME asm ⇒ code_prefix_terminal asm
Proof
  rw[codegen_assembly_def, AllCaseEqs()] >>
  simp[code_prefix_terminal_def, context_plan_ops_def, execute_plan_def,
       revert_postamble_def, exec_stack_op_def] >>
  Cases_on `unit.cu_data_segment` >>
  simp[data_segment_asm_def, data_section_asm_def]
  >- (qexists_tac `FLAT (MAP (exec_stack_op plan.cp_initial_fmp)
                     (FLAT (MAP (λr. r.sr_plan) plan.cp_regions))) ++
                   [AsmLabel "revert"; AsmPush (encode_num_bytes_fuel 32 0);
                    AsmOp "DUP1"]` >>
      simp[EVERY_FLAT, EVERY_MAP, is_data_inst_def, asm_terminal_op_def,
           exec_stack_op_not_data]) >>
  qexists_tac `FLAT (MAP (exec_stack_op plan.cp_initial_fmp)
                 (FLAT (MAP (λr. r.sr_plan) plan.cp_regions))) ++
               [AsmLabel "revert"; AsmPush (encode_num_bytes_fuel 32 0);
                AsmOp "DUP1"]` >>
  simp[EVERY_FLAT, EVERY_MAP, is_data_inst_def, asm_terminal_op_def,
       exec_stack_op_not_data]
QED

Theorem finalize_codegen_not_ef:
  finalize_codegen fin rpolicy unit = SOME bc ∧ fin ∈ accepted_finalizers ⇒
  ¬∃t. bc = 0xEFw :: t
Proof
  rw[finalize_codegen_def, AllCaseEqs()] >>
  drule codegen_assembly_code_prefix >> strip_tac >>
  drule_all accepted_finalizer_code_prefix >> strip_tac >>
  drule_all assemble_code_prefix_not_ef >> simp[]
QED
