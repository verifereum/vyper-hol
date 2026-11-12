Theory asmOptNonemptyScan
Ancestors
  asmOptimizer asmOptNonemptyJumps list rich_list


Theorem prune_unreachable_walk_no_labels[local]:
  !p d. EVERY (\i. !l. i <> AsmLabel l) p ==>
    EVERY (\i. !l. i <> AsmLabel l) (FST (prune_unreachable_walk d p))
Proof
  Induct >> simp[prune_unreachable_walk_def, prune_unreachable_walk_def, pairTheory.ELIM_UNCURRY, COND_RAND] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

Theorem prune_unreachable_walk_trailing[local]:
  !p d. (?pre t post. p = pre ++ t::post /\ asm_terminal_op t /\
     EVERY (\i. !l. i <> AsmLabel l) post) ==>
  (?pre t post. FST (prune_unreachable_walk d p) = pre ++ t::post /\
     asm_terminal_op t /\ EVERY (\i. !l. i <> AsmLabel l) post) \/
  (d /\ EVERY (\i. !l. i <> AsmLabel l)
        (FST (prune_unreachable_walk d p)))
Proof
  Induct >- simp[] >>
  rpt gen_tac >> rewrite_tac[PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND] asmOptNonemptyJumpsTheory.trailing_terminal_cons] >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac assume_tac)
  >- (pure_rewrite_tac[prune_unreachable_walk_def, pairTheory.ELIM_UNCURRY,
                         pairTheory.FST, COND_RAND] >> BETA_TAC >> IF_CASES_TAC >> asm_rewrite_tac[]
      >- simp[prune_unreachable_walk_no_labels]
      >> disj1_tac >>
      qexistsl [`[]`, `h`, `FST (prune_unreachable_walk T p)`] >>
      simp[prune_unreachable_walk_no_labels])
  >> pure_rewrite_tac[prune_unreachable_walk_def, pairTheory.ELIM_UNCURRY,
                         pairTheory.FST, COND_RAND] >> BETA_TAC >> IF_CASES_TAC >> asm_rewrite_tac[]
  >- (first_x_assum (qspec_then `T` mp_tac) >> simp[])
  >> first_x_assum (qspec_then `asm_terminal_op h` mp_tac) >>
  simp[] >> strip_tac >> disj1_tac
  >- (qexistsl [`h::pre`, `t`, `post`] >> simp[])
  >> qexistsl [`[]`, `h`, `FST (prune_unreachable_walk (asm_terminal_op h) p)`] >>
  simp[]
QED

Theorem prune_unreachable_code_trailing_terminal:
  (?pre t post. p = pre ++ t::post /\ asm_terminal_op t /\
     EVERY (\i. !l. i <> AsmLabel l) post) ==>
  ?pre t post. FST (prune_unreachable_code p) = pre ++ t::post /\
     asm_terminal_op t /\ EVERY (\i. !l. i <> AsmLabel l) post
Proof
  disch_tac >> drule prune_unreachable_walk_trailing >>
  disch_then (qspec_then `F` mp_tac) >>
  simp[prune_unreachable_code_def]
QED

Theorem rename_push_label_trailing[local]:
  (?pre t post. p = pre ++ t::post /\ asm_terminal_op t /\
     EVERY (\i. !l. i <> AsmLabel l) post) ==>
  ?pre t post. MAP (rename_push_label x y) p = pre ++ t::post /\
     asm_terminal_op t /\ EVERY (\i. !l. i <> AsmLabel l) post
Proof
  strip_tac >> qexistsl [`MAP (rename_push_label x y) pre`, `t`,
                         `MAP (rename_push_label x y) post`] >>
  gvs[asm_terminal_op_def, rename_push_label_def, MAP_APPEND, EVERY_MAP] >>
  irule EVERY_MONOTONIC >> first_assum (irule_at Any) >>
  Cases >> simp[rename_push_label_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()]
QED

Theorem prune_unused_jumpdests_trailing_terminal:
  (?pre t post. p = pre ++ t::post /\ asm_terminal_op t /\
     EVERY (\i. !l. i <> AsmLabel l) post) ==>
  ?pre t post. FST (prune_unused_jumpdests p) = pre ++ t::post /\
     asm_terminal_op t /\ EVERY (\i. !l. i <> AsmLabel l) post
Proof
  strip_tac >> simp[prune_unused_jumpdests_def] >>
  qexistsl [`FILTER ($~ o asm_unused_label (asm_label_refs p)) pre`, `t`,
            `FILTER ($~ o asm_unused_label (asm_label_refs p)) post`] >>
  gvs[FILTER_APPEND, asm_terminal_op_def, asm_unused_label_def] >>
  gvs[EVERY_FILTER, EVERY_MEM]
QED

Theorem merge_jumpdests_walk_trailing[local]:
  !done rest changed.
  (?pre t post. REVERSE done ++ rest = pre ++ t::post /\
    asm_terminal_op t /\ EVERY (\i. !l. i <> AsmLabel l) post) ==>
  ?pre t post. FST (merge_jumpdests_walk done rest changed) = pre ++ t::post /\
    asm_terminal_op t /\ EVERY (\i. !l. i <> AsmLabel l) post
Proof
  recInduct merge_jumpdests_walk_ind >> rpt gen_tac >> strip_tac >>
  Cases_on `rest` >- simp[Once merge_jumpdests_walk_def] >>
  rename1 `h::tail` >> Cases_on `tail`
  >- simp[Once merge_jumpdests_walk_def] >>
  rename1 `h::next::tail` >> Cases_on `tail`
  >- simp[Once merge_jumpdests_walk_def] >>
  rename1 `h::next::third::more` >>
  Cases_on `h` >> gvs[] >>
  simp[Once merge_jumpdests_walk_def] >> gvs[] >>
  qmatch_asmsub_abbrev_tac `target = NONE` >>
  Cases_on `target` >> gvs[] >>
  disch_tac >> first_x_assum irule >> simp[] >>
  drule (SRULE [] rename_push_label_trailing) >>
  disch_then (qspecl_then [`x`, `s`] mp_tac) >>
  simp[MAP_APPEND, MAP_REVERSE]
QED

Theorem merge_jumpdests_trailing_terminal:
  (?pre t post. p = pre ++ t::post /\ asm_terminal_op t /\
     EVERY (\i. !l. i <> AsmLabel l) post) ==>
  ?pre t post. FST (merge_jumpdests p) = pre ++ t::post /\
     asm_terminal_op t /\ EVERY (\i. !l. i <> AsmLabel l) post
Proof
  mp_tac (Q.SPECL [`[]`, `p`, `F`] merge_jumpdests_walk_trailing) >>
  simp[merge_jumpdests_def]
QED
