(* Compose the merge walk from its one-rename refinement interface. *)
Theory asmOwnMergeWalk
Ancestors
  finalizerContractOwn asmSymOwnCode asmOptimizer asmSem list

Theorem merge_jumpdests_walk_refines_own_under:
  (!pre x y next third more.
    (next = AsmLabel y /\ y <> x \/
     next = AsmPushLabel y /\ third = AsmOp "JUMP") ==>
    asm_refines_own (pre ++ AsmLabel x :: next :: third :: more)
      (MAP (rename_push_label x y)
        (pre ++ AsmLabel x :: next :: third :: more))) ==>
  !n done rest changed. LENGTH rest = n ==>
    asm_refines_own (REVERSE done ++ rest)
      (FST (merge_jumpdests_walk done rest changed))
Proof
  strip_tac >> completeInduct_on `n` >> rpt strip_tac >>
  `!d r c. LENGTH r < LENGTH rest ==>
      asm_refines_own (REVERSE d ++ r)
        (FST (merge_jumpdests_walk d r c))` by metis_tac[] >>
  qpat_x_assum `!m. m < n ==> _` kall_tac >>
  Cases_on `rest`
  >- simp[Once merge_jumpdests_walk_def, asm_refines_own_refl] >>
  rename1 `h :: t` >> Cases_on `t`
  >- simp[Once merge_jumpdests_walk_def, asm_refines_own_refl] >>
  rename1 `h :: next :: t` >> Cases_on `t`
  >- simp[Once merge_jumpdests_walk_def, asm_refines_own_refl] >>
  rename1 `h :: next :: third :: more` >>
  qpat_x_assum `LENGTH _ = n` kall_tac >>
  Cases_on `?x. h = AsmLabel x`
  >- (pop_assum (qx_choose_then `x` SUBST_ALL_TAC) >>
      Cases_on `?y. next = AsmLabel y /\ y <> x \/
                    next = AsmPushLabel y /\ third = AsmOp "JUMP"`
      >- (pop_assum (qx_choose_then `y` assume_tac) >>
          `merge_jumpdests_walk done (AsmLabel x :: next :: third :: more) changed =
           merge_jumpdests_walk
             (AsmLabel x :: MAP (rename_push_label x y) done)
             (MAP (rename_push_label x y) (next :: third :: more))
             (changed \/ push_label_used x
               (REVERSE done ++ AsmLabel x :: next :: third :: more))`
            by (CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [merge_jumpdests_walk_def])) >>
                qpat_x_assum `_ \/ _` strip_assume_tac >>
                gvs[LET_THM, rename_push_label_def]) >>
          pop_assum SUBST1_TAC >>
          irule asm_refines_own_trans >>
          qexists_tac `MAP (rename_push_label x y)
                         (REVERSE done ++ AsmLabel x :: next :: third :: more)` >>
          conj_tac >- metis_tac[] >>
          qmatch_goalsub_abbrev_tac `merge_jumpdests_walk _ _ cc` >>
          qpat_x_assum `!d r c. _`
            (qspecl_then [`AsmLabel x :: MAP (rename_push_label x y) done`,
                          `MAP (rename_push_label x y) (next :: third :: more)`,
                          `cc`] mp_tac) >>
          simp[MAP_REVERSE, rename_push_label_def] >>
          REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]) >>
      `merge_jumpdests_walk done (AsmLabel x :: next :: third :: more) changed =
       merge_jumpdests_walk (AsmLabel x :: done) (next :: third :: more) changed`
        by (CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [merge_jumpdests_walk_def])) >>
            Cases_on `next` >> gvs[LET_THM] >> rw[] >> gvs[]) >>
      pop_assum SUBST1_TAC >>
      qpat_x_assum `!d r c. _`
        (qspecl_then [`AsmLabel x :: done`, `next :: third :: more`,
                      `changed`] mp_tac) >>
      simp[] >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]) >>
  `merge_jumpdests_walk done (h :: next :: third :: more) changed =
   merge_jumpdests_walk (h :: done) (next :: third :: more) changed`
    by (CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [merge_jumpdests_walk_def])) >>
        Cases_on `h` >> gvs[]) >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `!d r c. _`
    (qspecl_then [`h :: done`, `next :: third :: more`, `changed`] mp_tac) >>
  simp[] >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]
QED
