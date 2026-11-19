(* Conditional syntactic preservation only: elementary global renames must
   preserve P. No concrete execution or pending-state invariant is assumed. *)
Theory staticAbortOptMergeJumpdestsWalk
Ancestors
  asmOptimizer list

Theorem merge_jumpdests_walk_preserves_contextual:
  !P.
    (!pre x y third tail.
      y <> x /\ P (pre ++ [AsmLabel x; AsmLabel y; third] ++ tail) ==>
      P (MAP (rename_push_label x y)
           (pre ++ [AsmLabel x; AsmLabel y; third] ++ tail))) /\
    (!pre x y tail.
      P (pre ++ [AsmLabel x; AsmPushLabel y; AsmOp "JUMP"] ++ tail) ==>
      P (MAP (rename_push_label x y)
           (pre ++ [AsmLabel x; AsmPushLabel y; AsmOp "JUMP"] ++ tail))) ==>
    !p. P p ==> P (FST (merge_jumpdests p))
Proof
  gen_tac >> strip_tac >>
  `!n done rest changed. LENGTH rest = n /\ P (REVERSE done ++ rest) ==>
     P (FST (merge_jumpdests_walk done rest changed))` suffices_by
    (simp[merge_jumpdests_def] >> metis_tac[REVERSE_DEF, APPEND]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  Cases_on `rest` >- (simp[Once merge_jumpdests_walk_def] >> gvs[]) >>
  rename1 `h :: t` >> Cases_on `t`
  >- (simp[Once merge_jumpdests_walk_def] >> gvs[]) >>
  rename1 `h :: next :: t` >> Cases_on `t`
  >- (simp[Once merge_jumpdests_walk_def] >> gvs[]) >>
  rename1 `h :: next :: third :: more` >>
  Cases_on `h` >>
  simp[Once merge_jumpdests_walk_def, LET_THM] >>
  TRY (first_x_assum irule >> conj_tac
       >- (pure_rewrite_tac[REVERSE_DEF, GSYM APPEND_ASSOC, APPEND] >>
           first_assum ACCEPT_TAC) >>
       gvs[] >> NO_TAC) >>
  Cases_on `next` >> simp[] >> rpt IF_CASES_TAC >> gvs[] >>
  TRY (first_x_assum irule >> conj_tac
       >- (pure_rewrite_tac[REVERSE_DEF, GSYM APPEND_ASSOC, APPEND] >>
           first_assum ACCEPT_TAC) >>
       simp[] >> NO_TAC) >>
  first_x_assum irule >> (reverse conj_tac >- simp[]) >>
  pure_rewrite_tac[REVERSE_DEF, GSYM APPEND_ASSOC, APPEND, GSYM MAP_REVERSE] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  metis_tac[]
QED
