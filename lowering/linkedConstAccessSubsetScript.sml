(* The state ownership check covers every access left after inlining. *)
Theory linkedConstAccessSubset
Ancestors
  constSubstMods vyperSubscriptOverlap vyperAST alist list pair

Triviality subst_expr_accesses_subset:
  (!key r. ALOOKUP E key = SOME r ==> accesses_expr r = []) ==>
  (!e a. MEM a (accesses_expr (subst_consts_expr_mods E e)) ==>
         MEM a (accesses_expr e)) /\
  (!t a. MEM a (accesses_target (subst_consts_btarget_mods E t)) ==>
         MEM a (accesses_target t)) /\
  (!es a. MEM a (accesses_exprs (subst_consts_exprs_mods E es)) ==>
          MEM a (accesses_exprs es)) /\
  (!opt a. MEM a (accesses_opt (subst_consts_opt_mods E opt)) ==>
           MEM a (accesses_opt opt)) /\
  (!fields a. MEM a (accesses_named_exprs (subst_consts_fields_mods E fields)) ==>
              MEM a (accesses_named_exprs fields))
Proof
  strip_tac >> ho_match_mp_tac accesses_expr_ind >>
  simp[subst_consts_expr_mods_def, accesses_expr_def, MEM_APPEND] >>
  rpt strip_tac >> gvs[]
  >~ [`subst_consts_expr_mods _ (TopLevelName _ _)`]
  >- (PairCases_on `nsid` >>
      Cases_on `ALOOKUP E (nsid0,nsid1)` >>
      gvs[subst_consts_expr_mods_def, accesses_expr_def] >>
      res_tac >> gvs[]) >>
  Cases_on `t` >> gvs[accesses_expr_def, subst_consts_expr_mods_def, MEM_APPEND]
QED

Triviality subst_atarget_accesses_subset:
  (!key r. ALOOKUP E key = SOME r ==> accesses_expr r = []) ==>
  (!t a. MEM a (accesses_atarget (subst_consts_target_mods E t)) ==>
         MEM a (accesses_atarget t)) /\
  (!ts a. MEM a (accesses_atargets (subst_consts_targets_mods E ts)) ==>
          MEM a (accesses_atargets ts))
Proof
  strip_tac >> drule_then (assume_tac o cj 2) subst_expr_accesses_subset >>
  ho_match_mp_tac accesses_atarget_ind >>
  simp[subst_consts_target_mods_def, accesses_atarget_def, MEM_APPEND] >>
  metis_tac[]
QED

Triviality custom_error_accesses_subset:
  (!key r. ALOOKUP E key = SOME r ==> accesses_expr r = []) ==>
  !err a. MEM a (accesses_exprs (custom_error_exprs (subst_consts_error_mods E err))) ==>
          MEM a (accesses_exprs (custom_error_exprs err))
Proof
  strip_tac >> drule_then (map_every assume_tac o CONJUNCTS) subst_expr_accesses_subset >>
  `!fields. accesses_exprs (MAP SND fields) = accesses_named_exprs fields` by
    (Induct >> simp[FORALL_PROD, accesses_expr_def]) >>
  `!es fs. accesses_exprs (es ++ fs) = accesses_exprs es ++ accesses_exprs fs` by
    (Induct >> simp[accesses_expr_def]) >>
  Cases >> simp[custom_error_exprs_def, subst_consts_error_mods_def, MEM_APPEND] >>
  metis_tac[]
QED

Theorem linked_subst_accesses_subset:
  (!key r. ALOOKUP E key = SOME r ==> accesses_expr r = []) ==>
  (!es a. MEM a (accesses_exprs (subst_consts_exprs_mods E es)) ==>
          MEM a (accesses_exprs es)) /\
  (!ss a. MEM a (accesses_stmts (subst_consts_stmts_mods E ss)) ==>
          MEM a (accesses_stmts ss))
Proof
  strip_tac >>
  drule_then (map_every assume_tac o CONJUNCTS) subst_expr_accesses_subset >>
  drule_then (assume_tac o cj 1) subst_atarget_accesses_subset >>
  drule_then assume_tac custom_error_accesses_subset >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `(!s a. MEM a (accesses_stmt (subst_consts_stmt_mods E s)) ==>
           MEM a (accesses_stmt s)) /\
    !ss a. MEM a (accesses_stmts (subst_consts_stmts_mods E ss)) ==>
           MEM a (accesses_stmts ss)`
    suffices_by (strip_tac >> first_assum ACCEPT_TAC) >>
  ho_match_mp_tac accesses_stmt_ind >>
  simp[subst_consts_stmt_mods_def, accesses_stmt_def, MEM_APPEND] >>
  rpt strip_tac >> gvs[]
  >~ [`accesses_iterator (subst_consts_iter_mods _ _)`]
  >- (Cases_on `iter` >> gvs[subst_consts_iter_mods_def, accesses_iterator_def, MEM_APPEND])
  >~ [`accesses_assert_reason (subst_consts_areason_mods _ _)`]
  >- (rename1 `accesses_assert_reason (subst_consts_areason_mods E reason)` >>
      Cases_on `reason` >> gvs[subst_consts_areason_mods_def, accesses_assert_reason_def])
  >~ [`accesses_raise_reason (subst_consts_rreason_mods _ _)`]
  >- (rename1 `accesses_raise_reason (subst_consts_rreason_mods E reason)` >>
      Cases_on `reason` >> gvs[subst_consts_rreason_mods_def, accesses_raise_reason_def])
QED
