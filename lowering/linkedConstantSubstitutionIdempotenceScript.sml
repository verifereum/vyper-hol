(* Qualified substitutions are idempotent when every replacement is fixed. *)
Theory linkedConstantSubstitutionIdempotence
Ancestors constSubstMods constSubst constSubstCorrect vyperSubscriptOverlap vyperTypeContract alist pair

Theorem subst_consts_expr_mods_idempotent:
  (!id rhs. ALOOKUP env id = SOME rhs ==> subst_consts_expr_mods env rhs = rhs) ==>
  (!e. subst_consts_expr_mods env (subst_consts_expr_mods env e) =
       subst_consts_expr_mods env e) /\
  (!t. subst_consts_btarget_mods env (subst_consts_btarget_mods env t) =
       subst_consts_btarget_mods env t) /\
  (!es. subst_consts_exprs_mods env (subst_consts_exprs_mods env es) =
        subst_consts_exprs_mods env es) /\
  (!d. subst_consts_opt_mods env (subst_consts_opt_mods env d) =
       subst_consts_opt_mods env d) /\
  (!fs. subst_consts_fields_mods env (subst_consts_fields_mods env fs) =
        subst_consts_fields_mods env fs)
Proof
  strip_tac >> ho_match_mp_tac fold_const_expr_ind >>
  simp[subst_consts_expr_mods_def] >>
  rpt gen_tac >> PairCases_on `ns` >>
  Cases_on `ALOOKUP env (ns0,ns1)` >>
  simp[subst_consts_expr_mods_def] >>
  first_x_assum drule >> simp[]
QED

Theorem subst_consts_stmts_mods_idempotent:
  (!id rhs. ALOOKUP env id = SOME rhs ==> subst_consts_expr_mods env rhs = rhs) ==>
  subst_consts_stmts_mods env (subst_consts_stmts_mods env ss) =
  subst_consts_stmts_mods env ss
Proof
  strip_tac >> drule_then strip_assume_tac subst_consts_expr_mods_idempotent >>
  `(!E t. E = env ==>
      subst_consts_target_mods E (subst_consts_target_mods E t) = subst_consts_target_mods E t) /\
   (!E ts. E = env ==>
      subst_consts_targets_mods E (subst_consts_targets_mods E ts) = subst_consts_targets_mods E ts)` by
    (ho_match_mp_tac subst_consts_target_mods_ind >> simp[subst_consts_target_mods_def]) >>
  `!iter. subst_consts_iter_mods env (subst_consts_iter_mods env iter) =
          subst_consts_iter_mods env iter` by (Cases >> simp[subst_consts_iter_mods_def]) >>
  `!err. subst_consts_error_mods env (subst_consts_error_mods env err) =
         subst_consts_error_mods env err` by (Cases >> simp[subst_consts_error_mods_def]) >>
  `!reason. subst_consts_areason_mods env (subst_consts_areason_mods env reason) =
            subst_consts_areason_mods env reason` by (Cases >> simp[subst_consts_areason_mods_def]) >>
  `!reason. subst_consts_rreason_mods env (subst_consts_rreason_mods env reason) =
            subst_consts_rreason_mods env reason` by (Cases >> simp[subst_consts_rreason_mods_def]) >>
  `(!E s. E = env ==>
      subst_consts_stmt_mods E (subst_consts_stmt_mods E s) = subst_consts_stmt_mods E s) /\
   (!E sl. E = env ==>
      subst_consts_stmts_mods E (subst_consts_stmts_mods E sl) = subst_consts_stmts_mods E sl)`
    suffices_by simp[] >>
  ho_match_mp_tac subst_consts_stmt_mods_ind >> simp[subst_consts_stmt_mods_def]
QED

Theorem subst_consts_expr_mods_closed:
  (!e. constant_expr mods e /\ vyperSubscriptOverlap$accesses_expr e = [] ==>
    subst_consts_expr_mods E e = e) /\
  (!es. EVERY (constant_expr mods) es /\ vyperSubscriptOverlap$accesses_exprs es = [] ==>
    subst_consts_exprs_mods E es = es) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) /\
    vyperSubscriptOverlap$accesses_named_exprs fs = [] ==>
    subst_consts_fields_mods E fs = fs)
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[vyperTypeContractTheory.constant_expr_def, subst_consts_expr_mods_def,
       vyperSubscriptOverlapTheory.accesses_expr_def, SF ETA_ss] >>
  rpt strip_tac >> rename1 `risky_builtin bi` >>
  Cases_on `vyperSubscriptOverlap$risky_builtin bi` >> gvs[SF ETA_ss]
QED
