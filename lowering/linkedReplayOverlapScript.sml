Theory linkedReplayOverlap
Ancestors
  constSubstMods constSubstStmtsPreserve constSubstCorrect vyperInterpreter vyperTypeContract
  vyperSubscriptOverlap vyperTypeCallGraph targetOverlapAccess alist list pair

Theorem linked_subst_accesses_aux[local]:
  ALL_DISTINCT (MAP FST mods) /\
  (!src id r. ALOOKUP E (src,id) = SOME r ==>
    declared_constant mods src id /\ constant_expr mods r /\ accesses_expr r = []) ==>
  ((!e. int_calls_expr (subst_consts_expr_mods E e) = int_calls_expr e /\
        nonconstant_reads mods (accesses_expr (subst_consts_expr_mods E e)) =
        nonconstant_reads mods (accesses_expr e) /\
        FILTER (\a. !r. a <> ReadAcc r) (accesses_expr (subst_consts_expr_mods E e)) =
        FILTER (\a. !r. a <> ReadAcc r) (accesses_expr e)) /\
   (!t. int_calls_target (subst_consts_btarget_mods E t) = int_calls_target t /\
        nonconstant_reads mods (accesses_target (subst_consts_btarget_mods E t)) =
        nonconstant_reads mods (accesses_target t) /\
        FILTER (\a. !r. a <> ReadAcc r) (accesses_target (subst_consts_btarget_mods E t)) =
        FILTER (\a. !r. a <> ReadAcc r) (accesses_target t)) /\
   (!es. int_calls_exprs (subst_consts_exprs_mods E es) = int_calls_exprs es /\
         nonconstant_reads mods (accesses_exprs (subst_consts_exprs_mods E es)) =
         nonconstant_reads mods (accesses_exprs es) /\
         FILTER (\a. !r. a <> ReadAcc r) (accesses_exprs (subst_consts_exprs_mods E es)) =
         FILTER (\a. !r. a <> ReadAcc r) (accesses_exprs es)) /\
   (!opt. int_calls_opt (subst_consts_opt_mods E opt) = int_calls_opt opt /\
          nonconstant_reads mods (accesses_opt (subst_consts_opt_mods E opt)) =
          nonconstant_reads mods (accesses_opt opt) /\
          FILTER (\a. !r. a <> ReadAcc r) (accesses_opt (subst_consts_opt_mods E opt)) =
          FILTER (\a. !r. a <> ReadAcc r) (accesses_opt opt)) /\
   (!fs. int_calls_named_exprs (subst_consts_fields_mods E fs) = int_calls_named_exprs fs /\
         nonconstant_reads mods (accesses_named_exprs (subst_consts_fields_mods E fs)) =
         nonconstant_reads mods (accesses_named_exprs fs) /\
         FILTER (\a. !r. a <> ReadAcc r) (accesses_named_exprs (subst_consts_fields_mods E fs)) =
         FILTER (\a. !r. a <> ReadAcc r) (accesses_named_exprs fs)))
Proof
  strip_tac >> ho_match_mp_tac accesses_expr_ind >>
  simp[subst_consts_expr_mods_def, int_calls_expr_def, accesses_expr_def,
       nonconstant_reads_append, FILTER_APPEND_DISTRIB] >>
  rpt strip_tac >> gvs[]
  >>~- ([`subst_consts_expr_mods E (TopLevelName _ _)`],
    rename1 `subst_consts_expr_mods E (TopLevelName ty ns)` >>
    PairCases_on `ns` >>
    simp[subst_consts_expr_mods_def, int_calls_expr_def, accesses_expr_def] >>
    Cases_on `ALOOKUP E (ns0,ns1)` >>
    simp[int_calls_expr_def, accesses_expr_def] >>
    first_x_assum drule >> strip_tac >>
    drule_all declared_constant_overlap_test >> strip_tac >>
    simp[nonconstant_reads_def] >>
    drule (CONJUNCT1 constant_expr_no_internal_calls) >> simp[]) >>
  Cases_on `t` >> gvs[int_calls_expr_def, accesses_expr_def]
QED

Theorem linked_replay_guard_spine:
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALL_DISTINCT (MAP FST mods) /\
  (!src id r. ALOOKUP E (src,id) = SOME r ==>
    declared_constant mods src id /\ constant_expr mods r /\ accesses_expr r = []) /\
  expr_type (subst_consts_expr_mods E a) = expr_type a /\
  subscript_reads_base cx a b <>
    subscript_reads_base cx (subst_consts_expr_mods E a) (subst_consts_expr_mods E b) ==>
  base_through_dynarray a <> base_through_dynarray (subst_consts_expr_mods E a)
Proof
  strip_tac >> drule_all linked_subst_accesses_aux >>
  disch_then (fn th =>
    qspec_then `a` strip_assume_tac (CONJUNCT1 th) >>
    qspec_then `b` strip_assume_tac (CONJUNCT1 th)) >>
  `!z. MEM z (FILTER (\a. !r. a <> ReadAcc r)
                  (accesses_expr (subst_consts_expr_mods E b))) <=>
       MEM z (FILTER (\a. !r. a <> ReadAcc r) (accesses_expr b))` by simp[] >>
  `!z. (!r. z <> ReadAcc r) ==>
       (MEM z (accesses_expr (subst_consts_expr_mods E b)) <=>
        MEM z (accesses_expr b))` by
    (gen_tac >> strip_tac >>
     qpat_assum `!z. MEM z (FILTER _ _) <=> _` (qspec_then `z` mp_tac) >>
     pure_rewrite_tac[MEM_FILTER] >> simp[]) >>
  CCONTR_TAC >> gvs[] >>
  qpat_x_assum `subscript_reads_base _ _ _ <> _` mp_tac >>
  simp[subscript_reads_base_def, subscript_overlap_def, expr_accesses_def,
       reached_functions_def, nonconstant_reads_append, any_written_MEM,
       MEM_APPEND]
QED
