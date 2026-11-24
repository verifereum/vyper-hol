Theory linkedSubstitutionAbiTargets
Ancestors
  constSubstMods whitelistLinkedBodyCallSites constSubstStmtsPreserve
  supportedProgram supportedExprTraverse supportedStmtTraverse
  vyperTypeContract vyperAST alist list pair

val decode_expression_reflection_tac =
  `EVERY (constant_expr mods o SND) (consts_env_mods mods)` by
    (qpat_assum `check_contract mode layouts addr mods = SOME art`
       (ACCEPT_TAC o MATCH_MP whitelistLinkedBodyCallSitesTheory.checked_const_mods_constant)) >>
  `!key replacement target. ALOOKUP (consts_env_mods mods) key = SOME replacement ==>
     ~supported_expr_exists (expr_abi_decode_target_root target) replacement` by
    (map_every qx_gen_tac [`decode_key`,`decode_replacement`,`decode_ty`] >> disch_tac >>
     `MEM (decode_key,decode_replacement) (consts_env_mods mods)` by
       (irule alistTheory.ALOOKUP_MEM >> FIRST_ASSUM ACCEPT_TAC) >>
     `constant_expr mods decode_replacement` by
       (qpat_assum `EVERY (constant_expr mods o SND) _`
          (qspec_then `(decode_key,decode_replacement)` mp_tac o REWRITE_RULE [listTheory.EVERY_MEM]) >>
        simp[combinTheory.o_THM]) >>
     irule (cj 1 constSubstStmtsPreserveTheory.constant_expr_no_abi_decode) >>
     qexists_tac `mods` >> FIRST_ASSUM ACCEPT_TAC) >>
  `!target.
     (!env e. (!key r. ALOOKUP env key = SOME r ==>
                 ~supported_expr_exists (expr_abi_decode_target_root target) r) ==>
          supported_expr_exists (expr_abi_decode_target_root target)
            (subst_consts_expr_mods env e) ==>
          supported_expr_exists (expr_abi_decode_target_root target) e) /\
     (!env t. (!key r. ALOOKUP env key = SOME r ==>
                 ~supported_expr_exists (expr_abi_decode_target_root target) r) ==>
          supported_target_exists (expr_abi_decode_target_root target)
            (subst_consts_btarget_mods env t) ==>
          supported_target_exists (expr_abi_decode_target_root target) t) /\
     (!env es. (!key r. ALOOKUP env key = SOME r ==>
                  ~supported_expr_exists (expr_abi_decode_target_root target) r) ==>
          supported_exprs_exists (expr_abi_decode_target_root target)
            (subst_consts_exprs_mods env es) ==>
          supported_exprs_exists (expr_abi_decode_target_root target) es) /\
     (!env opt. (!key r. ALOOKUP env key = SOME r ==>
                   ~supported_expr_exists (expr_abi_decode_target_root target) r) ==>
          supported_opt_exists (expr_abi_decode_target_root target)
            (subst_consts_opt_mods env opt) ==>
          supported_opt_exists (expr_abi_decode_target_root target) opt) /\
     (!env fs. (!key r. ALOOKUP env key = SOME r ==>
                  ~supported_expr_exists (expr_abi_decode_target_root target) r) ==>
          supported_fields_exists (expr_abi_decode_target_root target)
            (subst_consts_fields_mods env fs) ==>
          supported_fields_exists (expr_abi_decode_target_root target) fs)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> qx_gen_tac `decode_ty` >>
     ho_match_mp_tac constSubstModsTheory.subst_consts_expr_mods_ind >>
     simp[constSubstModsTheory.subst_consts_expr_mods_def,
          supportedExprTraverseTheory.supported_expr_exists_def,
          supportedProgramTheory.expr_abi_decode_target_root_def] >>
     rpt strip_tac >> gvs[]
     >~ [`F`]
     >- (qmatch_asmsub_rename_tac `ALOOKUP decode_env (decode_ns,decode_id)` >>
         Cases_on `ALOOKUP decode_env (decode_ns,decode_id)` >>
         gvs[supportedExprTraverseTheory.supported_expr_exists_def,
             supportedProgramTheory.expr_abi_decode_target_root_def] >> metis_tac[])
     >~ [`TypeBuiltin`]
     >- (Cases_on `bi` >> gvs[supportedProgramTheory.expr_abi_decode_target_root_def])
     >> metis_tac[]);

(* Lift qualified decode-root reflection from expressions to a whole body. *)
val decode_assignment_reflection_tac =
  `(!E' t. E' = E ==>
      supported_assignment_exists p (subst_consts_target_mods E' t) ==>
      supported_assignment_exists p t) /\
   (!E' ts. E' = E ==>
      supported_assignments_exists p (subst_consts_targets_mods E' ts) ==>
      supported_assignments_exists p ts)` by
    (ho_match_mp_tac constSubstModsTheory.subst_consts_target_mods_ind >>
     simp[constSubstModsTheory.subst_consts_target_mods_def,
          supportedStmtTraverseTheory.supported_assignment_exists_def] >>
     metis_tac[]);

val decode_statement_fields_reflection_tac =
  `!es fs. EXISTS (supported_expr_exists p) (es ++ MAP SND fs) <=>
      supported_exprs_exists p es \/ supported_fields_exists p fs` by
    simp[listTheory.EXISTS_APPEND, listTheory.EXISTS_MAP, combinTheory.o_DEF,
         supportedExprTraverseTheory.supported_exprs_exists_every,
         supportedExprTraverseTheory.supported_fields_exists_every] >>
  `!err. EXISTS (supported_expr_exists p)
          (custom_error_exprs (subst_consts_error_mods E err)) ==>
        EXISTS (supported_expr_exists p) (custom_error_exprs err)` by
    (Cases >> simp[constSubstModsTheory.subst_consts_error_mods_def,
                   vyperASTTheory.custom_error_exprs_def] >> metis_tac[]) >>
  `!r. supported_assert_exists p (subst_consts_areason_mods E r) ==>
       supported_assert_exists p r` by
    (Cases >> simp[constSubstModsTheory.subst_consts_areason_mods_def,
                   supportedStmtTraverseTheory.supported_assert_exists_def]) >>
  `!r. supported_raise_exists p (subst_consts_rreason_mods E r) ==>
       supported_raise_exists p r` by
    (Cases >> simp[constSubstModsTheory.subst_consts_rreason_mods_def,
                   supportedStmtTraverseTheory.supported_raise_exists_def]) >>
  `!it. supported_iterator_exists p (subst_consts_iter_mods E it) ==>
        supported_iterator_exists p it` by
    (Cases >> simp[constSubstModsTheory.subst_consts_iter_mods_def,
                   supportedStmtTraverseTheory.supported_iterator_exists_def] >>
     metis_tac[]);

val decode_statement_reflection_tac =
  decode_assignment_reflection_tac >>
  decode_statement_fields_reflection_tac >>
  `(!E' s. E' = E ==>
      supported_stmt_expr_exists p (subst_consts_stmt_mods E' s) ==>
      supported_stmt_expr_exists p s) /\
   (!E' ss. E' = E ==>
      supported_stmts_expr_exists p (subst_consts_stmts_mods E' ss) ==>
      supported_stmts_expr_exists p ss)` by
    (ho_match_mp_tac constSubstModsTheory.subst_consts_stmt_mods_ind >>
     simp[constSubstModsTheory.subst_consts_stmt_mods_def,
          supportedStmtTraverseTheory.supported_stmt_expr_exists_def] >>
     metis_tac[]) >>
  qpat_assum `!E' ss. E' = E ==> supported_stmts_expr_exists p _ ==> _`
    (qspec_then `E` mp_tac) >> simp[];

Theorem checked_linked_const_substitution_abi_decode_target:
  check_contract mode layouts addr mods = SOME art /\
  supported_stmts_expr_exists (expr_abi_decode_target_root target)
    (subst_consts_stmts_mods (consts_env_mods mods) ss) ==>
  supported_stmts_expr_exists (expr_abi_decode_target_root target) ss
Proof
  strip_tac >>
  decode_expression_reflection_tac >>
  qpat_assum `!target. (!env e. _ ==> _) /\ _`
    (qspec_then `target` assume_tac) >>
  qabbrev_tac `p = expr_abi_decode_target_root target` >>
  qabbrev_tac `E = consts_env_mods mods` >>
  `(!e. supported_expr_exists p (subst_consts_expr_mods E e) ==>
          supported_expr_exists p e) /\
    (!t. supported_target_exists p (subst_consts_btarget_mods E t) ==>
          supported_target_exists p t) /\
    (!es. supported_exprs_exists p (subst_consts_exprs_mods E es) ==>
          supported_exprs_exists p es) /\
    (!opt. supported_opt_exists p (subst_consts_opt_mods E opt) ==>
           supported_opt_exists p opt) /\
    (!fs. supported_fields_exists p (subst_consts_fields_mods E fs) ==>
          supported_fields_exists p fs)` by metis_tac[] >>
  qpat_assum `supported_stmts_expr_exists p (subst_consts_stmts_mods E ss)` mp_tac >>
  qpat_x_assum `!key replacement target. ALOOKUP _ _ = SOME _ ==> _` kall_tac >>
  qpat_x_assum `!target. (!env e. _ ==> _) /\ _` kall_tac >>
  disch_tac >> decode_statement_reflection_tac
QED
