Theory bodyLinkedSubstAbiTargetsMods
Ancestors
  alist constSubstMods list pair supportedExprTraverse supportedProgram
  supportedStmtTraverse vyperAST

Theorem linked_subst_expr_no_abi_target[local]:
  (!E e.
    (!key rhs. ALOOKUP E key = SOME rhs ==>
      ~supported_expr_exists (expr_abi_decode_target_root target) rhs) ==>
    ~supported_expr_exists (expr_abi_decode_target_root target) e ==>
    ~supported_expr_exists (expr_abi_decode_target_root target)
      (subst_consts_expr_mods E e)) /\
  (!E t.
    (!key rhs. ALOOKUP E key = SOME rhs ==>
      ~supported_expr_exists (expr_abi_decode_target_root target) rhs) ==>
    ~supported_target_exists (expr_abi_decode_target_root target) t ==>
    ~supported_target_exists (expr_abi_decode_target_root target)
      (subst_consts_btarget_mods E t)) /\
  (!E es.
    (!key rhs. ALOOKUP E key = SOME rhs ==>
      ~supported_expr_exists (expr_abi_decode_target_root target) rhs) ==>
    ~supported_exprs_exists (expr_abi_decode_target_root target) es ==>
    ~supported_exprs_exists (expr_abi_decode_target_root target)
      (subst_consts_exprs_mods E es)) /\
  (!E opt.
    (!key rhs. ALOOKUP E key = SOME rhs ==>
      ~supported_expr_exists (expr_abi_decode_target_root target) rhs) ==>
    ~supported_opt_exists (expr_abi_decode_target_root target) opt ==>
    ~supported_opt_exists (expr_abi_decode_target_root target)
      (subst_consts_opt_mods E opt)) /\
  (!E fs.
    (!key rhs. ALOOKUP E key = SOME rhs ==>
      ~supported_expr_exists (expr_abi_decode_target_root target) rhs) ==>
    ~supported_fields_exists (expr_abi_decode_target_root target) fs ==>
    ~supported_fields_exists (expr_abi_decode_target_root target)
      (subst_consts_fields_mods E fs))
Proof
  ho_match_mp_tac subst_consts_expr_mods_ind >>
  simp[subst_consts_expr_mods_def, supported_expr_exists_def,
       expr_abi_decode_target_root_def] >>
  rpt strip_tac >> gvs[]
  >~ [`TopLevelName`]
  >- (qmatch_asmsub_rename_tac `ALOOKUP env (src,name)` >>
      Cases_on `ALOOKUP env (src,name)` >>
      gvs[supported_expr_exists_def, expr_abi_decode_target_root_def] >>
      metis_tac[])
  >~ [`TypeBuiltin`]
  >- (Cases_on `?unwrap. bi = AbiDecode unwrap`
      >- gvs[expr_abi_decode_target_root_def] >>
      Cases_on `bi` >> gvs[expr_abi_decode_target_root_def]) >>
  metis_tac[]
QED

Theorem linked_subst_assignment_no_abi_target[local]:
  (!E t.
    (!key rhs. ALOOKUP E key = SOME rhs ==>
      ~supported_expr_exists (expr_abi_decode_target_root target) rhs) ==>
    ~supported_assignment_exists (expr_abi_decode_target_root target) t ==>
    ~supported_assignment_exists (expr_abi_decode_target_root target)
      (subst_consts_target_mods E t)) /\
  (!E ts.
    (!key rhs. ALOOKUP E key = SOME rhs ==>
      ~supported_expr_exists (expr_abi_decode_target_root target) rhs) ==>
    ~supported_assignments_exists (expr_abi_decode_target_root target) ts ==>
    ~supported_assignments_exists (expr_abi_decode_target_root target)
      (subst_consts_targets_mods E ts))
Proof
  ho_match_mp_tac subst_consts_target_mods_ind >>
  simp[subst_consts_target_mods_def, supported_assignment_exists_def] >>
  metis_tac[cj 2 linked_subst_expr_no_abi_target]
QED

Theorem custom_error_abi_target_exists[local]:
  EXISTS (supported_expr_exists p) (custom_error_exprs (CustomError ns es fs)) <=>
  supported_exprs_exists p es \/ supported_fields_exists p fs
Proof
  simp[custom_error_exprs_def, EXISTS_APPEND, EXISTS_MAP, combinTheory.o_DEF,
       supported_exprs_exists_every, supported_fields_exists_every]
QED

Theorem linked_subst_error_no_abi_target[local]:
  (!key rhs. ALOOKUP E key = SOME rhs ==>
     ~supported_expr_exists (expr_abi_decode_target_root target) rhs) ==>
  EVERY ($~ o supported_expr_exists (expr_abi_decode_target_root target))
     (custom_error_exprs err) ==>
  EVERY ($~ o supported_expr_exists (expr_abi_decode_target_root target))
     (custom_error_exprs (subst_consts_error_mods E err))
Proof
  Cases_on `err` >>
  pure_rewrite_tac[GSYM NOT_EXISTS, subst_consts_error_mods_def,
                   custom_error_abi_target_exists] >>
  metis_tac[cj 3 linked_subst_expr_no_abi_target, cj 5 linked_subst_expr_no_abi_target]
QED

Theorem linked_subst_stmt_no_abi_target[local]:
  (!E s.
    (!key rhs. ALOOKUP E key = SOME rhs ==>
      ~supported_expr_exists (expr_abi_decode_target_root target) rhs) ==>
    ~supported_stmt_expr_exists (expr_abi_decode_target_root target) s ==>
    ~supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (subst_consts_stmt_mods E s)) /\
  (!E ss.
    (!key rhs. ALOOKUP E key = SOME rhs ==>
      ~supported_expr_exists (expr_abi_decode_target_root target) rhs) ==>
    ~supported_stmts_expr_exists (expr_abi_decode_target_root target) ss ==>
    ~supported_stmts_expr_exists (expr_abi_decode_target_root target)
      (subst_consts_stmts_mods E ss))
Proof
  ho_match_mp_tac subst_consts_stmt_mods_ind >>
  simp[subst_consts_stmt_mods_def, supported_stmt_expr_exists_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> strip_tac
  >~ [`subst_consts_iter_mods`]
  >- (Cases_on `it` >>
      gvs[subst_consts_iter_mods_def, supported_iterator_exists_def] >>
      metis_tac[cj 1 linked_subst_expr_no_abi_target])
  >~ [`subst_consts_areason_mods`]
  >- (Cases_on `r` >>
      gvs[subst_consts_areason_mods_def, supported_assert_exists_def] >>
      metis_tac[cj 1 linked_subst_expr_no_abi_target, linked_subst_error_no_abi_target])
  >~ [`subst_consts_rreason_mods`]
  >- (Cases_on `r` >>
      gvs[subst_consts_rreason_mods_def, supported_raise_exists_def] >>
      metis_tac[cj 1 linked_subst_expr_no_abi_target, linked_subst_error_no_abi_target]) >>
  metis_tac[linked_subst_expr_no_abi_target, cj 1 linked_subst_assignment_no_abi_target]
QED

Theorem linked_subst_stmts_abi_target_back_mods:
  (!key rhs. ALOOKUP E key = SOME rhs ==>
     ~supported_expr_exists (expr_abi_decode_target_root target) rhs) /\
  supported_stmts_expr_exists (expr_abi_decode_target_root target)
    (subst_consts_stmts_mods E ss) ==>
  supported_stmts_expr_exists (expr_abi_decode_target_root target) ss
Proof
  metis_tac[cj 2 linked_subst_stmt_no_abi_target]
QED
