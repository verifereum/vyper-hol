Theory ctorDeployLoweringFrameStmtWidths
Ancestors
  ctorDeployLoweringFrameWidthsTyped vyperTypeSystem exprSimHypsDefs
  supportedStmtTraverse supportedExprTraverse vyperAST finite_map

Theorem deploy_frame_extend_local_well_formed:
  (!id ty. FLOOKUP env.var_types id = SOME ty ==>
     well_formed_type env.type_defs ty) /\
  well_formed_type env.type_defs typ ==>
  !id assignable key ty.
    FLOOKUP (extend_local env id typ assignable).var_types key = SOME ty ==>
    well_formed_type (extend_local env id typ assignable).type_defs ty
Proof
  simp[extend_local_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem deploy_frame_typed_expr_no_bad_widths:
  (!id ty. FLOOKUP env.var_types id = SOME ty ==>
     well_formed_type env.type_defs ty) /\
  (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
     well_formed_vtype env.type_defs vt) /\ well_typed_expr env e ==>
  ~supported_expr_exists (\e. ~byte_widths_expr e) e
Proof
  metis_tac[deploy_frame_typed_expr_widths,
            cj 1 deploy_frame_widths_no_bad_occurrences]
QED

Theorem deploy_frame_typed_target_no_bad_widths:
  (!id ty. FLOOKUP env.var_types id = SOME ty ==>
     well_formed_type env.type_defs ty) /\
  (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
     well_formed_vtype env.type_defs vt) /\ type_place_target env tgt = SOME vt ==>
  ~supported_target_exists (\e. ~byte_widths_expr e) tgt
Proof
  metis_tac[deploy_frame_typed_target_widths,
            cj 2 deploy_frame_widths_no_bad_occurrences]
QED

Theorem deploy_frame_assignment_list_rel_no_occurrences[local]:
  !ts (tys:type list) p R. LIST_REL R ts tys /\
    (!t ty. MEM t ts /\ MEM ty tys /\ R t ty ==>
      ~supported_assignment_exists p t) ==>
    ~supported_assignments_exists p ts
Proof
  Induct_on `ts` >> Cases_on `tys` >>
  simp[supported_assignment_exists_def] >> metis_tac[]
QED

Theorem deploy_frame_typed_atarget_no_bad_widths:
  !env tgt ty.
  (!id ty. FLOOKUP env.var_types id = SOME ty ==>
     well_formed_type env.type_defs ty) /\
  (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
     well_formed_vtype env.type_defs vt) /\ well_typed_atarget env tgt ty ==>
  ~supported_assignment_exists (\e. ~byte_widths_expr e) tgt
Proof
  ho_match_mp_tac well_typed_atarget_ind >>
  simp[well_typed_atarget_def, well_typed_target_def,
       supported_assignment_exists_def] >>
  rpt conj_tac >> rpt gen_tac >>
  all_tac >~ [`type_place_target env bt = SOME (Type ty)`]
  >- metis_tac[deploy_frame_typed_target_no_bad_widths] >>
  strip_tac >> strip_tac >> irule deploy_frame_assignment_list_rel_no_occurrences >>
  qexistsl [`\tgt ty. well_typed_atarget env tgt ty`, `tys`] >>
  simp[] >> metis_tac[]
QED

Theorem deploy_frame_typed_traversal_adapters:
  !env.
  (!id ty. FLOOKUP env.var_types id = SOME ty ==>
     well_formed_type env.type_defs ty) /\
  (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
     well_formed_vtype env.type_defs vt) ==>
  (!tgt ty. atarget_accepts env tgt ty ==>
     ~supported_assignment_exists (\e. ~byte_widths_expr e) tgt) /\
  (!tgt ty. well_typed_target env tgt ty ==>
     ~supported_target_exists (\e. ~byte_widths_expr e) tgt) /\
  (!typ it. well_typed_iterator env typ it ==>
     ~supported_iterator_exists (\e. ~byte_widths_expr e) it) /\
  (!err. well_typed_custom_error env err ==>
     ~EXISTS (supported_expr_exists (\e. ~byte_widths_expr e)) (custom_error_exprs err)) /\
  (!es. well_typed_exprs env es ==>
     ~supported_exprs_exists (\e. ~byte_widths_expr e) es)
Proof
  gen_tac >> strip_tac >> rpt conj_tac
  >- (Cases >> simp[atarget_accepts_def]
      >- (simp[supported_assignment_exists_def] >>
          rename1 `type_place_target env bt` >>
          Cases_on `type_place_target env bt` >> simp[] >>
          Cases_on `x` >> simp[] >>
          metis_tac[deploy_frame_typed_target_no_bad_widths]) >>
      metis_tac[SRULE [supported_assignment_exists_def]
        deploy_frame_typed_atarget_no_bad_widths])
  >- (simp[well_typed_target_def] >>
      metis_tac[deploy_frame_typed_target_no_bad_widths])
  >- (gen_tac >> Cases >> simp[well_typed_iterator_def, supported_iterator_exists_def] >>
      metis_tac[deploy_frame_typed_expr_no_bad_widths])
  >- (pure_rewrite_tac[well_typed_custom_error_def, GSYM supported_exprs_exists_every] >>
      metis_tac[deploy_frame_typed_exprs_widths,
                cj 3 deploy_frame_widths_no_bad_occurrences]) >>
  metis_tac[deploy_frame_typed_exprs_widths,
            cj 3 deploy_frame_widths_no_bad_occurrences]
QED

Theorem deploy_frame_typed_stmts_widths_mutual:
  (!env ret s.
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
       well_formed_type env.type_defs ty) /\
    (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
       well_formed_vtype env.type_defs vt) ==>
    !env'. type_stmt env ret s = SOME env' ==>
    (!id ty. FLOOKUP env'.var_types id = SOME ty ==>
       well_formed_type env'.type_defs ty) /\
    (!id vt. FLOOKUP env'.toplevel_vtypes id = SOME vt ==>
       well_formed_vtype env'.type_defs vt) /\
    ~supported_stmt_expr_exists (\e. ~byte_widths_expr e) s) /\
  (!env ret ss.
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
       well_formed_type env.type_defs ty) /\
    (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
       well_formed_vtype env.type_defs vt) ==>
    !env'. type_stmts env ret ss = SOME env' ==>
    (!id ty. FLOOKUP env'.var_types id = SOME ty ==>
       well_formed_type env'.type_defs ty) /\
    (!id vt. FLOOKUP env'.toplevel_vtypes id = SOME vt ==>
       well_formed_vtype env'.type_defs vt) /\
    ~supported_stmts_expr_exists (\e. ~byte_widths_expr e) ss)
Proof
  ho_match_mp_tac type_stmt_ind >>
  rpt conj_tac >> rpt (FIRST [gen_tac, disch_tac]) >>
  qpat_x_assum `_ = SOME env'` mp_tac >>
  simp[Once type_stmt_def, AllCaseEqs()] >>
  strip_tac >>
  gvs[supported_stmt_expr_exists_def,
      supported_assert_exists_def, supported_raise_exists_def,
      supported_expr_exists_def] >>
  drule_all_then strip_assume_tac deploy_frame_typed_traversal_adapters >>
  imp_res_tac deploy_frame_typed_expr_no_bad_widths >>
  asm_rewrite_tac[] >>
  all_tac >>~- ([`EVERY _ (custom_error_exprs err)`],
    gvs[listTheory.EVERY_MEM, listTheory.EXISTS_MEM] >> metis_tac[]) >>
  all_tac >>~- ([`~supported_exprs_exists _ es`], metis_tac[]) >>
  all_tac >~ [`FLOOKUP (extend_local env id typ T).var_types _ = SOME _`]
  >- (drule_then assume_tac assignable_type_well_formed >>
      conj_tac >- metis_tac[deploy_frame_extend_local_well_formed] >>
      simp[extend_local_def] >> asm_rewrite_tac[]) >>
  all_tac >>~- ([`~supported_target_exists _ bt`],
    metis_tac[deploy_frame_typed_target_no_bad_widths]) >>
  all_tac >>~- ([`~supported_assignment_exists _ tgt`], metis_tac[]) >>
  all_tac >~ [`~supported_stmts_expr_exists _ ss /\ ~supported_stmts_expr_exists _ ss'`]
  >- (gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  all_tac >~ [`~supported_iterator_exists _ it /\ _`]
  >- (conj_tac >- metis_tac[] >>
      drule_then assume_tac assignable_type_well_formed >>
      `(!key ty. FLOOKUP (extend_local env id typ F).var_types key = SOME ty ==>
          well_formed_type (extend_local env id typ F).type_defs ty)` by
        metis_tac[deploy_frame_extend_local_well_formed] >>
      `(!key vt. FLOOKUP (extend_local env id typ F).toplevel_vtypes key = SOME vt ==>
          well_formed_vtype (extend_local env id typ F).type_defs vt)` by
        (simp[extend_local_def] >> asm_rewrite_tac[]) >>
      gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem deploy_frame_type_stmt_preserves_well_formed:
  (!id ty. FLOOKUP env.var_types id = SOME ty ==>
     well_formed_type env.type_defs ty) /\
  (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
     well_formed_vtype env.type_defs vt) /\
  type_stmt env ret s = SOME env' ==>
  (!id ty. FLOOKUP env'.var_types id = SOME ty ==>
     well_formed_type env'.type_defs ty) /\
  (!id vt. FLOOKUP env'.toplevel_vtypes id = SOME vt ==>
     well_formed_vtype env'.type_defs vt)
Proof
  metis_tac[cj 1 deploy_frame_typed_stmts_widths_mutual]
QED

Theorem deploy_frame_type_stmts_preserves_well_formed:
  (!id ty. FLOOKUP env.var_types id = SOME ty ==>
     well_formed_type env.type_defs ty) /\
  (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
     well_formed_vtype env.type_defs vt) /\
  type_stmts env ret ss = SOME env' ==>
  (!id ty. FLOOKUP env'.var_types id = SOME ty ==>
     well_formed_type env'.type_defs ty) /\
  (!id vt. FLOOKUP env'.toplevel_vtypes id = SOME vt ==>
     well_formed_vtype env'.type_defs vt)
Proof
  metis_tac[cj 2 deploy_frame_typed_stmts_widths_mutual]
QED

Theorem deploy_frame_typed_stmt_no_bad_widths:
  (!id ty. FLOOKUP env.var_types id = SOME ty ==>
     well_formed_type env.type_defs ty) /\
  (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
     well_formed_vtype env.type_defs vt) /\
  type_stmt env ret s = SOME env' ==>
  ~supported_stmt_expr_exists (\e. ~byte_widths_expr e) s
Proof
  metis_tac[cj 1 deploy_frame_typed_stmts_widths_mutual]
QED

Theorem deploy_frame_typed_stmts_no_bad_widths:
  (!id ty. FLOOKUP env.var_types id = SOME ty ==>
     well_formed_type env.type_defs ty) /\
  (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
     well_formed_vtype env.type_defs vt) /\
  type_stmts env ret ss = SOME env' ==>
  ~supported_stmts_expr_exists (\e. ~byte_widths_expr e) ss
Proof
  metis_tac[cj 2 deploy_frame_typed_stmts_widths_mutual]
QED
