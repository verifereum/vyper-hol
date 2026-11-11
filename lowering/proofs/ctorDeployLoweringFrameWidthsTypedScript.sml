Theory ctorDeployLoweringFrameWidthsTyped
Ancestors
  compileEnv vyperTypeSystem vyperValue exprSafeOperand exprSimHypsDefs
  supportedExprTraverse

Theorem deploy_frame_type_bits_aligned:
  !tenv ty. well_formed_type tenv ty ==> type_bits ty MOD 8 = 0
Proof
  rpt gen_tac >> Cases_on `ty` >> simp[type_bits_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[type_bits_def, well_formed_type_def, evaluate_type_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem deploy_frame_subscript_vtype_well_formed:
  !tenv vt ity vt'.
    well_formed_vtype tenv vt /\ subscript_vtype vt ity = SOME vt' ==>
    well_formed_vtype tenv vt'
Proof
  rpt gen_tac >> Cases_on `vt`
  >- (rename1 `Type ty` >> Cases_on `ty` >>
      simp[subscript_vtype_def, well_formed_vtype_def] >>
      simp[well_formed_type_def, evaluate_type_def, AllCaseEqs()] >>
      rpt strip_tac >>
      gvs[well_formed_vtype_def, well_formed_type_def] >>
      Cases_on `evaluate_type tenv t` >> gvs[]) >>
  simp[subscript_vtype_def, well_formed_vtype_def] >> metis_tac[]
QED

Theorem deploy_frame_vtype_annotation_aligned:
  !tenv vt ty.
    well_formed_vtype tenv vt /\ vtype_annotation_ok vt ty ==>
    type_bits ty MOD 8 = 0
Proof
  rpt gen_tac >> Cases_on `vt` >>
  simp[well_formed_vtype_def, vtype_annotation_ok_def, type_bits_def] >>
  metis_tac[deploy_frame_type_bits_aligned]
QED

Theorem deploy_frame_typed_widths_mutual:
  (!env e.
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
       well_formed_type env.type_defs ty) /\
    (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
       well_formed_vtype env.type_defs vt) /\ well_typed_expr env e ==>
    byte_widths_expr e) /\
  (!env e.
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
       well_formed_type env.type_defs ty) /\
    (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
       well_formed_vtype env.type_defs vt) ==>
    !vt. type_place_expr env e = SOME vt ==>
    well_formed_vtype env.type_defs vt /\ byte_widths_expr e) /\
  (!env tgt.
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
       well_formed_type env.type_defs ty) /\
    (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
       well_formed_vtype env.type_defs vt) ==>
    !vt. type_place_target env tgt = SOME vt ==> byte_widths_target tgt) /\
  (!env es.
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
       well_formed_type env.type_defs ty) /\
    (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
       well_formed_vtype env.type_defs vt) /\ well_typed_exprs env es ==>
    byte_widths_exprs es) /\
  (!env oe.
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
       well_formed_type env.type_defs ty) /\
    (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
       well_formed_vtype env.type_defs vt) /\ well_typed_opt env oe ==>
    byte_widths_opt oe) /\
  (!env kes.
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
       well_formed_type env.type_defs ty) /\
    (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
       well_formed_vtype env.type_defs vt) /\ well_typed_named_exprs env kes ==>
    byte_widths_named_exprs kes)
Proof
  ho_match_mp_tac well_typed_expr_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >>
  gvs[byte_widths_expr_def, well_typed_expr_def, AllCaseEqs()] >>
  imp_res_tac deploy_frame_type_bits_aligned >>
  gvs[]
  >~ [`FLOOKUP env.var_types id = SOME ty`, `type_bits ty MOD 8 = 0`]
  >- (irule deploy_frame_type_bits_aligned >> qexists `env.type_defs` >>
      first_x_assum irule >>
      goal_assum (drule_at Any)) >>
  rpt (qpat_x_assum `_ /\ _ ==> _` (drule_all_then strip_assume_tac)) >>
  gvs[type_bits_def]
  >~ [`assignable_type env.type_defs (ArrayT ty (Dynamic n))`]
  >- (irule deploy_frame_type_bits_aligned >> qexists `env.type_defs` >>
      fs[assignable_type_def] >>
      gvs[well_formed_type_def, evaluate_type_def] >>
      Cases_on `evaluate_type env.type_defs ty` >> gvs[]) >>
  all_tac >>~- ([`type_bits (raw_call_return_type flags) MOD 8 = 0`],
    Cases_on `flags.rcf_revert_on_failure` >>
    Cases_on `flags.rcf_max_outsize = 0` >>
    simp[raw_call_return_type_def, type_bits_def]) >>
  metis_tac[deploy_frame_vtype_annotation_aligned,
            deploy_frame_subscript_vtype_well_formed]
QED

Theorem deploy_frame_widths_no_bad_occurrences:
  (!e. byte_widths_expr e ==>
    ~supported_expr_exists (\e. ~byte_widths_expr e) e) /\
  (!tgt. byte_widths_target tgt ==>
    ~supported_target_exists (\e. ~byte_widths_expr e) tgt) /\
  (!es. byte_widths_exprs es ==>
    ~supported_exprs_exists (\e. ~byte_widths_expr e) es) /\
  (!oe. byte_widths_opt oe ==>
    ~supported_opt_exists (\e. ~byte_widths_expr e) oe) /\
  (!kes. byte_widths_named_exprs kes ==>
    ~supported_fields_exists (\e. ~byte_widths_expr e) kes)
Proof
  ho_match_mp_tac byte_widths_expr_ind >>
  simp[byte_widths_expr_def, supported_expr_exists_def] >> metis_tac[]
QED

Theorem deploy_frame_typed_expr_widths:
  !env e.
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
       well_formed_type env.type_defs ty) /\
    (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
       well_formed_vtype env.type_defs vt) /\ well_typed_expr env e ==>
    byte_widths_expr e
Proof
  metis_tac[cj 1 deploy_frame_typed_widths_mutual]
QED

Theorem deploy_frame_typed_place_widths:
  !env e vt.
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
       well_formed_type env.type_defs ty) /\
    (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
       well_formed_vtype env.type_defs vt) /\ type_place_expr env e = SOME vt ==>
    well_formed_vtype env.type_defs vt /\ byte_widths_expr e
Proof
  metis_tac[cj 2 deploy_frame_typed_widths_mutual]
QED

Theorem deploy_frame_typed_target_widths:
  !env tgt vt.
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
       well_formed_type env.type_defs ty) /\
    (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
       well_formed_vtype env.type_defs vt) /\ type_place_target env tgt = SOME vt ==>
    byte_widths_target tgt
Proof
  metis_tac[cj 3 deploy_frame_typed_widths_mutual]
QED

Theorem deploy_frame_typed_exprs_widths:
  !env es.
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
       well_formed_type env.type_defs ty) /\
    (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
       well_formed_vtype env.type_defs vt) /\ well_typed_exprs env es ==>
    byte_widths_exprs es
Proof
  metis_tac[cj 4 deploy_frame_typed_widths_mutual]
QED

Theorem deploy_frame_typed_opt_widths:
  !env oe.
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
       well_formed_type env.type_defs ty) /\
    (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
       well_formed_vtype env.type_defs vt) /\ well_typed_opt env oe ==>
    byte_widths_opt oe
Proof
  metis_tac[cj 5 deploy_frame_typed_widths_mutual]
QED

Theorem deploy_frame_typed_fields_widths:
  !env kes.
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
       well_formed_type env.type_defs ty) /\
    (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
       well_formed_vtype env.type_defs vt) /\ well_typed_named_exprs env kes ==>
    byte_widths_named_exprs kes
Proof
  metis_tac[cj 6 deploy_frame_typed_widths_mutual]
QED
