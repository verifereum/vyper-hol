(* Byte-width and traversal facts about typed statements, kept free of the
   body simulation so that internal-call theories can use them. *)
Theory externalBodyWidths
Ancestors
  externalBodySupport memoryLocalRhsProps stmtSimProps stmtSimDefs
  exprSimDefs exprSimHypsDefs exprSimHyps loweringPosts list pair finite_map
  alist arithmetic combin integer option pred_set rich_list bodySim
  loweringHalt stmtLoweringMono exprLoweringProps compileEnv compileVyper
  moduleLowering stmtLowering exprLowering supportedProgram
  supportedProgramProps supportedDecls supportedNames supportedStmts
  supportedExprs supportedTypes supportedExprTraverse supportedStmtTraverse
  allocLimits allocLimitsProps rawReturnHeader immutableSectionRel
  immutableLocationProps placeTypingBuildProps entryDecodePlanProps
  structFieldsProps entryStateRel typedCopyProducer typedCopyMetadata
  vyperTypeSelectedEntrySoundness vyperTypeSystem vyperTypeStmtSoundness
  vyperTypeEvalSoundness vyperTypeExprSoundness vyperTypeInvariants
  vyperTypeContractFunction vyperTypeContractSoundness
  vyperTypeContractContext vyperTypeContract vyperTypeContractStaticMaps
  vyperTypeExternalDefaults vyperTypeInitialState vyperTypeBindArguments
  vyperTypeEvalStoragePreservation vyperTypeStoragePreservation
  vyperStorageLayoutSafety vyperStorageBackend vyperPlaceInvariants
  vyperInterpreter vyperState vyperContext venomState venomExecSemantics
  venomWf

val _ = Parse.hide "body";

Theorem supported_expr_exists_disj:
  (!p e q. supported_expr_exists (\x. p x \/ q x) e =
    (supported_expr_exists p e \/ supported_expr_exists q e)) /\
  (!p t q. supported_target_exists (\x. p x \/ q x) t =
    (supported_target_exists p t \/ supported_target_exists q t)) /\
  (!p es q. supported_exprs_exists (\x. p x \/ q x) es =
    (supported_exprs_exists p es \/ supported_exprs_exists q es)) /\
  (!p opt q. supported_opt_exists (\x. p x \/ q x) opt =
    (supported_opt_exists p opt \/ supported_opt_exists q opt)) /\
  (!p fs q. supported_fields_exists (\x. p x \/ q x) fs =
    (supported_fields_exists p fs \/ supported_fields_exists q fs))
Proof
  ho_match_mp_tac supported_expr_exists_ind >>
  simp[supported_expr_exists_def] >> metis_tac[]
QED

Theorem supported_assignment_exists_disj:
  (!p t q. supported_assignment_exists (\x. p x \/ q x) t =
    (supported_assignment_exists p t \/ supported_assignment_exists q t)) /\
  (!p ts q. supported_assignments_exists (\x. p x \/ q x) ts =
    (supported_assignments_exists p ts \/ supported_assignments_exists q ts))
Proof
  ho_match_mp_tac supported_assignment_exists_ind >>
  simp[supported_assignment_exists_def, supported_expr_exists_disj] >> metis_tac[]
QED

Theorem supported_iterator_exists_disj:
  !p it q. supported_iterator_exists (\x. p x \/ q x) it =
    (supported_iterator_exists p it \/ supported_iterator_exists q it)
Proof
  Cases_on `it` >> simp[supported_iterator_exists_def,
    supported_expr_exists_disj] >> metis_tac[]
QED

Theorem supported_assert_exists_disj:
  !p r q. supported_assert_exists (\x. p x \/ q x) r =
    (supported_assert_exists p r \/ supported_assert_exists q r)
Proof
  Cases_on `r` >> simp[supported_assert_exists_def,
    supported_expr_exists_disj, EXISTS_MEM] >> metis_tac[]
QED

Theorem supported_raise_exists_disj:
  !p r q. supported_raise_exists (\x. p x \/ q x) r =
    (supported_raise_exists p r \/ supported_raise_exists q r)
Proof
  Cases_on `r` >> simp[supported_raise_exists_def,
    supported_expr_exists_disj, EXISTS_MEM] >> metis_tac[]
QED

Theorem supported_stmt_expr_exists_disj:
  (!p s q. supported_stmt_expr_exists (\x. p x \/ q x) s =
    (supported_stmt_expr_exists p s \/ supported_stmt_expr_exists q s)) /\
  (!p ss q. supported_stmts_expr_exists (\x. p x \/ q x) ss =
    (supported_stmts_expr_exists p ss \/ supported_stmts_expr_exists q ss))
Proof
  ho_match_mp_tac supported_stmt_expr_exists_ind >>
  simp[supported_stmt_expr_exists_def, supported_expr_exists_disj,
       supported_assignment_exists_disj, supported_iterator_exists_disj,
       supported_assert_exists_disj, supported_raise_exists_disj] >> metis_tac[]
QED

Theorem typing_maps_well_formed_params:
  env_context_consistent env cx /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> MEM (n,ty) args) /\
  EVERY (\(n,ty). assignable_type env.type_defs ty) args ==>
  (!n ty. FLOOKUP env.var_types n = SOME ty ==>
    well_formed_type env.type_defs ty) /\
  (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
    well_formed_vtype env.type_defs vt) /\
  (!src id ty. FLOOKUP env.bare_global_assignable (src,id) = SOME ty ==>
    well_formed_type env.type_defs ty)
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >> irule assignable_type_well_formed >>
      qpat_x_assum `EVERY _ args` mp_tac >> simp[EVERY_MEM] >>
      disch_then (qspec_then `(n,ty)` mp_tac) >> simp[])
  >> conj_tac
  >- (gvs[env_context_consistent_def] >> metis_tac[])
  >> rpt strip_tac >>
  qpat_x_assum `env_context_consistent _ _` mp_tac >>
  simp[env_context_consistent_def] >> strip_tac >>
  qpat_x_assum `!src id ty. FLOOKUP env.bare_global_assignable _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!src id vt. FLOOKUP env.toplevel_vtypes _ = _ ==> _`
    (drule_then mp_tac) >> simp[well_formed_vtype_def]
QED


Theorem well_formed_type_byte_bits:
  well_formed_type tenv ty ==> type_bits ty MOD 8 = 0
Proof
  Cases_on `ty` >> simp[type_bits_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[type_bits_def, well_formed_type_def, vyperValueTheory.evaluate_type_def] >>
  metis_tac[]
QED

Theorem subscript_vtype_well_formed:
  well_formed_vtype tenv vt /\ subscript_vtype vt idx = SOME vt' ==>
  well_formed_vtype tenv vt'
Proof
  Cases_on `vt`
  >- (rename1 `Type ty` >> Cases_on `ty` >>
      simp[subscript_vtype_def, well_formed_vtype_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >>
      gvs[well_formed_vtype_def, well_formed_type_def,
          vyperValueTheory.evaluate_type_def] >>
      Cases_on `evaluate_type tenv t` >> gvs[]) >>
  simp[subscript_vtype_def, well_formed_vtype_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem vtype_annotation_byte_bits:
  well_formed_vtype tenv vt /\ vtype_annotation_ok vt ty ==>
  type_bits ty MOD 8 = 0
Proof
  Cases_on `vt` >>
  simp[well_formed_vtype_def, vtype_annotation_ok_def, type_bits_def] >>
  metis_tac[well_formed_type_byte_bits]
QED

Theorem assignable_array_element_byte_bits:
  assignable_type tenv (ArrayT ty bd) ==> type_bits ty MOD 8 = 0
Proof
  simp[assignable_type_def] >>
  metis_tac[assignable_type_well_formed, well_formed_type_byte_bits]
QED

Theorem typed_byte_widths_mutual:
  (!env e. well_typed_expr env e ==> ((!n ty. FLOOKUP env.var_types n = SOME ty ==>
      well_formed_type env.type_defs ty) /\
     (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
      well_formed_vtype env.type_defs vt)) ==> byte_widths_expr e) /\
  (!env e. !vt. type_place_expr env e = SOME vt ==> ((!n ty. FLOOKUP env.var_types n = SOME ty ==>
      well_formed_type env.type_defs ty) /\
     (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
      well_formed_vtype env.type_defs vt)) ==>
    byte_widths_expr e /\ well_formed_vtype env.type_defs vt) /\
  (!env tgt. !vt. type_place_target env tgt = SOME vt ==> ((!n ty. FLOOKUP env.var_types n = SOME ty ==>
      well_formed_type env.type_defs ty) /\
     (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
      well_formed_vtype env.type_defs vt)) ==> byte_widths_target tgt) /\
  (!env es. well_typed_exprs env es ==> ((!n ty. FLOOKUP env.var_types n = SOME ty ==>
      well_formed_type env.type_defs ty) /\
     (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
      well_formed_vtype env.type_defs vt)) ==> byte_widths_exprs es) /\
  (!env opt. well_typed_opt env opt ==> ((!n ty. FLOOKUP env.var_types n = SOME ty ==>
      well_formed_type env.type_defs ty) /\
     (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
      well_formed_vtype env.type_defs vt)) ==> byte_widths_opt opt) /\
  (!env kes. well_typed_named_exprs env kes ==> ((!n ty. FLOOKUP env.var_types n = SOME ty ==>
      well_formed_type env.type_defs ty) /\
     (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
      well_formed_vtype env.type_defs vt)) ==> byte_widths_named_exprs kes)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  ho_match_mp_tac well_typed_expr_ind >> conj_tac
  >- (simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[assignable_array_element_byte_bits]) >>
  suspend "calls_places"
QED

Resume typed_byte_widths_mutual[calls_places]:
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits])
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits])
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def, type_bits_def] >>
      metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def, raw_call_return_type_def,
           type_bits_def] >>
      Cases_on `flags.rcf_revert_on_failure` >>
      Cases_on `flags.rcf_max_outsize = 0` >>
      simp[type_bits_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def, raw_call_return_type_def,
           type_bits_def] >>
      Cases_on `flags.rcf_revert_on_failure` >>
      Cases_on `flags.rcf_max_outsize = 0` >>
      simp[type_bits_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def, type_bits_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def, type_bits_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def, type_bits_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def, type_bits_def] >> metis_tac[])
  >- (simp[well_typed_expr_def, byte_widths_expr_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >>
      metis_tac[vtype_annotation_byte_bits])
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >>
      metis_tac[subscript_vtype_well_formed, vtype_annotation_byte_bits]) >>
  (* Impossible place expressions and empty containers simplify immediately. *)
  simp[well_typed_expr_def, byte_widths_expr_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Finalise typed_byte_widths_mutual

Theorem well_typed_expr_byte_widths:
  well_typed_expr env e /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> well_formed_type env.type_defs ty) /\
  (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
    well_formed_vtype env.type_defs vt) ==> byte_widths_expr e
Proof
  mp_tac typed_byte_widths_mutual >> simp[LET_THM] >> metis_tac[]
QED

Theorem type_place_target_byte_widths:
  type_place_target env tgt = SOME vt /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> well_formed_type env.type_defs ty) /\
  (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
    well_formed_vtype env.type_defs vt) ==> byte_widths_target tgt
Proof
  mp_tac typed_byte_widths_mutual >> simp[LET_THM] >> metis_tac[]
QED

Theorem byte_widths_exclude_bad_widths:
  (!e. byte_widths_expr e ==>
    ~supported_expr_exists (\e. ~byte_widths_expr e) e) /\
  (!tgt. byte_widths_target tgt ==>
    ~supported_target_exists (\e. ~byte_widths_expr e) tgt) /\
  (!es. byte_widths_exprs es ==>
    ~supported_exprs_exists (\e. ~byte_widths_expr e) es) /\
  (!opt. byte_widths_opt opt ==>
    ~supported_opt_exists (\e. ~byte_widths_expr e) opt) /\
  (!kes. byte_widths_named_exprs kes ==>
    ~supported_fields_exists (\e. ~byte_widths_expr e) kes)
Proof
  ho_match_mp_tac byte_widths_expr_ind >>
  simp[byte_widths_expr_def, supported_expr_exists_def]
QED

Theorem supported_assignments_exists_mem[local]:
  !ts. supported_assignments_exists p ts <=>
    ?t. MEM t ts /\ supported_assignment_exists p t
Proof
  Induct >> simp[supported_assignment_exists_def] >> metis_tac[]
QED

Theorem well_typed_atarget_excludes_bad_widths:
  !env tgt ty.
    well_typed_atarget env tgt ty /\
    (!n ty. FLOOKUP env.var_types n = SOME ty ==> well_formed_type env.type_defs ty) /\
    (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
      well_formed_vtype env.type_defs vt) ==>
    ~supported_assignment_exists (\e. ~byte_widths_expr e) tgt
Proof
  recInduct well_typed_atarget_ind >> conj_tac
  >- (simp[well_typed_atarget_def, well_typed_target_def,
           supported_assignment_exists_def] >> rpt strip_tac >>
      metis_tac[type_place_target_byte_widths, byte_widths_exclude_bad_widths]) >>
  simp[well_typed_atarget_def, supported_assignment_exists_def,
       supported_assignments_exists_mem] >> rpt strip_tac >>
  gvs[LIST_REL_EL_EQN, MEM_EL] >> metis_tac[]
QED

Theorem typed_expr_excludes_bad_widths:
  well_typed_expr env e /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> well_formed_type env.type_defs ty) /\
  (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
    well_formed_vtype env.type_defs vt) ==>
  ~supported_expr_exists (\e. ~byte_widths_expr e) e
Proof
  metis_tac[well_typed_expr_byte_widths, cj 1 byte_widths_exclude_bad_widths]
QED

Theorem typed_exprs_exclude_bad_widths:
  well_typed_exprs env es /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> well_formed_type env.type_defs ty) /\
  (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
    well_formed_vtype env.type_defs vt) ==>
  ~supported_exprs_exists (\e. ~byte_widths_expr e) es
Proof
  qid_spec_tac `es` >> Induct >>
  simp[well_typed_expr_def, supported_expr_exists_def] >>
  metis_tac[typed_expr_excludes_bad_widths]
QED

Theorem type_stmts_byte_widths_mutual:
    (!env ret s env'. ((!n ty. FLOOKUP env.var_types n = SOME ty ==>
      well_formed_type env.type_defs ty) /\
     (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
      well_formed_vtype env.type_defs vt)) /\ type_stmt env ret s = SOME env' ==>
      ((!n ty. FLOOKUP env'.var_types n = SOME ty ==>
      well_formed_type env'.type_defs ty) /\
     (!src id vt. FLOOKUP env'.toplevel_vtypes (src,id) = SOME vt ==>
      well_formed_vtype env'.type_defs vt)) /\ ~supported_stmt_expr_exists (\e. ~byte_widths_expr e) s) /\
    (!env ret ss env'. ((!n ty. FLOOKUP env.var_types n = SOME ty ==>
      well_formed_type env.type_defs ty) /\
     (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
      well_formed_vtype env.type_defs vt)) /\ type_stmts env ret ss = SOME env' ==>
      ((!n ty. FLOOKUP env'.var_types n = SOME ty ==>
      well_formed_type env'.type_defs ty) /\
     (!src id vt. FLOOKUP env'.toplevel_vtypes (src,id) = SOME vt ==>
      well_formed_vtype env'.type_defs vt)) /\ ~supported_stmts_expr_exists (\e. ~byte_widths_expr e) ss)
Proof
  simp_tac bool_ss [LET_THM] >>
  ho_match_mp_tac type_stmt_ind >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def] >> rpt strip_tac >>
      gvs[AllCaseEqs()] >> metis_tac[typed_expr_excludes_bad_widths]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def, supported_expr_exists_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def, supported_expr_exists_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[typed_expr_excludes_bad_widths]) >>
  suspend "remaining_statements"
QED

Resume type_stmts_byte_widths_mutual[remaining_statements]:
  conj_tac
  >- simp[type_stmt_def, supported_stmt_expr_exists_def, supported_raise_exists_def] >> conj_tac
  >- simp[type_stmt_def, supported_stmt_expr_exists_def, supported_raise_exists_def] >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def, supported_raise_exists_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[typed_expr_excludes_bad_widths]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def, supported_raise_exists_def,
           well_typed_custom_error_def, GSYM supported_exprs_exists_every] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[typed_exprs_exclude_bad_widths]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def, supported_assert_exists_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[typed_expr_excludes_bad_widths]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def, supported_assert_exists_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[typed_expr_excludes_bad_widths]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def, supported_assert_exists_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[typed_expr_excludes_bad_widths]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def, supported_assert_exists_def,
           well_typed_custom_error_def, GSYM supported_exprs_exists_every] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >>
      metis_tac[typed_expr_excludes_bad_widths, typed_exprs_exclude_bad_widths]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[typed_exprs_exclude_bad_widths]) >>
  suspend "assignments_and_control"
QED

Resume type_stmts_byte_widths_mutual[assignments_and_control]:
  conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >>
      `well_formed_type env.type_defs typ` by metis_tac[assignable_type_well_formed] >>
      simp[extend_local_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
      gvs[extend_local_def, FLOOKUP_UPDATE, AllCaseEqs()] >>
      metis_tac[typed_expr_excludes_bad_widths]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >>
      metis_tac[typed_expr_excludes_bad_widths, type_place_target_byte_widths,
                cj 2 byte_widths_exclude_bad_widths]) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      gvs[type_stmt_def, supported_stmt_expr_exists_def, AllCaseEqs()] >>
      `~supported_expr_exists (\e. ~byte_widths_expr e) e` by
        metis_tac[typed_expr_excludes_bad_widths] >> simp[] >>
      Cases_on `tgt`
      >- (rename1 `atarget_accepts env (BaseTarget bt) _` >>
          gvs[atarget_accepts_def, supported_assignment_exists_def] >>
          Cases_on `type_place_target env bt` >> gvs[] >>
          rename1 `SOME vt` >> Cases_on `vt` >> gvs[] >>
          metis_tac[type_place_target_byte_widths, cj 2 byte_widths_exclude_bad_widths]) >>
      gvs[atarget_accepts_def] >>
      metis_tac[well_typed_atarget_excludes_bad_widths]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def, well_typed_target_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >>
      metis_tac[typed_expr_excludes_bad_widths, type_place_target_byte_widths,
                cj 2 byte_widths_exclude_bad_widths]) >>
  suspend "control_and_lists"
QED

Resume type_stmts_byte_widths_mutual[control_and_lists]:
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
      pure_once_rewrite_tac[type_stmt_def] >>
      simp_tac std_ss [AllCaseEqs()] >> strip_tac >> gvs[] >>
      simp[supported_stmt_expr_exists_def] >>
      metis_tac[typed_expr_excludes_bad_widths, optionTheory.IS_SOME_EXISTS]) >> conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[type_stmt_def, supported_stmt_expr_exists_def, AllCaseEqs()] >>
      `well_formed_type env.type_defs typ` by metis_tac[assignable_type_well_formed] >>
      `!n ty. FLOOKUP (extend_local env id typ F).var_types n = SOME ty ==>
        well_formed_type (extend_local env id typ F).type_defs ty` by
        (simp[extend_local_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
         gvs[AllCaseEqs()] >> metis_tac[]) >>
      `!src nm vt. FLOOKUP (extend_local env id typ F).toplevel_vtypes (src,nm) = SOME vt ==>
        well_formed_vtype (extend_local env id typ F).type_defs vt` by
        (simp[extend_local_def] >> metis_tac[]) >>
      `~supported_stmts_expr_exists (\e. ~byte_widths_expr e) ss` by
        metis_tac[optionTheory.IS_SOME_EXISTS] >>
      simp[] >> Cases_on `it` >>
      gvs[well_typed_iterator_def, supported_iterator_exists_def] >>
      metis_tac[typed_expr_excludes_bad_widths]) >> conj_tac
  >- simp[type_stmt_def, supported_stmt_expr_exists_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[type_stmt_def, supported_stmt_expr_exists_def, AllCaseEqs()] >>
  qpat_x_assum `_ ==> _ /\ ~supported_stmt_expr_exists _ s` mp_tac >>
  (impl_tac >- (rpt strip_tac >> metis_tac[])) >> strip_tac >>
  qpat_x_assum `_ ==> _ /\ ~supported_stmts_expr_exists _ ss` mp_tac >>
  (impl_tac >- (rpt strip_tac >> metis_tac[])) >> strip_tac >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

Finalise type_stmts_byte_widths_mutual

Theorem type_stmts_preserves_well_formed_maps:
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> well_formed_type env.type_defs ty) /\
  (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
    well_formed_vtype env.type_defs vt) /\
  type_stmts env ret ss = SOME env' ==>
  (!n ty. FLOOKUP env'.var_types n = SOME ty ==> well_formed_type env'.type_defs ty) /\
  (!src id vt. FLOOKUP env'.toplevel_vtypes (src,id) = SOME vt ==>
    well_formed_vtype env'.type_defs vt)
Proof
  strip_tac >>
  drule_all (cj 2 (SRULE [LET_THM] type_stmts_byte_widths_mutual)) >>
  strip_tac >> rpt strip_tac >> metis_tac[]
QED

Theorem type_stmts_excludes_bad_widths:
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> well_formed_type env.type_defs ty) /\
  (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
    well_formed_vtype env.type_defs vt) /\
  type_stmts env ret ss = SOME env' ==>
  ~supported_stmts_expr_exists (\e. ~byte_widths_expr e) ss
Proof
  strip_tac >>
  drule_all (cj 2 (SRULE [LET_THM] type_stmts_byte_widths_mutual)) >> simp[]
QED

Theorem type_stmt_excludes_bad_widths:
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> well_formed_type env.type_defs ty) /\
  (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
    well_formed_vtype env.type_defs vt) /\
  type_stmt env ret s = SOME env' ==>
  ~supported_stmt_expr_exists (\e. ~byte_widths_expr e) s
Proof
  strip_tac >>
  drule_all (cj 1 (SRULE [LET_THM] type_stmts_byte_widths_mutual)) >> simp[]
QED

Theorem typed_parameter_body_excludes_bad_widths:
  env_context_consistent env cx /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> MEM (n,ty) args) /\
  EVERY (\(n,ty). assignable_type env.type_defs ty) args /\
  type_stmts env ret ss = SOME env' ==>
  ~supported_stmts_expr_exists (\e. ~byte_widths_expr e) ss
Proof
  strip_tac >> drule_all typing_maps_well_formed_params >> strip_tac >>
  drule_all type_stmts_excludes_bad_widths >> simp[]
QED

Theorem stmt_exprs_ok_from_traversal_bounds:
  ~supported_stmts_expr_exists (\e. ~byte_widths_expr e) ss /\
  ~supported_stmts_expr_exists
     (\e. ~is_extcode e /\ ~alloc_limits_expr cenv e) ss /\
  alloc_limits_stmts cenv ss /\
  (stmts_valued_return ss /\ cenv.ce_is_external /\ ~cenv.ce_raw_return ==>
   return_buffer_ok cenv) ==>
  EVERY (stmt_exprs_ok cenv) ss
Proof
  strip_tac >>
  `~supported_stmts_expr_exists
      (\e. ~is_extcode e /\ ~byte_widths_expr e) ss` by
    (qpat_x_assum `~supported_stmts_expr_exists (\e. ~byte_widths_expr e) _`
       mp_tac >>
     `(\e. ~byte_widths_expr e) =
      (\e. (~is_extcode e /\ ~byte_widths_expr e) \/
           (is_extcode e /\ ~byte_widths_expr e))` by
       (simp[FUN_EQ_THM] >> metis_tac[]) >>
     pop_assum SUBST1_TAC >> simp[supported_stmt_expr_exists_disj]) >>
  `~supported_stmts_expr_exists
      (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e))
      ss` by
    (`(\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) =
      (\e. (~is_extcode e /\ ~byte_widths_expr e) \/
           (~is_extcode e /\ ~alloc_limits_expr cenv e))` by
       (simp[FUN_EQ_THM] >> metis_tac[]) >>
     pop_assum SUBST1_TAC >> simp[supported_stmt_expr_exists_disj]) >>
  qpat_x_assum `~supported_stmts_expr_exists (\e. ~is_extcode e /\ ~(_ /\ _)) _`
    mp_tac >>
  qpat_x_assum `alloc_limits_stmts _ _` mp_tac >>
  qpat_x_assum `_ ==> return_buffer_ok _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[EVERY_MEM, stmt_exprs_ok_def, supported_stmts_expr_exists_list,
       EXISTS_MEM] >>
  Induct_on `ss` >>
  simp[allocLimitsTheory.alloc_limits_stmt_def, stmt_valued_return_def] >>
  metis_tac[]
QED
