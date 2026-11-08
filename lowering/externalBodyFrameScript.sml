(* A piece of S1 (loweringRuntimeCorrect's lower_vyper_runtime_unit_correct). *)
Theory externalBodyFrame
Ancestors
  externalBodySupport
  stmtSimProps stmtSimDefs exprSimDefs exprSimHypsDefs exprSimHyps
  loweringPosts
  list pair finite_map alist arithmetic combin integer option pred_set rich_list
  fragExec bodySim bodySimMain bodySimEntry bodySimStmtCases
  loweringHalt stmtLoweringMono exprLoweringProps
  compileEnv compileVyper moduleLowering stmtLowering exprLowering
  e2eDefs supportedProgram supportedProgramProps supportedDecls supportedNames
  supportedStmts supportedExprs supportedTypes
  supportedExprTraverse supportedStmtTraverse allocLimits allocLimitsProps
  vyperLoweringCorrect rawReturnHeader immutableSectionRel immutableLocationProps
  placeTypingBuildProps entryDecodePlanProps structFieldsProps entryStateRel
  typedCopyProducer typedCopyMetadata
  vyperTypeSelectedEntrySoundness vyperTypeSystem vyperTypeStmtSoundness
  vyperTypeEvalSoundness vyperTypeExprSoundness vyperTypeInvariants
  vyperTypeContractFunction vyperTypeContractSoundness vyperTypeContractContext
  vyperTypeContract vyperTypeContractStaticMaps vyperTypeExternalDefaults
  vyperTypeInitialState vyperTypeBindArguments
  vyperTypeEvalStoragePreservation vyperTypeStoragePreservation
  vyperStorageLayoutSafety vyperStorageBackend vyperPlaceInvariants
  vyperInterpreter vyperState vyperContext
  venomState venomExecSemantics venomWf

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

Theorem collect_locals_supported_bindings_mem:
  !ss n. MEM n (MAP FST (collect_locals ss)) <=>
    MEM n (MAP FST (supported_stmts_bindings T ss)) \/
    MEM n (MAP FST (supported_stmts_bindings F ss))
Proof
  recInduct collect_locals_ind >>
  simp[collect_locals_def, supported_stmt_bindings_def] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem supported_function_arg_not_collect_locals:
  supported_function_body tops vis args ss /\ MEM (id,ty) args ==>
  ~MEM id (MAP FST (collect_locals ss))
Proof
  strip_tac >> drule supported_function_body_binding_contract >>
  simp[supported_function_bindings_def, ALL_DISTINCT_APPEND,
       collect_locals_supported_bindings_mem] >>
  strip_tac >>
  `MEM id (MAP FST args)` by (simp[MEM_MAP] >> qexists `(id,ty)` >> simp[]) >>
  metis_tac[]
QED

Theorem supported_function_names_mem:
  !tops vis mut nr rr name args defaults ret body.
    MEM (FunctionDecl vis mut nr rr name args defaults ret body) tops ==>
    MEM name (supported_function_names tops)
Proof
  Induct >> simp[supported_function_names_def] >>
  rpt gen_tac >> Cases_on `h` >> simp[supported_function_names_def] >>
  metis_tac[]
QED

Theorem distinct_external_classification:
  !tops mut nr rr name args defaults ret body exts ints fb ctor.
    ALL_DISTINCT (supported_function_names tops) /\
    MEM (FunctionDecl External mut nr rr name args defaults ret body) tops /\
    classify_functions tops = (exts,ints,fb,ctor) ==>
    (if name = "__default__" then
       fb = SOME (mut,nr,rr,name,args,defaults,ret,body)
     else MEM (mut,nr,rr,name,args,defaults,ret,body) exts)
Proof
  Induct >- simp[] >> rpt gen_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  Cases_on `h` >>
  simp[supported_function_names_def, classify_functions_def,
       classify_function_def] >>
  rpt strip_tac >> gvs[GSYM classify_functions_def] >>
  gvs[classify_function_def, AllCaseEqs()] >>
  drule supported_function_names_mem >> strip_tac >>
  Cases_on `name = "__default__"` >> gvs[] >> metis_tac[]
QED

Theorem supported_external_classification:
  supported_program tops /\
  MEM (FunctionDecl External mut nr rr name args defaults ret fbody) tops /\
  classify_functions tops = (exts,ints,fb,ctor) ==>
  (if name = "__default__" then
     fb = SOME (mut,nr,rr,name,args,defaults,ret,fbody)
   else MEM (mut,nr,rr,name,args,defaults,ret,fbody) exts)
Proof
  strip_tac >> irule distinct_external_classification >>
  drule supported_program_names >>
  simp[supported_declaration_names_def] >> metis_tac[]
QED

Theorem supported_external_allocs_ok:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  MEM (FunctionDecl External mut nr rr name args defaults ret fbody) tops ==>
  fn_allocs_ok tops (mut,nr,rr,name,args,defaults,ret,fbody)
Proof
  strip_tac >> Cases_on `classify_functions tops` >> PairCases_on `r` >>
  drule_all supported_external_classification >> strip_tac >>
  irule lower_vyper_runtime_unit_allocs_ok >>
  conj_tac >- metis_tac[] >>
  qexistsl [`r2`, `q`, `r1`, `r0`] >>
  simp[] >> Cases_on `name = "__default__"` >> gvs[]
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

Theorem build_compile_env_return_buffer_ok:
  !tops vis mut name args ret body use_trans.
    return_buffer_ok
      (build_compile_env tops vis mut name args ret body use_trans)
Proof
  rpt gen_tac >> simp[build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[return_buffer_ok_def]
QED

Theorem update_cenv_ret_abi_word_return_buffer_ok:
  !cenv ret. is_word_type ret ==>
    return_buffer_ok (update_cenv_ret_abi cenv ret)
Proof
  Cases_on `ret` >> simp[is_word_type_def] >-
    (Cases_on `b` >>
     simp[is_word_type_def, update_cenv_ret_abi_def, return_buffer_ok_def,
          type_to_abi_enc_info_def, abi_size_bound_def, is_abi_dynamic_def,
          abi_static_size_def, type_memory_bytes_def] >>
     rename1 `BytesT kind` >> Cases_on `kind` >>
     simp[is_word_type_def, update_cenv_ret_abi_def, return_buffer_ok_def,
          type_to_abi_enc_info_def, abi_size_bound_def, is_abi_dynamic_def,
          abi_static_size_def, type_memory_bytes_def]) >>
  simp[update_cenv_ret_abi_def, return_buffer_ok_def,
       type_to_abi_enc_info_def, abi_size_bound_def, is_abi_dynamic_def,
       abi_static_size_def, type_memory_bytes_def]
QED

Theorem package_external_fn_return_buffer_ok:
  !target tops use_trans nkeys mut nr rr name args dflts ret body'
   lbl cenv pos_args min_cds is_payable nr' nkey ut iv body rt.
  set_external_package_target target
    (package_external_fn tops use_trans nkeys
      (mut,nr,rr,name,args,dflts,ret,body')) =
      (lbl,cenv,pos_args,min_cds,is_payable,nr',nkey,ut,iv,body,rt) /\
  external_return_buffer_ok
      (lbl,cenv,pos_args,min_cds,is_payable,nr',nkey,ut,iv,body,rt) ==>
  (stmts_valued_return body /\ ~cenv.ce_raw_return ==>
    return_buffer_ok cenv)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ret = NoneT`
  >- (qpat_x_assum `external_return_buffer_ok _` kall_tac >>
      `return_buffer_ok
         (build_compile_env tops External mut name args ret body' use_trans)`
        by irule build_compile_env_return_buffer_ok >>
      gvs[package_external_fn_def, set_external_package_target_def,
          update_cenv_nonreentrant_def, return_buffer_ok_def]) >>
  Cases_on `is_word_type ret`
  >- (qpat_x_assum `external_return_buffer_ok _` kall_tac >>
      drule update_cenv_ret_abi_word_return_buffer_ok >>
      disch_then (qspec_then
        `build_compile_env tops External mut name args ret body' use_trans
           with ce_raw_return := rr` mp_tac) >>
      gvs[package_external_fn_def, set_external_package_target_def,
          update_cenv_nonreentrant_def, return_buffer_ok_def]) >>
  gvs[package_external_fn_def, set_external_package_target_def,
      external_return_buffer_ok_def]
QED

Theorem supported_lookup_raw:
  !ts ambient name mut nr args defaults ret body.
  EVERY (supported_declaration_header ambient) ts /\
  lookup_function (NONE : num option) name External ts =
    SOME (mut,nr,args,defaults,ret,body) ==>
  ?rr. MEM (FunctionDecl External mut nr rr name args defaults ret body) ts /\
       lookup_raw_return (NONE : num option) name External ts = SOME rr
Proof
  Induct_on `ts` >- simp[lookup_function_def] >>
  rpt gen_tac >> Cases_on `h`
  >- (simp[listTheory.EVERY_DEF, lookup_function_def, lookup_raw_return_def,
           listTheory.MEM] >>
      Cases_on `s = name /\ f = External` >> gvs[] >> metis_tac[])
  >- (Cases_on `v` >>
      simp[listTheory.EVERY_DEF, lookup_function_def, lookup_raw_return_def,
           listTheory.MEM, supported_public_variables_rejected] >>
      metis_tac[])
  >- (simp[listTheory.EVERY_DEF, supported_hashmap_header_contract] >>
      strip_tac >> gvs[lookup_function_def, lookup_raw_return_def,
                      listTheory.MEM] >> metis_tac[])
  >> simp[listTheory.EVERY_DEF, lookup_function_def, lookup_raw_return_def,
          listTheory.MEM] >> metis_tac[]
QED

Theorem make_struct_fields_map_fields:
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  (!name args. MEM (StructDecl name args) tops ==>
     ALL_DISTINCT (MAP FST args)) /\
  FLOOKUP (make_struct_fields_map tops) name = SOME fields ==>
  ALL_DISTINCT (MAP FST fields) /\
  EVERY (\(fname,fty,sz). !tv.
    evaluate_type (type_env tops) fty = SOME tv ==>
    sz = type_memory_size tv) fields
Proof
  strip_tac >>
  `struct_args_unique tops` by
    metis_tac[distinct_type_keys_struct_args_unique] >>
  fs[make_struct_fields_map_def] >>
  drule built_struct_fields_origin >> simp[] >> strip_tac >>
  `fields = build_struct_fields_one (type_env tops) args` by
    (drule_all build_struct_fields_map_lookup >>
     disch_then (qspecl_then [`type_env tops`, `FEMPTY`] mp_tac) >> gvs[]) >>
  conj_tac >- metis_tac[built_struct_fields_names] >>
  simp[EVERY_MEM, build_struct_fields_one_def, MEM_MAP, FORALL_PROD,
       PULL_EXISTS, field_mem_bytes_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem checked_single_module_bare_global_no_hashmap:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  FLOOKUP art.cta_bare_globals nsid = SOME ty ==>
  build_hashmap_info tops nsid = NONE
Proof
  Cases_on `nsid` >> rw[check_contract_def] >>
  gvs[live_artifact_fields] >>
  drule_all build_contract_type_artifact_bare_globals_sound >>
  strip_tac >> gvs[] >>
  irule build_hashmap_info_variable >>
  gvs[contract_namespaces_ok_def, contract_keys_def] >>
  metis_tac[]
QED

Theorem package_external_target_param_memory:
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,fname,fargs,dflts,ret,fbody)) =
    (lbl,cenv,pos_args,rest) /\ ALL_DISTINCT (MAP FST fargs) ==>
  EVERY (\a. ?off sz. FLOOKUP cenv.ce_vars (FST a) =
                       SOME (MemLoc off sz)) fargs /\
  MAP FST pos_args = MAP FST fargs
Proof
  strip_tac >>
  Cases_on `package_external_fn tops use_trans nkey_map
    (mut,nr,rr,fname,fargs,dflts,ret,fbody)` >>
  PairCases_on `r` >> gvs[set_external_package_target_def] >>
  drule_all package_external_fn_vars >> strip_tac >>
  conj_tac
  >- (gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
      metis_tac[]) >>
  qpat_x_assum `package_external_fn _ _ _ _ = _` mp_tac >>
  simp[package_external_fn_def] >> strip_tac >>
  gvs[build_positional_args_names]
QED

Theorem external_entry_target_param_pointer:
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,fname,fargs,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,rest) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,st') /\
  ALL_DISTINCT (MAP FST fargs) /\ MEM (id,ty) fargs ==>
  ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)
Proof
  strip_tac >> drule_all package_external_target_param_memory >>
  strip_tac >> gvs[EVERY_MEM] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  `MEM id (MAP FST pos_args)` by
    (qpat_x_assum `MAP FST pos_args = _` SUBST1_TAC >>
     simp[MEM_MAP] >> qexists `(id,ty)` >> simp[]) >>
  `var_location_memory_size (MemLoc off sz) = SOME sz` by
    simp[var_location_memory_size_def] >>
  drule_all compile_register_positional_args_ptrs >> metis_tac[]
QED

Theorem external_entry_target_param_type:
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,fname,fargs,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,rest) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,st') /\
  supported_function_body tops External fargs fbody /\ MEM (id,ty) fargs ==>
  cenv.ce_var_type id = SOME ty
Proof
  strip_tac >>
  `~MEM id (MAP FST (collect_locals fbody))` by
    metis_tac[supported_function_arg_not_collect_locals] >>
  `ALL_DISTINCT (MAP FST fargs)` by
    (drule supported_function_body_binding_contract >>
     simp[supported_function_bindings_def, ALL_DISTINCT_APPEND]) >>
  `ALOOKUP (REVERSE fargs) id = SOME ty` by
    (irule ALOOKUP_ALL_DISTINCT_MEM >>
     simp[MAP_REVERSE, ALL_DISTINCT_REVERSE]) >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  `cenv.ce_var_type = cenv0.ce_var_type` by
    (qpat_x_assum `cenv = _` SUBST1_TAC >> simp[]) >>
  qpat_x_assum `cenv.ce_var_type = _` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` kall_tac >>
  qpat_x_assum `cenv = _` kall_tac >>
  `ALOOKUP (REVERSE (collect_locals fbody)) id = NONE` by
    simp[ALOOKUP_NONE, MAP_REVERSE] >>
  qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
  simp[package_external_fn_def, set_external_package_target_def,
       update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
  Cases_on `ret = NoneT` >> simp[] >> strip_tac >>
  gvs[build_compile_env_def] >> rpt (pairarg_tac >> gvs[]) >>
  simp[REVERSE_APPEND, ALOOKUP_APPEND]
QED

Theorem external_package_registered_hashmap_info:
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,fname,args,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr',nkey,ut',iv,fbody',rt) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) ==>
  cenv.ce_hashmap_info = build_hashmap_info tops
Proof
  strip_tac >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `cenv = _` SUBST1_TAC >>
  gvs[package_external_fn_def, set_external_package_target_def] >>
  Cases_on `ret = NoneT` >>
  gvs[update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
      build_compile_env_ce_hashmap_info]
QED

Theorem external_entry_target_declared:
  !tops use_trans nkey_map mut nr rr fname fargs dflts ret fbody
   target lbl cenv0 pos_args rest st cenv st' n l.
    set_external_package_target target
      (package_external_fn tops use_trans nkey_map
        (mut,nr,rr,fname,fargs,dflts,ret,fbody)) =
      (lbl,cenv0,pos_args,rest) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv,st') /\
    FLOOKUP cenv.ce_vars n = SOME l ==>
    MEM n (MAP FST fargs)
Proof
  rpt gen_tac >> strip_tac >>
  `cenv0.ce_vars = (build_compile_env tops External mut fname fargs ret fbody
                    use_trans).ce_vars` by
    (gvs[package_external_fn_def, set_external_package_target_def,
         update_cenv_nonreentrant_def] >> rw[update_cenv_ret_abi_def]) >>
  drule_all compile_register_positional_args_bound >> strip_tac >>
  gvs[] >> drule build_compile_env_bound >> simp[]
QED

Theorem external_entry_target_locals_declared:
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,fname,fargs,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,rest) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,st') /\
  (!id ty. MEM (id,ty) fargs ==> FLOOKUP env.var_types id = SOME ty) ==>
  ce_locals_declared cenv env
Proof
  rw[ce_locals_declared_def] >>
  drule_all external_entry_target_declared >>
  simp[MEM_MAP, PULL_EXISTS] >> strip_tac >>
  PairCases_on `y` >> gvs[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[FLOOKUP_DEF] >> metis_tac[]
QED

(* The packaged external env reads the module's variables and the internal
   functions' return types as build_compile_env does, as fn_allocs_ok_body
   needs. *)
Theorem external_package_alloc_env_agree:
  set_external_package_target target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,F,rr,fname,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) ==>
  alloc_env_agree (build_compile_env tops Internal mut fname args ret fbody F)
    cenv
Proof
  strip_tac >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `cenv = _` SUBST1_TAC >>
  gvs[set_external_package_target_def, package_external_fn_def] >>
  simp[alloc_env_agree_def] >>
  rw[update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem external_body_support_bounds:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  MEM (FunctionDecl External mut nr rr name args defaults ret ss) tops /\
  cenv.ce_struct_fields = make_struct_fields_map tops /\
  cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE) /\
  alloc_env_agree (build_compile_env tops Internal mut name args ret ss F)
    cenv /\
  env_context_consistent env cx /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> MEM (n,ty) args) /\
  EVERY (\(n,ty). assignable_type env.type_defs ty) args /\
  type_stmts env ret ss = SOME env' /\
  (stmts_valued_return ss /\ cenv.ce_is_external /\ ~cenv.ce_raw_return ==>
   return_buffer_ok cenv) ==>
  locals_alloc_ok cenv env /\ EVERY (stmt_exprs_ok cenv) ss /\
  ?bindings. supported_stmts tops bindings ss
Proof
  disch_then strip_assume_tac >>
  drule_all supported_external_allocs_ok >> strip_tac >>
  drule_all fn_allocs_ok_body >> strip_tac >>
  `~supported_stmts_expr_exists (\e. ~byte_widths_expr e) ss` by
    (drule_all typed_parameter_body_excludes_bad_widths >> simp[]) >>
  `EVERY (stmt_exprs_ok cenv) ss` by
    (irule stmt_exprs_ok_from_traversal_bounds >> simp[]) >>
  conj_tac
  >- (simp[locals_alloc_ok_def] >> rpt strip_tac >>
      `MEM (id,ty) args` by metis_tac[] >>
      qpat_x_assum `EVERY (\(_,ty). type_memory_bytes cenv ty < _) args` mp_tac >>
      simp[EVERY_MEM] >>
      disch_then (qspec_then `(id,ty)` mp_tac) >> simp[]) >>
  simp[] >> drule_all supported_program_function >>
  simp[supported_function_body_def] >> metis_tac[]
QED

Theorem external_bind_arguments_popped:
  !args tenv vals env.
    bind_arguments tenv args vals = SOME env ==>
    popped_keys_indexed [env]
Proof
  Induct >> simp[Once bind_arguments_def]
  >- (Cases_on `vals` >>
      simp[bind_arguments_def, popped_keys_indexed_def]) >>
  Cases_on `h` >> Cases_on `vals` >>
  simp[Once bind_arguments_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> first_x_assum drule >>
  simp[popped_keys_indexed_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs(), popped_history_typed_def] >>
  metis_tac[]
QED

Theorem external_body_prefix_storage:
  source_storage_ok tops am tx /\ call_outcomes_ok am tx os /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with <|outcomes := SOME os; requests := []|>) =
    (INL (),es0) ==>
  contract_storage_well_formed
    (initial_evaluation_context am.sources am.layouts tx NONE) es0 /\
  storage_layout_safe
    (initial_evaluation_context am.sources am.layouts tx NONE) /\
  oracle_storage_ok
    (initial_evaluation_context am.sources am.layouts tx NONE) es0 /\
  outcomes_accounts_typed es0.outcomes /\ IS_SOME es0.outcomes
Proof
  strip_tac >>
  `es0.outcomes = SOME os` by
    (drule external_send_call_value_frame >>
     simp[evaluation_state_component_equality, initial_state_def]) >>
  `contract_storage_well_formed
     (initial_evaluation_context am.sources am.layouts tx NONE)
     (initial_state am [env] with <|outcomes := SOME os; requests := []|>)` by
    (gvs[source_storage_ok_def] >>
     irule contract_storage_well_formed_storage_frame >>
     goal_assum (drule_at Any) >>
     Cases >> simp[get_storage_def, initial_state_def]) >>
  reverse conj_tac
  >- (gvs[source_storage_ok_def, call_outcomes_ok_def,
           oracle_storage_ok_def, outcomes_accounts_typed_def,
           EVERY_MEM] >>
      rpt strip_tac >> first_x_assum drule >> simp[] >> strip_tac >>
      irule contract_storage_well_formed_storage_frame >>
      goal_assum (drule_at Any) >>
      Cases >> simp[get_storage_def, initial_state_def]) >>
  qpat_x_assum `send_call_value _ _ _ = _` mp_tac >>
  simp[send_call_value_def, vyperStateTheory.assert_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
       vyperStateTheory.raise_def, vyperStateTheory.return_def] >>
  rpt IF_CASES_TAC >> simp[] >> strip_tac >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.assert_def,
      vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()] >>
  drule_all transfer_value_preserves_contract_storage_well_formed >> simp[]
QED

Theorem external_selected_args_distinct:
  supported_program tops /\ source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  ALL_DISTINCT (MAP FST args)
Proof
  strip_tac >>
  `?raw. MEM (FunctionDecl External mut F raw tx.function_name args [] ret fbody) tops` by
    (irule lookup_function_external_decl >> simp[] >>
     qexists `tops` >> gvs[supported_program_def, supported_declaration_headers_def]) >>
  gvs[source_typing_ok_def] >>
  `module_allocated am.layouts tx.target NONE tops` by
    (drule check_contract_main_module_allocated >> simp[]) >>
  `check_function_body am.layouts tx.target [(NONE,tops)] art NONE
     External mut F args [] ret fbody` by
    (irule check_contract_runtime_function_body_MEM >> simp[] >>
     qexistsl [`tx.function_name`, `raw`] >> simp[]) >>
  gvs[check_function_body_def, params_ok_def]
QED

Theorem external_package_body_inv:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) ==>
  body_inv tops unit.cu_context cenv
    (initial_evaluation_context am.sources am.layouts tx NONE) /\
  cenv.ce_return_pc = NONE
Proof
  strip_tac >>
  `acyclic_struct_metadata (make_struct_fields_map tops)` by
    (gvs[source_typing_ok_def] >>
     drule_all supported_checked_struct_metadata_acyclic >> simp[]) >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `cenv = _` SUBST1_TAC >>
  `ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[source_typing_ok_vtype_keys_distinct] >>
  gvs[set_external_package_target_def, package_external_fn_def] >>
  Cases_on `ret = NoneT` >>
  gvs[update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
  simp[body_inv_def, build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[source_deployment_rel_def, get_module_code_def,
      initial_evaluation_context_def, get_tenv_def,
      type_env_all_modules_def, GSYM type_env_def] >>
  gvs[source_typing_ok_def] >>
  metis_tac[]
QED

Theorem external_package_dec_metadata:
  source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  set_external_package_target target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) ==>
  dec_cenv_agrees cenv
    (get_tenv (initial_evaluation_context am.sources am.layouts tx NONE))
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))`
    by metis_tac[source_typing_ok_type_def_keys_distinct] >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `cenv = _` SUBST1_TAC >>
  Cases_on `package_external_fn tops T (K global_nonreentrant_slot)
    (mut,F,rr,tx.function_name,args,[],ret,fbody)` >>
  PairCases_on `r` >> gvs[set_external_package_target_def] >>
  drule_all package_external_fn_dec_cenv_agrees >> strip_tac >>
  gvs[dec_cenv_agrees_def, source_deployment_rel_def,
      get_tenv_def, initial_evaluation_context_def, get_module_code_def,
      type_env_all_modules_def, type_env_def] >>
  rpt strip_tac >>
  irule EQ_TRANS >> irule_at Any type_memory_bytes_struct_fields >>
  simp[] >> metis_tac[]
QED

Theorem supported_lookup_flag_none:
  !ts fid members.
  EVERY (supported_declaration_header tops) ts ==>
  lookup_flag fid ts <> SOME members
Proof
  Induct >> simp[lookup_flag_def] >>
  Cases >> simp[lookup_flag_def, supported_flags_rejected] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem external_source_no_flags:
  supported_program tops /\ source_deployment_rel tops am tx /\
  get_module_code
    (initial_evaluation_context am.sources am.layouts tx NONE) src = SOME ts ==>
  lookup_flag fid ts <> SOME members
Proof
  strip_tac >>
  gvs[source_deployment_rel_def, get_module_code_def,
      initial_evaluation_context_def, AllCaseEqs()] >>
  irule supported_lookup_flag_none >>
  gvs[supported_program_def, supported_declaration_headers_def] >>
  qexists `tops` >> simp[]
QED

Theorem external_package_struct_fields:
  source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  set_external_package_target target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) /\
  FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
  ALL_DISTINCT (MAP FST fields) /\
  EVERY (\(fname,fty,sz). !tv.
    evaluate_type
      (get_tenv (initial_evaluation_context am.sources am.layouts tx NONE))
      fty = SOME tv ==> sz = type_memory_size tv) fields
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))`
    by metis_tac[source_typing_ok_type_def_keys_distinct] >>
  `!name args. MEM (StructDecl name args) tops ==>
     ALL_DISTINCT (MAP FST args)` by
    (rpt strip_tac >> gvs[source_typing_ok_def] >>
     drule check_contract_struct_fields_distinct >>
     simp[] >> disch_then drule >> simp[]) >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `cenv = _` SUBST_ALL_TAC >>
  gvs[set_external_package_target_def, package_external_fn_def] >>
  Cases_on `ret = NoneT` >>
  gvs[update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
      build_compile_env_ce_struct_fields] >>
  gvs[source_deployment_rel_def, get_tenv_def,
      initial_evaluation_context_def, get_module_code_def,
      type_env_all_modules_def, GSYM type_env_def] >>
  irule make_struct_fields_map_fields >> metis_tac[]
QED

(* The packaged external env's method ids are the selectors over the
   source's type environment, as expr_sim_inv asks. *)
Theorem external_package_method_id:
  source_deployment_rel tops am tx /\
  set_external_package_target target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) ==>
  !fname tys.
    cenv.ce_method_id fname tys =
    w2n (calldata_method_id
           (function_selector fname
              (vyper_to_abi_types
                 (get_tenv (initial_evaluation_context am.sources am.layouts
                              tx NONE)) tys)))
Proof
  strip_tac >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `cenv = _` SUBST1_TAC >>
  gvs[set_external_package_target_def, package_external_fn_def] >>
  rw[update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[source_deployment_rel_def, get_tenv_def,
      initial_evaluation_context_def, get_module_code_def,
      type_env_all_modules_def, GSYM type_env_def]
QED

Theorem external_package_global_maps:
  set_external_package_target target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) /\
  check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
  env_t.toplevel_vtypes = art.cta_toplevel_vtypes /\
  env_t.bare_globals = art.cta_bare_globals ==>
  place_map_tables_agree_on_defined cenv env_t /\
  (!nsid ty. FLOOKUP env_t.bare_globals nsid = SOME ty ==>
     cenv.ce_hashmap_info nsid = NONE)
Proof
  strip_tac >>
  drule_all external_package_registered_hashmap_info >> strip_tac >>
  conj_tac
  >- (drule checked_single_module_defined_map_agreement >>
      disch_then irule >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  drule_all checked_single_module_bare_global_no_hashmap >> simp[]
QED

Theorem external_package_bare_globals:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  es0.immutables = am.immutables /\
  env_consistent env_t
    (initial_evaluation_context am.sources am.layouts tx NONE) es0 /\
  set_external_package_target target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) ==>
  !src id ty. FLOOKUP env_t.bare_globals (src,id) = SOME ty ==>
    src = cenv.ce_module /\
    ?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
      !tv. evaluate_type (get_tenv
        (initial_evaluation_context am.sources am.layouts tx NONE)) ty = SOME tv ==>
        off + type_memory_size tv < dimword (:256)
Proof
  strip_tac >>
  drule lower_vyper_runtime_unit_immutables_bound >> strip_tac >>
  `immutables_section_rel tops (account_immutables am tx.target)
     vs.vs_data_section` by gvs[initial_venom_state_rel_def] >>
  drule immutables_section_rel_length >> strip_tac >>
  `LENGTH vs.vs_data_section < dimword (:256)` by
    (simp[wordsTheory.dimword_def] >> decide_tac) >>
  `get_module_code (initial_evaluation_context am.sources am.layouts tx NONE)
     NONE = SOME tops /\
   (!src ts. get_module_code
      (initial_evaluation_context am.sources am.layouts tx NONE) src = SOME ts ==>
      src = NONE)` by
    (gvs[source_deployment_rel_def, get_module_code_def,
         initial_evaluation_context_def] >> rpt strip_tac >> gvs[]) >>
  Cases_on `ALOOKUP am.immutables tx.target`
  >- (gvs[env_consistent_def, env_immutables_consistent_def,
          initial_evaluation_context_def, get_source_immutables_def] >>
      rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `!src id ty. FLOOKUP env_t.bare_globals (src,id) = SOME ty ==>
     src = (build_compile_env tops External mut tx.function_name args ret fbody F).ce_module /\
     ?off. FLOOKUP (build_compile_env tops External mut tx.function_name args ret fbody F).ce_module_vars
       (src,id) = SOME (ImmutableLoc off) /\
       !tv. evaluate_type (get_tenv
         (initial_evaluation_context am.sources am.layouts tx NONE)) ty = SOME tv ==>
         off + type_memory_size tv < dimword (:256)` by
    (drule_at (Pat `supported_program _`) build_compile_env_bare_globals >>
     simp[] >>
     disch_then (drule_at (Pat `env_consistent _ _ _`)) >>
     gvs[account_immutables_def, initial_evaluation_context_def,
         build_compile_env_module_vars] >>
     disch_tac >> metis_tac[]) >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  gvs[package_external_fn_def, set_external_package_target_def] >>
  Cases_on `ret = NoneT` >>
  gvs[update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
  qpat_x_assum `cenv = _` (fn th => once_rewrite_tac [th]) >>
  simp[] >> metis_tac[]
QED

(* package_external_fn reads the defaults only through their number, so
   the type of an empty default list does not matter. *)
Theorem set_external_package_target_dflts[local]:
  set_external_package_target target
    (package_external_fn tops use_trans nkeys
      (mut,nr,rr,name,args,d1,ret,body)) = X ==>
  !d2. LENGTH d1 = LENGTH d2 ==>
    set_external_package_target target
      (package_external_fn tops use_trans nkeys
        (mut,nr,rr,name,args,d2,ret,body)) = X
Proof
  rpt strip_tac >> qpat_x_assum `_ = X` (SUBST1_TAC o SYM) >>
  simp[package_external_fn_def]
QED

Theorem external_selected_return_buffer_ok:
  !tops rpolicy unit tx calldata ret mut args fbody lbl cenv0 pos_args
   min_cds is_payable nkey ut iv rt st cenv sa.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    valid_vyper_call tops tx calldata ret /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut,F,args,[],ret,fbody) /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
        (mut,F,lookup_raw_return_or_F (NONE : num option)
          tx.function_name External tops,tx.function_name,args,[],ret,fbody)) =
      (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) ==>
    (stmts_valued_return fbody /\ cenv.ce_is_external /\
     ~cenv.ce_raw_return ==> return_buffer_ok cenv)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `set_external_package_target _ _ = _`
    (fn th => mp_tac (Q.ISPEC `[]:expr list`
       (MATCH_MP set_external_package_target_dflts th))) >>
  simp[] >> strip_tac >>
  `EVERY (supported_declaration_header tops) tops` by
    gvs[supported_program_def, supported_declaration_headers_def] >>
  drule_all supported_lookup_raw >> strip_tac >>
  `tx.function_name <> "__default__"` by gvs[valid_vyper_call_def] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  drule_all supported_external_classification >> simp[] >> strip_tac >>
  drule_all lower_vyper_runtime_unit_return_buffer_ok >>
  gvs[lookup_raw_return_or_F_def] >> strip_tac >>
  qpat_x_assum `external_return_buffer_ok _` mp_tac >>
  qpat_assum `set_external_package_target _ _ = _`
    (fn th => rewrite_tac [th]) >> strip_tac >>
  drule package_external_fn_return_buffer_ok >>
  disch_then drule >> strip_tac >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `cenv = _` (fn th => once_rewrite_tac [th]) >>
  gvs[return_buffer_ok_def]
QED


(* At the start of the selected function's body, the
   premises of body_stmts_sim other than the frame's returns: the frame is
   the lowered program's (body_inv), the body is supported and typed at
   the return type in a type environment env_t of the parameters, which
   the compile env and the source state agree with and whose locals fit
   the allocation limit, and the external frame has no return PC and no
   lock. expr_sim_inv's storage-variable clause (each storage variable has
   its declared module type and no hash-map info) follows from body_inv
   and the single-module fact via body_inv_storage_var_types. *)
Theorem external_body_frame:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 lbl cenv0 pos_args
   min_cds is_payable nkey ut' iv rt st cenv sa.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
         (mut, F, lookup_raw_return_or_F (NONE : num option)
                     tx.function_name External tops,
          tx.function_name, args, [], ret, fbody)) =
      (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
       rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) ==>
    body_inv tops unit.cu_context cenv
      (initial_evaluation_context am.sources am.layouts tx NONE) /\
    cenv.ce_return_pc = NONE /\
    ?bindings env_t env'.
      supported_stmts tops bindings fbody /\
      expr_sim_inv cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) env_t es0 /\
      ce_locals_declared cenv env_t /\ locals_alloc_ok cenv env_t /\
      type_stmts env_t ret fbody = SOME env' /\
      EVERY (stmt_exprs_ok cenv) fbody /\
      call_evaluation_safe
        (initial_evaluation_context am.sources am.layouts tx NONE)
        (int_calls_stmts fbody)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all external_package_body_inv >> strip_tac >> simp[] >>
  drule_all external_selected_body_typing >> strip_tac >>
  `machine_well_typed am` by gvs[source_typing_ok_def] >>
  drule_all external_body_prefix_state >> strip_tac >>
  drule_all external_selected_env_consistent >> strip_tac >>
  drule_all external_body_prefix_storage >> strip_tac >>
  drule external_source_context_typed >> strip_tac >>
  drule_all external_package_dec_metadata >> strip_tac >>
  drule_all external_package_global_maps >> strip_tac >>
  drule external_package_bare_globals >>
  disch_then (drule_at (Pat `initial_venom_state_rel _ _ _ _`)) >>
  disch_then (drule_at (Pat `env_consistent _ _ _`)) >>
  disch_then (drule_at (Pat `set_external_package_target _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  `?raw. MEM (FunctionDecl External mut F raw tx.function_name args [] ret fbody) tops` by
    (irule lookup_function_external_decl >> simp[] >> qexists `tops` >>
     gvs[supported_program_def, supported_declaration_headers_def]) >>
  `supported_function_body tops External args fbody` by
    (drule_all supported_program_function >> simp[]) >>
  `ALL_DISTINCT (MAP FST args)` by
    (drule_all external_selected_args_distinct >> simp[]) >>
  `EVERY (\(n,ty). assignable_type env_t.type_defs ty) args` by
    (`module_allocated am.layouts tx.target NONE tops` by
       (drule check_contract_main_module_allocated >> simp[]) >>
     `check_function_body am.layouts tx.target [(NONE,tops)] art NONE
        External mut F args [] ret fbody` by
       (irule check_contract_runtime_function_body_MEM >> simp[] >>
        qexistsl [`tx.function_name`, `raw`] >> simp[]) >>
     gvs[check_function_body_def, params_ok_def, get_tenv_def,
         checked_contract_runtime_ready_def,
         initial_evaluation_context_def, type_env_all_modules_def]) >>
  `cenv.ce_struct_fields = make_struct_fields_map tops /\
   cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE)` by
    gvs[body_inv_def] >>
  `env_context_consistent env_t
     (initial_evaluation_context am.sources am.layouts tx NONE)` by
    gvs[env_consistent_def] >>
  `stmts_valued_return fbody /\ cenv.ce_is_external /\
   ~cenv.ce_raw_return ==> return_buffer_ok cenv` by
    (strip_tac >> drule external_selected_return_buffer_ok >>
     rpt (disch_then drule) >> simp[]) >>
  drule_all external_package_alloc_env_agree >> strip_tac >>
  drule_all external_body_support_bounds >> strip_tac >>
  qexistsl [`bindings`, `env_t`, `env'`] >> simp[] >>
  reverse conj_tac
  >- (irule external_entry_target_locals_declared >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  simp[expr_sim_inv_def] >> rpt conj_tac
  >- (rpt strip_tac >> irule external_entry_target_param_pointer >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[])
  >- (rpt strip_tac >> irule external_entry_target_param_type >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[])
  >- (rpt strip_tac >> drule_all external_source_no_flags >>
      disch_then (qspecl_then [`ls`, `fid`] mp_tac) >> simp[])
  >- gvs[dec_cenv_agrees_def]
  >- (drule_all external_package_method_id >> simp[])
  >- gvs[dec_cenv_agrees_def]
  >- (rpt strip_tac >>
      `FLOOKUP cenv.ce_struct_fields name = SOME fields` by simp[] >>
      drule_all external_package_struct_fields >> simp[])
  >- (`!src ts. get_module_code
         (initial_evaluation_context am.sources am.layouts tx NONE) src =
         SOME ts ==> src = NONE` by
        gvs[source_deployment_rel_def, get_module_code_def,
            initial_evaluation_context_def] >>
      drule body_inv_storage_var_types >> disch_then drule >>
      strip_tac >> rpt gen_tac >> strip_tac >>
      first_x_assum drule_all >> simp[])
  >- (simp[] >> irule external_bind_arguments_popped >> goal_assum (drule_at Any)) >>
  rpt strip_tac >>
  qpat_x_assum `!src id ty. FLOOKUP art.cta_bare_globals (src,id) = SOME ty ==> _`
    drule >> simp[]
QED

