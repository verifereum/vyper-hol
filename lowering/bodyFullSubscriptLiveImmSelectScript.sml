(* Selecting a subplace from the current immutable representation. *)
Theory bodyFullSubscriptLiveImmSelect
Ancestors
  exprBodyPreCallSafetyProps exprBodyPreTypingProps
  bodyInvCodeProps bodyInvSplit bodyCallSupport exprBodyPreProps alist
  bodyFullExtCallPosTransport bodySimFull loweringPosts
  exprSimSubscriptArrayLiveImmutableSuffix exprSimSubscriptArrayLiveImmutableView
  exprSimSubscriptArrayLiveImmutableMetadata exprSimWordArgs exprSimSource
  vyperFixedShapePath vyperState stateRelProj vyperAST vyperInterpreter
  vyperSubscriptOverlap vyperStoragePlaceProvenance vyperBareGlobalName
  vyperCallFrame vyperCreateFrame vyperLocalAccessFrame vyperMisc pair
  bodySim constSubst constSubstCorrect exprSimHypsDefs exprSimSubscriptArraySource gasContext
  supportedNames supportedProgram targetOverlapAccess vyperContext
  vyperImmutableAccessFrame vyperTypeContractStaticMaps externalBodyFrame
  vyperTypeInvariants vyperTypeExprSoundness vyperTypeEvalSoundness vyperTypeSystem
  exprPtrCtorCodeLoad exprSimCopy bodyFullUnwrapRun exprSimBopRestWordLoadSafety
  immutableCopyExecution entrySinkExtraction fragGasOriginPtrDead exprSimStorageCopy
  bodyFullSubscriptArrayCodeOps bodyFullSubscriptArrayCodeBounds
  bodyPtrSignedConvertSourceFrame exprSimSubscriptArrayEndpoint
  exprSimSubscriptArrayCompose bodyFullGhostFrame bodyFullPathHistory
  targetSubscriptMemory vyperStorageFootprint
  exprSimSubscriptArraySuffix gasOutcomeFullCompose compileEnv bodyPtrDefs
  freshWrites wordArgsPtr gasSummary fragExec exprSimMemDefs venomState

Theorem selected_constructor_code_read[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env fin /\
  cenv.ce_is_ctor /\ p.ptr_location = LocCode /\ dead_lo_ok H D lo cenv cx /\
  stmt_state_rel H ctx func cenv cx fin q /\
  ghost_inv_at D lo d cenv cx fin G tn q /\
  read_result cx raw fin = (INL v,fin) /\
  vv_holds cenv cx ty raw (LocatedValue ty p) fin q ==>
  ?val. read_result cx raw fin = (INL val,fin) /\
    !rt w. evaluate_type (get_tenv cx) ty = SOME rt /\
           eval_operand p.ptr_operand q = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      !mem. mem_agree_outside tn.t_mem q.vs_memory mem ==>
            val_in_memory rt val (w2n w) mem
Proof
  strip_tac >> qexists `v` >> simp[arithmeticTheory.ADD_COMM] >>
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.INST [`entry` |-> `fin`, `ee` |-> `fin`, `u` |-> `q`]
                  extcall_request_saved_ctor_read) >>
  simp[arithmeticTheory.ADD_COMM] >>
  (impl_tac >- (qexists `raw` >> simp[])) >> simp[]
QED

(* A fixed projection can be read from the current root even if the index
   changed that root.  The last selected value may itself be dynamic. *)
Theorem current_immutable_fixed_path_live[local]:
  expr_sim_inv cenv cx env fin /\
  FLOOKUP (case ALOOKUP fin.immutables cx.txn.target of
             NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
    SOME (itv,iv) /\
  fixed_shape_path itv path ==>
  ?v. evaluate_subscripts itv iv path = INL v
Proof
  strip_tac >>
  `value_has_type itv iv /\ well_formed_type_value itv` by
    (irule imm_place_at_value_type >> goal_assum (drule_at Any) >>
     qexistsl [`cenv`, `env`, `0`, `[]`] >>
     simp[mem_path_offset_def, evaluate_subscripts_def]) >>
  irule fixed_shape_path_live >> simp[]
QED

Theorem evaluated_immutable_spine[local]:
  !e cx es src id path t.
    eval_expr cx e es = (INL (PlaceR (ImmutablePlace src id path)),t) ==>
    ((?ann. e = TopLevelName ann (src,id) /\ path = []) \/
     (?ann obj idx pre mid key. e = Subscript ann obj idx /\
        eval_expr cx obj es = (INL (PlaceR (ImmutablePlace src id pre)),mid) /\
        path = pre ++ [ValueSubscript key]) \/
     (?ann obj fld pre mid. e = Attribute ann obj fld /\
        eval_expr cx obj es = (INL (PlaceR (ImmutablePlace src id pre)),mid) /\
        path = pre ++ [AttrSubscript fld]))
Proof
  Cases >> rpt gen_tac
  >- simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()]
  >- (rename1 `TopLevelName ann nsid` >> PairCases_on `nsid` >>
      simp[Once evaluate_def] >>
      metis_tac[lookup_global_immutable_root])
  >- (rename1 `FlagMember ann nsid mid` >> PairCases_on `nsid` >>
      simp[Once evaluate_def, lookup_flag_mem_def, bind_def,
           option_CASE_rator, lift_option_type_def, return_def, raise_def, AllCaseEqs()])
  >- suspend "ifexp"
  >- simp[Once evaluate_def, return_def]
  >- (rename1 `StructLit ann nsid fields` >> PairCases_on `nsid` >>
      simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()])
  >- suspend "subscript"
  >- suspend "attribute"
  >- simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()]
  >- simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()]
  >- suspend "pop"
  >> suspend "call"
QED

Resume evaluated_immutable_spine[ifexp]:
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  qpat_x_assum `conditional_result _ _ _ = _` mp_tac >>
  rename1 `conditional_result cx raw mid = _` >>
  Cases_on `raw` >> simp[conditional_result_def, return_def, raise_def] >>
  rename1 `PlaceR pl` >> Cases_on `pl` >>
  simp[conditional_result_def, bind_def, return_def, AllCaseEqs()] >>
  simp[COND_RATOR, bind_def, return_def, AllCaseEqs()]
QED

Resume evaluated_immutable_spine[subscript]:
  rename1 `Subscript ann obj idx` >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >> rename1 `select_result cx _ raw _ _ = _` >>
  Cases_on `raw` >>
  gvs[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
      return_def, raise_def, AllCaseEqs()] >>
  drule extend_place_immutable_root >> strip_tac >> gvs[] >>
  qpat_x_assum `(if subscript_reads_base _ _ _ then _ else _) _ = _` mp_tac >>
  IF_CASES_TAC >> simp[bind_def, return_def, AllCaseEqs()] >> rpt strip_tac >>
  metis_tac[]
QED

Resume evaluated_immutable_spine[attribute]:
  rename1 `Attribute ann obj attr_id` >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >> rename1 `select_result cx _ raw _ _ = _` >>
  Cases_on `raw` >>
  gvs[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
      return_def, raise_def, AllCaseEqs()] >>
  drule extend_place_immutable_root >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Resume evaluated_immutable_spine[pop]:
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  rename1 `pop_place cx bp _ = _` >> Cases_on `bp`
  >- (rename1 `StoragePlace tr slot tv` >> Cases_on `tv` >>
      gvs[pop_place_def, bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
      rename1 `ArrayTV et bd` >> Cases_on `bd` >>
      gvs[pop_place_def, bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()]) >>
  gvs[pop_place_def, bind_def, ignore_bind_def, return_def, raise_def,
      UNCURRY, AllCaseEqs()]
QED

Resume evaluated_immutable_spine[call]:
  rename1 `Call ann call_target call_args call_default` >> Cases_on `call_target` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac
  >~ [`IntCall nsid`]
  >- (PairCases_on `nsid` >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, return_def,
          raise_def, UNCURRY, AllCaseEqs()])
  >~ [`eval_send`]
  >- (drule eval_send_success_value >> simp[])
  >~ [`eval_ext_call`]
  >- (drule eval_ext_call_success_value >> simp[])
  >~ [`eval_raw_call`]
  >- (drule eval_raw_call_success_value >> simp[])
  >~ [`eval_raw_call`]
  >- (drule eval_raw_call_success_value >> simp[])
  >> drule vyperLocalAccessFrameTheory.eval_create_operands_success_value >> simp[]
QED
Finalise evaluated_immutable_spine

Theorem evaluated_immutable_direct_read[local]:
  !e cx es src id path t.
    eval_expr cx e es = (INL (PlaceR (ImmutablePlace src id path)),t) ==>
    MEM (ReadAcc (StateRef (src,id))) (accesses_expr e)
Proof
  measureInduct_on `expr_size e` >> rpt strip_tac >>
  drule evaluated_immutable_spine >> strip_tac >> gvs[accesses_expr_def] >>
  first_x_assum (qspec_then `obj` mp_tac) >> simp[expr_size_def] >> metis_tac[]
QED

Theorem constant_decl_mem_consts:
  !tops acc id. constant_decl id tops ==>
    MEM id (MAP FST (module_consts_env tops acc))
Proof
  recInduct module_consts_env_ind >>
  simp[constant_decl_def, module_consts_env_def] >> rpt strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `module_consts_env rest acc'` >>
  qspecl_then [`rest`, `acc'`] strip_assume_tac module_consts_env_acc_prefix >>
  simp[Abbr `acc'`]
QED

Theorem nonconstant_state_read_mem[local]:
  !mods accs src id.
    MEM (ReadAcc (StateRef (src,id))) accs /\
    (!ts. ALOOKUP mods src = SOME ts ==> ~constant_decl id ts) ==>
    MEM (StateRef (src,id)) (nonconstant_reads mods accs)
Proof
  recInduct nonconstant_reads_ind >> rw[nonconstant_reads_def] >>
  gvs[AllCaseEqs()] >>
  Cases_on `ALOOKUP mods src` >> gvs[] >>
  TRY (IF_CASES_TAC >> gvs[]) >> metis_tac[]
QED

Theorem contract_inv_subscript_overlap[local]:
  contract_inv mods exps ctx cenv cx ==>
  subscript_reads_base cx obj idx = subscript_overlap mods obj idx
Proof
  simp[contract_inv_def, subscript_reads_base_def]
QED

Theorem immutable_no_copy_index_access_mods[local]:
  contract_inv mods exps ctx cenv cx /\
  ~cx_const_name_mods mods (src,id) /\
  eval_expr cx obj es = (INL (PlaceR (ImmutablePlace src id path)),mid) /\
  is_ArrayT (expr_type obj) /\ base_through_dynarray obj /\
  ~subscript_reads_base cx obj idx ==>
  ~MEM RiskyAcc (expr_accesses mods idx) /\
  ~MEM (WriteAcc (StateRef (src,id))) (expr_accesses mods idx)
Proof
  strip_tac >>
  `MEM (StateRef (src,id)) (nonconstant_reads mods (expr_accesses mods obj))` by
    (irule nonconstant_state_read_mem >> conj_tac
     >- (fs[cx_const_name_mods_def] >> metis_tac[constant_decl_mem_consts]) >>
     simp[expr_accesses_def] >> metis_tac[evaluated_immutable_direct_read]) >>
  qpat_x_assum `~subscript_reads_base _ _ _` mp_tac >>
  drule_then (fn th => simp[th, subscript_overlap_def, any_written_MEM])
    contract_inv_subscript_overlap >>
  metis_tac[listTheory.MEM]
QED

Theorem find_function_distinct_decl[local]:
  !tops vis mut nr rr fn args dflts ret body.
    ALL_DISTINCT (supported_function_names tops) /\
    MEM (FunctionDecl vis mut nr rr fn args dflts ret body) tops ==>
    find_function fn tops = SOME (dflts,body)
Proof
  Induct_on `tops` >> simp[] >>
  Cases_on `h` >>
  simp[supported_function_names_def, find_function_def] >>
  metis_tac[externalBodyFrameTheory.supported_function_names_mem]
QED

Theorem immutable_index_callable_closed_mods:
  !mods exps ctx cenv cx src ts fn mut nr args dflts ret body.
  contract_inv mods exps ctx cenv cx /\ get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
  ALOOKUP mods src = SOME ts /\
  (find_function fn ts = SOME (dflts,body) \/ (dflts = [] /\ body = []))
Proof
  rpt strip_tac >>
  drule_then (assume_tac o Q.SPEC `src`) contract_inv_module_codes >>
  `ALOOKUP mods src = SOME ts` by fs[] >>
  `supported_module_headers ts` by
    (fs[bodyInvSplitTheory.contract_inv_def] >> res_tac) >>
  fs[lookup_callable_function_def, bodyCallSupportTheory.supported_module_headers_def,
     supported_declaration_names_def, AllCaseEqs()] >>
  metis_tac[lookup_function_Internal_SOME_MEM, lookup_function_Deploy_SOME_cases,
            find_function_distinct_decl]
QED

Theorem immutable_no_copy_dynamic_frame_mods[local]:
  contract_inv mods exps ctx cenv cx /\
  ~cx_const_name_mods mods (src,id) /\
  eval_expr cx obj es = (INL (PlaceR (ImmutablePlace src id path)),mid) /\
  is_ArrayT (expr_type obj) /\ base_through_dynarray obj /\
  ~subscript_reads_base cx obj idx /\
  expr_body_pre_mods mods cenv cx env idx ix /\ ix.immutables = mid.immutables /\
  eval_expr cx idx ix = (res,fin) ==>
  FLOOKUP (case ALOOKUP fin.immutables cx.txn.target of
       NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
  FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of
       NONE => FEMPTY | SOME imms => get_source_immutables src imms) id
Proof
  strip_tac >> drule_all_then strip_assume_tac immutable_no_copy_index_access_mods >>
  qpat_assum `ix.immutables = mid.immutables`
    (once_rewrite_tac o single o GSYM) >>
  irule eval_expr_unwritten_immutable >>
  fs[expr_body_pre_mods_def, expr_sim_inv_mods_def] >>
  qexistsl [`idx`, `env`, `mods`, `res`] >> simp[] >>
  rpt strip_tac >> drule_all_then strip_assume_tac immutable_index_callable_closed_mods >>
  simp[]
QED

(* An index following a dynamic ancestor must leave that ancestor live. *)
Theorem immutable_target_index_frame_mods:
  contract_inv mods exps ctx cenv cx /\ expr_body_pre_mods mods cenv cx env idx es /\
  target_root bt = TopLevelNameTarget (src,id) /\ ~cx_const_name_mods mods (src,id) /\
  target_through_dynarray cenv bt /\ ~target_subscript_overlap cenv bt idx /\
  eval_expr cx idx es = (res,ee) ==>
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables src imms) id
Proof
  strip_tac >> drule_then assume_tac contract_inv_cenv_modules >>
  `MEM (StateRef (src,id)) (nonconstant_reads cenv.ce_modules
      (expr_accesses cenv.ce_modules (target_to_expr bt)))` by
    (irule target_root_state_nonconstant_read >>
     fs[cx_const_name_mods_def] >> metis_tac[constant_decl_mem_consts]) >>
  drule_all_then strip_assume_tac target_subscript_overlap_unwritten >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  gvs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
  irule eval_expr_unwritten_immutable >> simp[] >>
  qexistsl [`idx`,`env`,`cenv.ce_modules`,`res`] >> simp[] >>
  rpt gen_tac >> strip_tac >> drule_all_then ACCEPT_TAC immutable_index_callable_closed_mods
QED

Theorem immutable_target_index_frame:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env idx es /\
  target_root bt = TopLevelNameTarget (NONE,id) /\ ~cx_const_name cx (NONE,id) /\
  target_through_dynarray cenv bt /\ ~target_subscript_overlap cenv bt idx /\
  eval_expr cx idx es = (res,ee) ==>
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables NONE imms) id =
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables NONE imms) id
Proof
  strip_tac >> drule_then strip_assume_tac body_inv_main_code >>
  drule_then assume_tac body_inv_contract >>
  drule_all_then assume_tac body_inv_expr_body_pre_mods >>
  irule immutable_target_index_frame_mods >>
  qexistsl [`bt`,`cenv`,`ctx`,`env`,`[]`,`idx`,`[(NONE,tops)]`,`res`] >>
  fs[cx_const_name_split_def]
QED

Theorem immutable_target_path_after_index:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env idx es /\
  target_root bt = TopLevelNameTarget (NONE,id) /\ ~cx_const_name cx (NONE,id) /\
  ~target_subscript_overlap cenv bt idx /\
  eval_expr cx idx es = (res,ee) /\
  FLOOKUP env.bare_globals (NONE,id) = SOME root_ty /\
  evaluate_type (get_tenv cx) root_ty = SOME itv /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables NONE imms) id = SOME (itv,old) /\
  evaluate_subscripts itv old path = INL v /\
  (~target_through_dynarray cenv bt ==> fixed_shape_path itv path) ==>
  expr_sim_inv cenv cx env ee /\
  ?current a.
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
      NONE => FEMPTY | SOME imms => get_source_immutables NONE imms) id =
      SOME (itv,current) /\
    evaluate_subscripts itv current path = INL a
Proof
  strip_tac >> drule_all_then strip_assume_tac expr_body_pre_eval_result >> simp[] >>
  Cases_on `target_through_dynarray cenv bt`
  >- (drule_all_then assume_tac immutable_target_index_frame >>
      qexistsl [`old`,`v`] >> simp[]) >>
  `fixed_shape_path itv path` by simp[] >>
  drule_all_then strip_assume_tac live_immutable_root_current >>
  drule_all_then strip_assume_tac current_immutable_fixed_path_live >>
  metis_tac[]
QED

Theorem immutable_typed_path[local]:
  env_consistent env cx s /\
  eval_result_typed (env,cx,s) (PlaceR (ImmutablePlace src id path)) vt /\
  FLOOKUP env.bare_globals (src,id) = SOME root_ty /\
  evaluate_type (get_tenv cx) root_ty = SOME itv ==>
  ?ty tv. vt = Type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
          subscripts_type itv path = SOME tv
Proof
  Cases_on `vt` >> gvs[eval_result_typed_def] >>
  simp[vyperPlaceTypingTheory.runtime_place_typed_immutable] >> strip_tac >>
  Cases_on `ALOOKUP s.immutables cx.txn.target` >>
  gvs[env_consistent_def, get_immutables_def, get_address_immutables_def,
      bind_def, lift_option_type_def, return_def, raise_def] >>
  `env.type_defs = get_tenv cx` by fs[env_context_consistent_def] >>
  `evaluate_type (get_tenv cx) root_ty = SOME root` by
    (qpat_x_assum `env_immutables_consistent _ _ _` mp_tac >>
     simp[env_immutables_consistent_def] >> strip_tac >>
     qpat_assum `!s' i' ty tv' v. FLOOKUP env.bare_globals (s',i') = SOME ty /\ _ ==> _`
       drule_all >> simp[]) >>
  gvs[]
QED

Theorem fixed_shape_path_snoc[local]:
  fixed_shape_path itv path /\ subscripts_type itv path = SOME tv /\
  subscripts_type itv (path ++ [sb]) = SOME tv' /\
  (~(?et n. tv = ArrayTV et (Dynamic n))) ==>
  fixed_shape_path itv (path ++ [sb])
Proof
  simp[fixed_shape_path_append, fixed_shape_path_def,
       vyperPlaceStatePreservationTheory.subscripts_type_append,
       subscripts_type_def, AllCaseEqs(), SF CONJ_ss] >> metis_tac[]
QED

Theorem immutable_annotated_path[local]:
  (well_typed_expr env e \/ (?vt. type_place_expr env e = SOME vt)) /\
  runtime_consistent env cx es /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e es = (INL (PlaceR (ImmutablePlace src id path)),t) /\
  FLOOKUP env.bare_globals (src,id) = SOME root_ty /\
  evaluate_type (get_tenv cx) root_ty = SOME itv ==>
  ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
       subscripts_type itv path = SOME tv
Proof
  simp[vyperTypeExprSoundnessTheory.runtime_consistent_def] >> strip_tac >>
  drule_all (cj 1 (cj 5 eval_scc_type_sound_mutual)) >> simp[] >> strip_tac >>
  `?vt. env_consistent env cx t /\
         eval_result_typed (env,cx,t) (PlaceR (ImmutablePlace src id path)) vt /\
         vtype_annotation_ok vt (expr_type e)` suffices_by
    (strip_tac >> drule_all immutable_typed_path >> strip_tac >>
     gvs[vtype_annotation_ok_def])
  >- (qexists `Type (expr_type e)` >> simp[vtype_annotation_ok_def]) >>
  drule vyperTypeSystemTheory.type_place_expr_vtype_annotation >> strip_tac >>
  qexists `vt` >> simp[]
QED

Theorem immutable_path_container_not_dynamic[local]:
  evaluate_type tenv ty = SOME tv /\
  (~(?et n. ty = ArrayT et (Dynamic n))) ==>
  ~(?et n. tv = ArrayTV et (Dynamic n))
Proof
  Cases_on `ty` >>
  simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> rw[] >> gvs[]
QED

Theorem immutable_fixed_spine[local]:
  !e env cx es src id path t root_ty itv.
    (well_typed_expr env e \/ (?vt. type_place_expr env e = SOME vt)) /\
    runtime_consistent env cx es /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    eval_expr cx e es = (INL (PlaceR (ImmutablePlace src id path)),t) /\
    FLOOKUP env.bare_globals (src,id) = SOME root_ty /\
    evaluate_type (get_tenv cx) root_ty = SOME itv /\
    ~base_through_dynarray e ==>
    fixed_shape_path itv path
Proof
  measureInduct_on `expr_size e` >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule evaluated_immutable_spine >> strip_tac >> gnvs[fixed_shape_path_def]
  >- suspend "subscript"
  >> suspend "attribute"
QED

Resume immutable_fixed_spine[subscript]:
  `well_typed_expr env obj \/ (?vt. type_place_expr env obj = SOME vt)` by
    (drule constSubstCorrectTheory.frame_subscript_typing >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr obj)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Subscript _ _ _))` mp_tac >>
     simp[NoAsms, vyperTypeCallGraphTheory.int_calls_expr_def] >>
     metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left]) >>
  `~base_through_dynarray obj /\ ~(?et n. expr_type obj = ArrayT et (Dynamic n))` by
    (Cases_on `expr_type obj` >> gvs[base_through_dynarray_def] >>
     rename1 `expr_type obj = ArrayT _ bd` >> Cases_on `bd` >> gvs[]) >>
  `fixed_shape_path itv pre` by
    (first_x_assum (qspec_then `obj` mp_tac) >> simp[expr_size_def] >> metis_tac[]) >>
  `?tv. evaluate_type (get_tenv cx) (expr_type obj) = SOME tv /\
        subscripts_type itv pre = SOME tv` by metis_tac[immutable_annotated_path] >>
  `?tv'. subscripts_type itv (pre ++ [ValueSubscript key]) = SOME tv'` by
    metis_tac[immutable_annotated_path] >>
  irule fixed_shape_path_snoc >>
  metis_tac[immutable_path_container_not_dynamic]
QED

Resume immutable_fixed_spine[attribute]:
  `well_typed_expr env obj` by
    (qpat_assum `well_typed_expr env (Attribute _ _ _) \/ _` mp_tac >>
     simp[NoAsms, cj 8 well_typed_expr_def,
          constSubstCorrectTheory.frame_place_expr_other]) >>
  `call_evaluation_safe cx (int_calls_expr obj) /\ ~base_through_dynarray obj` by
    fs[vyperTypeCallGraphTheory.int_calls_expr_def, base_through_dynarray_def] >>
  `fixed_shape_path itv pre` by
    (first_x_assum (qspec_then `obj` mp_tac) >> simp[expr_size_def] >> metis_tac[]) >>
  `?tv. subscripts_type itv pre = SOME tv` by metis_tac[immutable_annotated_path] >>
  `?tv'. subscripts_type itv (pre ++ [AttrSubscript fld]) = SOME tv'` by
    metis_tac[immutable_annotated_path] >>
  `~(?et n. tv = ArrayTV et (Dynamic n))` by
    (strip_tac >>
     gvs[vyperPlaceStatePreservationTheory.subscripts_type_append,
         subscripts_type_def, subscript_type_def]) >>
  irule fixed_shape_path_snoc >> metis_tac[]
QED
Finalise immutable_fixed_spine

Theorem live_immutable_path_after_index[local]:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env obj es /\
  eval_expr cx obj es = (INL (PlaceR (ImmutablePlace src id path)),mid) /\
  read_result cx (PlaceR (ImmutablePlace src id path)) mid = (INL saved,mid) /\
  FLOOKUP env.bare_globals (src,id) = SOME root_ty /\
  evaluate_type (get_tenv cx) root_ty = SOME itv /\
  is_ArrayT (expr_type obj) /\ ~subscript_reads_base cx obj idx /\
  expr_body_pre cenv cx env idx ix /\ ix.immutables = mid.immutables /\
  eval_expr cx idx ix = (res,fin) /\ expr_sim_inv cenv cx env fin ==>
  !rt rv. FLOOKUP (case ALOOKUP fin.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables src imms) id = SOME (rt,rv) ==>
    ?v. evaluate_subscripts rt rv path = INL v
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >> disch_tac >>
  Cases_on `base_through_dynarray obj`
  >- (`~supported_expr_exists (const_name_root cx) obj` by metis_tac[expr_body_pre_static_facts] >>
      drule_then assume_tac body_inv_contract >>
      drule_then strip_assume_tac body_inv_main_code >>
      drule_all_then assume_tac eval_expr_immutable_root_nonconstant >>
      `~cx_const_name_mods [(NONE,tops)] (src,id)` by
        (qpat_assum `cx_tops cx = tops` (SUBST1_TAC o SYM) >>
         fs[cx_const_name_split_def]) >>
      `expr_body_pre_mods [(NONE,tops)] cenv cx env idx ix` by
        metis_tac[body_inv_expr_body_pre_mods] >>
      drule_all_then strip_assume_tac immutable_no_copy_dynamic_frame_mods >>
      qexists `saved` >>
      qpat_x_assum `read_result cx _ mid = _` mp_tac >>
      Cases_on `ALOOKUP mid.immutables cx.txn.target` >>
      gvs[read_result_def, read_place_def, get_immutables_def,
          get_address_immutables_def, bind_def, lift_option_type_def,
          lift_sum_def, return_def, raise_def, AllCaseEqs()] >>
      Cases_on `evaluate_subscripts rt rv path` >> simp[return_def, raise_def]) >>
  `fixed_shape_path itv path` by
    (irule immutable_fixed_spine >> goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     qexistsl [`env`,`root_ty`] >>
     qpat_assum `expr_body_pre cenv cx env obj es`
       (strip_assume_tac o REWRITE_RULE [expr_body_pre_split_def, expr_body_pre_mods_def]) >>
     fs[expr_sim_inv_def, vyperTypeExprSoundnessTheory.runtime_consistent_def]) >>
  drule_all live_immutable_root_current >> strip_tac >> gvs[] >>
  irule current_immutable_fixed_path_live >> metis_tac[]
QED

Theorem live_immutable_index_cut_view[local]:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env obj es /\ expr_body_pre cenv cx env idx mid /\
  expr_type obj = ArrayT et bd /\ post_value_type cenv obj = expr_type obj /\
  ~subscript_reads_base cx obj idx /\
  eval_expr cx obj es = (INL (PlaceR (ImmutablePlace src id path)),mid) /\
  eval_expr cx idx (mid with gas_obs := gs) = (INL ir,fin) /\
  vv_post H ctx func cenv cx obj es sa sb s0 mid
    (PlaceR (ImmutablePlace src id path)) (LocatedValue (ArrayT et bd) p) u /\
  expr_post H ctx func cenv cx idx (mid with gas_obs := gs) sb sc u fin key iop s /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  (!l. p.ptr_operand <> Label l) ==>
  ?etv off itv k iv av.
    evaluate_type (get_tenv cx) et = SOME etv /\
    src = cenv.ce_module /\ p.ptr_location = LocCode /\
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP fin.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables src imms) id = SOME (itv,iv) /\
    mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
    off + type_memory_size itv < dimword (:256) /\
    eval_operand p.ptr_operand s = SOME (n2w (off+k)) /\
    evaluate_subscripts itv iv path = INL (ArrayV av) /\
    value_has_type (ArrayTV etv bd) (ArrayV av) /\ well_formed_type_value (ArrayTV etv bd) /\
    read_result cx (PlaceR (ImmutablePlace src id path)) fin = (INL (ArrayV av),fin) /\
    vv_place_ptr cenv cx fin s (PlaceR (ImmutablePlace src id path))
      (LocatedValue (ArrayT et bd) p) /\
    immutable_holds cenv cx (ArrayT et bd)
      (PlaceR (ImmutablePlace src id path)) (n2w (off+k)) fin s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac expr_body_pre_place_metadata >>
  `?etv. evaluate_type (get_tenv cx) et = SOME etv /\
     evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
     runtime_place_typed cx mid (ImmutablePlace src id path) (ArrayTV etv bd)` by
    (qpat_x_assum `evaluate_type _ (expr_type obj) = _` mp_tac >>
     simp[Once vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >> simp[vyperValueTheory.evaluate_type_def]) >>
  `expr_body_pre cenv cx env idx (mid with gas_obs := gs)` by simp[] >>
  drule_all_then strip_assume_tac exprSimSourceTheory.expr_body_pre_eval_result >>
  `expr_sim_inv cenv cx env mid /\ expr_sim_inv cenv cx env fin` by
    metis_tac[cj 1 exprSimSourceTheory.expr_body_pre_eval_result] >>
  `~cx_const_name cx (src,id)` by
    (irule eval_expr_immutable_root_nonconstant >>
     goal_assum (drule_at Any) >> metis_tac[expr_body_pre_static_facts]) >>
  `stmt_state_rel H ctx func cenv cx fin s` by fs[expr_post_def] >>
  `vv_place_ptr cenv cx mid u (PlaceR (ImmutablePlace src id path))
     (LocatedValue (ArrayT et bd) p)` by fs[vv_post_def] >>
  `!w. eval_operand p.ptr_operand u = SOME w ==> eval_operand p.ptr_operand s = SOME w` by
    (rpt strip_tac >> irule exprBopSimPropsTheory.eval_operand_frame >>
     simp[] >> qexistsl [`sb`,`u`] >> simp[] >> drule_all expr_post_frame >> simp[wb_frame_def]) >>
  `!rt rv. FLOOKUP (case ALOOKUP fin.immutables cx.txn.target of
      NONE => FEMPTY | SOME imms => get_source_immutables src imms) id = SOME (rt,rv) ==>
      ?v. evaluate_subscripts rt rv path = INL v` by
    (qpat_assum `vv_place_ptr _ _ _ _ _ _` (strip_assume_tac o SRULE [vv_place_ptr_def]) >>
     `?root_ty. FLOOKUP env.bare_globals (src,id) = SOME root_ty /\
               evaluate_type (get_tenv cx) root_ty = SOME itv` by
       (qpat_x_assum `src = cenv.ce_module` SUBST_ALL_TAC >>
        drule_then (irule_at Any) (cj 2 live_immutable_captured_root) >>
        simp[] >> goal_assum (drule_at Any) >> simp[]) >>
     `?saved. read_result cx (PlaceR (ImmutablePlace src id path)) mid = (INL saved,mid)` by
       fs[vv_post_def, vv_holds_def, immutable_holds_def] >>
     drule_at (Pat `eval_expr _ _ _ = (INL (PlaceR _),_)`) live_immutable_path_after_index >>
     disch_then (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     simp[vyperASTTheory.is_ArrayT_def] >> metis_tac[]) >>
  drule_at (Pat `vv_place_ptr _ _ _ _ _ _`) live_immutable_captured_array_view >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`etv`,`env`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `?av. v = ArrayV av` by (Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]) >>
  gvs[] >> metis_tac[]
QED

(* Use the existing LocCode load safety proof and keep the raw execution and
   pointer execution at the same endpoint. Only the counted cursor moves. *)
Theorem live_ctor_header_origin[local]:
  compile_imm_load_word T imm arg sa = (op,sb) /\
  copy_old_operand sa arg /\ eval_operand arg s = SOME a /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\ w2n a + 32 <= lo /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
     copy_old_operand sa region /\ op_taint tn region = {} /\
     op_prov G region = NONE) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  lo <= s.vs_alloca_next /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tnf t.
    copy_runtime_frame sa s sb t /\ t.vs_memory = s.vs_memory /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_prev_bb = s.vs_prev_bb /\
    ~t.vs_halted /\
    eval_operand op t = SOME (mload (w2n a) s) /\
    op_taint tnf op = mem_word_taint tn.t_mem (w2n a) /\
    op_prov Gf op = NONE /\ copy_old_operand sb op /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tnf p t n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `D = <|d_stor := (\a st. {}); d_trans := (\a st. {});
                     d_imm := (\im. {}); d_ret := (\ret. {})|>` >>
  drule_all code_copy_ctor_load >>
  disch_then (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule rest_word_ptr_load_mem_ok >> qexistsl [`a`,`arg`,`T`,`imm`,`LocCode`,`op`] >>
     simp[contextTheory.compile_ptr_load_def] >>
     Cases_on `imm` >> fs[] >> rpt strip_tac >> decide_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
               ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (drule copy_ctor_load_shape >> simp[listTheory.EVERY_MEM] >>
     rpt strip_tac >> first_x_assum drule >>
     strip_tac >> gvs[venomInstTheory.is_terminator_def]) >>
  `t.vs_memory = s.vs_memory` by
    (rename1 `copy_runtime_frame sa s sb t` >>
     drule copy_ctor_load >> disch_then (qspecl_then [`s`,`a`] mp_tac) >>
     (impl_tac >- metis_tac[]) >> fs[copy_runtime_frame_def]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK t /\
   sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    fs[copy_runtime_frame_def,exprLoweringPropsTheory.same_blocks_def] >>
  `t.vs_current_bb = sb.cs_current_bb /\ t.vs_prev_bb = s.vs_prev_bb /\
   ~t.vs_halted` by
    (drule run_inst_seq_preserves_entry_control >>
     (impl_tac >- fs[listTheory.EVERY_MEM]) >> simp[]) >>
  `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf` by
    (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)` by
    (irule emitted_origin_ptr_path >> simp[] >>
     qexistsl [`emitted_insts sa sb`,`sa`] >> simp[] >>
     rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     drule copy_ctor_load_shape >> simp[listTheory.EVERY_APPEND] >>
     strip_tac >> gvs[]) >>
  qexistsl [`Gf`,`tnf`,`t`] >> simp[immutable_copy_read_def] >>
  drule gas_origin_ptr_path_dead_mono >> simp[Abbr `D`]
QED

(* Literal lengths and the two code loaders have the same interface to the
   bounds check.  In constructor mode the header is a safe memory read. *)
Theorem live_code_length_joint[local]:
  (if dyn then compile_imm_load_word ctor imm arg
   else comp_return (Lit (n2w cnt))) sa = (len,sb) /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (dyn ==> eval_operand arg s = SOME a /\ copy_old_operand sa arg /\
    op_taint tn arg = {} /\ op_prov G arg = NONE /\
    immutable_copy_read ctor a s = n2w cnt /\
    (ctor ==> w2n a + 32 <= lo /\ mem_word_taint tn.t_mem (w2n a) = {} /\
      (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
         copy_old_operand sa region /\ op_taint tn region = {} /\ op_prov G region = NONE)) /\
    (~ctor ==> w2n a <= LENGTH s.vs_data_section)) ==>
  ?Gf tnf t.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    eval_operand len t = SOME (n2w cnt) /\ op_taint tnf len = {} /\ op_prov Gf len = NONE /\
    copy_old_operand sb len /\ (!l. len <> Label l) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_immutables = s.vs_immutables /\ t.vs_fmp = s.vs_fmp /\
    t.vs_initial_fmp = s.vs_initial_fmp /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
      stmt_state_rel H ctx func cenv cx es t)
Proof
  Cases_on `dyn` >> simp[compileEnvTheory.comp_return_def] >>
  disch_then (map_every assume_tac o CONJUNCTS)
  >- (Cases_on `ctor` >- suspend "constructor" >> suspend "runtime") >>
  gvs[] >> qexistsl [`G`,`tn`,`s`] >>
  simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules,
       venomStateTheory.eval_operand_def, copy_old_operand_def,
       ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def]
QED

Resume live_code_length_joint[constructor]:
  gvs[immutable_copy_read_def] >>
  drule_all live_ctor_header_origin >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rename1 `copy_runtime_frame sa s sb raw` >>
  qexistsl [`Gf`,`tnf`,`raw with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  `?v. len = Var v` by
    (Cases_on `imm`
     >- (gvs[contextTheory.compile_imm_load_word_def] >>
         drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[])
     >> drule contextTheory.compile_imm_load_word_ctor_result >> simp[]) >>
  `raw.vs_current_bb = s.vs_current_bb` by fs[copy_runtime_frame_def, exprLoweringPropsTheory.same_blocks_def] >>
  `raw with vs_inst_idx := LENGTH sb.cs_current_insts =
    s with <|vs_vars := raw.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|>` by
    fs[copy_runtime_frame_def, copy_static_def, venomStateTheory.venom_state_component_equality] >>
  `!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
      stmt_state_rel H ctx func cenv cx es (raw with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (rpt strip_tac >> irule stmt_state_rel_readonly_vars_pc >> qexistsl [`s`,`sa`] >>
     fs[copy_runtime_frame_def, venomStateTheory.lookup_var_def]) >>
  fs[copy_runtime_frame_def, copy_static_def, venomStateTheory.venom_state_component_equality,
     venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]
QED

Resume live_code_length_joint[runtime]:
  gvs[immutable_copy_read_def] >>
  drule_all compile_imm_load_word_runtime_joint_frame >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qpat_x_assum `!G. ?out Gf tnf sf. _` (qspec_then `G` strip_assume_tac) >>
  qexistsl [`Gf`,`tnf`,`sf`] >>
  `not_fresh_at sb out` by
    (fs[contextTheory.compile_imm_load_word_runtime] >>
     drule emitHelperPropsTheory.emitted_insts_emit_op >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[]) >>
  gvs[venomStateTheory.eval_operand_def, copy_old_operand_def]
QED
Finalise live_code_length_joint

(* The final code-address calculation is independent of the length loader. *)
Theorem live_code_element_joint[local]:
  array_elem_ptr base_op idx dyn 32 esz sa = (dst,sb) /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  copy_old_operand sa base_op /\ copy_old_operand sa idx /\
  (!l. base_op <> Label l /\ idx <> Label l) /\
  eval_operand base_op s = SOME a /\ op_taint tn base_op = {} /\ op_prov G base_op = NONE /\
  eval_operand idx s = SOME (n2w i) /\ op_taint tn idx = {} /\ op_prov G idx = NONE ==>
  ?Gf tnf sf.
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sf,Gf,tnf)) /\
    sf.vs_current_bb = sb.cs_current_bb /\ sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand dst sf = SOME (a + n2w ((if dyn then 32 else 0) + i * esz)) /\
    op_taint tnf dst = {} /\ op_prov Gf dst = NONE /\
    sf.vs_immutables = s.vs_immutables /\ sf.vs_memory = s.vs_memory /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel H ctx func cenv cx es sf)
Proof
  Cases_on `dyn` >>
  simp[exprSimArrayIndexTheory.array_elem_ptr_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_return_def, copy_old_operand_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(!l. base_op <> Label l) /\ (!l. idx <> Label l)` by simp[]
  >- suspend "dynamic" >> suspend "fixed"
QED

Resume live_code_element_joint[dynamic]:
  Cases_on `emit_op ADD [base_op;Lit 32w] sa` >> gvs[] >>
  drule_all_then strip_assume_tac loweringShapeRulesTheory.emit_op_facts >> gvs[] >>
  pairarg_tac >> gvs[] >>
  qpat_assum `emit_op MUL _ _ = _` (strip_assume_tac o MATCH_MP loweringShapeRulesTheory.emit_op_facts) >> gvs[] >>
  qpat_assum `emit_op ADD [Var _;Var _] _ = _` (strip_assume_tac o MATCH_MP loweringShapeRulesTheory.emit_op_facts) >>
  gvs[] >>
  drule_all code_dynamic_address_joint_frame >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl [`Gf`,`tnf`,`sf`] >> simp[venomStateTheory.eval_operand_def]
QED

Resume live_code_element_joint[fixed]:
  pairarg_tac >> gvs[] >>
  qpat_assum `emit_op MUL _ _ = _` (strip_assume_tac o MATCH_MP loweringShapeRulesTheory.emit_op_facts) >>
  gvs[] >>
  drule_then strip_assume_tac (Q.SPEC `ADD` loweringShapeRulesTheory.emit_op_facts) >>
  gvs[] >>
  drule_all scalar_mul_add_joint_frame >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl [`Gf`,`tnf`,`sf`] >> simp[venomStateTheory.eval_operand_def]
QED
Finalise live_code_element_joint

Theorem live_code_compiler_cuts[local]:
  compile_array_subscript arg idx dyn cnt 32 esz sgn
    (compile_ptr_load ctor imm LocCode) sa = (dst,sb) /\
  fn_has_code sa sb func ==>
  ?len sh sk.
    (if dyn then compile_imm_load_word ctor imm arg
     else comp_return (Lit (n2w cnt))) sa = (len,sh) /\
    array_bounds_check idx len sgn sh = ((),sk) /\
    array_elem_ptr arg idx dyn 32 esz sk = (dst,sb) /\
    fn_has_code sa sh func /\ fn_has_code sh sk func /\ fn_has_code sk sb func /\
    sa.cs_next_var <= sh.cs_next_var /\ sh.cs_next_var <= sk.cs_next_var
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[exprSimArrayIndexTheory.compile_array_subscript_split,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       contextTheory.compile_ptr_load_def] >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `array_bounds_check idx len sgn sh = ((),sk)` >>
  `ci_mono sa sh` by
    (Cases_on `dyn` >> gvs[compileEnvTheory.comp_return_def,
         exprLoweringPropsTheory.ci_mono_refl] >>
     qspecl_then [`ctor`,`imm`,`LocCode`,`arg`,`sa`] mp_tac
       exprLoweringPropsTheory.ci_mono_compile_ptr_load >>
     simp[contextTheory.compile_ptr_load_def]) >>
  `ci_mono sh sk` by
    (qpat_assum `array_bounds_check _ _ _ _ = _` mp_tac >>
     qsuff_tac `ci_mono sh (SND (array_bounds_check idx len sgn sh))`
     >- simp[] >>
     Cases_on `sgn` >> simp[NoAsms, exprSimArrayIndexTheory.array_bounds_check_def,
                                    exprSimArrayIndexTheory.array_bounds_valid_def] >>
     rpt (irule exprLoweringPropsTheory.ci_mono_bind >> conj_tac >> rpt gen_tac >>
          simp[NoAsms, exprLoweringPropsTheory.ci_mono_emit_op,
               exprLoweringPropsTheory.ci_mono_emit_void,
               exprLoweringPropsTheory.ci_mono_comp_return])) >>
  `ci_mono sk sb` by
    (qpat_assum `array_elem_ptr _ _ _ _ _ _ = _` mp_tac >>
     qsuff_tac `ci_mono sk (SND (array_elem_ptr arg idx dyn 32 esz sk))`
     >- simp[] >>
     Cases_on `dyn` >> simp[NoAsms, exprSimArrayIndexTheory.array_elem_ptr_def] >>
     rpt (irule exprLoweringPropsTheory.ci_mono_bind >> conj_tac >> rpt gen_tac >>
          simp[NoAsms, exprLoweringPropsTheory.ci_mono_emit_op,
               exprLoweringPropsTheory.ci_mono_comp_return])) >>
  fs[exprLoweringPropsTheory.ci_mono_def] >>
  metis_tac[fragExecTheory.fn_has_code_split,
            compileEnvTheory.cs_extends_trans]
QED

(* The length read, bounds check and address arithmetic form one no-mark
   path.  The abort branch stops before executing the address arithmetic. *)
Theorem live_code_select_joint:
  compile_array_subscript arg idx dyn (if dyn then 0 else cnt) 32 esz sgn
    (compile_ptr_load ctor imm LocCode) sa = (dst,sb) /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  eval_operand arg s = SOME a /\ copy_old_operand sa arg /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\
  eval_operand idx s = SOME (n2w i) /\ copy_old_operand sa idx /\
  op_taint tn idx = {} /\ op_prov G idx = NONE /\
  (!l. arg <> Label l /\ idx <> Label l) /\
  (dyn ==> immutable_copy_read ctor a s = n2w cnt /\
    (ctor ==> w2n a + 32 <= lo /\ mem_word_taint tn.t_mem (w2n a) = {} /\
      (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
         copy_old_operand sa region /\ op_taint tn region = {} /\ op_prov G region = NONE)) /\
    (~ctor ==> w2n a <= LENGTH s.vs_data_section)) ==>
  ?Gf tnf q.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      ((if idx_in_range sgn (n2w i) (n2w cnt) then OK q else Abort Revert_abort q),Gf,tnf)) /\
    q.vs_immutables = s.vs_immutables /\ q.vs_memory = s.vs_memory /\
    q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
    q.vs_fmp = s.vs_fmp /\ q.vs_accounts = s.vs_accounts /\
    q.vs_transient = s.vs_transient /\ q.vs_call_ctx = s.vs_call_ctx /\
    q.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v q = lookup_var v s /\
      FLOOKUP Gf v = FLOOKUP G v /\ op_taint tnf (Var v) = op_taint tn (Var v)) /\
    (idx_in_range sgn (n2w i) (n2w cnt) ==>
      q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~q.vs_halted /\
      eval_operand dst q = SOME (a + n2w ((if dyn then 32 else 0) + i * esz)) /\
      op_taint tnf dst = {} /\ op_prov Gf dst = NONE /\
      !(H:(bool # bytes32 # type_value) list # num list) cenv cx es.
        stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
        stmt_state_rel H ctx func cenv cx es q)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all live_code_compiler_cuts >>
  simp[boolTheory.COND_EXPAND_IMP] >> strip_tac >>
  `dyn ==> eval_operand arg s = SOME a /\ copy_old_operand sa arg /\
    op_taint tn arg = {} /\ op_prov G arg = NONE /\
    immutable_copy_read ctor a s = n2w cnt /\
    (ctor ==> w2n a + 32 <= lo /\ mem_word_taint tn.t_mem (w2n a) = {} /\
      (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
        copy_old_operand sa region /\ op_taint tn region = {} /\ op_prov G region = NONE)) /\
    (~ctor ==> w2n a <= LENGTH s.vs_data_section)` by simp[] >>
  drule_all (INST_TYPE [Type.alpha |-> ``:256``] live_code_length_joint) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`Gh`,`tnh`,`h`] strip_assume_tac)) >>
  `!l. arg <> Label l` by metis_tac[] >>
  `!l. idx <> Label l` by metis_tac[] >>
  `eval_operand arg h = SOME a /\ op_taint tnh arg = {} /\ op_prov Gh arg = NONE` by
    (Cases_on `arg` >> fs[copy_old_operand_def, venomStateTheory.eval_operand_def,
      ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def] >> metis_tac[]) >>
  `copy_old_operand sh idx /\ copy_old_operand sh arg` by
    metis_tac[copy_old_operand_mono] >>
  `eval_operand idx h = SOME (n2w i) /\ op_taint tnh idx = {} /\ op_prov Gh idx = NONE` by
    (Cases_on `idx` >> fs[copy_old_operand_def, venomStateTheory.eval_operand_def,
      ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def] >> metis_tac[]) >>
  `!v. idx = Var v \/ len = Var v ==> not_fresh_at sh v` by
    fs[copy_old_operand_def, boolTheory.DISJ_IMP_THM] >>
  `!l. idx <> Label l /\ len <> Label l` by simp[] >>
  `allocas_from lo h` by (simp[ptrDisciplineTheory.allocas_from_def] >> metis_tac[ptrDisciplineTheory.allocas_from_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp h` by
    (`allocas_below_fmp h <=> allocas_below_fmp s` by
       asm_rewrite_tac[ptrDisciplineTheory.allocas_below_fmp_def] >>
     qpat_assum `allocas_below_fmp h <=> allocas_below_fmp s`
       (fn th => PURE_REWRITE_TAC [th]) >>
     first_assum ACCEPT_TAC) >>
  Cases_on `idx_in_range sgn (n2w i) (n2w cnt)` >> simp[]
  >- suspend "in_range" >> suspend "out_of_range"
QED

Resume live_code_select_joint[in_range]:
  drule_all (INST_TYPE [Type.alpha |-> ``:256``] array_bounds_check_read_only_joint_ok_frame) >>
  disch_then (qspec_then `PG` (qx_choosel_then [`Gk`,`tnk`,`k`] strip_assume_tac)) >>
  `copy_old_operand sk idx /\ copy_old_operand sk arg` by
    metis_tac[copy_old_operand_mono] >>
  `eval_operand idx k = SOME (n2w i) /\ op_taint tnk idx = {} /\ op_prov Gk idx = NONE` by
    (Cases_on `idx` >> fs[copy_old_operand_def, venomStateTheory.eval_operand_def,
      ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def] >> metis_tac[]) >>
  `eval_operand arg k = SOME a /\ op_taint tnk arg = {} /\ op_prov Gk arg = NONE` by
    (Cases_on `arg` >> fs[copy_old_operand_def, venomStateTheory.eval_operand_def,
      ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def] >> metis_tac[]) >>
  `allocas_from lo k` by (simp[ptrDisciplineTheory.allocas_from_def] >> metis_tac[ptrDisciplineTheory.allocas_from_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp k` by
    (`allocas_below_fmp k <=> allocas_below_fmp h` by
       asm_rewrite_tac[ptrDisciplineTheory.allocas_below_fmp_def] >>
     qpat_assum `allocas_below_fmp k <=> allocas_below_fmp h`
       (fn th => PURE_REWRITE_TAC [th]) >>
     first_assum ACCEPT_TAC) >>
  drule_all (INST_TYPE [Type.alpha |-> ``:256``] live_code_element_joint) >>
  disch_then (qspec_then `PG` (qx_choosel_then [`Gq`,`tnq`,`q`] strip_assume_tac)) >>
  qexistsl [`Gq`,`tnq`,`q`] >> simp[] >>
  conj_tac
  >- (gen_tac >> metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]) >>
  `!v. not_fresh_at sa v ==> not_fresh_at sh v /\ not_fresh_at sk v` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac >- metis_tac[] >> rpt strip_tac >>
  `local_ptrs_reserved cenv sh /\ local_ptrs_reserved cenv sk` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  metis_tac[]
QED

Resume live_code_select_joint[out_of_range]:
  drule_all array_bounds_check_joint_oob_frame >>
  disch_then (qspec_then `PG` (qx_choosel_then [`Gq`,`tnq`,`q`] strip_assume_tac)) >>
  qexistsl [`Gq`,`tnq`,`q`] >> simp[] >>
  conj_tac
  >- (gen_tac >> metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]) >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED
Finalise live_code_select_joint

Theorem current_immutable_dynamic_header:
  stmt_state_rel H ctx func cenv cx fin s /\
  immutable_holds cenv cx (ArrayT et (Dynamic cap)) raw w fin s /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) (ArrayT et (Dynamic cap)) = SOME (ArrayTV etv (Dynamic cap)) /\
  read_result cx raw fin = (INL (ArrayV av),fin) /\
  value_has_type (ArrayTV etv (Dynamic cap)) (ArrayV av) /\
  (cenv.ce_is_ctor ==>
    w2n w + type_memory_size (ArrayTV etv (Dynamic cap)) <= lo /\
    !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV av) (w2n w) m) ==>
  immutable_copy_read cenv.ce_is_ctor w s =
    n2w (array_length (ArrayTV etv (Dynamic cap)) av) /\
  (cenv.ce_is_ctor ==> w2n w + 32 <= lo /\ mem_word_taint tn.t_mem (w2n w) = {}) /\
  (~cenv.ce_is_ctor ==> w2n w <= LENGTH s.vs_data_section)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `cenv.ce_is_ctor` >> gvs[immutable_copy_read_def]
  >- (Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def] >>
      `val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV l))
          (w2n w) s.vs_memory` by simp[bodyPtrDefsTheory.mem_agree_outside_def] >>
      simp[vyperValueOperationTheory.array_length_def] >> rpt conj_tac
      >- fs[valueEncodingPropsTheory.val_in_memory_dynarray,
            valueEncodingPropsTheory.mem_word_at_eq_mload]
      >- fs[valueEncodingTheory.type_memory_size_def] >>
      metis_tac[bodyPtrBopInMemoryContentsTheory.dynarray_memory_header_clean]) >>
  conj_tac
  >- (drule_all exprSimSubscriptArraySuffixTheory.framed_array_code_length_view >> simp[]) >>
  drule_all exprSimBopRestWordLoadSafetyTheory.rest_word_immutable_region_bound >> simp[]
QED


(* The selected immutable place supplies its own value facts. Compose only
   the base and index writeback and purity facts from their actual runs. *)
Theorem live_immutable_selected_post[local]:
  stmt_state_rel H ctx func cenv cx es s0 /\
  vv_post H ctx func cenv cx obj es sa sm s0 mid raw bvv u /\
  expr_post H ctx func cenv cx idx (mid with gas_obs := gs) sm sn u fin key iop s /\
  is_word_type (expr_type idx) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  copy_old_operand sn iop /\ (!l. iop <> Label l) /\
  (!x. not_fresh_at sn x ==> lookup_var x q = lookup_var x s) /\
  q.vs_allocas = s.vs_allocas /\ q.vs_memory = s.vs_memory /\
  stmt_state_rel H ctx func cenv cx fin q /\
  vv_holds cenv cx et (PlaceR (ImmutablePlace src id path))
    (LocatedValue et (mk_ptr dst LocCode)) fin q /\
  vv_place_ptr cenv cx fin q (PlaceR (ImmutablePlace src id path))
    (LocatedValue et (mk_ptr dst LocCode)) ==>
  vv_post H ctx func cenv cx (Subscript et obj idx) es sa sb s0 fin
    (PlaceR (ImmutablePlace src id path)) (LocatedValue et (mk_ptr dst LocCode)) q
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_post H ctx func cenv cx idx mid sm sn u fin key iop q` by
    (irule exprSimSubscriptArrayEndpointTheory.word_expr_post_readonly_tail >>
     simp[] >> qexistsl [`s`,`sn`] >> fs[exprSimSubscriptArrayComposeTheory.expr_post_initial_gas,
                                copy_old_operand_def]) >>
  `wb_frame cenv es mid sa s0 u` by (fs[vv_post_def, wb_frame_def] >> metis_tac[]) >>
  `wb_frame cenv mid fin sm u q` by metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `wb_frame cenv es fin sa s0 q` by (drule_all exprSimWordArgsTheory.wb_frame_trans >> simp[]) >>
  `~expr_has_effect obj /\ ~expr_has_effect idx ==> pure_frame cenv func es sa s0 q` by
    (strip_tac >>
     `pure_frame cenv func es sa s0 u` by fs[vv_post_def] >>
     `pure_frame cenv func mid sm u q` by metis_tac[exprSimWordArgsTheory.expr_post_pure_frame] >>
     irule exprSimPropsTheory.pure_frame_trans >> simp[] >>
     qexistsl [`mid`,`sm`,`u`] >> fs[wb_frame_def] >> metis_tac[]) >>
  `storage_well_formed_on cx fin (FST H)` by fs[expr_post_def] >>
  irule exprSimHashTheory.vv_post_frame_intro >>
  simp[vyperASTTheory.expr_type_def, vv_at_def, vv_storage_live_def,
       contextTheory.mk_ptr_def, expr_has_effect_thm] >>
  fs[contextTheory.mk_ptr_def]
QED

Theorem live_immutable_selected_facts[local]:
  src = cenv.ce_module /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP fin.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables src imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  read_result cx (PlaceR (ImmutablePlace src id path)) fin = (INL (ArrayV av),fin) /\
  immutable_holds cenv cx (ArrayT et bd) (PlaceR (ImmutablePlace src id path))
    (n2w (off+k)) fin s /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  eval_operand dst q = SOME (n2w (off+k) + n2w
    ((case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv)) ==>
  select_result cx (ArrayT et bd) (PlaceR (ImmutablePlace src id path)) (ValueSubscript (IntV i)) fin =
    (INL (PlaceR (ImmutablePlace src id (path ++ [ValueSubscript (IntV i)]))),fin) /\
  read_result cx (PlaceR (ImmutablePlace src id (path ++ [ValueSubscript (IntV i)]))) fin = (INL v,fin) /\
  vv_holds cenv cx et (PlaceR (ImmutablePlace src id (path ++ [ValueSubscript (IntV i)])))
    (LocatedValue et (mk_ptr dst LocCode)) fin q /\
  vv_place_ptr cenv cx fin q (PlaceR (ImmutablePlace src id (path ++ [ValueSubscript (IntV i)])))
    (LocatedValue et (mk_ptr dst LocCode))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `src = cenv.ce_module` SUBST_ALL_TAC >>
  `evaluate_subscripts (ArrayTV etv bd) (ArrayV av) [ValueSubscript (IntV i)] = INL v` by
    simp[evaluate_subscripts_def] >>
  drule_all live_immutable_select >> disch_then (qspec_then `ArrayT et bd` strip_assume_tac) >>
  simp[] >> conj_tac
  >- (simp[vv_holds_def, contextTheory.mk_ptr_def] >>
      `well_formed_type_value etv` by
        (drule vyperTypeValuesTheory.evaluate_type_well_formed_type_value >> simp[]) >>
      `value_has_type etv v` by
        (drule vyperAssignPreservesTypeTheory.array_index_has_type >>
         disch_then (qspecl_then [`etv`,`bd`] mp_tac) >> simp[]) >>
      drule_all exprSimSubscriptArrayFramedTheory.immutable_holds_array_element >>
      simp[immutable_holds_def] >> strip_tac >>
      qexistsl [`name`,`off'`,`itv'`,`iv'`,`k'`,`v`] >> simp[]) >>
  simp[contextTheory.mk_ptr_def] >>
  irule (SIMP_RULE (srw_ss()) [contextTheory.mk_ptr_def]
    (Q.SPEC `mk_ptr dst LocCode`
      (Q.GEN `p` (SPEC_ALL live_immutable_element_place_ptr)))) >>
  simp[] >> metis_tac[]
QED

(* The successful index cut, before executing the immutable bounds suffix. *)
Theorem subscript_live_immutable_select_full:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Subscript et obj idx) es /\
  expr_type obj = ArrayT et bd /\ post_value_type cenv obj = expr_type obj /\
  ~subscript_reads_base cx obj idx /\
  eval_expr cx obj (es with gas_obs := bgs) = (INL (PlaceR (ImmutablePlace src id path)),mid) /\
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs) = (INL key,fin) /\
  storage_trace_domain cx st0 fin.storage_trace /\ fin.gas_obs = [] /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  copy_old_operand sm p.ptr_operand /\ (!l. p.ptr_operand <> Label l) /\
  copy_old_operand sn iop /\ (!l. iop <> Label l) /\
  ptr_vv_ok cx (post_value_type cenv obj) (PlaceR (ImmutablePlace src id path))
    (LocatedValue (ArrayT et bd) p) mid Gb tnb u /\
  ptr_val_ok cx (post_value_type cenv idx) key iop Gi tni s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gb tnb /\
  ghost_kept_at lo cenv mid sm Gb tnb u Gi tni /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T) (case bd of Fixed n => n | Dynamic _ => 0)
    32 (type_memory_bytes cenv et) (is_signed_type (expr_type idx))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca p.ptr_location) sn = (dst,sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    vv_post H ctx func cenv cx obj es sa sm s0 mid
      (PlaceR (ImmutablePlace src id path)) (LocatedValue (ArrayT et bd) p) u /\
    expr_post H ctx func cenv cx idx (mid with gas_obs := gs) sm sn u fin key iop s /\
    ghost_inv_at (DF H) lo d cenv cx fin Gi tni s) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (select_result cx (ArrayT et bd) (PlaceR (ImmutablePlace src id path)) (ValueSubscript key))
    (fin,s,Gi,tni)
    (\H res ee Gz tnz z. ?r. res = INL r /\
       vv_post H ctx func cenv cx (Subscript et obj idx) es sa sb s0 ee
         r (LocatedValue et (mk_ptr dst LocCode)) z /\
       vv_store_bound cx (post_value_type cenv (Subscript et obj idx))
         (lowered_value_type cenv (Subscript et obj idx)) ee
         r (LocatedValue et (mk_ptr dst LocCode)) z /\
       z.vs_current_bb = sb.cs_current_bb /\
       z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func z /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
       s0.vs_alloca_next <= z.vs_alloca_next /\
       ghost_inv_at (DF H) lo d cenv cx ee Gz tnz z /\
       ptr_vv_ok cx (post_value_type cenv (Subscript et obj idx))
         r (LocatedValue et (mk_ptr dst LocCode)) ee Gz tnz z /\
       (!v. r = Value v /\ ~is_word_type (post_value_type cenv (Subscript et obj idx)) /\
          ~is_bytestring_type (post_value_type cenv (Subscript et obj idx)) ==>
          vv_own cenv cx (post_value_type cenv (Subscript et obj idx)) sa sb ee
            r (LocatedValue et (mk_ptr dst LocCode)) z /\
          (!t' p'. LocatedValue et (mk_ptr dst LocCode) = LocatedValue t' p' ==>
                   p'.ptr_location = LocMemory)) /\
       (cenv.ce_is_ctor /\ vv_location (LocatedValue et (mk_ptr dst LocCode)) = SOME LocCode ==>
        ?v. read_result cx r ee = (INL v,ee) /\
            !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Subscript et obj idx)) = SOME rt /\
              eval_operand (vv_operand (LocatedValue et (mk_ptr dst LocCode))) z = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==>
                val_in_memory rt v (w2n w) mem)) /\
       (!t' op. LocatedValue et (mk_ptr dst LocCode) = StackValue t' op /\
          ~is_word_type (post_value_type cenv (Subscript et obj idx)) ==>
          ptr_buf_ok cenv (Subscript et obj idx) op Gz z) /\
       (!t' p'. LocatedValue et (mk_ptr dst LocCode) = LocatedValue t' p' /\
          p'.ptr_location = LocMemory ==>
          ptr_buf_ok cenv (Subscript et obj idx) p'.ptr_operand Gz z) /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tnz)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon fin.storage_trace` >>
  `valid_horizon cx st0 H0 fin.storage_trace` by simp[Abbr `H0`, GSYM storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `stmt_state_rel H0 ctx func cenv cx fin s` by fs[expr_post_def] >>
  `expr_body_pre cenv cx env obj (es with gas_obs := bgs)` by
    (simp[] >> irule expr_body_pre_array_subscript_base_eval >>
     qpat_assum `eval_expr cx obj _ = (INL _,_)` (irule_at Any) >> simp[] >>
     metis_tac[]) >>
  `expr_body_pre cenv cx env idx mid` by
    (`expr_body_pre cenv cx env (Subscript et obj idx) (es with gas_obs := bgs)` by simp[] >>
     drule_all expr_body_pre_array_subscript_index_after_base >> simp[]) >>
  `?ir. eval_expr cx idx (mid with gas_obs := gs) = (INL ir,fin) /\
        read_result cx ir fin = (INL key,fin)` by
    (qpat_assum `bind (eval_expr _ _) _ _ = _` mp_tac >>
     simp[NoAsms, bind_def, AllCaseEqs()] >> strip_tac >>
     drule_then SUBST_ALL_TAC read_result_state >> metis_tac[]) >>
  `vv_post H0 ctx func cenv cx obj (es with gas_obs := bgs) sa sm s0 mid
      (PlaceR (ImmutablePlace src id path)) (LocatedValue (ArrayT et bd) p) u` by
    simp[exprSimPropsTheory.vv_post_initial_gas] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by fs[copy_old_operand_def] >>
  drule_all live_immutable_index_cut_view >> strip_tac >>
  `expr_body_pre cenv cx env idx (mid with gas_obs := gs)` by simp[] >>
  `expr_sim_inv cenv cx env fin` by
    (drule_all exprSimSourceTheory.expr_body_pre_eval_result >> simp[]) >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >> strip_tac >>
  `value_has_type tvt key` by metis_tac[] >>
  drule_all framed_array_index_post_view >> strip_tac >>
  `is_word_type (expr_type idx)` by
    (qpat_assum `value_has_type tvt key` mp_tac >>
     qpat_assum `evaluate_type _ (expr_type idx) = _` mp_tac >>
     qpat_assum `key = IntV i` SUBST1_TAC >> rpt (pop_assum kall_tac) >>
     Cases_on `expr_type idx` >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
          vyperTypingTheory.value_has_type_def, is_word_type_def] >>
     rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def, is_word_type_def]) >>
  `post_value_type cenv idx = expr_type idx` by
    (Cases_on `idx` >> gvs[post_value_type_def, expr_type_def] >>
     BasicProvers.TOP_CASE_TAC >> gvs[post_value_type_def]) >>
  `op_taint tni iop = {} /\ op_prov Gi iop = NONE` by fs[ptr_val_ok_def] >>
  `op_taint tnb p.ptr_operand = {} /\ op_prov Gb p.ptr_operand = NONE` by fs[ptr_vv_ok_def] >>
  `op_taint tni p.ptr_operand = {} /\ op_prov Gi p.ptr_operand = NONE` by
    (Cases_on `p.ptr_operand` >> fs[copy_old_operand_def, ghost_kept_at_def,
         ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def] >> metis_tac[]) >>
  `copy_old_operand sn p.ptr_operand` by metis_tac[copy_old_operand_mono] >>
  `evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd)` by
    (qpat_assum `immutable_holds _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms, immutable_holds_def] >> strip_tac >>
     qpat_assum `evaluate_type _ (ArrayT _ _) = _`
       (mp_tac o MATCH_MP vyperTypeValuesTheory.evaluate_type_ArrayT_cases) >>
     strip_tac >> gvs[]) >>
  `type_memory_bytes cenv et = type_memory_size etv` by
    (irule exprSimHypsTheory.expr_sim_inv_memory_size >> goal_assum (drule_at Any) >> simp[]) >>
  `val_wf (ArrayTV etv bd) (ArrayV av)` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  qabbrev_tac `cnt = array_length (ArrayTV etv bd) av` >>
  `cnt < dimword (:256)` by
    (simp[Abbr `cnt`] >> drule_all target_memory_array_length_bound >> simp[]) >>
  `valid_index (ArrayTV etv bd) av i <=> idx_in_range (is_signed_type (expr_type idx)) iw (n2w cnt)` by
    (unabbrev_all_tac >> irule array_index_word_bounds >> simp[]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  qabbrev_tac `dyn = case bd of Fixed _ => F | Dynamic _ => T` >>
  `compile_array_subscript p.ptr_operand iop dyn (if dyn then 0 else cnt) 32
      (type_memory_size etv) (is_signed_type (expr_type idx))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode) sn = (dst,sb)` by
    (Cases_on `bd` >> fs[Abbr `dyn`, Abbr `cnt`, vyperValueOperationTheory.array_length_def] >>
     Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def, vyperValueOperationTheory.array_length_def]) >>
  `dyn ==> immutable_copy_read cenv.ce_is_ctor (n2w (off+k)) s = n2w cnt /\
    (cenv.ce_is_ctor ==> w2n (n2w (off+k):256 word) + 32 <= lo /\
      mem_word_taint tni.t_mem (w2n (n2w (off+k):256 word)) = {} /\
      (!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w /\
         copy_old_operand sn region /\ op_taint tni region = {} /\ op_prov Gi region = NONE)) /\
    (~cenv.ce_is_ctor ==> w2n (n2w (off+k):256 word) <= LENGTH s.vs_data_section)` by
    (Cases_on `bd` >> simp[Abbr `dyn`, Abbr `cnt`] >>
     `cenv.ce_is_ctor ==> w2n (n2w (off+k):256 word) + type_memory_size (ArrayTV etv (Dynamic n)) <= lo /\
       !m. mem_agree_outside tni.t_mem s.vs_memory m ==>
            val_in_memory (ArrayTV etv (Dynamic n)) (ArrayV av) (w2n (n2w (off+k):256 word)) m` by
       (strip_tac >>
        `vv_holds cenv cx (ArrayT et (Dynamic n)) (PlaceR (ImmutablePlace src id path))
            (LocatedValue (ArrayT et (Dynamic n)) p) fin s` by
          gvs[vv_holds_def] >>
        `dead_lo_ok H0 (DF H0) lo cenv cx` by simp[] >>
        drule_all selected_constructor_code_read >> simp[]) >>
     drule_all current_immutable_dynamic_header >> strip_tac >>
     gvs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
     rpt strip_tac >>
     `lo <> 0` by fs[] >>
     `eval_operand region s = SOME 0w` by
       metis_tac[bodyPtrBopInRepresentationTheory.membership_immutable_base_value] >>
     Cases_on `region` >>
     gvs[copy_old_operand_def, venomStateTheory.eval_operand_def, ghost_inv_at_def,
         ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def] >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_imm_base]) >>
  `!l. p.ptr_operand <> Label l /\ iop <> Label l` by simp[] >>
  `eval_operand iop s = SOME (n2w (w2n iw))` by simp[] >>
  qpat_x_assum `eval_operand iop s = SOME iw` kall_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx fin s`
       (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
     simp[]) >>
  drule_all live_code_select_joint >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`Gf`,`tnf`,`q`] (strip_assume_tac o SIMP_RULE (srw_ss()) []))) >>
  reverse (Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw (n2w cnt)`)
  >- (`~valid_index (ArrayTV etv bd) av i` by metis_tac[] >>
      `!al. av = SArrayV al ==> ?n. bd = Fixed n` by
        (rpt strip_tac >> Cases_on `bd` >> gvs[vyperTypingTheory.value_has_type_def]) >>
      `select_result cx (ArrayT et bd) (PlaceR (ImmutablePlace src id path))
         (ValueSubscript (IntV i)) fin = (INR (Error (RuntimeError "evaluate_subscripts array_index")),fin)` by
        (irule live_immutable_select_error >> metis_tac[]) >>
      qpat_x_assum `i = if _ then _ else _` kall_tac >>
      qpat_x_assum `key = IntV i` SUBST_ALL_TAC >>
      irule gas_outcome_full_intro >>
      qexistsl [`Gf`,`fin`,`[]`,`Abort Revert_abort q`,
                `INR (Error (RuntimeError "evaluate_subscripts array_index"))`,`tnf`] >>
      simp[gasSummaryTheory.gas_explicit_def, fragExecTheory.exit_result_def,
           exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def] >>
      conj_tac
      >- (gen_tac >>
          `!tr slot vt. PlaceR (ImmutablePlace src id path) <> PlaceR (StoragePlace tr slot vt)` by simp[] >>
          `SND (select_result cx (ArrayT et bd) (PlaceR (ImmutablePlace src id path))
             (ValueSubscript (IntV i)) fin) = fin` by simp[] >>
          drule_all select_result_nonstorage_gas_obs >> simp[]) >>
      rpt strip_tac >>
      qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (assume_tac o Q.SPEC `DF H`) >> gvs[]) >>
  `valid_index (ArrayTV etv bd) av i` by metis_tac[] >>
  `Num i = w2n iw` by
    (`0 <= i` by fs[vyperArrayTheory.valid_index_def, IgnAsm `i = _`] >>
     Cases_on `is_signed_type (expr_type idx)` >>
     gvs[overflowElimHelpersTheory.nonneg_w2i_eq_w2n]) >>
  drule_then (qx_choose_then `v` assume_tac)
    (REWRITE_RULE [optionTheory.IS_SOME_EXISTS] vyperArrayTheory.array_index_valid) >>
  qpat_assum `idx_in_range _ _ _ ==> _` (drule_then strip_assume_tac) >>
  `eval_operand dst q = SOME (n2w (off+k) + n2w
    ((case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv))` by
    (Cases_on `bd` >> fs[Abbr `dyn`, IgnAsm `i = _`]) >>
  drule_all live_immutable_selected_facts >> strip_tac >>
  qpat_assum `idx_in_range _ _ _` (fn ok =>
    qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _` (assume_tac o REWRITE_RULE [ok])) >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  qpat_x_assum `key = IntV i` SUBST_ALL_TAC >>
  qabbrev_tac `rsel = PlaceR (ImmutablePlace src id (path ++ [ValueSubscript (IntV i)]))` >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `eval_expr cx obj _ = _`
       (mp_then Any mp_tac vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom) >> simp[]) >>
  `!x. not_fresh_at sa x ==>
     lookup_var x q = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP Gi x /\
     op_taint tnf (Var x) = op_taint tni (Var x)` by
    (gen_tac >> disch_tac >> qpat_assum `!v. not_fresh_at sn v ==> _` irule >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[] >> decide_tac) >>
  irule gas_outcome_full_intro >>
  qexistsl [`Gf`,`fin`,`[]`,`OK q`,`INL rsel`,`tnf`] >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  simp[gasSummaryTheory.gas_explicit_def, fragExecTheory.exit_result_def] >>
  conj_tac
  >- (gen_tac >>
      `!tr slot vt. PlaceR (ImmutablePlace src id path) <> PlaceR (StoragePlace tr slot vt)` by simp[] >>
      `SND (select_result cx (ArrayT et bd) (PlaceR (ImmutablePlace src id path))
         (ValueSubscript (IntV i)) fin) = fin` by simp[] >>
      drule_all select_result_nonstorage_gas_obs >> simp[]) >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `stmt_state_rel H ctx func cenv cx fin s` by
    (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then Any ACCEPT_TAC exprSimWordArgsTheory.expr_post_state)) >>
  `stmt_state_rel H ctx func cenv cx fin q` by
    metis_tac[] >>
  conj_tac
  >- (simp[Abbr `rsel`] >> irule live_immutable_selected_post >>
      simp[] >>
      conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
      qexistsl [`LocatedValue (ArrayT et bd) p`,`gs`,`iop`,`IntV i`,
        `mid`,`PlaceR (ImmutablePlace src id path)`,`s`,`sm`,`sn`,`u`] >> simp[]) >>
  simp[contextTheory.mk_ptr_def, contextTheory.vv_location_def, contextTheory.vv_operand_def,
       vyperASTTheory.expr_type_def, Abbr `rsel`, vv_store_bound_nonmem,
       ptr_vv_ok_def] >>
  conj_tac
  >- (`alloca_inv s` by
         metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
      qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `DF H` assume_tac) >>
      drule_all body_full_path_alloca_history >> simp[]) >>
  `ghost_inv_at (DF H) lo d cenv cx fin Gf tnf q` by
    (irule ghost_inv_at_exterior_frame >>
     qexistsl [`Gi`,`fin`,`s`,`sa`,`tni`] >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx fin q`
       (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
     simp[]) >>
  simp[] >> conj_tac
  >- (strip_tac >>
      `dead_lo_ok H (DF H) lo cenv cx` by simp[] >>
      `(mk_ptr dst LocCode).ptr_location = LocCode` by simp[contextTheory.mk_ptr_def] >>
      drule_all (Q.INST [`p` |-> `mk_ptr dst LocCode`] selected_constructor_code_read) >>
      simp[contextTheory.mk_ptr_def, arithmeticTheory.ADD_COMM]) >>
  `wb_frame cenv es mid sa s0 u` by
    (qpat_assum `vv_post _ _ _ _ _ obj _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms, vv_post_def, wb_frame_def] >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni` by
    (drule_all wordArgsPtrTheory.ghost_kept_at_wb_trans >> simp[]) >>
  irule ghost_kept_at_clean_suffix >> qexistsl [`Gi`,`tni`] >> simp[] >> metis_tac[]
QED
