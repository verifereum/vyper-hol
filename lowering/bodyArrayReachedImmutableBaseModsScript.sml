(* Recover the qualified immutable coordinate from a reached array base. *)
Theory bodyArrayReachedImmutableBaseMods
Ancestors
  bodyArrayNoCopySourceMods bodyArrayNoCopyCutsMods bodyFullPostsMods
  immutableRegionTypingProps bodyInvCodeProps moduleVariableKeyProps
  supportedNameRoot forNestedArrayCapture
  bodySubscriptArrayRouteDefsMods loweringPosts context
  exprSimProps exprBodyPreProps bodyInvSplit compileEnv
  vyperTypeEvalStoragePreservation vyperTypeExprSoundness vyperTypeEnv
  vyperPlaceTyping vyperTypeValues vyperTypeSystem vyperInterpreter
  vyperState vyperAST vyperStorageFootprint finite_map alist option list words
  vyperBareGlobalName vyperTyping vyperTypeInvariants exprSimHypsDefs
Libs
  monadsyntax

Theorem immutable_array_post_coordinate[local]:
  vv_post_mods H ctx func cenv cx obj es sa sm s0 mid
    (PlaceR (ImmutablePlace owner id path)) bvv s /\
  post_value_type cenv obj = ArrayT et bd ==>
  ?p tops off imms itv old k tv etv av.
    bvv = LocatedValue (ArrayT et bd) p /\ p.ptr_location = LocCode /\
    ALOOKUP cenv.ce_modules owner = SOME tops /\
    FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
    ALOOKUP mid.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables owner imms) id = SOME (itv,old) /\
    mem_path_offset itv path = SOME (k,tv) /\
    evaluate_subscripts itv old path = INL (ArrayV av) /\
    eval_operand p.ptr_operand s = SOME (n2w (off+k)) /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd)
Proof
  simp[vv_post_mods_def] >> strip_tac >> Cases_on `bvv`
  >- (qhdtm_x_assum `vv_at` mp_tac >> simp[vv_at_def, is_word_type_def]) >>
  qhdtm_x_assum `vv_place_ptr_mods` mp_tac >>
  simp[vv_place_ptr_mods_def, vv_place_ptr_def, IS_SOME_EXISTS] >> strip_tac >>
  qhdtm_x_assum `vv_holds_mods` mp_tac >>
  simp[vv_holds_mods_def, immutable_holds_mods_def, immutable_holds_def] >>
  strip_tac >>
  drule_then strip_assume_tac evaluate_type_ArrayT_cases >>
  Cases_on `ALOOKUP mid.immutables cx.txn.target` >> gvs[] >>
  fs[read_result_immutable_place, lookup_immutable_def] >>
  Cases_on `bd` >> Cases_on `v` >> gvs[value_has_type_def] >> metis_tac[]
QED

Theorem immutable_array_base_path_type[local]:
  expr_sim_inv_mods mods cenv cx env start /\ well_typed_expr env obj /\
  call_evaluation_safe cx (int_calls_expr obj) /\ expr_type obj = ArrayT et bd /\
  eval_expr cx obj start = (INL (PlaceR (ImmutablePlace owner id path)),mid) /\
  ALOOKUP mid.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (itv,old) /\
  mem_path_offset itv path = SOME (k,tv) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) ==>
  tv = ArrayTV etv bd
Proof
  strip_tac >>
  `runtime_consistent env cx start /\ functions_well_typed cx` by
    fs[expr_sim_inv_mods_def, runtime_consistent_def] >>
  drule_all_then strip_assume_tac eval_expr_success_storage_facts >>
  `env.type_defs = get_tenv cx` by
    fs[runtime_consistent_def, env_consistent_def, env_context_consistent_def] >>
  `subscripts_type itv path = SOME (ArrayTV etv bd)` by
    gvs[eval_result_typed_def, runtime_place_typed_immutable,
        get_immutables_def, get_address_immutables_def,
        bind_def, lift_option_type_def, return_def] >>
  drule mem_path_offset_sound >> simp[]
QED

(* Use the region of the actual declaration, rather than the existential
   region from the value representation predicate. *)
Theorem immutable_array_base_root[local]:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env mid /\
  FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
  ALOOKUP mid.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (itv,old) ==>
  off + type_memory_size itv < dimword (:256) /\ ~cx_const_name_mods mods (owner,id) /\
  value_has_type itv old /\ well_formed_type_value itv /\
  ?root_ty. FLOOKUP env.bare_globals (owner,id) = SOME root_ty /\
            evaluate_type (get_tenv cx) root_ty = SOME itv
Proof
  strip_tac >>
  drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
    contract_inv_immutable_section_layout >>
  qpat_x_assum `!src name off. FLOOKUP _ _ = _ <=> _`
    (qspecl_then [`owner`,`id`,`off`] (drule_then strip_assume_tac o iffLR)) >>
  `~cx_const_name_mods mods (owner,id)` by
    (qhdtm_assum `immutable_region_mods`
       (strip_assume_tac o REWRITE_RULE [immutable_region_mods_def]) >>
     `MEM (VariableDecl vis Immutable id ty slot) tops` by simp[] >>
     drule_then assume_tac contract_inv_unqualified_variable_keys >>
     `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))`
       by metis_tac[] >>
     `?vis ty slot. supported_variable_decl tops (NONE,id) = SOME (vis,Immutable,ty,slot)` by
       metis_tac[supported_variable_decl_distinct_mem] >>
     qpat_x_assum `tops = _` kall_tac >>
     simp[cx_const_name_mods_def] >>
     drule_then (qspec_then `id` mp_tac) distinct_module_consts_env_names_constant >> simp[]) >>
  drule_all_then strip_assume_tac immutable_region_mods_type >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `env_immutables_consistent env cx mid` by fs[env_consistent_def] >>
  `evaluate_type (get_tenv cx) ty = SOME itv` by
    (qhdtm_x_assum `env_immutables_consistent` mp_tac >>
     simp[env_immutables_consistent_def] >> strip_tac >> first_x_assum drule_all >> simp[]) >>
  `state_well_typed mid` by fs[expr_sim_inv_mods_def] >>
  drule_all_then assume_tac state_well_typed_immutables_ALOOKUP >>
  drule_all_then strip_assume_tac imms_well_typed_get_source_immutables >>
  simp[] >> fs[expr_sim_inv_mods_def] >>
  qpat_assum `!src id ty. _ /\ (~cx_const_name_mods _ _ \/ _) ==> _`
    (qspecl_then [`owner`,`id`,`ty`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then strip_assume_tac >>
  qpat_x_assum `IS_SOME (FLOOKUP cenv.ce_module_vars (owner,id)) ==> _` mp_tac >>
  (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
  qpat_assum `!tv. evaluate_type _ ty = SOME tv ==> _`
    (qspec_then `itv` mp_tac) >> gvs[]
QED

Theorem array_reached_immutable_base_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
      DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  ~subscript_reads_base cx obj idx /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty obj idx et bd st0 (es,s0,G0,tn0)
      (sa,sm,st2,sb,bvv,iop,dst,loc)
      (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
      (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) /\
  raw = PlaceR (ImmutablePlace owner id path) ==>
  ?p owner_tops off imms0 itv old k etv av0 root_ty.
    bvv = LocatedValue (ArrayT et bd) p /\ p.ptr_location = LocCode /\ loc = LocCode /\
    ALOOKUP cenv.ce_modules owner = SOME owner_tops /\
    FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
    ALOOKUP mid.immutables cx.txn.target = SOME imms0 /\
    FLOOKUP (get_source_immutables owner imms0) id = SOME (itv,old) /\
    mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
    evaluate_subscripts itv old path = INL (ArrayV av0) /\
    eval_operand p.ptr_operand s = SOME (n2w (off+k)) /\
    off + type_memory_size itv < dimword (:256) /\
    ~cx_const_name_mods mods (owner,id) /\
    FLOOKUP env.bare_globals (owner,id) = SOME root_ty /\
    evaluate_type (get_tenv cx) root_ty = SOME itv /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
    value_has_type itv old /\
    well_formed_type_value itv
Proof
  rpt strip_tac >>
  drule_all_then strip_assume_tac array_nocopy_base_inputs_mods >>
  qhdtm_assum `array_nocopy_cut_mods`
    (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
  qabbrev_tac `H0 = storage_trace_horizon fin.storage_trace` >>
  `valid_horizon cx st0 H0 fin.storage_trace` by fs[Abbr `H0`, storage_trace_domain_def] >>
  drule_all_then strip_assume_tac array_nocopy_cut_posts_mods >>
  drule_all_then strip_assume_tac array_nocopy_index_inputs_mods >>
  qpat_assum `expr_body_pre_mods _ _ _ _ idx mid`
    (assume_tac o MATCH_MP expr_body_pre_mods_inv) >>
  qhdtm_x_assum `linked_subscript_array_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  `post_value_type cenv obj = ArrayT et bd` by simp[] >>
  qpat_x_assum `raw = _` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac immutable_array_post_coordinate >>
  `expr_sim_inv_mods mods cenv cx env (es with gas_obs := gs1)` by simp[] >>
  drule_all_then SUBST_ALL_TAC immutable_array_base_path_type >>
  drule_all_then strip_assume_tac immutable_array_base_root >>
  qexistsl [`p`,`tops'`,`off`,`imms`,`itv`,`old`,`k`,`etv`,`av`,`root_ty`] >>
  fs[vv_location_def, arithmeticTheory.ADD_COMM]
QED
