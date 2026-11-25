(* Memory-array write targets use the current local, after the index run. *)
Theory bodyWriteArrayMemoryMods
Ancestors
  bodyWriteArrayPacketMods bodyWriteArrayOperandsMods bodyWriteTargetStageMods
  bodyFullTargetArrayLoad bodyFullTargetDefs bodyFullPostsMods bodyFullShadowBodyInv
  targetSubscriptMemory loweringPosts exprLoweringProps gasOutcomeFull
  vyperTypeInvariants vyperSubscriptOverlap vyperAST exprLowering option
  targetPlaceSimCasesBase targetOverlapAccess bodyPtrBopInMemoryContents
  exprSimSubscriptArraySuffix typedMemoryCopy exprBodyPreProps
  vyperTypeEvalCaseProofs vyperPlaceResultTyping vyperPlaceStatePreservation
  vyperFixedShapePath vyperLocalAccessFrame vyperTypeEnv vyperTypeSystem
  allocLimitsProps stateRelProj bodyPtrDefs freshWrites valueEncodingProps
  contextCodegenRel codegenRel memLocDefs ptrDiscipline venomExecSemantics
  unitTransformDefs exprSimBuffer exprSimProps integer_word words
  finite_map list alist pair combin
  loweringStateRelDefs compileEnv targetPlaceSim vyperInterpreter vyperState
  exprSimHypsDefs allocLimits vyperValue
  bodyWriteArrayMemoryLoadMods bodyWriteArrayMemoryChildMods
Libs
  pairLib monadsyntax

Theorem write_memory_fields_lookup[local]:
  !fields args fld fty.
    MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args /\
    ALOOKUP args fld = SOME fty ==>
    ?fsz. ALOOKUP fields fld = SOME (fty,fsz)
Proof
  Induct >> Cases_on `args` >> simp[] >>
  PairCases_on `h` >> gen_tac >> PairCases_on `h'` >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem write_memory_struct_lookup[local]:
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  attribute_type tenv (StructT sid) fld = SOME ty ==>
  ?sz. ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld =
    SOME (ty,sz)
Proof
  simp[attribute_type_def, sfields_tenv_consistent_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> first_x_assum drule >> strip_tac >>
  drule_all write_memory_fields_lookup >> simp[get_struct_fields_def]
QED

(* The type of each prefix of the returned path is fixed by the target
   syntax. No comparison of the values in the intermediate scopes is used. *)
Theorem write_memory_path_fit[local]:
  !bt cenv cx env st es id path ee root rtv tv vt.
    expr_sim_inv_mods mods cenv cx env st /\
    eval_base_place cx bt es = (INL (PlaceR (MemoryPlace id path)),ee) /\
    type_place_target env bt = SOME vt /\
    cenv.ce_var_type id = SOME root /\
    evaluate_type (get_tenv cx) root = SOME rtv /\
    subscripts_type rtv path = SOME tv ==>
    ?ty. vt = Type ty /\ target_place_type cenv bt = SOME (ValPT ty) /\
         evaluate_type (get_tenv cx) ty = SOME tv /\
         (~target_through_dynarray cenv bt ==> fixed_shape_path rtv path)
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule target_base_memory_root_ptr >> simp[target_root_def] >> strip_tac >> gvs[] >>
      qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, get_scopes_def, ignore_bind_def,
           type_check_def, assert_def, check_def, return_def, raise_def, AllCaseEqs()] >>
      strip_tac >> gvs[subscripts_type_def, type_place_target_NameTarget] >>
      fs[expr_sim_inv_mods_def, target_place_type_def, fixed_shape_path_def] >>
      qpat_assum `!id ty. FLOOKUP env.var_types id = SOME ty ==> cenv.ce_var_type id = SOME ty`
        (drule_then assume_tac) >> gvs[])
  >- (rpt strip_tac >> drule target_base_memory_root_ptr >> simp[target_root_def])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      drule extend_place_memory_origin >> strip_tac >> gvs[] >>
      drule aug_place_extend_name_memory >> strip_tac >> gvs[] >>
      gvs[vyperPlaceStatePreservationTheory.subscripts_type_append, AllCaseEqs(),
          type_place_target_SubscriptTarget] >>
      first_x_assum drule_all >> strip_tac >> gvs[] >>
      rename1 `subscript_vtype (Type ty) (expr_type e) = SOME vt` >>
      Cases_on `ty` >> gvs[subscript_vtype_def, AllCaseEqs()] >>
      gvs[evaluate_type_def, AllCaseEqs(), target_place_type_def] >>
      gvs[subscripts_type_def, optionTheory.option_case_eq] >>
      drule subscript_type_value_int_shape >> strip_tac >> gvs[] >>
      simp[subscript_type_def, fixed_shape_path_append, fixed_shape_path_def,
           subscripts_type_def, target_through_dynarray_def] >>
      Cases_on `b` >> fs[subscript_type_def]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  drule extend_place_memory_origin >> strip_tac >> gvs[] >>
  drule aug_place_extend_name_memory >> strip_tac >> gvs[] >>
  gvs[vyperPlaceStatePreservationTheory.subscripts_type_append, AllCaseEqs(),
      type_place_target_AttributeTarget] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  drule_then (mp_then Any assume_tac env_consistent_type_defs_get_tenv)
    expr_sim_inv_mods_env >>
  rename1 `attribute_type _ base_ty fld = SOME ty` >>
  `?sid. base_ty = StructT sid` by (Cases_on `base_ty` >> fs[attribute_type_def]) >>
  gvs[] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by fs[expr_sim_inv_mods_def] >>
  drule_all write_memory_struct_lookup >> strip_tac >>
  drule_all attribute_type_runtime_step >> strip_tac >>
  gvs[subscripts_type_def, target_place_type_def, target_through_dynarray_def,
      fixed_shape_path_append, fixed_shape_path_def, evaluate_type_def, AllCaseEqs()]
QED

Theorem write_memory_scope_type[local]:
  expr_sim_inv_mods mods cenv cx env st /\
  cenv.ce_var_type id = SOME ty /\
  lookup_scopes id st.scopes = SOME entry ==>
  evaluate_type (get_tenv cx) ty = SOME entry.type /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type
Proof
  simp[expr_sim_inv_mods_def, env_consistent_def, env_scopes_consistent_def,
       IS_SOME_EXISTS] >> strip_tac >> gvs[] >>
  `?vty. FLOOKUP env.var_types id = SOME vty` by metis_tac[] >>
  `cenv.ce_var_type id = SOME vty` by simp[] >>
  `evaluate_type (get_tenv cx) vty = SOME entry.type` by
    (first_assum (qspecl_then [`id`,`vty`,`entry`] mp_tac) >> simp[]) >>
  gvs[state_well_typed_def] >> drule_all scope_well_typed_lookup_scopes >> simp[]
QED

Theorem write_memory_live_after_index[local]:
  expr_sim_inv_mods mods cenv cx env mid1 /\
  expr_sim_inv_mods mods cenv cx env mid2 /\
  type_place_target env bt = SOME vt /\
  cenv.ce_var_type id = SOME rt /\
  evaluate_type (get_tenv cx) rt = SOME rtv /\
  subscripts_type rtv path = SOME tv /\
  eval_base_place cx bt es = (INL (PlaceR (MemoryPlace id path)),mid1) /\
  (?entry a. lookup_scopes id mid1.scopes = SOME entry /\
     evaluate_subscripts entry.type entry.value path = INL a) /\
  alloc_limits_target cenv (SubscriptTarget bt e) /\
  bind (eval_expr cx e) (read_result cx) (mid1 with gas_obs := gs) = (INL v,mid2) ==>
  ?entry a. lookup_scopes id mid2.scopes = SOME entry /\ entry.type = rtv /\
    value_has_type rtv entry.value /\ well_formed_type_value rtv /\
    evaluate_subscripts rtv entry.value path = INL a
Proof
  strip_tac >>
  `?entry'. lookup_scopes id mid2.scopes = SOME entry'` by
    (fs[expr_sim_inv_mods_def, env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS] >>
     metis_tac[]) >>
  `entry'.type = rtv /\ value_has_type rtv entry'.value /\ well_formed_type_value rtv` by
    (drule_at (Pat `expr_sim_inv_mods _ _ _ _ mid2`) write_memory_scope_type >>
     disch_then drule_all >> simp[]) >>
  qexists `entry'` >> simp[] >>
  Cases_on `target_through_dynarray cenv bt`
  >- (drule_then assume_tac target_base_memory_root_ptr >>
      drule target_root_local_nonconstant_read >>
      disch_then (qspec_then `cenv.ce_modules` assume_tac) >>
      `~MEM (WriteAcc (LocalRef id)) (expr_accesses cenv.ce_modules e)` by
        (fs[alloc_limits_expr_def] >> drule_all target_subscript_overlap_unwritten >> simp[]) >>
      `lookup_scopes id mid2.scopes = lookup_scopes id mid1.scopes` by
        (qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def, AllCaseEqs()] >>
         strip_tac >> drule read_result_state >> strip_tac >> gvs[expr_accesses_def] >>
         drule_all eval_expr_unwritten_local >> simp[]) >>
      gvs[]) >>
  drule_all write_memory_path_fit >> strip_tac >>
  `fixed_shape_path rtv path` by simp[] >>
  irule fixed_shape_path_live >> simp[]
QED

Theorem write_memory_retained_ptr[local]:
  local_ptrs_reserved cenv sa /\ ci_mono sa sm /\ ci_mono sm sn /\
  write_target_post_mods H D lo d ctx func cenv cx bt es sa sm s0 mid1
    (PlaceR (MemoryPlace id path)) (Type (ArrayT et bd)) rb G0 tn0 G1 tn1 t1 /\
  expr_post_mods H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2 /\
  ghost_kept_at lo cenv mid1 sm G1 tn1 t1 G2 tn2 /\
  eval_operand (FST rb) t1 = SOME b ==>
  local_ptrs_reserved cenv sn /\ stmt_state_rel H ctx func cenv cx mid2 t2 /\
  FST (SND rb) = SOME LocMemory /\ SND (SND rb) = SOME (ValPT (ArrayT et bd)) /\
  place_readable cx mid1 (PlaceR (MemoryPlace id path)) /\
  place_ptr_rel cenv cx t2 (PlaceR (MemoryPlace id path)) b
    (SOME LocMemory) (Type (ArrayT et bd)) /\
  (!p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at sn p /\ op_prov G1 (FST rb) = FLOOKUP G2 p)
Proof
  strip_tac >> drule write_target_post_view_mods >> strip_tac >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var]) >>
  `place_readable cx mid1 (PlaceR (MemoryPlace id path)) /\
   place_ptr_rel cenv cx t1 (PlaceR (MemoryPlace id path)) b
     (FST (SND rb)) (Type (ArrayT et bd))` by gvs[write_target_location_mods_def] >>
  `FST (SND rb) = SOME LocMemory` by fs[place_ptr_rel_def] >>
  simp[value_type_place_def] >>
  fs[expr_post_mods_def, expr_post_def] >> conj_tac
  >- (irule target_place_ptr_values_frame >> qexistsl_tac [`t1`,`sm`] >> simp[]) >>
  rpt strip_tac >>
  `not_fresh_at sm p /\ not_fresh_at sn p` by
    (fs[local_ptrs_reserved_def] >>
     qpat_assum `!name q n. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) n) ==> not_fresh_at sm q`
       (drule_then assume_tac) >>
     fs[ci_mono_def] >> drule_all not_fresh_at_mono >> simp[]) >>
  fs[ghost_kept_at_def, target_ptr_ok_def] >> metis_tac[]
QED

(* Carry just the final typed entry through the recursive target walk.
   The index can change this entry when the saved prefix is fixed-shape. *)
Theorem write_memory_base_live:
  !bt cenv cx env st s t id path entry root vt tv.
    expr_sim_inv_mods mods cenv cx env st /\ alloc_limits_target cenv bt /\
    type_place_target env bt = SOME vt /\
    eval_base_place cx bt s = (INL (PlaceR (MemoryPlace id path)),t) /\
    lookup_scopes id t.scopes = SOME entry /\
    cenv.ce_var_type id = SOME root /\
    evaluate_type (get_tenv cx) root = SOME entry.type /\
    well_formed_type_value entry.type /\ value_has_type entry.type entry.value /\
    subscripts_type entry.type path = SOME tv ==>
    ?a. evaluate_subscripts entry.type entry.value path = INL a
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, get_scopes_def, ignore_bind_def,
           type_check_def, assert_def, check_def, return_def, raise_def, AllCaseEqs()] >>
      strip_tac >> gvs[evaluate_subscripts_def])
  >- (rpt strip_tac >> drule target_base_memory_root_ptr >> simp[target_root_def])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      drule extend_place_memory_origin >> strip_tac >> gvs[] >>
      drule aug_place_extend_name_memory >> strip_tac >> gvs[] >>
      drule vyperPlaceFramesTheory.extend_place_PlaceR_state >> strip_tac >> gvs[] >>
      gvs[vyperPlaceStatePreservationTheory.subscripts_type_append, AllCaseEqs(),
          type_place_target_SubscriptTarget, alloc_limits_expr_def] >>
      rename1 `eval_base_place cx bt s = (INL (PlaceR (MemoryPlace id pref)),at_base)` >>
      `?a. evaluate_subscripts entry.type entry.value pref = INL a` by
        (Cases_on `target_through_dynarray cenv bt`
         >- (drule_then assume_tac target_base_memory_root_ptr >>
             drule target_root_local_nonconstant_read >>
             disch_then (qspec_then `cenv.ce_modules` assume_tac) >>
             drule_all target_subscript_overlap_unwritten >> strip_tac >>
             drule_then assume_tac read_result_state >> gvs[expr_accesses_def] >>
             drule_all eval_expr_unwritten_local >> strip_tac >>
             `lookup_scopes id at_base.scopes = SOME entry` by
               (qpat_assum `_ = lookup_scopes id at_base.scopes`
                  (fn th => pure_once_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
             first_x_assum drule_all >> simp[]) >>
         drule_all write_memory_path_fit >> strip_tac >>
         `fixed_shape_path entry.type pref` by simp[] >>
         irule fixed_shape_path_live >> simp[]) >>
      drule_all extend_place_memory_live >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  drule extend_place_memory_origin >> strip_tac >> gvs[] >>
  drule aug_place_extend_name_memory >> strip_tac >> gvs[] >>
  drule vyperPlaceFramesTheory.extend_place_PlaceR_state >> strip_tac >> gvs[] >>
  gvs[vyperPlaceStatePreservationTheory.subscripts_type_append, AllCaseEqs(),
      type_place_target_AttributeTarget, alloc_limits_expr_def] >>
  first_x_assum drule_all >> strip_tac >>
  drule_all extend_place_memory_live >> simp[]
QED

Theorem write_array_memory_current_mods:
  write_array_reached_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,PlaceR (MemoryPlace id path),t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2)) /\
  valid_horizon cx st0 H mid2.storage_trace /\
  eval_operand (FST rb) t1 = SOME b ==>
  local_ptrs_reserved cenv sn /\ stmt_state_rel H ctx func cenv cx mid2 t2 /\
  FST (SND rb) = SOME LocMemory /\ SND (SND rb) = SOME (ValPT (ArrayT et bd)) /\
  place_ptr_rel cenv cx t2 (PlaceR (MemoryPlace id path)) b
    (SOME LocMemory) (Type (ArrayT et bd)) /\
  (!p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at sn p /\ op_prov G1 (FST rb) = FLOOKUP G2 p) /\
  ?entry etv av.
    lookup_scopes id mid2.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
    subscripts_type entry.type path = SOME (ArrayTV etv bd) /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
    value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
    value_has_type (ArrayTV etv bd) (ArrayV av) /\
    well_formed_type_value (ArrayTV etv bd)
Proof
  strip_tac >> drule_all_then strip_assume_tac write_array_reached_posts_mods >>
  qhdtm_x_assum `write_array_reached_mods`
    (strip_assume_tac o REWRITE_RULE [write_array_reached_mods_def]) >>
  `local_ptrs_reserved cenv sa` by fs[write_target_entry_mods_def] >>
  drule_all_then strip_assume_tac write_memory_retained_ptr >> simp[] >>
  qpat_assum `place_ptr_rel _ _ t2 _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [place_ptr_rel_def]) >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `alloc_limits_target cenv bt` by fs[alloc_limits_expr_def] >>
  `?entry. lookup_scopes id mid1.scopes = SOME entry` by
    (qpat_x_assum `place_readable _ _ _` mp_tac >>
     simp[place_readable_def, read_place_def, get_scopes_def, bind_def,
          lift_option_type_def, lift_sum_def, return_def, raise_def] >>
     Cases_on `lookup_scopes id mid1.scopes` >> simp[return_def, raise_def]) >>
  `entry.type = tv0 /\ value_has_type tv0 entry.value /\ well_formed_type_value tv0` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ mid1`
       (mp_then Any (qspecl_then [`t0`,`id`,`entry`] mp_tac) write_memory_scope_type) >>
     simp[] >> metis_tac[]) >>
  `?a. evaluate_subscripts entry.type entry.value path = INL a` by
    (irule write_memory_base_live >>
     qpat_assum `eval_base_place _ _ _ = _` (irule_at Any) >>
     qpat_assum `expr_sim_inv_mods _ _ _ _ es` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `?entry' a'. lookup_scopes id mid2.scopes = SOME entry' /\
    entry'.type = tv0 /\ value_has_type tv0 entry'.value /\
    well_formed_type_value tv0 /\ evaluate_subscripts tv0 entry'.value path = INL a'` by
    (irule write_memory_live_after_index >>
     qpat_assum `bind (eval_expr _ _) (read_result _) _ = _` (irule_at Any) >>
     qpat_assum `eval_base_place _ _ _ = _` (irule_at Any) >>
     qpat_assum `expr_sim_inv_mods _ _ _ _ mid1` (irule_at Any) >>
     qpat_assum `type_place_target _ bt = _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
  `?etv. evaluate_type (get_tenv cx) et = SOME etv /\ tv = ArrayTV etv bd` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  `value_has_type (ArrayTV etv bd) a'` by
    (irule evaluate_subscripts_type >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  Cases_on `a'` >> gvs[vyperTypingTheory.value_has_type_def] >>
  drule_all subscripts_type_well_formed >> simp[] >> metis_tac[]
QED

(* The current lookup identifies the word independently of the horizon. *)
Theorem write_array_memory_length_mods:
  write_array_reached_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,PlaceR (MemoryPlace id path),t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2)) /\
  valid_horizon cx st0 H mid2.storage_trace /\
  eval_operand (FST rb) t1 = SOME b ==>
  FST (SND rb) = SOME LocMemory /\ SND (SND rb) = SOME (ValPT (ArrayT et bd)) /\
  allocas_from lo t2 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t2) /\
  ?nw.
    (!entry etv av. lookup_scopes id mid2.scopes = SOME entry /\
        evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
        evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) ==>
      nw = n2w (array_length (ArrayTV etv bd) av)) /\
    (!n. bd = Fixed n ==> nw = n2w n) /\
    (!cap len sl. bd = Dynamic cap /\
      compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory (FST rb) sn = (len,sl) ==>
      ?ul Gl tl. array_length_loader_ok cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory
          (FST rb) nw sn len sl lo ctx func PG t2 G2 tn2 ul Gl tl /\
        op_prov Gl len = NONE /\ op_taint tl len = {})
Proof
  strip_tac >> drule_all_then strip_assume_tac write_array_memory_current_mods >>
  drule_all_then strip_assume_tac write_array_reached_operands_mods >>
  drule_all_then strip_assume_tac write_array_reached_posts_mods >>
  `allocas_from lo t2` by fs[ghost_inv_at_mods_def] >>
  drule_then assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  `eval_operand (FST rb) t2 = SOME b` by fs[] >>
  `!p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
          op_prov G2 (FST rb) = FLOOKUP G2 p` by simp[] >>
  drule_all write_array_memory_load_from_current_mods >> simp[LET_THM] >> strip_tac >>
  qexists `n2w (array_length (ArrayTV etv bd) av)` >> simp[] >>
  rpt strip_tac >> gvs[]
QED

Theorem write_array_memory_extend_mods:
  write_array_reached_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,PlaceR (MemoryPlace id path),t1,G1,tn1),
     (index_gas,mid2,IntV i,t2,G2,tn2)) /\
  valid_horizon cx st0 H mid2.storage_trace /\
  eval_operand (FST rb) t1 = SOME b /\
  i = (if is_signed_type (expr_type e) then w2i iw else &(w2n iw)) /\
  (!entry etv av. lookup_scopes id mid2.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
      evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) ==>
    nw = n2w (array_length (ArrayTV etv bd) av)) /\
  write_array_select_frame
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,PlaceR (MemoryPlace id path),t1,G1,tn1),
     (index_gas,mid2,IntV i,t2,G2,tn2))
    (LocMemory,b,iw,nw) (t3,G3,tn3) ==>
  let child = PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])) in
  let in_range = idx_in_range (is_signed_type (expr_type e)) iw nw in
    extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i)) mid2 =
      ((if in_range then INL child else
        INR (Error (RuntimeError "evaluate_subscripts array_index"))),mid2) /\
    (in_range ==> target_ptr_ok cenv child r G3 tn3 t3 /\
      write_target_location_mods cenv cx (SubscriptTarget bt e) mid2 child vt r G3 t3)
Proof
  strip_tac >> drule_all_then strip_assume_tac write_array_memory_current_mods >>
  drule_all_then strip_assume_tac write_array_reached_operands_mods >>
  `!p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
          op_prov G2 (FST rb) = FLOOKUP G2 p` by simp[] >>
  qpat_x_assum `!entry etv av. _ ==> nw = _` (drule_all_then SUBST_ALL_TAC) >>
  drule_all write_array_memory_child_from_current_mods >> simp[]
QED
