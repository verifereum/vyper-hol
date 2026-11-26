(* The qualified source extension and its pointer on the selected run. *)
Theory bodyWriteArrayImmutableExtendMods
Ancestors
  bodyWriteArrayPacketMods exprBodyPreProps vyperTypeEvalCaseProofs
  exprSimProps typedMemoryCopy exprSimSubscriptArraySuffix exprSimSubscriptArraySource
  targetSubscriptMemory targetSubscriptSplit vyperPlaceResultTyping
  valueTypingMemoryProps vyperArray vyperTypeEnv overflowElimHelpers integer_word
  vyperState vyperInterpreter vyperValue bodyPtrDefs allocLimits
  exprSimHypsDefs targetPlaceSim targetPlaceSimCasesBase loweringPosts compileEnv loweringStateRelDefs
  bodyWriteTargetStageMods bodyFullTargetDefs vyperFixedShapePath
  vyperTypeSystem vyperTyping words finite_map alist bodyWriteArraySelectMods

Theorem immutable_extend_result[local]:
  FLOOKUP (get_source_immutables owner imms) id = SOME (itv,iv) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  subscripts_type itv path = SOME ptv /\
  evaluate_subscripts itv iv path = INL a ==>
  extend_place cx (PlaceR (ImmutablePlace owner id path)) sb es =
    ((case evaluate_subscripts ptv a [sb] of
       INL _ => INL (PlaceR (ImmutablePlace owner id (path ++ [sb])))
     | INR err => INR (Error err)),es)
Proof
  strip_tac >> Cases_on `evaluate_subscripts ptv a [sb]` >>
  simp[extend_place_def, place_type_value_def, read_place_def, get_immutables_def,
       get_address_immutables_def, extend_memory_place_def,
       bind_def, ignore_bind_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def]
QED

Theorem lookup_field_descriptor[local]:
  !fields args fld ty.
    MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args /\
    ALOOKUP args fld = SOME ty ==>
    ?sz. ALOOKUP fields fld = SOME (ty,sz)
Proof
  Induct >> rpt gen_tac >> Cases_on `args` >> simp[] >>
  PairCases_on `h` >> Cases_on `h'` >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem linked_target_struct_field[local]:
  expr_sim_inv_mods mods cenv cx env es /\ attribute_type env.type_defs t fld = SOME ty ==>
  ?sid sz. t = StructT sid /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld = SOME (ty,sz)
Proof
  strip_tac >>
  `env.type_defs = get_tenv cx` by
    (drule expr_sim_inv_mods_env >> strip_tac >> drule env_consistent_type_defs_get_tenv >> simp[]) >>
  Cases_on `t` >> gvs[attribute_type_def, AllCaseEqs()] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by fs[expr_sim_inv_mods_def] >>
  qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
  simp[sfields_tenv_consistent_def] >> strip_tac >> first_x_assum drule >> strip_tac >>
  simp[get_struct_fields_def] >> metis_tac[lookup_field_descriptor]
QED

Theorem qualified_immutable_target_type[local]:
  !bt mods cenv cx env es owner id off vt.
    target_root bt = TopLevelNameTarget (owner,id) /\
    FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
    expr_sim_inv_mods mods cenv cx env es /\
    type_place_target env bt = SOME vt ==>
    ?ty. vt = Type ty /\ target_place_type cenv bt = SOME (ValPT ty)
Proof
  recInduct base_assignment_target_induct >> simp[target_root_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `?ty. FLOOKUP env.bare_globals (owner,id) = SOME ty` by
        (fs[expr_sim_inv_mods_def, bare_globals_layout_def] >> first_x_assum drule >> simp[]) >>
      `cenv.ce_hashmap_info (owner,id) = NONE` by fs[expr_sim_inv_mods_def] >>
      `!ty. FLOOKUP env.bare_globals (owner,id) = SOME ty ==>
            cenv.ce_module_var_type (owner,id) = SOME ty` by
        fs[expr_sim_inv_mods_def, bare_globals_layout_def] >>
      gvs[type_place_target_TopLevelNameTarget, target_place_type_def] >>
      drule expr_sim_inv_mods_env >>
      simp[vyperTypeInvariantsTheory.env_consistent_def,
           vyperTypeInvariantsTheory.env_context_consistent_def] >>
      strip_tac >> first_x_assum drule >> strip_tac >> gvs[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[type_place_target_SubscriptTarget] >> strip_tac >>
      first_x_assum drule_all >> strip_tac >> gvs[] >>
      rename1 `subscript_vtype (Type ty) _ = _` >> Cases_on `ty` >>
      gvs[subscript_vtype_def, target_place_type_def, AllCaseEqs()]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[type_place_target_AttributeTarget] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  drule_all linked_target_struct_field >> strip_tac >> gvs[target_place_type_def]
QED

Theorem linked_immutable_type_at[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (itv,iv) ==>
  ?ty. FLOOKUP env.bare_globals (owner,id) = SOME ty /\
       evaluate_type (get_tenv cx) ty = SOME itv
Proof
  strip_tac >>
  `?ty. FLOOKUP env.bare_globals (owner,id) = SOME ty` by
    (fs[expr_sim_inv_mods_def, bare_globals_layout_def] >> first_x_assum drule >> simp[]) >>
  qexists `ty` >> simp[] >>
  drule expr_sim_inv_mods_env >> simp[vyperTypeInvariantsTheory.env_consistent_def] >>
  strip_tac >>
  qpat_x_assum `env_immutables_consistent _ _ _` mp_tac >>
  simp[vyperTypeInvariantsTheory.env_immutables_consistent_def] >>
  strip_tac >> first_x_assum drule_all >> simp[]
QED

(* The expressions evaluated between the two lookups may change the value,
   but not its declared type. *)
Theorem linked_immutable_type_agrees[local]:
  expr_sim_inv_mods mods cenv cx env es1 /\ expr_sim_inv_mods mods cenv cx env es2 /\
  FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es1.immutables cx.txn.target = SOME imms1 /\
  FLOOKUP (get_source_immutables owner imms1) id = SOME (itv1,iv1) /\
  ALOOKUP es2.immutables cx.txn.target = SOME imms2 /\
  FLOOKUP (get_source_immutables owner imms2) id = SOME (itv2,iv2) ==>
  itv1 = itv2
Proof
  strip_tac >>
  `!tv. (?m v s. expr_sim_inv_mods mods cenv cx env s /\
          ALOOKUP s.immutables cx.txn.target = SOME m /\
          FLOOKUP (get_source_immutables owner m) id = SOME (tv,v)) ==>
        ?ty. FLOOKUP env.bare_globals (owner,id) = SOME ty /\
             evaluate_type (get_tenv cx) ty = SOME tv` by
    (rpt strip_tac >> drule_all linked_immutable_type_at >> simp[]) >>
  `?ty. FLOOKUP env.bare_globals (owner,id) = SOME ty /\
        evaluate_type (get_tenv cx) ty = SOME itv1` by
    (first_x_assum irule >> qexistsl [`imms1`,`iv1`,`es1`] >> simp[]) >>
  `?ty. FLOOKUP env.bare_globals (owner,id) = SOME ty /\
        evaluate_type (get_tenv cx) ty = SOME itv2` by
    (first_x_assum irule >> qexistsl [`imms2`,`iv2`,`es2`] >> simp[]) >>
  gvs[]
QED

Theorem immutable_extend_array_source[local]:
  FLOOKUP (get_source_immutables owner imms) id = SOME (itv,iv) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) ==>
  let sub = ValueSubscript (IntV i) in
    extend_place cx (PlaceR (ImmutablePlace owner id path)) sub es =
      ((if valid_index (ArrayTV etv bd) av i then
          INL (PlaceR (ImmutablePlace owner id (path ++ [sub])))
        else INR (Error (RuntimeError "evaluate_subscripts array_index"))),es) /\
    (valid_index (ArrayTV etv bd) av i ==>
     ?el. evaluate_subscripts itv iv (path ++ [sub]) = INL el /\
          mem_path_offset itv (path ++ [sub]) = SOME
            (k + ((case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv),etv))
Proof
  simp[LET_THM, Excl "valid_index_def"] >> strip_tac >>
  drule mem_path_offset_sound >> strip_tac >>
  drule_all immutable_extend_result >>
  disch_then (qspec_then `ValueSubscript (IntV i)` assume_tac) >>
  Cases_on `valid_index (ArrayTV etv bd) av i`
  >- (drule (REWRITE_RULE [optionTheory.IS_SOME_EXISTS] array_index_valid) >> strip_tac >>
      `val_wf (ArrayTV etv bd) (ArrayV av)` by metis_tac[value_has_type_memory_wf] >>
      drule_all array_element_step_offset >> strip_tac >>
      drule_all mem_path_offset_snoc >> strip_tac >>
      drule_all evaluate_subscripts_append >>
      disch_then (qspec_then `[ValueSubscript (IntV i)]` mp_tac) >>
      simp[evaluate_subscripts_def]) >>
  `!al. av = SArrayV al ==> ?n. bd = Fixed n` by
    (rpt strip_tac >> Cases_on `bd` >> gvs[value_has_type_def]) >>
  drule_all evaluate_array_subscript_oob >> simp[]
QED

Theorem write_array_immutable_extend_mods:
  write_array_reached_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,PlaceR (ImmutablePlace owner id path),t1,G1,tn1),
     (index_gas,mid2,IntV i,t2,G2,tn2)) /\
  write_array_select_frame
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,PlaceR (ImmutablePlace owner id path),t1,G1,tn1),
     (index_gas,mid2,IntV i,t2,G2,tn2))
    (LocCode,n2w (off+k),iw,n2w (array_length (ArrayTV etv bd) av)) (t3,G3,tn3) /\
  valid_horizon cx st0 H mid2.storage_trace /\
  FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
  ALOOKUP mid2.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  op_prov G2 (FST rb) = NONE /\
  i = (if is_signed_type (expr_type e) then w2i iw else &(w2n iw)) ==>
  let child = PlaceR (ImmutablePlace owner id (path ++ [ValueSubscript (IntV i)])) in
  let in_range = idx_in_range (is_signed_type (expr_type e)) iw
    (n2w (array_length (ArrayTV etv bd) av)) in
    extend_place cx (PlaceR (ImmutablePlace owner id path)) (ValueSubscript (IntV i)) mid2 =
      ((if in_range then INL child else
         INR (Error (RuntimeError "evaluate_subscripts array_index"))),mid2) /\
    (in_range ==>
      write_target_location_mods cenv cx (SubscriptTarget bt e) mid2 child vt r G3 t3 /\
      target_ptr_ok cenv child r G3 tn3 t3)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  drule_all immutable_extend_array_source >>
  disch_then (qspec_then `i` (strip_assume_tac o
    CONV_RULE (REDEPTH_CONV BETA_CONV) o REWRITE_RULE [LET_THM, Excl "valid_index_def"])) >>
  `valid_index (ArrayTV etv bd) av i <=> idx_in_range (is_signed_type (expr_type e)) iw
      (n2w (array_length (ArrayTV etv bd) av))` by
    (irule array_index_word_bounds >> simp[] >> drule_all target_memory_array_length_bound >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `i = _` kall_tac >> fs[Excl "valid_index_def"]) >>
  strip_tac >>
  `0 <= i` by fs[valid_index_def, IgnAsm `i = _`] >>
  `w2n iw = Num i` by
    (Cases_on `is_signed_type (expr_type e)` >> gvs[nonneg_w2i_eq_w2n]) >>
  `evaluate_type (get_tenv cx) et = SOME etv` by
    fs[evaluate_type_def, AllCaseEqs()] >>
  drule_all write_array_reached_immutable_mods >> strip_tac >>
  drule_all write_array_reached_posts_mods >> strip_tac >>
  drule write_target_post_view_mods >> strip_tac >>
  fs[write_array_reached_mods_def] >>
  `target_place_type cenv bt = SOME (ValPT (ArrayT et bd))` by
    (drule_all qualified_immutable_target_type >> simp[]) >>
  `vt = Type et` by
    gvs[type_place_target_SubscriptTarget, subscript_vtype_def, AllCaseEqs()] >>
  `type_memory_bytes cenv et = type_memory_size etv` by
    (irule typed_copy_memory_size >> qexists `get_tenv cx` >>
     fs[expr_sim_inv_mods_def] >> rpt strip_tac >>
     qpat_assum `!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==> _` drule >> simp[]) >>
  rename1 `mem_path_offset pre_tv path = SOME (_,ptv)` >>
  `pre_tv = itv` by
    (irule linked_immutable_type_agrees >>
     goal_assum (drule_at (Pat `FLOOKUP (get_source_immutables _ _) _ = SOME (pre_tv,_)`)) >>
     goal_assum (drule_at (Pat `FLOOKUP (get_source_immutables _ _) _ = SOME (itv,_)`)) >>
     goal_assum (drule_at (Pat `ALOOKUP mid1.immutables _ = _`)) >>
     goal_assum (drule_at (Pat `ALOOKUP mid2.immutables _ = _`)) >>
     qexistsl [`cenv`,`env`,`mods`,`off`] >> simp[]) >>
  `SND (SND rb) = SOME (ValPT (ArrayT et bd))` by fs[exprLoweringTheory.value_type_place_def] >>
  drule_all write_array_select_cut_mods >> strip_tac >>
  fs[write_array_select_frame_def] >>
  simp[target_ptr_ok_def, write_target_location_mods_def, target_root_def] >>
  conj_tac
  >- (PairCases_on `r` >> gvs[]) >>
  conj_tac
  >- (`iw = n2w (Num i)` by metis_tac[n2w_w2n] >>
      Cases_on `bd` >>
      simp[word_scale_def, elem_size_in_location_def, is_slot_addressed_def,
           word_mul_n2w, word_add_n2w, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  qpat_x_assum `ValPT _ = value_type_place _` kall_tac >>
  Cases_on `bd` >> simp[target_through_dynarray_def] >>
  strip_tac >> irule bodyFullTargetRootsTheory.immutable_target_fixed_snoc >>
  simp[] >> qexistsl [`k`, `ArrayTV etv (Fixed n)`] >> gvs[]
QED
