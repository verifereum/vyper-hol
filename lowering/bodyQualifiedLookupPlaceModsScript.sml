(* The immutable cell belongs to the selected module, not to the caller. *)
Theory bodyQualifiedLookupPlaceMods
Ancestors
  bodyFullPostsMods bodyInvSplit exprBodyPreProps exprSimHypsDefs
  loweringPosts loweringStateRelDefs context vyperBareGlobalName vyperTypeEnv
  vyperTypeInvariants vyperInterpreter vyperState vyperContext venomState
  moduleVariableKeyProps supportedNameRoot list finite_map alist words

Theorem allocated_immutable_not_constant[local]:
  contract_inv mods exps ctx cenv cx /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) ==>
  ~cx_const_name_mods mods (src,id)
Proof
  rpt strip_tac >>
  drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
    contract_inv_immutable_section_layout >>
  `?bytes. immutable_region_mods mods src id off bytes` by metis_tac[] >>
  qpat_x_assum `immutable_region_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_region_mods_def]) >>
  `MEM (VariableDecl vis Immutable id ty slot) tops` by simp[] >>
  drule_then assume_tac contract_inv_unqualified_variable_keys >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))`
    by metis_tac[] >>
  `supported_variable_decl tops (NONE,id) = SOME (vis,Immutable,ty,slot)` by
    metis_tac[supported_variable_decl_distinct_mem] >>
  fs[cx_const_name_mods_def] >>
  `MEM id (MAP FST (module_consts_env tops []))` by metis_tac[optionTheory.SOME_11] >>
  drule distinct_module_consts_env_names_constant >>
  disch_then (qspec_then `id` mp_tac) >> simp[]
QED

Theorem qualified_lookup_place_mods:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  get_module_code cx src = SOME tops /\
  immutable_frame_mods func cenv cx es s /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  lookup_immutable cx es src id = SOME (rt,v) /\
  evaluate_type (get_tenv cx) ann = SOME rt ==>
  ALOOKUP cenv.ce_modules src = SOME tops /\
  off + type_memory_size rt < dimword (:256) /\
  read_result cx (PlaceR (ImmutablePlace src id [])) es = (INL v,es) /\
  vv_holds_mods cenv cx ann (PlaceR (ImmutablePlace src id []))
    (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode)) es s /\
  vv_place_ptr_mods cenv cx es s (PlaceR (ImmutablePlace src id []))
    (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode)) /\
  immutable_value_admissible rt v /\
  (~cenv.ce_is_ctor ==> off + type_memory_size rt <= LENGTH s.vs_data_section) /\
  val_in_memory rt v off (if cenv.ce_is_ctor then s.vs_memory else s.vs_data_section)
Proof
  strip_tac >> drule_all_then assume_tac allocated_immutable_not_constant >>
  qpat_x_assum `lookup_immutable _ _ _ _ = _` mp_tac >>
  simp[lookup_immutable_def, AllCaseEqs()] >>
  disch_then (qx_choose_then `imms` strip_assume_tac) >>
  `ALOOKUP cenv.ce_modules src = SOME tops /\
   ?ty. FLOOKUP env.bare_globals (src,id) = SOME ty` by
    (gvs[expr_sim_inv_mods_def, bare_globals_layout_def] >> metis_tac[]) >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `evaluate_type (get_tenv cx) ty = SOME rt` by
    (fs[env_consistent_def, env_immutables_consistent_def] >>
     qpat_assum `!src id ty tv v. _` (qspecl_then [`src`,`id`,`ty`,`rt`,`v`] mp_tac) >>
     simp[]) >>
  `off + type_memory_size rt < dimword (:256)` by
    (fs[expr_sim_inv_mods_def] >>
     qpat_assum `!src id ty. _ /\ (~cx_const_name_mods _ _ \/ _) ==> _`
       (qspecl_then [`src`,`id`,`ty`] mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (mp_tac o CONJUNCT2) >> (impl_tac >- simp[]) >>
     disch_then strip_assume_tac >>
     qpat_assum `!tv. evaluate_type _ ty = SOME tv ==> _`
       (qspec_then `rt` mp_tac) >> gvs[]) >>
  `value_has_type rt v` by
    (fs[expr_sim_inv_mods_def] >>
     drule_all_then assume_tac state_well_typed_immutables_ALOOKUP >>
     drule_all imms_well_typed_get_source_immutables >> simp[]) >>
  `read_result cx (PlaceR (ImmutablePlace src id [])) es = (INL v,es)` by
    simp[read_result_def, read_place_def, get_immutables_def,
         get_address_immutables_def, lift_option_type_def, bind_def,
         return_def, evaluate_subscripts_def, lift_sum_def] >>
  simp[vv_holds_mods_def, vv_place_ptr_mods_def, vv_place_ptr_def,
       mk_ptr_def, eval_operand_def, mem_path_offset_def] >>
  conj_tac >-
    (simp[immutable_holds_mods_def] >> qexistsl [`src`,`tops`] >>
     simp[immutable_holds_def] >> qexistsl [`id`,`off`,`rt`,`v`,`0`] >>
     simp[sub_layout_def]) >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def] >>
  `immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es s` by metis_tac[] >>
  fs[immutables_rel_def] >> metis_tac[]
QED
