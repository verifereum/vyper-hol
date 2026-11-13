(* The body invariant supplies decoder headers in descended type environments. *)
Theory extcallDecoderCallerMemory
Ancestors
  exprSimHyps exprSimHypsDefs abiTypeBoundProps retAbiPlanProps sourceAbiShape
  abiCallerTupleLayout abiDecoderCoherence abiDecodeRanges compileEnv
  abiDecoderPrimitiveCaller abiDecoderConstructors
  valueEncoding vyperValue vyperABI contractABI vyperTypeSystem vyperTypeABI finite_map list

Theorem extcall_decoder_header:
  expr_sim_inv cenv cx root es /\ env SUBMAP get_tenv cx /\
  evaluate_type env ty = SOME tv ==>
  abi_decoder_header cenv env ty tv
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) ty = SOME tv /\
   vyper_to_abi_type env ty = vyper_to_abi_type (get_tenv cx) ty` by
    (irule (cj 1 vyper_to_abi_type_submap) >> simp[]) >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    (irule expr_sim_inv_memory_size >> metis_tac[]) >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    fs[expr_sim_inv_def] >>
  drule_all abi_props_vyper_typed >> strip_tac >>
  `is_dynamic (vyper_to_abi_type (get_tenv cx) ty) =
     vyper_is_dynamic (get_tenv cx) ty` by
    simp[source_abi_dynamic_shape] >>
  simp[abi_decoder_header_def] >>
  Cases_on `is_dynamic (vyper_to_abi_type (get_tenv cx) ty)` >>
  gvs[abi_embedded_static_size_def, abi_member_head_size_def] >>
  drule_all (cj 1 vyper_to_abi_static_length) >>
  drule_all abi_caller_static_memory >> simp[vyper_abi_size_bound_def]
QED

Theorem extcall_decoder_struct_fields[local]:
  expr_sim_inv cenv cx root es /\ env SUBMAP get_tenv cx /\
  sf SUBMAP cenv.ce_struct_fields /\
  FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
  MAP FST fields = MAP FST args /\
  MAP (FST o SND) fields = MAP SND args /\
  EVERY (assignable_type (env \\ nsid)) (MAP SND args) ==>
  MAP (\(name,ty,sz). (name,ty)) fields = args /\
  EVERY (\(name,ty,sz). sz = type_memory_bytes cenv ty) fields
Proof
  strip_tac >> conj_tac
  >- (`MAP FST (MAP (\(name,ty,sz). (name,ty)) fields) = MAP FST fields` by
        (rewrite_tac[MAP_MAP_o] >> irule MAP_CONG >>
         simp[pairTheory.FORALL_PROD, combinTheory.o_DEF]) >>
      `MAP SND (MAP (\(name,ty,sz). (name,ty)) fields) = MAP (FST o SND) fields` by
        (rewrite_tac[MAP_MAP_o] >> irule MAP_CONG >>
         simp[pairTheory.FORALL_PROD, combinTheory.o_DEF]) >>
      metis_tac[LIST_EQ_MAP_PAIR]) >>
  `FLOOKUP cenv.ce_struct_fields (nsid_to_string nsid) = SOME fields` by
    (irule FLOOKUP_SUBMAP >> qexists_tac `sf` >> simp[]) >>
  `env \\ nsid SUBMAP get_tenv cx` by
    (irule SUBMAP_TRANS >> qexists_tac `env` >> simp[]) >>
  `EVERY (assignable_type (env \\ nsid)) (MAP (FST o SND) fields)` by metis_tac[] >>
  simp[EVERY_MEM, pairTheory.FORALL_PROD] >>
  map_every qx_gen_tac [`name`, `fty`, `sz`] >> strip_tac >>
  `assignable_type (env \\ nsid) fty` by
    (fs[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD, combinTheory.o_DEF] >>
     metis_tac[]) >>
  `?ftv. evaluate_type (env \\ nsid) fty = SOME ftv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def,
      optionTheory.IS_SOME_EXISTS] >>
  `evaluate_type (get_tenv cx) fty = SOME ftv` by
    metis_tac[cj 1 vyper_to_abi_type_submap] >>
  `type_memory_bytes cenv fty = type_memory_size ftv` by
    (irule expr_sim_inv_memory_size >> metis_tac[]) >>
  fs[expr_sim_inv_def] >>
  qpat_x_assum `!name fields. _ ==> ALL_DISTINCT _ /\ EVERY _ _` drule >>
  simp[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]
QED

Theorem extcall_decoder_coherent_upto[local]:
  !tv env ty sf.
    expr_sim_inv cenv cx root es /\ env SUBMAP get_tenv cx /\
    evaluate_type env ty = SOME tv /\ assignable_type env ty /\
    sf SUBMAP cenv.ce_struct_fields /\
    abi_sfields_consistent_upto (type_value_size tv) sf env ==>
    abi_decoder_coherent cenv env sf ty tv
Proof
  measureInduct_on `type_value_size tv` >> rpt gen_tac >> strip_tac >>
  `abi_decoder_header cenv env ty tv` by
    (irule extcall_decoder_header >> metis_tac[]) >>
  Cases_on `ty`
  >~ [`BaseT bt`]
  >- metis_tac[abi_decoder_base_caller_coherent]
  >~ [`ArrayT elem bound`] >- suspend "array"
  >~ [`TupleT tys`] >- suspend "tuple"
  >~ [`StructT nsid`] >- suspend "struct"
  >~ [`FlagT nsid`] >- suspend "flag" >>
  fs[assignable_type_def]
QED

Resume extcall_decoder_coherent_upto[array]:
  gvs[Once evaluate_type_def, AllCaseEqs(), Once assignable_type_def] >>
  irule decoder_caller_array >>
  conj_tac >- simp[Once evaluate_type_def] >>
  first_x_assum irule >> simp[] >>
  irule abi_sfields_consistent_upto_mono >>
  qexists_tac `type_value_size (ArrayTV tv' bound)` >> simp[]
QED

Resume extcall_decoder_coherent_upto[tuple]:
  gvs[Once evaluate_type_def, AllCaseEqs(), Once assignable_type_def] >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  fs[LIST_REL_EL_EQN] >>
  irule decoder_caller_tuple >>
  conj_tac >- simp[Once evaluate_type_def] >>
  simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  `evaluate_type env (EL n tys) = SOME (EL n tvs)` by
    fs[LIST_REL_EL_EQN] >>
  `MEM (EL n tys) tys` by (simp[MEM_EL] >> qexists_tac `n` >> simp[]) >>
  `evaluate_type env (TupleT tys) = SOME (TupleTV tvs)` by
    simp[Once evaluate_type_def] >>
  drule_all evaluate_type_tuple_child_size >> strip_tac >>
  gvs[] >> first_x_assum irule >>
  simp[] >> conj_tac >- fs[EVERY_EL] >>
  irule abi_sfields_consistent_upto_mono >>
  qexists_tac `type_value_size (TupleTV tvs)` >> simp[]
QED

Resume extcall_decoder_coherent_upto[flag]:
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  simp[abi_decoder_coherent_flag_iff] >>
  `FLOOKUP (get_tenv cx) nsid = SOME (FlagArgs m)` by
    (irule FLOOKUP_SUBMAP >> qexists_tac `env` >> simp[]) >>
  fs[expr_sim_inv_def] >> metis_tac[]
QED

Resume extcall_decoder_coherent_upto[struct]:
  gvs[Once evaluate_type_def, AllCaseEqs(), Once assignable_type_def] >>
  rename1 `FLOOKUP env nsid = SOME (StructArgs source_fields)` >>
  rename1 `evaluate_types (env \\ nsid) (MAP SND source_fields) [] = SOME field_tvs` >>
  `evaluate_type env (StructT nsid) =
     SOME (StructTV (ZIP (MAP FST source_fields,field_tvs)))` by
    fs[abi_decoder_header_def] >>
  `type_value_size (StructTV (ZIP (MAP FST source_fields,field_tvs))) <=
     list_size (pair_size (list_size char_size) type_value_size)
       (ZIP (MAP FST source_fields,field_tvs)) + 1` by simp[] >>
  drule_all abi_sfields_consistent_upto_lookup >> strip_tac >>
  `EVERY (assignable_type (env \\ nsid)) (MAP SND source_fields)` by
    fs[EVERY_MAP, combinTheory.o_DEF] >>
  drule_all extcall_decoder_struct_fields >> strip_tac >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  fs[LIST_REL_EL_EQN] >>
  simp[abi_decoder_coherent_struct_iff] >>
  qexists_tac `field_tvs` >> simp[] >>
  simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  `evaluate_type (env \\ nsid) (EL n (MAP SND source_fields)) =
     SOME (EL n field_tvs)` by simp[] >>
  `MEM (EL n (MAP SND source_fields)) (MAP SND source_fields)` by
    (simp[MEM_EL] >> qexists_tac `n` >> simp[]) >>
  drule_all evaluate_type_struct_child_size >> strip_tac >> gvs[] >>
  first_x_assum irule >> simp[] >> conj_tac
  >- (irule SUBMAP_TRANS >> qexists_tac `sf` >> simp[]) >>
  conj_tac >- (irule SUBMAP_TRANS >> qexists_tac `env` >> simp[]) >>
  conj_tac >- fs[EVERY_EL] >>
  irule abi_sfields_consistent_upto_domsub >> conj_tac >- metis_tac[] >>
  qpat_assum `evaluate_type env (StructT nsid) = SOME _` (irule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Finalise extcall_decoder_coherent_upto

Theorem extcall_decoder_caller_coherent:
  expr_sim_inv cenv cx env es /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  assignable_type (get_tenv cx) ty ==>
  abi_decoder_coherent cenv (get_tenv cx) cenv.ce_struct_fields ty tv
Proof
  strip_tac >> irule extcall_decoder_coherent_upto >>
  simp[] >> conj_tac
  >- (irule abi_sfields_consistent_upto_init >> fs[expr_sim_inv_def]) >>
  qexistsl_tac [`cx`, `es`, `env`] >> simp[]
QED
