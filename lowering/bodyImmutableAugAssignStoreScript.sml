Theory bodyImmutableAugAssignStore
Ancestors
  bodyImmutableAugAssignFacts bodySim exprSimHypsDefs compileEnv
  exprLoweringProps immutableConstructorRelation immutableMemoryFrame
  immutableEncoding immutableEncodingProofs immutableValue valueEncodingProps
  localPtrsProps vyperState vyperInterpreter vyperValueOperation
  finite_map alist list vyperValue vyperTyping valueEncoding
  vyperTypeInitialState loweringSlice valueMemoryTransport venomMemProps
  exprSimProps

Theorem immutable_augassign_write_source:
  ALOOKUP st.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (tv,old) ==>
  write_place cx (ImmutablePlace src id []) v st =
    (INL (), st with immutables :=
      (cx.txn.target, update_immutable src id tv v imms) ::
      ADELKEY cx.txn.target st.immutables)
Proof
  strip_tac >>
  simp[write_place_def, get_immutables_def, get_address_immutables_def,
       bind_def, return_def, lift_option_type_def, lift_sum_def,
       assign_subscripts_def, set_immutable_def, set_address_immutables_def,
       update_immutable_def, evaluation_state_component_equality]
QED

Theorem immutable_augassign_local_frame:
  stmt_state_rel ctx func cenv cx es ss /\ cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  cenv.ce_module_var_type (cenv.ce_module,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ type_memory_size tv = 32 ==>
  local_ptrs_rel func cenv es.scopes (mstore off w ss)
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes ss` by
    fs[stmt_state_rel_def, state_rel_def] >>
  irule local_ptrs_rel_mstore >> simp[] >>
  rpt strip_tac >>
  `immutable_decl_sep cenv cx es.scopes ss.vs_vars ss.vs_allocas
     ss.vs_alloca_next` by
    fs[stmt_state_rel_def, immutable_alloca_sep_def] >>
  fs[immutable_decl_sep_alt] >>
  first_x_assum drule_all >> strip_tac >>
  fs[regions_disjoint_def] >> metis_tac[]
QED

Theorem immutable_augassign_word_encoding:
  evaluate_type tenv ty = SOME tv /\ is_word_type ty /\
  value_has_type tv v ==>
  type_memory_size tv = 32 /\ immutable_value_admissible tv v /\
  encode_immutable_value tv v = word_to_bytes (typed_val_to_w256 tv v) T
Proof
  Cases_on `ty` >>
  simp[is_word_type_def, evaluate_type_def] >>
  rpt strip_tac >> gvs[] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt`) >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
  gvs[is_word_type_def, evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[value_has_type_def, type_memory_size_def,
      immutable_value_admissible_def, encode_immutable_value_def,
      immutable_fit_def, immutable_word_bytes_def,
      byteTheory.LENGTH_word_to_bytes,
      fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  simp[listTheory.TAKE_APPEND1, byteTheory.LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``, wordsTheory.dimword_def]
QED

Theorem immutable_augassign_word_representation:
  evaluate_type tenv ty = SOME tv /\ is_word_type ty /\
  value_has_type tv v ==>
  val_in_memory tv v off (mstore off (typed_val_to_w256 tv v) ss).vs_memory /\
  immutable_value_bytes_rel tv v
    (mem_bytes_at off (type_memory_size tv)
      (mstore off (typed_val_to_w256 tv v) ss).vs_memory)
Proof
  strip_tac >> drule_all immutable_augassign_word_encoding >> strip_tac >>
  pure_rewrite_tac[immutable_mstore_as_write] >>
  pure_once_rewrite_tac[GSYM immutable_istore_as_write] >>
  irule immutable_word_store_representation >> simp[]
QED

Theorem immutable_augassign_relation_update:
  immutables_rel cenv addr src T es ss /\
  ALOOKUP es.immutables addr = SOME imms /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  evaluate_type tenv ty = SOME tv /\ is_word_type ty /\ value_has_type tv v /\
  (!name ot ov at.
    name <> id /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc at) /\
    FLOOKUP (get_source_immutables src imms) name = SOME (ot,ov) ==>
    regions_disjoint off 32 at (type_memory_size ot)) ==>
  immutables_rel cenv addr src T
    (es with immutables :=
      (addr,update_immutable src id tv v imms)::ADELKEY addr es.immutables)
    (mstore off (typed_val_to_w256 tv v) ss)
Proof
  strip_tac >>
  simp[immutables_rel_def, update_immutable_def,
       get_source_immutables_set_same, FLOOKUP_UPDATE] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `name = id`
  >- (gvs[] >>
      drule_all immutable_augassign_word_representation >> strip_tac >>
      drule_all immutable_augassign_word_encoding >> simp[]) >>
  gvs[] >>
  `immutable_value_admissible tv' v' /\
   val_in_memory tv' v' byte_offset ss.vs_memory /\
   immutable_value_bytes_rel tv' v'
     (mem_bytes_at byte_offset (type_memory_size tv') ss.vs_memory)` by
    (fs[immutables_rel_def] >> metis_tac[]) >>
  `regions_disjoint off 32 byte_offset (type_memory_size tv')` by metis_tac[] >>
  `mem_bytes_at byte_offset (type_memory_size tv')
     (mstore off (typed_val_to_w256 tv v) ss).vs_memory =
   mem_bytes_at byte_offset (type_memory_size tv') ss.vs_memory` by
    (irule mstore_mem_bytes_at_disjoint >> fs[regions_disjoint_def] >> decide_tac) >>
  simp[] >> irule val_in_memory_transport >>
  conj_tac >- metis_tac[immutable_admissible_val_wf] >>
  qexistsl_tac [`ss.vs_memory`, `byte_offset`] >> simp[]
QED

Theorem immutable_augassign_regions:
  expr_sim_inv cenv cx env es /\
  FLOOKUP env.bare_globals (src,id) = SOME ty /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ is_word_type ty /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  name <> id /\
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc at) /\
  FLOOKUP (get_source_immutables src imms) name = SOME (ot,ov) ==>
  regions_disjoint off 32 at (type_memory_size ot)
Proof
  strip_tac >>
  `?oty. FLOOKUP env.bare_globals (src,name) = SOME oty` by
    (fs[expr_sim_inv_def, bare_globals_layout_def] >> metis_tac[]) >>
  drule_all immutable_augassign_entry >> strip_tac >> gvs[] >>
  `type_memory_size tv = 32` by metis_tac[word_tv_memory_size] >>
  fs[expr_sim_inv_def, bare_globals_layout_def] >>
  qpat_x_assum `!src id1 id2 ty1 ty2 off1 off2 tv1 tv2. _` mp_tac >>
  disch_then (drule_at Any) >> simp[] >>
  disch_then drule_all >> simp[regions_disjoint_def] >> decide_tac
QED

Theorem immutable_augassign_alloca_sep_update:
  immutable_alloca_sep func cenv cx es ss /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables cenv.ce_module imms) id = SOME (tv,old) ==>
  immutable_alloca_sep func cenv cx
    (es with immutables :=
      (cx.txn.target,update_immutable cenv.ce_module id tv v imms)::
      ADELKEY cx.txn.target es.immutables)
    (mstore off w ss)
Proof
  simp[immutable_alloca_sep_def, venomStateTheory.mstore_def,
       update_immutable_def, get_source_immutables_set_same,
       local_region_def, venomStateTheory.lookup_var_def, FLOOKUP_UPDATE] >>
  strip_tac >> simp[] >> rpt strip_tac >>
  Cases_on `name = id` >> gvs[] >> metis_tac[]
QED

Theorem immutable_augassign_store:
  body_inv tops ctx cenv cx /\ cx.in_deploy /\
  expr_sim_inv cenv cx env es /\ stmt_state_rel ctx func cenv cx es ss /\
  FLOOKUP env.bare_globals (cenv.ce_module,id) = SOME ty /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  cenv.ce_module_var_type (cenv.ce_module,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ is_word_type ty /\
  value_has_type tv v /\
  write_place cx (ImmutablePlace cenv.ce_module id []) v es = (INL (),es') ==>
  stmt_state_rel ctx func cenv cx es'
    (mstore off (typed_val_to_w256 tv v) ss)
Proof
  strip_tac >>
  `cenv.ce_is_ctor` by fs[body_inv_def] >>
  drule_all immutable_augassign_entry >> strip_tac >> gvs[] >>
  drule_all immutable_augassign_write_source >> strip_tac >> gvs[] >>
  `type_memory_size tv = 32` by metis_tac[word_tv_memory_size] >>
  `local_ptrs_rel func cenv es.scopes
     (mstore off (typed_val_to_w256 tv v) ss)` by
    (irule immutable_augassign_local_frame >> metis_tac[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module T
     (es with immutables :=
       (cx.txn.target,update_immutable cenv.ce_module id tv v imms)::
       ADELKEY cx.txn.target es.immutables)
     (mstore off (typed_val_to_w256 tv v) ss)` by
    (irule immutable_augassign_relation_update >>
     simp[] >> reverse conj_tac
     >- (conj_tac >- metis_tac[] >> fs[stmt_state_rel_def, state_rel_def]) >>
     rpt strip_tac >> irule immutable_augassign_regions >> metis_tac[]) >>
  `immutable_alloca_sep func cenv cx
     (es with immutables :=
       (cx.txn.target,update_immutable cenv.ce_module id tv v imms)::
       ADELKEY cx.txn.target es.immutables)
     (mstore off (typed_val_to_w256 tv v) ss)` by
    (irule immutable_augassign_alloca_sep_update >>
     metis_tac[stmt_state_rel_def]) >>
  fs[stmt_state_rel_def, state_rel_def] >>
  gvs[stmt_state_rel_def, state_rel_def, venomStateTheory.mstore_def,
       storage_rel_def, transient_rel_def, accounts_rel_def, logs_rel_def,
       venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def,
       venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def,
       alloca_room_def, fmp_room_def,
       pending_alloca_size_def, immutable_base_zero_def] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
