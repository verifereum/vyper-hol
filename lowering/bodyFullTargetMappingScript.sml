(* The element suffix of a subscript into a mapping target on the joint
   line: the key's hash (for a bytestring key) and the slot computation
   after the index (subscript_tail_full, bodyFullTargetSubscript).

   TOP-LEVEL:
     target_mapping_tail_full -- subscript_tail_full when the base is a
       mapping *)
Theory bodyFullTargetMapping
Ancestors
  bodyFullTargetSubscript bodyFullTargetDefs bodySimFull targetPlaceSim
  bodyFullTargetMappingFacts bodyFullTargetMappingKey bodyFullTargetMappingScratch
  targetSubscriptMapping targetSubscriptSplit vyperStorageTrace
  gasOutcomeFull fragGasOriginPtr vyperStorageFootprint loweringPosts
  vyperTypeSystem vyperInterpreter vyperState

Theorem target_mapping_tail_full:
  body_inv tops ctx cenv cx /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  type_place_target env bt = SOME (HashMapT kt vt) ==>
  subscript_tail_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt e es
Proof
  strip_tac >> simp[subscript_tail_full_def] >> rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace)
     mid2.storage_trace` by gvs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid2.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all target_mapping_source_cut >> strip_tac >> gvs[] >>
  drule_all target_mapping_compile_cut >> strip_tac >>
  Cases_on `extend_place cx (HashMapRef tr base_slot (expr_type e) vt)
    (ValueSubscript v) mid2` >> rename1 `extend_place _ _ _ _ = (res,ee)` >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     storage_well_formed_on cx mid2 (FST H)` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H mid2.storage_trace` by
       metis_tac[valid_horizon_frame, storage_trace_frame_extend_place] >>
     qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >> gvs[expr_post_def]) >>
  suspend "join"
QED

Resume target_mapping_tail_full[join]:
  cheat
QED

Finalise target_mapping_tail_full
