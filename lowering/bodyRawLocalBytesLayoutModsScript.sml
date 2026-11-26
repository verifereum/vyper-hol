(* Local byte ownership is disjoint from the length words exempted by
   locals_kept. This uses linked type-table facts, not singleton code facts. *)
Theory bodyRawLocalBytesLayoutMods
Ancestors
  exprSimAttributeFields exprSimFieldLayout exprSimProps exprSimHypsDefs
  loweringPosts compileEnv typedMemoryCopy placeMemoryTypedBase
  vyperTypeABI vyperValue valueEncoding list rich_list pair finite_map
Libs pairLib

Triviality offset_layout_tables:
  expr_sim_inv_mods mods cenv cx env es ==>
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    EVERY (\(nm,ty,sz). !tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
                            sz = type_memory_size tv) fields)
Proof
  simp[expr_sim_inv_mods_def] >> strip_tac >> simp[] >> rpt gen_tac >>
  disch_tac >> qpat_assum `!name fields. FLOOKUP _ name = SOME fields ==> ALL_DISTINCT _ /\ _`
    drule >> simp[]
QED

Triviality offset_fields_layout_lookup:
  !fields tvs.
    OPT_MMAP f (MAP (FST o SND) fields) = SOME tvs /\
    EVERY (\(nm,ty,sz). !tv. f ty = SOME tv ==> sz = type_memory_size tv) fields ==>
    fields_layout fields (ZIP (MAP FST fields,tvs)) /\
    !id ty sz. ALOOKUP fields id = SOME (ty,sz) ==>
      ?tv. ALOOKUP (ZIP (MAP FST fields,tvs)) id = SOME tv /\ f ty = SOME tv
Proof
  Induct >- simp[fields_layout_def] >>
  PairCases >> rpt gen_tac >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  fs[fields_layout_def] >> rpt gen_tac >> IF_CASES_TAC >> simp[] >>
  rpt strip_tac >> gvs[]
QED

Triviality offset_struct_step:
  expr_sim_inv_mods mods cenv cx env es /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME tv /\
  type_step_offset cenv (StructT sid) (AttrSubscript id) = SOME (k,pt) ==>
  ?ptv. mem_step_offset tv (AttrSubscript id) = SOME (k,ptv) /\
        evaluate_type (get_tenv cx) pt = SOME ptv
Proof
  strip_tac >> drule_then strip_assume_tac offset_layout_tables >>
  drule_all_then strip_assume_tac typed_memory_struct_evaluation >>
  `EVERY (\(nm,ty,sz). !tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
                            sz = type_memory_size tv) fields` by
    (first_assum irule >> goal_assum (drule_at Any)) >>
  gvs[vyperValueTheory.evaluate_types_OPT_MMAP, type_step_offset_def,
      get_struct_fields_def, AllCaseEqs(), EXISTS_PROD] >>
  `OPT_MMAP (evaluate_type (get_tenv cx)) (MAP (FST o SND) fields) = SOME tvs` by simp[] >>
  drule_all_then strip_assume_tac offset_fields_layout_lookup >>
  qpat_assum `!id ty sz. ALOOKUP fields id = _ ==> _` (drule_then strip_assume_tac) >>
  drule_all_then assume_tac mem_field_offset_layout >>
  qpat_assum `MAP FST fields = MAP FST args` (rewrite_tac o single o SYM) >>
  simp[mem_step_offset_def]
QED

Triviality offset_tuple_sizes:
  !tys tvs i.
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      EVERY (\(nm,ty,sz). !tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
                              sz = type_memory_size tv) fields) ==>
    SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) =
      type_memory_size_list (TAKE i tvs)
Proof
  Induct >- simp[type_memory_size_def] >>
  rpt gen_tac >> Cases_on `i` >> simp[type_memory_size_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> drule_all_then assume_tac typed_copy_memory_size >>
  first_x_assum drule_all >> simp[type_memory_size_def]
QED

Triviality offset_tuple_step:
  expr_sim_inv_mods mods cenv cx env es /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME tv /\
  type_step_offset cenv (TupleT tys) (ValueSubscript (IntV i)) = SOME (k,pt) ==>
  ?ptv. mem_step_offset tv (ValueSubscript (IntV i)) = SOME (k,ptv) /\
        evaluate_type (get_tenv cx) pt = SOME ptv
Proof
  strip_tac >> drule_then strip_assume_tac offset_layout_tables >>
  gvs[type_step_offset_def, evaluate_type_def, AllCaseEqs(),
      evaluate_types_OPT_MMAP] >>
  drule_all_then strip_assume_tac opt_mmap_el >>
  simp[mem_step_offset_def] >> sym_tac >> irule offset_tuple_sizes >>
  goal_assum (drule_at Any) >> simp[]
QED

Triviality offset_array_step:
  expr_sim_inv_mods mods cenv cx env es /\
  evaluate_type (get_tenv cx) (ArrayT ty bd) = SOME tv /\
  type_step_offset cenv (ArrayT ty bd) (ValueSubscript (IntV i)) = SOME (k,pt) ==>
  ?ptv. mem_step_offset tv (ValueSubscript (IntV i)) = SOME (k,ptv) /\
        evaluate_type (get_tenv cx) pt = SOME ptv
Proof
  strip_tac >> drule_then strip_assume_tac offset_layout_tables >>
  Cases_on `bd` >> gvs[type_step_offset_def, evaluate_type_def, AllCaseEqs()] >>
  drule_all_then assume_tac typed_copy_memory_size >> simp[mem_step_offset_def]
QED

Triviality offset_step_mods:
  expr_sim_inv_mods mods cenv cx env es /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_step_offset cenv ty sb = SOME (k,pt) ==>
  ?ptv. mem_step_offset tv sb = SOME (k,ptv) /\
        evaluate_type (get_tenv cx) pt = SOME ptv
Proof
  Cases_on `ty` >> Cases_on `sb` >>
  TRY (rename1 `ValueSubscript x` >> Cases_on `x`) >>
  FIRST [MATCH_ACCEPT_TAC offset_struct_step,
         MATCH_ACCEPT_TAC offset_tuple_step,
         MATCH_ACCEPT_TAC offset_array_step,
         simp[type_step_offset_def]]
QED

Theorem type_path_offset_mem_mods:
  !path ty tv k pt.
    expr_sim_inv_mods mods cenv cx env es /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    type_path_offset cenv ty path = SOME (k,pt) ==>
    ?ptv. mem_path_offset tv path = SOME (k,ptv) /\
          evaluate_type (get_tenv cx) pt = SOME ptv
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[type_path_offset_def, mem_path_offset_def] >>
  gvs[type_path_offset_def, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  drule_all_then strip_assume_tac offset_step_mods >>
  first_x_assum drule_all >> strip_tac >> simp[mem_path_offset_def]
QED

Triviality offset_local_dynarray_apart:
  expr_sim_inv_mods mods cenv cx env es /\
  local_path_at cenv cx n k (BaseTV bt) /\
  dynarray_len_at cenv n k' ==>
  k + type_memory_size (BaseTV bt) <= k' \/ k' + 32 <= k
Proof
  rw[local_path_at_def, dynarray_len_at_def] >> gvs[] >>
  drule_all_then strip_assume_tac type_path_offset_mem_mods >>
  qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
  simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  `dynarray_free (BaseTV bt)` by simp[dynarray_free_base] >>
  drule_all mem_path_offset_dynarray_apart >> simp[]
QED

Theorem local_bytes_dynarray_apart_mods:
  expr_sim_inv_mods mods cenv cx env es /\
  local_val_at cenv cx n k (BaseTV (BytesT (Dynamic cap))) (BytesV bs) /\
  val_wf (BaseTV (BytesT (Dynamic cap))) (BytesV bs) /\
  dynarray_len_at cenv n k' ==>
  k + val_footprint (BaseTV (BytesT (Dynamic cap))) (BytesV bs) <= k' \/ k' + 32 <= k
Proof
  rw[local_val_at_def]
  >- (drule_all offset_local_dynarray_apart >> drule val_footprint_le >> decide_tac) >>
  drule_all offset_local_dynarray_apart >> decide_tac
QED
