(* Static layout at the linked external-return cut. *)
Theory bodyExtReturnLayoutMods
Ancestors
  exprBodyPreProps exprSimHypsDefs vyperTypeInvariants allocLimits
  typedMemoryCopy exprExtReturnDecodeMetadata exprExtReturnDecodeCoherence
  exprSimAbiDecodeMinimumLayout exprSimAbiDecodeComplexOutcome
  exprLoweringProps exprLowering abiDecoderLayoutBounds abiDecoderCoherence
  abiTypeBoundProps vyperTypeSystem vyperTyping vyperValue vyperABI
  compileEnv contractABI words arithmetic

Theorem extcall_linked_root_metadata[local]:
  expr_body_pre_mods mods ce cx env e es ==>
  env.type_defs = get_tenv cx /\ abi_decode_root_metadata ce (get_tenv cx)
Proof
  strip_tac >> drule expr_body_pre_mods_inv >> strip_tac >> conj_tac
  >- (drule expr_sim_inv_mods_env >>
      simp[vyperTypeInvariantsTheory.env_consistent_def,
           vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  fs[expr_sim_inv_mods_def, abi_decode_root_metadata_def] >> metis_tac[]
QED

Theorem extcall_linked_return_type[local]:
  expr_body_pre_mods mods ce cx env
    (Call ann (ExtCall stat skip (fname,arg_types,ty) opts) args dflt) es /\
  ty <> NoneT ==>
  ann = ty /\ well_formed_type (get_tenv cx) ty /\
  assignable_type (get_tenv cx) ty /\ abi_decode_bytes_widths (get_tenv cx) ty /\
  type_alloc_ok ce ty /\
  abi_size_bound ce.ce_struct_fields
    (if needs_external_call_wrap ty then TupleT [ty] else ty) + 32 < 2 ** 64
Proof
  strip_tac >> drule extcall_linked_root_metadata >> strip_tac >>
  drule expr_body_pre_mods_well_typed >>
  simp[Once well_typed_expr_def] >> strip_tac >>
  `alloc_limits_expr ce (Call ty (ExtCall stat skip (fname,arg_types,ty) opts) args dflt)` by
    fs[expr_body_pre_mods_def] >>
  pop_assum mp_tac >> simp[Once alloc_limits_expr_def, ext_call_alloc_ok_def] >>
  strip_tac >> gvs[] >>
  irule LESS_EQ_LESS_TRANS >> goal_assum (drule_at Any) >> simp[]
QED

Theorem extcall_linked_store_bound[local]:
  type_alloc_ok ce ty /\ type_memory_bytes ce ty = type_memory_size tv ==>
  type_memory_size tv + 64 < dimword (:256)
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (Cases_on `ty` >>
      gvs[is_word_type_def, type_memory_bytes_def, dimword_def] >>
      rename1 `is_word_type (BaseT bt)` >>
      Cases_on `bt` >> gvs[is_word_type_def, type_memory_bytes_def] >>
      rename1 `is_word_type (BaseT (BytesT bl))` >>
      Cases_on `bl` >> gvs[is_word_type_def, type_memory_bytes_def]) >>
  gvs[type_alloc_ok_def, dimword_def]
QED

Theorem extcall_wrapped_head_positive[local]:
  rt = (if needs_external_call_wrap ty then TupleT [ty] else ty) /\
  assignable_type env rt /\ abi_decoder_coherent ce env ce.ce_struct_fields rt tv ==>
  0 < abi_static_size ce.ce_struct_fields rt
Proof
  strip_tac >>
  `?tys. rt = TupleT tys` by
    (qpat_assum `rt = _` SUBST1_TAC >>
     pure_rewrite_tac[needs_external_call_wrap_extcall] >>
     Cases_on `ty` >> simp[] >> IF_CASES_TAC >> simp[]) >>
  qpat_x_assum `rt = TupleT tys` SUBST_ALL_TAC >>
  qpat_assum `assignable_type _ _` mp_tac >>
  qpat_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `tys` >>
  simp[assignable_type_def, abi_decoder_coherent_tuple_iff] >>
  strip_tac >> Cases_on `tvs` >> gvs[] >> strip_tac >>
  rename1 `abi_decoder_coherent _ _ _ hd _` >>
  `0 < abi_embedded_static_size ce.ce_struct_fields hd` by
    (irule abi_decode_assignable_embedded_head_positive >>
     goal_assum (drule_at Any) >> simp[SF SFY_ss]) >>
  simp[abi_static_size_def, GSYM abi_embedded_static_size_def]
QED

Theorem extcall_return_layout_mods:
  expr_body_pre_mods mods ce cx env
    (Call ann (ExtCall stat skip (fname,arg_types,ty) opts) args dflt) es /\
  ty <> NoneT ==>
  ann = ty /\
  ?actual_tv.
    evaluate_type (get_tenv cx) ty = SOME actual_tv /\
    type_memory_bytes ce ty = type_memory_size actual_tv /\
    type_memory_size actual_tv + 64 < dimword (:256) /\
    let rt = if needs_external_call_wrap ty then TupleT [ty] else ty;
        tv = if needs_external_call_wrap ty then TupleTV [actual_tv] else actual_tv
    in
      assignable_type (get_tenv cx) rt /\ abi_decode_bytes_widths (get_tenv cx) rt /\
      evaluate_type (get_tenv cx) rt = SOME tv /\
      abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields rt tv /\
      abi_static_size ce.ce_struct_fields rt =
        abi_static_length (vyper_to_abi_type (get_tenv cx) rt) /\
      type_memory_bytes ce rt = type_memory_bytes ce ty /\
      abi_size_bound ce.ce_struct_fields rt = vyper_abi_size_bound (get_tenv cx) rt /\
      0 < abi_static_size ce.ce_struct_fields rt /\
      0 < abi_size_bound ce.ce_struct_fields rt /\
      abi_static_size ce.ce_struct_fields rt <= abi_size_bound ce.ce_struct_fields rt /\
      abi_static_size ce.ce_struct_fields rt < dimword (:256) /\
      abi_size_bound ce.ce_struct_fields rt < dimword (:256) /\
      type_memory_size tv < dimword (:256) /\
      (~is_dynamic (vyper_to_abi_type (get_tenv cx) rt) ==>
        abi_size_bound ce.ce_struct_fields rt =
          static_length (vyper_to_abi_type (get_tenv cx) rt))
Proof
  strip_tac >> drule extcall_linked_root_metadata >> strip_tac >>
  drule_all extcall_linked_return_type >> strip_tac >> simp[] >>
  `?actual_tv. evaluate_type (get_tenv cx) ty = SOME actual_tv` by
    fs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  qexists `actual_tv` >> simp[] >>
  `type_memory_bytes ce ty = type_memory_size actual_tv` by
    (irule typed_copy_memory_size >> qexists `get_tenv cx` >>
     fs[abi_decode_root_metadata_def] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `type_memory_size actual_tv + 64 < dimword (:256)` by
    (irule extcall_linked_store_bound >> goal_assum (drule_at Any) >> simp[]) >>
  simp[] >>
  qabbrev_tac `rt = if needs_external_call_wrap ty then TupleT [ty] else ty` >>
  qabbrev_tac `tv = if needs_external_call_wrap ty then TupleTV [actual_tv] else actual_tv` >>
  `type_slot_size actual_tv <= dimword (:256)` by
    metis_tac[cj 1 evaluate_type_well_formed, well_formed_type_value_slot_size] >>
  `assignable_type (get_tenv cx) rt /\ abi_decode_bytes_widths (get_tenv cx) rt /\
   evaluate_type (get_tenv cx) rt = SOME tv` by
    (Cases_on `needs_external_call_wrap ty` >>
     gvs[Abbr `rt`, Abbr `tv`, Once assignable_type_def, Once abi_decode_bytes_widths_def,
         Once evaluate_type_def, evaluate_types_OPT_MMAP] >>
     simp[Once well_formed_type_def, type_slot_size_def,
          Once evaluate_type_def, evaluate_types_OPT_MMAP]) >>
  `abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields rt tv` by
    (irule abi_decode_root_coherent >> simp[]) >>
  `type_memory_bytes ce rt = type_memory_bytes ce ty` by
    (Cases_on `needs_external_call_wrap ty` >> gvs[Abbr `rt`, type_memory_bytes_def]) >>
  `0 < abi_static_size ce.ce_struct_fields rt` by
    (irule extcall_wrapped_head_positive >> conj_tac
     >- (qexists `ty` >> simp[Abbr `rt`]) >>
     qexistsl_tac [`get_tenv cx`, `tv`] >> simp[]) >>
  `abi_static_size ce.ce_struct_fields rt <= abi_size_bound ce.ce_struct_fields rt` by
    simp[abi_static_size_le_size_bound] >>
  `abi_size_bound ce.ce_struct_fields rt < dimword (:256)` by
    (qpat_x_assum `_ + 32 < 2 ** 64` mp_tac >> simp[Abbr `rt`, dimword_def]) >>
  `abi_sfields_consistent_upto (type_value_size tv) ce.ce_struct_fields (get_tenv cx)` by
    fs[abi_decode_root_metadata_def, abi_sfields_consistent_upto_init] >>
  drule_all abi_props_vyper_upto >> strip_tac >>
  drule abi_decoder_coherent_header >> simp[abi_decoder_header_def] >> strip_tac >>
  drule abi_decode_coherent_minimum >> strip_tac >>
  gvs[] >> decide_tac
QED
