(* Dynamic decoder descriptors agree with coherent source types. *)
Theory abiDecoderDynamic
Ancestors
  abiDecoderCoherence abiDecoderConstructors abiEncoder exprLowering compileEnv
  abiDecoderSingletonSetup abiDecoderComplexHead abiDecoderGuard vyperABI contractABI emitHelper
  list pair combin finite_map

Definition abi_decoder_dynamic_def:
  abi_decoder_dynamic (DecPrimWord c) = F /\
  abi_decoder_dynamic (DecBytestring n) = T /\
  abi_decoder_dynamic (DecDynArray ei asz msz d n) = T /\
  abi_decoder_dynamic (DecComplex d elems) = d
End

Theorem abi_decoder_dynamic_case:
  (case di of DecPrimWord c => F | DecBytestring n => T |
     DecDynArray ei asz msz d n => T | DecComplex d elems => d) =
  abi_decoder_dynamic di
Proof
  Cases_on `di` >> simp[abi_decoder_dynamic_def]
QED

Theorem abi_decoder_struct_dynamic[local]:
  abi_decoder_coherent ce env sf (StructT nsid) tv ==>
  abi_decoder_dynamic (type_to_abi_dec_info sf ce (StructT nsid)) =
    is_dynamic (vyper_to_abi_type env (StructT nsid))
Proof
  simp_tac bool_ss [abi_decoder_coherent_struct_iff] >> strip_tac >>
  qabbrev_tac `args = MAP (\(name,ty,sz). (name,ty)) fields` >>
  `LIST_REL (abi_decoder_header ce (env \\ nsid)) (MAP SND args) tvs` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     match_mp_tac LIST_REL_mono >> rpt strip_tac >>
     drule_all abi_decoder_coherent_header >> simp[]) >>
  drule abi_decoder_header_list >> strip_tac >>
  `MAP (FST o SND) fields = MAP SND args` by
    (simp[Abbr `args`, MAP_MAP_o] >> irule MAP_CONG >> simp[FORALL_PROD]) >>
  gvs[type_to_abi_dec_info_def, abi_decoder_dynamic_def,
      vyper_to_abi_type_def, is_dynamic_def]
QED

Theorem abi_decoder_base_dynamic[local]:
  abi_decoder_dynamic (type_to_abi_dec_info sf ce (BaseT bt)) =
    is_dynamic (vyper_base_to_abi_type bt)
Proof
  Cases_on `bt` >>
  gvs[type_to_abi_dec_info_def, abi_decoder_dynamic_def,
      vyper_base_to_abi_type_def, is_dynamic_def] >>
  rename1 `vyper_base_to_abi_type (BytesT bound)` >> Cases_on `bound` >>
  gvs[type_to_abi_dec_info_def, abi_decoder_dynamic_def,
      vyper_base_to_abi_type_def, is_dynamic_def]
QED

Theorem abi_decoder_coherent_dynamic:
  abi_decoder_coherent ce env sf ty tv ==>
  abi_decoder_dynamic (type_to_abi_dec_info sf ce ty) =
    is_dynamic (vyper_to_abi_type env ty)
Proof
  strip_tac >> drule abi_decoder_coherent_header >> strip_tac >>
  Cases_on `ty` >> TRY (drule_all abi_decoder_struct_dynamic >> simp[]) >>
  gvs[abi_decoder_base_dynamic, type_to_abi_dec_info_def, abi_decoder_dynamic_def,
      vyper_to_abi_type_def, is_dynamic_def, is_abi_dynamic_def,
      abi_decoder_header_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[] >>
  rename1 `abi_decoder_coherent ce env sf (ArrayT elem bound) tv` >>
  Cases_on `bound` >> gvs[type_to_abi_dec_info_def, abi_decoder_dynamic_def,
    is_abi_dynamic_def, is_dynamic_def]
QED

Theorem abi_decode_dynamic_singleton_members[local]:
  dec_info_needs_offset di ==>
  compile_abi_decode_complex_elems dst src opc hi [(di,32,mem_sz)] 0 0 =
    do child_src <- compile_getelemptr_abi src T 0 opc hi;
       child_dst <- emit_op ADD [dst; Lit 0w];
       compile_abi_decode_to_buf child_dst child_src opc hi di
    od
Proof
  strip_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_abi_decode_to_buf_def])) >>
  simp[FUN_EQ_THM, abi_decoder_dynamic_case, abi_decode_complex_nil,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_decoder_singleton_info:
  abi_decoder_coherent ce env sf ty tv /\ is_dynamic (vyper_to_abi_type env ty) ==>
  type_to_abi_dec_info sf ce (TupleT [ty]) =
    DecComplex T [(type_to_abi_dec_info sf ce ty,32,type_memory_bytes ce ty)]
Proof
  strip_tac >> drule abi_decoder_coherent_header >> strip_tac >>
  gvs[type_to_abi_dec_info_def, abi_decoder_header_def, abi_embedded_static_size_def]
QED

Theorem abi_decoder_coherent_singleton_dynamic:
  abi_decoder_coherent ce env sf (TupleT [ty]) (TupleTV [tv]) /\
  DecComplex T elems = type_to_abi_dec_info sf ce (TupleT [ty]) ==>
  is_dynamic (vyper_to_abi_type env ty)
Proof
  strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_tuple_iff] >>
  drule_all abi_decoder_coherent_header >> strip_tac >>
  gvs[type_to_abi_dec_info_def, abi_decoder_header_def]
QED

Theorem abi_decode_dynamic_singleton_phases:
  dec_info_needs_offset di ==>
  compile_abi_decode_to_buf dst src opc hi (DecComplex T [(di,32,mem_sz)]) =
    do child_ops <- abi_decode_singleton_setup dst src opc hi;
       compile_abi_decode_to_buf (SND child_ops) (FST child_ops) opc hi di
    od
Proof
  strip_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_abi_decode_to_buf_def])) >>
  Cases_on `hi = Lit 0w` >>
  simp[FUN_EQ_THM, abi_decode_singleton_setup_def, abi_decode_complex_head_guard_def,
       abi_decode_le_guard_def, abi_decode_dynamic_singleton_members,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED
