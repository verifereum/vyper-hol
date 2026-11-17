(* Width-aware dynamic parent, consuming fixed-function child outcomes. *)
Theory abiMalformedWidthDynamic
Ancestors
  abiDecoderValidArraySetupInputs abiValidMembers abiMalformedPrefix abiValidAggregateHeads abiDecoderOffset abiDecoderWordTyped abiMalformedInitializedLoop abiWidthInhabited abiMalformedOutcomeParents abiMalformedOutcomeLoop abiMalformedInitTotal
  abiMalformedBoundedContract abiEncoder
  abiMalformedInitResource abiMalformedBulkCaller abiMalformedChildPremises
  abiMalformedZeroTraversal abiMalformedConstructorInduction
  abiDecoderArrayLoopInit abiDecoderIndexInit abiDecoderArrayInitReentry
  abiDecoderRecursiveArray exprSimAlloc rich_list abiDecoderDynarrayPrefix
  abiDecoderLoopCode abiDecoderCounters abiDecoderCode abiDecoderContract abiDecoderReentry
  abiMalformedOutcomeContract abiMalformedRecursiveInterface
  abiDecoderCoherence abiDecoderMemberInfos abiVyperAdmissible abiDecodeRanges
  exprLowering exprLoweringProps localPtrsProps emitHelperProps emitHelper context fragExec compileEnv
  vyperTypeSystem vyperTyping vyperValue vyperABI contractABI valueEncoding
  venomInst words list arithmetic

Theorem abi_malformed_width_dynamic_outcome:
  abi_decoder_coherent ce env sf ty tv /\
  abi_decode_bytes_widths env ty /\
  abi_malformed_bounded_type_outcome ce env sf ty tv /\
  abi_decoder_header ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) ==>
  abi_malformed_bounded_type_outcome ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  strip_tac >>
  `abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))` by
    simp[abi_decoder_coherent_array_iff] >>
  simp_tac bool_ss [abi_malformed_bounded_type_outcome_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all abi_malformed_array_capacity >> simp[] >> strip_tac >>
  fs[Once type_to_abi_dec_info_def] >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- suspend "recursive" >>
  `~is_abi_dynamic ce.ce_struct_fields ty /\ ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)` by fs[] >>
  fs[] >> irule abi_malformed_constructor_to_outcome >>
  irule abi_malformed_bulk_constructor_parent >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`ce`, `sf`, `tv`] >> simp[Once type_to_abi_dec_info_def]
QED

Resume abi_malformed_width_dynamic_outcome[recursive]:
  drule_all abi_decode_loop_array_trace >> strip_tac >>
  drule abi_decode_array_loop_init_trace >> strip_tac >>
  simp_tac bool_ss [abi_malformed_constructor_outcome_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_assum `abi_decoder_coherent ce env sf ty tv`
    (mp_tac o MATCH_MP abi_decoder_coherent_header) >> strip_tac >>
  `abi_embedded_static_size ce.ce_struct_fields ty = abi_member_head_size (vyper_to_abi_type env ty)` by
    fs[abi_decoder_header_def] >>
  `32 <= outsz` by fs[type_memory_bytes_def] >>
  `maxn < dimword (:256)` by
    (qpat_assum `abi_decoder_header ce env (ArrayT ty (Dynamic maxn)) _` mp_tac >>
     simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
     drule (cj 1 evaluate_type_well_formed) >> simp[well_formed_type_value_def]) >>
  `maxn <> 0 ==>
    abi_embedded_static_size ce.ce_struct_fields ty = abi_member_head_size (vyper_to_abi_type env ty) /\
    dec_info_needs_offset (type_to_abi_dec_info sf ce ty) = is_dynamic (vyper_to_abi_type env ty) /\
    (case type_to_abi_dec_info sf ce ty of DecPrimWord clamp =>
      ~is_dynamic (vyper_to_abi_type env ty) /\ abi_embedded_static_size ce.ce_struct_fields ty = 32 | _ => T) /\
    abi_embedded_static_size ce.ce_struct_fields ty < dimword (:256) /\
    (!j. j<maxn ==> d+32+j*type_memory_bytes ce ty+type_memory_bytes ce ty <= d+outsz) /\
    (!childsrc childdst child child_end.
      compile_abi_decode_to_buf childdst childsrc MLOAD base_op hi
        (type_to_abi_dec_info sf ce ty) child = ((),child_end) /\
      fn_has_code child child_end func ==>
      abi_malformed_constructor_outcome env ty (type_to_abi_dec_info sf ce ty)
        ctx func cenv cx es child child_end base_op hi childsrc childdst (type_memory_bytes ce ty))` by
    (strip_tac >>
     `assignable_type env ty /\ type_memory_size tv < dimword (:256)` by
       (irule abi_malformed_array_child_bound >> qexists_tac `Dynamic maxn` >> simp[]) >>
     `?a. has_type (vyper_to_abi_type env ty) a` by
       (irule abi_width_coherent_inhabited >> metis_tac[]) >>
     `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) = is_dynamic (vyper_to_abi_type env ty)` by
       (irule abi_decoder_array_child_offset >> goal_assum (drule_at Any)) >>
     simp[] >>
     conj_tac
     >- (Cases_on `type_to_abi_dec_info sf ce ty` >> simp[] >>
         qpat_assum `abi_decoder_coherent ce env sf ty tv`
           (mp_tac o MATCH_MP abi_decoder_primitive_cases) >> disch_then drule >>
         strip_tac >> fs[abi_decoder_header_def, abi_member_head_size_def]) >>
     conj_tac
     >- (`abi_member_head_size (vyper_to_abi_type env ty) <= maxn * abi_member_head_size (vyper_to_abi_type env ty)` by
           (Cases_on `maxn` >> fs[MULT_CLAUSES]) >> decide_tac) >>
     conj_tac
     >- (rpt strip_tac >>
         `SUC j <= maxn` by decide_tac >>
         `SUC j * type_memory_bytes ce ty <= maxn * type_memory_bytes ce ty` by simp[] >>
         qpat_x_assum `type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= outsz`
           (assume_tac o REWRITE_RULE [type_memory_bytes_def]) >>
         qpat_x_assum `SUC j * _ <= _` mp_tac >>
         pure_rewrite_tac [MULT_CLAUSES] >> decide_tac) >>
     rpt strip_tac >>
     qpat_x_assum `abi_malformed_bounded_type_outcome ce env sf ty tv` mp_tac >>
     simp_tac bool_ss [abi_malformed_bounded_type_outcome_def] >>
     disch_then irule >> simp[] >> qexists_tac `a` >> simp[]) >>
  `maxn * abi_embedded_static_size ce.ce_struct_fields ty < dimword (:256)` by simp[] >>
  drule_all abi_malformed_initialized_loop_outcome >>
  disch_tac >> irule frag_outcome_compose >> goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> irule frag_outcome_refl >> simp[] >>
  simp[abi_malformed_reflected_post_def] >>
  qpat_x_assum `frag_outcome _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `maxn <> 0 ==> _` kall_tac >>
  `LENGTH xs = L` by
    (fs[abi_malformed_entry_def, abi_malformed_allocated_window_def] >>
     metis_tac[valueEncodingPropsTheory.LENGTH_mem_bytes_at]) >>
  drule abi_reflected_prefix_valid >> strip_tac >>
  `vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) (DROP p xs)` by
    (asm_simp_tac bool_ss [Once vyper_decode_valid_enc_def, LET_THM, GSYM abi_head_word_def] >>
     fs[DROP_DROP_T, LENGTH_DROP, dec_number_def, is_num_value_def]) >>
  simp[] >>
  drule abi_valid_dynamic_array_view >> strip_tac >>
  rewrite_tac[GSYM abi_head_word_def, abi_decode_array_members, abi_decode_members_value] >>
  simp[abi_vyper_admissible_array_iff, compatible_bound_def] >>
  qexists_tac `tv` >>
  `evaluate_type env ty = SOME tv` by fs[abi_decoder_header_def] >>
  simp[GSYM abi_head_word_def] >>
  `avs = abi_decode_members (REPLICATE (abi_head_word (DROP p xs)) (vyper_to_abi_type env ty))
      (DROP 32 (DROP p xs)) (DROP 32 (DROP p xs))` by
    (irule LIST_EQ >>
     `LENGTH avs = abi_head_word (DROP p xs)` by fs[abi_reflected_prefix_def] >>
     simp[] >> qx_gen_tac `k` >> strip_tac >>
     drule_all abi_decode_array_member_EL >> simp[] >> disch_then kall_tac >>
     qpat_x_assum `abi_reflected_prefix _ _ _ _ _` mp_tac >>
     simp_tac std_ss [abi_reflected_prefix_def] >> strip_tac >>
     first_x_assum (qspec_then `k` mp_tac) >>
     simp[abi_reflected_child_def, abi_decode_member_bytes_def, abi_member_head_size_def, DROP_DROP_T]) >>
  drule abi_reflected_prefix_admissible >>
  fs[abi_head_word_def]
QED
Finalise abi_malformed_width_dynamic_outcome
