(* Instantiate the recursive contract using the checked primitive-array decoder. *)
Theory abiDecoderCorrectPrimitiveArray
Ancestors
  abiDecoderCorrect abiDecoderEffect abiDecoderPrimitiveArrayReentry abiDecoderCoherence
  abiDecoderTypedContract abiDecoderArrayAdvance abiDecoderWordTyped abiDecoderAllocation
  abiDecoderContract abiDecodeRanges abiDecoderArraySetupCode abiDecoderRecursiveArray exprLowering
  compileEnv valueEncoding vyperABI vyperValue vyperTyping contractABI venomState words list

Theorem abi_decoder_dynarray_metadata_shape:
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di av v ==>
  ?avs vs. av = ListV avs /\ v = ArrayV (DynArrayV vs)
Proof
  Cases_on `av` >> simp_tac bool_ss [abi_decoder_metadata_def] >> strip_tac >>
  gvs[Once vyper_to_abi_type_def, Once has_type_def, Once abi_to_vyper_def,
    make_array_value_def, AllCaseEqs()]
QED

Theorem abi_decoder_primitive_array_info:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray (DecPrimWord clamp) 32 32 F maxn
Proof
  strip_tac >> drule_all abi_decoder_primitive_array_sizes >> strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
  asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_header ce env ty tv` by metis_tac[abi_decoder_coherent_header] >>
  `abi_embedded_static_size ce.ce_struct_fields ty = 32`
    by fs[abi_decoder_header_def, abi_member_head_size_def] >>
  asm_simp_tac bool_ss [Once type_to_abi_dec_info_def]
QED

Theorem abi_decoder_correct_primitive_array:
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
  abi_decoder_correct ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  strip_tac >> simp_tac bool_ss [abi_decoder_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o
      PURE_REWRITE_RULE [abi_decoder_recursive_pre_def, abi_decoder_pre_def]) >>
  drule_all abi_decoder_primitive_array_info >> strip_tac >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >> gvs[Excl "enc_def"] >>
  (SUBGOAL_THEN ``dec_info_needs_clamp (DecPrimWord clamp) ==>
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0`` assume_tac
  >- (strip_tac >>
      `abi_decode_source_opcode opc` by fs[abi_decoder_ranges_def, Excl "enc_def"] >>
      drule_all (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `F`]
        abi_decoder_recursive_array_adds_blocks)) >> strip_tac >> metis_tac[]) >>
  drule_all abi_decoder_primitive_array_reentry >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >>
  gvs[abi_decoder_effect_def, abi_decoder_scratch_frame_def, abi_decoder_ids_def,
    Excl "enc_def"] >> metis_tac[])
QED

(* TOP-LEVEL: execute an array body whose child is a primitive-element dynamic
   array, including the child's own loop and protected scratch effects. *)
val nested_child_instance = Q.INST
  [`ty` |-> `inner_ty:vyperAST$type`, `tv` |-> `inner_tv:vyperValue$type_value`,
   `maxn` |-> `inner_bound:num`] abi_decoder_correct_primitive_array;
val nested_word_hyp = fst (dest_imp (concl nested_child_instance));
val nested_child_correct = UNDISCH nested_child_instance;

Theorem abi_decoder_nested_array_body =
  GEN_ALL (DISCH nested_word_hyp
    (SIMP_RULE bool_ss [nested_child_correct]
      (Q.INST [`ty` |-> `ArrayT inner_ty (Dynamic inner_bound)`,
        `tv` |-> `ArrayTV inner_tv (Dynamic inner_bound)`] abi_decoder_array_body)));
