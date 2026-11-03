Theory abiEmptyAggregateInput
Ancestors
  valueEncodingTyping abiStaticLayoutProps abiStaticAggregateProps abiEncoderMemory
  abiEmptySequence abiEncoderInput exprLowering compileEnv valueEncoding vyperABI contractABI
  integer_word words list rich_list arithmetic abiEncoderInputFrame valueEncodingProofs
  abiDecoderLayout abiDecoderCoherence abiEmptyAllocate abiEmptySize abiEmptyEffect
  abiBuiltinAllocation abiDecoderReentry abiCallerBuiltinInput exprLoweringProps builtinSimple
  compileVyper vyperTypeSystem vyperValue vyperContext venomState venomExecSemantics finite_map
  abiTupleEncodeAssembly abiTupleEncodeMemory abiTupleEncodeSourceLayout abiDecoderMembers

(* Actual default ABI bytes for statically laid out source values.
   These are byte equalities, independent of sparse val_in_memory predicates. *)
Theorem abi_empty_fixed_bytes_default:
  enc (Bytes (SOME n)) (BytesV (REPLICATE n 0w)) = REPLICATE 32 0w
Proof
  `TAKE 32 (REPLICATE n (0w:word8)) = REPLICATE (MIN 32 n) 0w` by
    simp[REPLICATE_GENLIST, TAKE_GENLIST] >>
  simp_tac bool_ss [enc_def] >> asm_rewrite_tac[] >>
  rewrite_tac[REPLICATE_APPEND] >> AP_THM_TAC >> AP_TERM_TAC >>
  rw[MIN_DEF] >> decide_tac
QED

Theorem abi_empty_bytes_default:
  enc (vyper_base_to_abi_type (BytesT bd)) (default_to_abi (BaseTV (BytesT bd))) =
    REPLICATE 32 0w
Proof
  Cases_on `bd` >> simp[default_to_abi_def, abi_empty_fixed_bytes_default,
    abi_encoder_zero_word, enc_def, enc_number_def, ceil32_def]
QED

Theorem abi_empty_base_default:
  enc (vyper_base_to_abi_type bt) (default_to_abi (BaseTV bt)) = REPLICATE 32 0w
Proof
  Cases_on `bt` >> simp[default_to_abi_def, abi_empty_bytes_default,
    abi_encoder_zero_word, enc_def, enc_number_def, ceil32_def, i2w_0]
QED

Theorem abi_empty_flat_zero:
  !n. FLAT (REPLICATE n (REPLICATE m (0w:word8))) = REPLICATE (n*m) 0w
Proof
  Induct >> simp[REPLICATE_APPEND, MULT_CLAUSES]
QED

Theorem abi_empty_default_list:
  !tys tvs. LIST_REL (\ty tv.
    ~is_dynamic (vyper_to_abi_type tenv ty) /\
    enc (vyper_to_abi_type tenv ty) (default_to_abi tv) =
      REPLICATE (type_memory_size tv) 0w) tys tvs ==>
  ~any_dynamic (vyper_to_abi_types tenv tys) /\
  LENGTH (vyper_to_abi_types tenv tys) = LENGTH (default_to_abi_list tvs) /\
  FLAT (MAP2 enc (vyper_to_abi_types tenv tys) (default_to_abi_list tvs)) =
    REPLICATE (type_memory_size_list tvs) 0w
Proof
  Induct >> Cases_on `tvs` >>
  simp[default_to_abi_def, type_memory_size_def, is_dynamic_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[REPLICATE_APPEND]
QED

Theorem abi_empty_default_tuple:
  LIST_REL (\ty tv.
    ~is_dynamic (vyper_to_abi_type tenv ty) /\
    enc (vyper_to_abi_type tenv ty) (default_to_abi tv) =
      REPLICATE (type_memory_size tv) 0w) tys tvs ==>
  enc (Tuple (vyper_to_abi_types tenv tys)) (ListV (default_to_abi_list tvs)) =
    REPLICATE (type_memory_size_list tvs) 0w
Proof
  strip_tac >> drule abi_empty_default_list >> strip_tac >>
  drule_all enc_static_tuple >> simp[]
QED

Theorem abi_empty_static_default:
  !cenv tenv ty tv. static_layout_compatible cenv tenv ty tv ==>
  enc (vyper_to_abi_type tenv ty) (default_to_abi tv) = REPLICATE (type_memory_size tv) 0w
Proof
  ho_match_mp_tac static_layout_compatible_strongind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (simp_tac bool_ss [vyper_to_abi_type_def, abi_empty_base_default] >>
      Cases_on `bt` >> gvs[is_word_type_def, type_memory_size_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_word_type_def, type_memory_size_def])
  >- simp[default_to_abi_def, enc_def, enc_number_def,
    type_memory_size_def, abi_encoder_zero_word]
  >- (drule static_layout_compatible_properties >> strip_tac >>
      simp[default_to_abi_def, enc_static_array, map_replicate,
        abi_empty_flat_zero, type_memory_size_def])
  >- (pure_rewrite_tac[default_to_abi_def, type_memory_size_def, vyper_to_abi_type_def] >>
      irule abi_empty_default_tuple >> qpat_x_assum `LIST_REL _ _ _` mp_tac >>
      match_mp_tac LIST_REL_mono >> simp[] >> rpt strip_tac >>
      drule static_layout_compatible_properties >> simp[])
  >> `LENGTH (MAP FST args) = LENGTH tvs` by
       (imp_res_tac LIST_REL_LENGTH >> gvs[])
  >> drule type_memory_size_fields_zip >> strip_tac
  >> asm_simp_tac bool_ss [default_to_abi_def, type_memory_size_def, vyper_to_abi_type_def]
  >> asm_simp_tac (srw_ss()) [default_to_abi_fields_MAP, default_to_abi_list_MAP,
       MAP_ZIP, Excl "enc_def"]
  >> irule (REWRITE_RULE [default_to_abi_list_MAP] abi_empty_default_tuple)
  >> qpat_x_assum `LIST_REL _ _ _` mp_tac
  >> match_mp_tac LIST_REL_mono >> simp[] >> rpt strip_tac
  >> drule static_layout_compatible_properties >> simp[]
QED

Theorem abi_empty_static_descriptor:
  static_layout_compatible ce tenv ty tv ==>
  type_to_abi_enc_info sf ce ty = AbiCopy (type_memory_bytes ce ty)
Proof
  strip_tac >>
  `ty <> NoneT` by (strip_tac >> gvs[Once static_layout_compatible_cases]) >>
  drule static_layout_compatible_properties >> strip_tac >>
  Cases_on `ty` >> gvs[type_to_abi_enc_info_def, is_abi_dynamic_def] >>
  FIRST [rename1 `BaseT bt` >> Cases_on `bt`, ALL_TAC] >>
  FIRST [rename1 `BytesT bd` >> Cases_on `bd`, ALL_TAC] >>
  FIRST [rename1 `ArrayT elem bd` >> Cases_on `bd`, ALL_TAC] >>
  gvs[type_to_abi_enc_info_def, is_abi_dynamic_def]
QED

Theorem abi_empty_static_input:
  static_layout_compatible ce tenv ty tv /\
  has_type (vyper_to_abi_type tenv ty) (default_to_abi tv) /\
  mem_bytes_at p (type_memory_bytes ce ty) mem = REPLICATE (type_memory_bytes ce ty) 0w /\
  type_memory_bytes ce ty <= cap ==>
  abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type tenv ty)
    (default_to_abi tv) p cap mem
Proof
  strip_tac >> drule abi_empty_static_descriptor >> strip_tac >>
  drule abi_empty_static_default >> strip_tac >>
  drule static_layout_compatible_properties >> strip_tac >>
  asm_rewrite_tac[] >> irule abi_empty_zero_copy_input >>
  asm_simp_tac bool_ss []
QED

(* ===== Transport ===== *)

(* Transfer pure zero-memory encoder inputs to an actually initialized buffer.
   Count-only producers need only their initialized first word. *)

Theorem abi_empty_memory_observation:
  mem_bytes_at p sz [] = REPLICATE sz 0w /\ mem_word_at p [] = 0w
Proof
  simp[mem_bytes_at_def, mem_word_at_def, TAKE_LENGTH_TOO_LONG,
    word_of_bytes_replicate_zero]
QED

Theorem abi_empty_count_word:
  mem_bytes_at p 32 mem = REPLICATE 32 0w ==> mem_word_at p mem = 0w
Proof
  simp[mem_word_at_bytes, word_of_bytes_replicate_zero]
QED

Theorem abi_empty_input_relocate:
  abi_encoder_input ei at av 0 cap [] /\
  mem_bytes_at p cap mem = REPLICATE cap 0w ==>
  abi_encoder_input ei at av p cap mem
Proof
  strip_tac >> drule abi_encoder_input_relocate >>
  disch_then (qspecl_then [`p`, `mem`] mp_tac) >>
  simp[abi_empty_memory_observation]
QED

Theorem abi_empty_input_zero_address:
  abi_encoder_input ei at av 0 cap [] ==> abi_encoder_input ei at av p cap []
Proof
  strip_tac >> irule abi_empty_input_relocate >> simp[abi_empty_memory_observation]
QED

Theorem abi_empty_bytes_input:
  (at = Bytes NONE \/ at = String) /\ 32 <= cap /\ mem_word_at p mem = 0w ==>
  abi_encoder_input (AbiBytestring maxlen) at (BytesV []) p cap mem
Proof
  rw[abi_encoder_input_bytes_iff, has_type_def, valid_length_def,
    mem_bytes_at_def, dimword_def] >>
  simp[has_type_def, valid_bytes_bound_def, valid_length_def, dimword_def]
QED

Theorem abi_empty_array_input:
  abi_sz = abi_member_head_size ct /\ dyn = is_dynamic ct /\
  32 <= cap /\ mem_word_at p mem = 0w ==>
  abi_encoder_input (AbiDynArray ei abi_sz mem_sz dyn) (Array NONE ct) (ListV []) p cap mem
Proof
  simp[abi_encoder_array_input_iff, has_type_def, valid_length_def, dimword_def]
QED

(* ===== Leaves ===== *)

(* Establish default leaf encoder inputs from real initialized memory windows. *)

Theorem abi_empty_coherent_static_input:
  abi_decoder_coherent ce env sf ty tv /\
  ~is_dynamic (vyper_to_abi_type env ty) /\
  has_type (vyper_to_abi_type env ty) (default_to_abi tv) /\
  mem_bytes_at p (type_memory_bytes ce ty) mem = REPLICATE (type_memory_bytes ce ty) 0w ==>
  abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
    (default_to_abi tv) p (type_memory_bytes ce ty) mem
Proof
  strip_tac >> drule_all abi_decoder_coherent_static >> strip_tac >>
  irule abi_empty_static_input >> simp[]
QED

Theorem abi_empty_bytestring_inputs:
  mem_bytes_at p 32 mem = REPLICATE 32 0w ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (BaseT (BytesT (Dynamic n))))
    (vyper_to_abi_type env (BaseT (BytesT (Dynamic n))))
    (default_to_abi (BaseTV (BytesT (Dynamic n)))) p
    (type_memory_bytes ce (BaseT (BytesT (Dynamic n)))) mem /\
  abi_encoder_input (type_to_abi_enc_info sf ce (BaseT (StringT m)))
    (vyper_to_abi_type env (BaseT (StringT m)))
    (default_to_abi (BaseTV (StringT m))) p
    (type_memory_bytes ce (BaseT (StringT m))) mem
Proof
  strip_tac >> drule abi_empty_count_word >> strip_tac >>
  simp_tac bool_ss [type_to_abi_enc_info_def, vyper_to_abi_type_def,
    default_to_abi_def, type_memory_bytes_def] >>
  conj_tac >> irule abi_empty_bytes_input >> simp[]
QED

Theorem abi_empty_dynamic_array_input:
  abi_decoder_header ce env ty tv /\
  mem_bytes_at p 32 mem = REPLICATE 32 0w ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (ArrayT ty (Dynamic n)))
    (vyper_to_abi_type env (ArrayT ty (Dynamic n)))
    (default_to_abi (ArrayTV tv (Dynamic n))) p
    (type_memory_bytes ce (ArrayT ty (Dynamic n))) mem
Proof
  strip_tac >> drule abi_empty_count_word >> strip_tac >>
  simp_tac bool_ss [type_to_abi_enc_info_def, vyper_to_abi_type_def,
    default_to_abi_def, type_memory_bytes_def] >>
  irule abi_empty_array_input >> gvs[abi_decoder_header_def]
QED

(* The real allocator and initializer establish a complete static encoder input.
   No initial or final source-memory layout is assumed. *)
Theorem abi_empty_producer_operand_live:
  compile_builtin_empty_complex outsz length_only st = (buf,final) ==>
  abi_decoder_operand_live final.cs_next_var buf.buf_operand
Proof
  strip_tac >> drule abi_empty_complex_parts >> strip_tac >>
  rename1 `compile_alloc_buffer outsz st = (buf,allocated)` >>
  drule abi_empty_alloc_buffer_shape >> strip_tac >>
  drule abi_empty_initializer_shape >> strip_tac >>
  irule abi_decoder_operand_live_mono >> qexists_tac `allocated.cs_next_var` >> simp[]
QED

Theorem abi_empty_static_producer:
  abi_decoder_coherent ce env sf ty tv /\
  ~is_dynamic (vyper_to_abi_type env ty) /\
  has_type (vyper_to_abi_type env ty) (default_to_abi tv) /\
  compile_builtin_empty_complex (type_memory_bytes ce ty) F st = (buf,final) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,type_memory_bytes ce ty)) /\
  p+type_memory_bytes ce ty < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\
    eval_operand buf.buf_operand actual = SOME (n2w p) /\
    buf.buf_size = type_memory_bytes ce ty /\
    abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
      (default_to_abi tv) p (type_memory_bytes ce ty) actual.vs_memory /\
    abi_empty_effect st.cs_next_var p (type_memory_bytes ce ty) limit_st
      (abi_builtin_allocate_state st.cs_next_id (type_memory_bytes ce ty) initial) actual /\
    inst_extends st final
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `type_memory_bytes ce ty < dimword (:256)` by decide_tac >>
  drule abi_empty_round_coherent >> strip_tac >>
  mp_tac (Q.INST [`outsz` |-> `type_memory_bytes ce ty`, `length_only` |-> `F`]
    abi_empty_complex_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >> gvs[] >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK actual` >>
  drule_all abi_empty_coherent_static_input >> strip_tac >>
  qexists_tac `actual` >> asm_rewrite_tac[]
QED

Theorem abi_empty_checked_static_producer:
  let ce = build_compile_env tops vis mut func_name fargs ret_type
    (code_stmts:stmt list) use_trans in
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ty /\ evaluate_type (type_env tops) ty = SOME tv /\
  ~is_dynamic (vyper_to_abi_type (type_env tops) ty) /\
  has_type (vyper_to_abi_type (type_env tops) ty) (default_to_abi tv) /\
  compile_builtin_empty_complex (type_memory_bytes ce ty) F st = (buf,final) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,type_memory_bytes ce ty)) /\
  p+type_memory_bytes ce ty < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\
    eval_operand buf.buf_operand actual = SOME (n2w p) /\ buf.buf_size = type_memory_bytes ce ty /\
    abi_encoder_input (type_to_abi_enc_info ce.ce_struct_fields ce ty)
      (vyper_to_abi_type (type_env tops) ty) (default_to_abi tv)
      p (type_memory_bytes ce ty) actual.vs_memory /\
    abi_empty_effect st.cs_next_var p (type_memory_bytes ce ty) limit_st
      (abi_builtin_allocate_state st.cs_next_id (type_memory_bytes ce ty) initial) actual /\
    inst_extends st final
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent
     (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans)
     (type_env tops)
     (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans).
       ce_struct_fields ty tv` by
    (irule abi_caller_coherent >> asm_rewrite_tac[] >>
     qexists_tac `in_deploy` >> asm_rewrite_tac[]) >>
  drule_all abi_empty_static_producer >> simp[]
QED

(* Assemble recursive default inputs over concrete zero-filled memory.
   Child premises are pure data properties for structural induction. *)
Theorem abi_empty_tuple_type_typed:
  abi_encoder_tuple_type at ats /\ has_type at (ListV avs) ==>
  has_type (Tuple ats) (ListV avs)
Proof
  rw[abi_encoder_tuple_type_def] >>
  gvs[has_type_def, valid_length_def, have_type_has_types_REPLICATE]
QED

Theorem abi_empty_complex_type:
  abi_encoder_input (AbiComplex infos) (Tuple ats) (ListV avs) p cap mem /\
  abi_encoder_tuple_type at ats /\ has_type at (ListV avs) ==>
  abi_encoder_input (AbiComplex infos) at (ListV avs) p cap mem
Proof
  strip_tac >>
  qpat_x_assum `abi_encoder_input _ (Tuple ats) _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [abi_encoder_complex_input_iff, abi_encoder_tuple_type_def]) >>
  ONCE_REWRITE_TAC [abi_encoder_complex_input_iff] >>
  qexists_tac `ats` >> qexists_tac `avs` >> asm_rewrite_tac[]
QED

Theorem abi_empty_tuple_memory:
  !(ops:operand list) tys tvs p.
  LENGTH ops = LENGTH tys /\
  LIST_REL (\ty tv.
    has_type (vyper_to_abi_type env ty) (default_to_abi tv) ==>
    abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
      (default_to_abi tv) 0 (type_memory_bytes ce ty) []) tys tvs /\
  has_types (vyper_to_abi_types env tys) (default_to_abi_list tvs) ==>
  abi_tuple_encode_memory (sf:string |-> (string # vyperAST$type # num) list)
    ce (ZIP (ops,tys)) (vyper_to_abi_types env tys)
    (default_to_abi_list tvs) p []
Proof
  Induct_on `ops` >> rpt gen_tac >> Cases_on `tys` >> Cases_on `tvs` >>
  simp[abi_tuple_encode_memory_def, default_to_abi_def, has_type_def] >> strip_tac >>
  FIRST [irule abi_empty_input_zero_address >> first_x_assum irule >> simp[],
    first_x_assum irule >> simp[]]
QED

Theorem abi_empty_complex_zero:
  LENGTH ops = LENGTH tys /\
  LIST_REL (\ty tv. abi_decoder_coherent ce env sf ty tv /\
    (has_type (vyper_to_abi_type env ty) (default_to_abi tv) ==>
      abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
        (default_to_abi tv) 0 (type_memory_bytes ce ty) [])) tys tvs /\
  abi_encoder_tuple_type at (vyper_to_abi_types env tys) /\
  has_type at (ListV (default_to_abi_list tvs)) ==>
  abi_encoder_input (AbiComplex (abi_tuple_encode_infos sf ce (ZIP (ops,tys))))
    at (ListV (default_to_abi_list tvs)) p (abi_tuple_bytes ce (ZIP (ops,tys))) []
Proof
  simp_tac bool_ss [LIST_REL_CONJ, ETA_AX] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  drule_all abi_empty_tuple_type_typed >> strip_tac >>
  `has_types (vyper_to_abi_types env tys) (default_to_abi_list tvs)` by
    (qpat_assum `has_type (Tuple _) (ListV _)`
      (ACCEPT_TAC o CONJUNCT2 o ONCE_REWRITE_RULE [has_type_def])) >>
  `abi_tuple_encode_memory sf ce (ZIP (ops,tys)) (vyper_to_abi_types env tys)
     (default_to_abi_list tvs) p []` by
    (mp_tac (Q.SPECL [`ops`, `tys`, `tvs`, `p`] abi_empty_tuple_memory) >>
     impl_tac >- asm_rewrite_tac[] >> simp[]) >>
  drule_all abi_tuple_encode_layout_coherent >> strip_tac >>
  drule_all abi_tuple_encode_complex_input >> strip_tac >>
  drule_all abi_empty_complex_type >> simp[]
QED

(* Recursive default inputs use the real descriptor and semantic memory size.
   The operand list used for tuple assembly is internal to the proof. *)
Theorem abi_empty_infos_zip:
  !tys. abi_tuple_encode_infos sf ce (ZIP (REPLICATE (LENGTH tys) (Lit 0w),tys)) =
    MAP (\ty. (type_to_abi_enc_info sf ce ty,
      abi_embedded_static_size ce.ce_struct_fields ty, type_memory_bytes ce ty,
      is_abi_dynamic ce.ce_struct_fields ty)) tys
Proof
  simp_tac bool_ss [abi_tuple_encode_infos_def] >> Induct >> simp[]
QED

Theorem abi_empty_members_zero:
  LIST_REL (\ty tv. abi_decoder_coherent ce env sf ty tv /\
    (has_type (vyper_to_abi_type env ty) (default_to_abi tv) ==>
      abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
        (default_to_abi tv) 0 (type_memory_bytes ce ty) [])) tys tvs /\
  abi_encoder_tuple_type at (vyper_to_abi_types env tys) /\
  has_type at (ListV (default_to_abi_list tvs)) ==>
  abi_encoder_input (AbiComplex (MAP (\ty. (type_to_abi_enc_info sf ce ty,
      abi_embedded_static_size ce.ce_struct_fields ty, type_memory_bytes ce ty,
      is_abi_dynamic ce.ce_struct_fields ty)) tys)) at
    (ListV (default_to_abi_list tvs)) p (type_memory_bytes ce (TupleT tys)) []
Proof
  strip_tac >>
  mp_tac (Q.INST [`ops` |-> `REPLICATE (LENGTH tys) (Lit 0w)`]
    abi_empty_complex_zero) >>
  impl_tac >- simp[] >>
  simp[abi_empty_infos_zip, abi_tuple_encode_bytes_zip]
QED

Theorem abi_empty_tuple_default_input:
  abi_decoder_coherent ce env sf (TupleT tys) (TupleTV tvs) /\
  LIST_REL (\ty tv.
    has_type (vyper_to_abi_type env ty) (default_to_abi tv) ==>
      abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
        (default_to_abi tv) 0 (type_memory_bytes ce ty) []) tys tvs /\
  has_type (vyper_to_abi_type env (TupleT tys)) (default_to_abi (TupleTV tvs)) ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (TupleT tys))
    (vyper_to_abi_type env (TupleT tys)) (default_to_abi (TupleTV tvs))
    0 (type_memory_bytes ce (TupleT tys)) []
Proof
  strip_tac >> Cases_on `is_dynamic (vyper_to_abi_type env (TupleT tys))`
  >- (drule abi_decoder_coherent_header >> strip_tac >>
      `is_abi_dynamic ce.ce_struct_fields (TupleT tys)` by fs[abi_decoder_header_def] >>
      asm_simp_tac bool_ss [Once type_to_abi_enc_info_def,
        vyper_to_abi_type_def, default_to_abi_def] >>
      mp_tac (Q.INST [`tys` |-> `tys`, `tvs` |-> `tvs`, `env` |-> `env`,
        `at` |-> `Tuple (vyper_to_abi_types env tys)`, `p` |-> `0`]
        abi_empty_members_zero) >>
      impl_tac
      >- (fs[abi_encoder_tuple_type_def, LIST_REL_CONJ, ETA_AX,
             abi_decoder_coherent_tuple_iff, default_to_abi_def] >>
          CONV_TAC (DEPTH_CONV ETA_CONV) >> asm_rewrite_tac[]) >>
      simp[]) >>
  irule abi_empty_coherent_static_input >> simp[abi_empty_memory_observation]
QED

Theorem abi_empty_fixed_memory_size:
  type_memory_bytes ce (TupleT (REPLICATE n ty)) =
    type_memory_bytes ce (ArrayT ty (Fixed n))
Proof
  simp[type_memory_bytes_def, map_replicate, SUM_REPLICATE]
QED

Theorem abi_empty_fixed_default_input:
  abi_decoder_coherent ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) /\
  (has_type (vyper_to_abi_type env ty) (default_to_abi tv) ==>
    abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
      (default_to_abi tv) 0 (type_memory_bytes ce ty) []) /\
  has_type (vyper_to_abi_type env (ArrayT ty (Fixed n)))
    (default_to_abi (ArrayTV tv (Fixed n))) ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (ArrayT ty (Fixed n)))
    (vyper_to_abi_type env (ArrayT ty (Fixed n))) (default_to_abi (ArrayTV tv (Fixed n)))
    0 (type_memory_bytes ce (ArrayT ty (Fixed n))) []
Proof
  strip_tac >> Cases_on `is_dynamic (vyper_to_abi_type env (ArrayT ty (Fixed n)))`
  >- (drule abi_decoder_coherent_header >> strip_tac >>
      `is_abi_dynamic ce.ce_struct_fields (ArrayT ty (Fixed n))` by
        fs[abi_decoder_header_def] >>
      mp_tac (Q.INST [`tys` |-> `REPLICATE n ty`, `tvs` |-> `REPLICATE n tv`,
        `at` |-> `vyper_to_abi_type env (ArrayT ty (Fixed n))`, `p` |-> `0`]
        abi_empty_members_zero) >>
      impl_tac
      >- (simp[LIST_REL_REPLICATE_same, abi_encoder_tuple_type_def,
            vyper_to_abi_type_def, vyper_to_abi_types_MAP, map_replicate,
            default_to_abi_def, default_to_abi_list_MAP] >>
          fs[abi_decoder_coherent_array_iff, default_to_abi_def, has_type_def,
             valid_length_def, have_type_has_types_REPLICATE]) >>
      asm_simp_tac bool_ss [Once type_to_abi_enc_info_def, default_to_abi_def,
        default_to_abi_list_MAP, map_replicate, GSYM REPLICATE_GENLIST,
        abi_empty_fixed_memory_size]) >>
  irule abi_empty_coherent_static_input >> simp[abi_empty_memory_observation]
QED
