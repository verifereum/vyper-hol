(* Caller facts and compiler views for the actual decoder callback. *)
Theory abiDecodePtrCallbackMetadata
Ancestors
  abiDecodePtrExpr abiDecodePtrCallerMetadata abiDecodePtrCallerBounds
  abiBuiltinDecodeHeader abiDecoderAppend abiBuiltinDecodeAllocation
  exprSimHyps allocLimits vyperValue words venomMemProps
  fragExec context compileEnv list exprSimHypsDefs vyperABI vyperAST
  exprOperandVar exprLowering exprLoweringProps freshWrites calldataDynOwned
  abiCallerAbiBound combinatorics supportedTypes

Theorem abi_decode_body_machine_bounds:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiDecode b) (TupleT tys) args) es /\
  EVERY supported_scalar_type tys /\ 2 <= LENGTH tys ==>
  type_memory_bytes ce (TupleT tys) < 2 ** 64 /\
  type_memory_bytes ce (TupleT tys) < dimword(:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT tys) < dimword(:256) /\
  LENGTH tys < dimword(:256)
Proof
  strip_tac >>
  `LENGTH tys <= type_memory_bytes ce (TupleT tys)` by
    (simp[type_memory_bytes_def] >>
     `EVERY (\ty. 0 < type_memory_bytes ce ty) tys` by
       (qpat_x_assum `EVERY supported_scalar_type tys` mp_tac >>
        ho_match_mp_tac MONO_EVERY >> Cases >>
        simp[supported_scalar_type_def, supported_word_type_def,
             supported_string_type_def] >>
        rename1 `BaseT bt` >> Cases_on `bt` >>
        simp[type_memory_bytes_def] >>
        rename1 `BytesT bd` >> Cases_on `bd` >> simp[type_memory_bytes_def]) >>
     mp_tac (Q.SPEC `MAP (type_memory_bytes ce) tys` list_length_le_sum) >>
     simp[EVERY_MAP] >> metis_tac[]) >>
  `alloc_limits_expr ce (TypeBuiltin ann (AbiDecode b) (TupleT tys) args)` by
    fs[expr_body_pre_def] >>
  drule alloc_limits_abi_decode_output >>
  simp[needs_external_call_wrap_def] >> strip_tac >>
  `abi_size_bound ce.ce_struct_fields (TupleT tys) <=
     2 * type_memory_bytes ce (TupleT tys)` by
    metis_tac[abi_decode_flat_abi_capacity] >>
  simp[dimword_def, venomMemPropsTheory.dimindex_256] >> decide_tac
QED

Theorem abi_decode_body_tuple_coherence:
  expr_body_pre ce cx env (TypeBuiltin (TupleT tys) (AbiDecode b) (TupleT tys) args) es /\
  EVERY supported_scalar_type tys ==>
  ?tvs. evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields
      (TupleT tys) (TupleTV tvs)
Proof
  strip_tac >> drule expr_body_pre_type_evaluates >>
  simp[expr_type_def] >>
  simp[Once evaluate_type_def] >>
  Cases_on `evaluate_types (get_tenv cx) tys []` >> simp[] >>
  rename1 `evaluate_types _ _ _ = SOME tvs` >>
  strip_tac >>
  qexists_tac `tvs` >>
  `evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs)` by
    simp[Once evaluate_type_def] >>
  simp[] >> irule abi_decode_flat_tuple_coherence >> simp[]
QED

Theorem abi_decode_located_compile_view:
  as_ptr_val ty LocMemory (lower_abi_decode data info mn mx cap sa) = (vv,sb) /\
  fn_has_code sa sb func ==>
  ?len src sh buf ready.
    abi_builtin_decode_header data mn mx sa = ((len,src),sh) /\
    compile_alloc_buffer cap sh = (buf,ready) /\
    compile_abi_decode_to_buf buf.buf_operand (Lit 0w) MLOAD src len info ready = ((),sb) /\
    vv = LocatedValue ty (mk_ptr buf.buf_operand LocMemory) /\
    cs_extends sa sh /\ cs_extends sh ready /\ cs_extends ready sb /\
    fn_has_code sa sh func /\ fn_has_code sa ready func /\
    fn_has_code ready sb func
Proof
  Cases_on `lower_abi_decode data info mn mx cap sa` >>
  simp[exprLoweringTheory.as_ptr_val_def] >> strip_tac >> gvs[] >>
  rename1 `fn_has_code sa sb func` >>
  drule lower_abi_decode_trace >> strip_tac >>
  PairCases_on `inputs` >> gvs[] >>
  `cs_extends sa header_st` by
    (drule abi_builtin_decode_header_shape >>
     simp[cs_extends_def] >> strip_tac >> qexists_tac `[]` >> simp[]) >>
  `cs_extends header_st ready` by
    metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends ready sb` by metis_tac[cs_extends_abi_decode] >>
  `cs_extends header_st sb` by metis_tac[cs_extends_trans] >>
  `cs_extends sa ready` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  simp[] >> metis_tac[fn_has_code_split]
QED

Theorem abi_decode_operand_compile_freshness:
  lower_value compile_expr ce ty e sa = (Var p,sm) /\
  local_ptrs_reserved ce sa /\
  (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) ==>
  not_fresh_at sm p /\ abi_decoder_operand_live sm.cs_next_var (Var p) /\
  (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z)
Proof
  strip_tac >>
  drule_at (Pos hd) compile_lower_value_var >> simp[] >> strip_tac >>
  drule (CONJUNCT2 compile_expr_grows) >> strip_tac >>
  simp[calldata_operand_live_not_fresh] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem abi_decode_flat_source_bound:
  EVERY supported_scalar_type tys ==>
  abi_size_bound sf (TupleT tys) = vyper_abi_size_bound env (TupleT tys)
Proof
  strip_tac >>
  `abi_caller_abi_bound sf env (TupleT tys)` suffices_by
    simp[abi_caller_abi_bound_def] >>
  irule abi_caller_abi_bound_tuple >> fs[EVERY_MEM] >>
  rpt strip_tac >> first_x_assum drule >>
  rename1 `supported_scalar_type ty ==> _` >> Cases_on `ty` >>
  simp[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def, abi_caller_abi_bound_base]
QED
