Theory stmtSimLogDataInput
Ancestors
  stmtSimLogDataRun stmtSimLogSource abiEncoderSourceCorrect
  abiBuiltinEncodeWord entryDecodeProps entryDecodeStaticProps
  supportedTypes vyperTyping vyperABI contractABI vyperValue words integer arithmetic typedCopyMetadata
  abiEncoderInput valueEncoding compileEnv exprLowering stmtSimLogData
  valueEncodingProps list abiDecodeRanges exprSimAttributeFields vyperTypeDefaults abiDecoderMembers

Theorem log_word_abi_type:
  supported_word_type ty /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
  has_type (vyper_to_abi_type env ty) av /\
  ~is_dynamic (vyper_to_abi_type env ty) /\
  static_length (vyper_to_abi_type env ty) = 32
Proof
  Cases_on `ty` >> simp[supported_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, evaluate_type_def] >>
  TRY (rename1 `BytesT bound` >> Cases_on `bound` >>
       simp[supported_word_type_def]) >>
  rpt strip_tac >> Cases_on `v` >>
  gvs[value_has_type_def, vyper_to_abi_base_def,
      vyper_to_abi_type_def, vyper_base_to_abi_type_def,
      has_type_def, is_dynamic_def, static_length_def,
      valid_int_bound_def, int_bits_bound_def, within_int_bound_def]
  >~ [`(if b then 1 else 0) < 2`] >- (Cases_on `b` >> simp[])
  >~ [`w2n (word_of_bytes_be bs) < _`]
  >- (qspec_then `word_of_bytes_be bs : 160 word` mp_tac
        (INST_TYPE [alpha |-> ``:160``] w2n_lt) >>
      CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> simp[dimword_def]) >>
  Cases_on `i < 0` >> gvs[PRE_SUB1] >>
  `Num (i + 1) < Num (-i)` by
    (`Num (i+1) = Num (-(i+1))` by simp[Num_neg] >>
     pop_assum SUBST1_TAC >>
     irule (iffRL NUM_LT) >> intLib.ARITH_TAC) >> decide_tac
QED

Theorem log_word_memory_input:
  supported_word_type ty /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ val_in_memory tv v p mem ==>
  ?av. vyper_to_abi env ty v = SOME av /\
    abi_encoder_input (type_to_abi_enc_info sf ce ty)
      (vyper_to_abi_type env ty) av p (type_memory_bytes ce ty) mem
Proof
  rpt strip_tac >>
  `supported_scalar_type ty` by simp[supported_scalar_type_def] >>
  drule_all log_scalar_abi_exists >> strip_tac >>
  drule_all log_word_abi_type >> strip_tac >>
  drule supported_word_type_is_word >> strip_tac >>
  drule abi_builtin_encode_word_info >> strip_tac >>
  drule_all val_in_memory_word >> strip_tac >>
  drule_all vyper_to_abi_word_enc >> strip_tac >>
  qexists_tac `av` >> simp[abi_encoder_input_copy_iff, mem_bytes_at_word_eq] >>
  metis_tac[]
QED

Theorem log_scalar_memory_input:
  supported_scalar_type ty /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\ val_in_memory tv v p mem /\
  type_memory_bytes ce ty < dimword (:256) ==>
  ?av. vyper_to_abi env ty v = SOME av /\
    abi_encoder_input (type_to_abi_enc_info sf ce ty)
      (vyper_to_abi_type env ty) av p (type_memory_bytes ce ty) mem
Proof
  rpt strip_tac >> Cases_on `supported_word_type ty`
  >- (drule_all log_word_memory_input >> simp[]) >>
  `supported_string_type ty` by gvs[supported_scalar_type_def] >>
  Cases_on `ty` >> gvs[supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[supported_string_type_def]
  >~ [`BytesT bound`] >- (Cases_on `bound` >>
      gvs[supported_string_type_def, evaluate_type_def, AllCaseEqs()] >>
      Cases_on `v` >> gvs[value_has_type_def] >>
      drule_all (SRULE[value_has_type_def] abi_encoder_bytes_source_input) >>
      simp[type_memory_bytes_def, type_memory_size_def, vfmConstantsTheory.word_size_def]) >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  `n < dimword (:256)` by
    (gvs[type_memory_bytes_def, type_memory_size_def] >> decide_tac) >>
  drule_all (SRULE[value_has_type_def] abi_encoder_string_source_input) >>
  simp[type_memory_bytes_def, type_memory_size_def,
       vfmConstantsTheory.word_size_def, vyperMiscTheory.n2w_o_ORD_def]
QED

Theorem log_scalar_abi_metadata:
  supported_scalar_type ty ==>
  is_abi_dynamic sf ty = is_dynamic (vyper_to_abi_type env ty) /\
  abi_embedded_static_size sf ty = abi_member_head_size (vyper_to_abi_type env ty) /\
  (~is_dynamic (vyper_to_abi_type env ty) ==>
    static_length (vyper_to_abi_type env ty) = type_memory_bytes ce ty)
Proof
  Cases_on `ty` >> simp[supported_scalar_type_def, supported_word_type_def,
    supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, supported_string_type_def,
    is_abi_dynamic_def, abi_embedded_static_size_def, abi_static_size_def,
    abi_member_head_size_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
    is_dynamic_def, static_length_def, type_memory_bytes_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >>
  simp[supported_word_type_def, supported_string_type_def,
    is_abi_dynamic_def, abi_embedded_static_size_def, abi_static_size_def,
    abi_member_head_size_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
    is_dynamic_def, static_length_def, type_memory_bytes_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem log_data_layout_inputs:
  !tys vs p.
    EVERY supported_scalar_type tys /\
    LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                          value_has_type tv v) tys vs /\
    log_data_layout cx tys vs p mem /\
    SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) ==>
    ?avs. vyper_to_abi_list (get_tenv cx) tys vs = SOME avs /\
      LIST_REL (\ty av. has_type (vyper_to_abi_type (get_tenv cx) ty) av) tys avs /\
      (!i. i < LENGTH tys ==>
        abi_encoder_input (type_to_abi_enc_info sf ce (EL i tys))
          (vyper_to_abi_type (get_tenv cx) (EL i tys)) (EL i avs)
          (p + SUM (MAP (type_memory_bytes ce) (TAKE i tys)))
          (type_memory_bytes ce (EL i tys)) mem)
Proof
  Induct_on `tys` >> Cases_on `vs` >> simp[log_data_layout_def] >>
  rpt strip_tac >> gvs[] >>
  rename1 `evaluate_type (get_tenv cx) ty = SOME tv` >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    (irule log_scalar_memory_size >> simp[] >> metis_tac[]) >>
  `type_memory_bytes ce ty < dimword (:256)` by (simp[] >> decide_tac) >>
  `SUM (MAP (type_memory_bytes ce) tys) < dimword (:256)` by (simp[] >> decide_tac) >>
  drule_all log_scalar_memory_input >>
  disch_then (qspec_then `sf` strip_assume_tac) >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `vyper_to_abi_list (get_tenv cx) tys _ = SOME avs` >>
  qexists_tac `av::avs` >> simp[Once vyper_to_abi_def] >> conj_tac
  >- (drule abi_encoder_input_typed >> simp[]) >>
  Cases >- gvs[] >> simp[] >> rpt strip_tac >>
  first_x_assum drule >>
  pure_rewrite_tac[AC ADD_ASSOC ADD_COMM] >> simp[]
QED

Theorem log_tuple_abi_metadata[local]:
  !tys. EVERY supported_scalar_type tys ==>
  is_abi_dynamic sf (TupleT tys) =
    is_dynamic (vyper_to_abi_type env (TupleT tys)) /\
  type_memory_bytes ce (TupleT tys) = SUM (MAP (type_memory_bytes ce) tys) /\
  (~is_dynamic (vyper_to_abi_type env (TupleT tys)) ==>
    static_length (vyper_to_abi_type env (TupleT tys)) =
      SUM (MAP (type_memory_bytes ce) tys))
Proof
  Induct >> simp[Once is_abi_dynamic_def, Once type_memory_bytes_def,
    vyper_to_abi_type_def, is_dynamic_def, static_length_def] >>
  rpt strip_tac >> drule log_scalar_abi_metadata >>
  disch_then (qspecl_then [`sf`, `env`, `ce`] strip_assume_tac) >>
  gvs[Once is_abi_dynamic_def, vyper_to_abi_type_def,
      is_dynamic_def, static_length_def, SF ETA_ss]
QED

Theorem log_tuple_types[local]:
  !tys tvs vs.
    EVERY supported_scalar_type tys /\
    LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
    LIST_REL (\ty v. ?tv. evaluate_type env ty = SOME tv /\ value_has_type tv v) tys vs ==>
    LIST_REL value_has_type tvs vs /\
    type_memory_size_list tvs = SUM (MAP (type_memory_bytes ce) tys) /\
    !acc. evaluate_types env tys acc = SOME (REVERSE acc ++ tvs)
Proof
  Induct_on `tys` >> Cases_on `tvs` >> Cases_on `vs` >>
  simp[Once evaluate_type_def, type_memory_size_def] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `evaluate_type env ty = SOME tv` >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    (irule log_scalar_memory_size >> simp[] >> metis_tac[]) >>
  simp[Once evaluate_type_def, type_memory_size_def] >>
  metis_tac[]
QED

Theorem log_data_layout_typed_tuple:
  EVERY supported_scalar_type tys /\
  LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                        value_has_type tv v) tys vs /\
  log_data_layout cx tys vs p mem /\
  SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) ==>
  ?tv. evaluate_type (get_tenv cx) (TupleT tys) = SOME tv /\
    value_has_type tv (ArrayV (TupleV vs)) /\
    val_in_memory tv (ArrayV (TupleV vs)) p mem /\
    type_memory_size tv = SUM (MAP (type_memory_bytes ce) tys)
Proof
  rpt strip_tac >> drule log_data_layout_tuple >> strip_tac >>
  drule_all log_tuple_types >> disch_then (qspec_then `ce` strip_assume_tac) >>
  `type_slot_size (TupleTV tvs) <= dimword (:256)` by
    (gvs[type_memory_size_def, type_slot_size_def] >>
     mp_tac (cj 2 valueEncodingPropsTheory.type_memory_size_slots) >>
     disch_then (qspec_then `tvs` assume_tac) >> decide_tac) >>
  qexists_tac `TupleTV tvs` >>
  simp[Once evaluate_type_def, value_has_type_def, val_in_memory_def,
       type_memory_size_def, values_have_types_LIST_REL] >>
  gvs[dimword_def]
QED

Theorem log_scalar_memory_positive[local]:
  supported_scalar_type ty ==> 0 < type_memory_bytes ce ty
Proof
  Cases_on `ty` >> simp[supported_scalar_type_def, supported_word_type_def,
    supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, supported_string_type_def, type_memory_bytes_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >>
  simp[supported_word_type_def, supported_string_type_def, type_memory_bytes_def]
QED

Theorem log_tuple_length_bound[local]:
  !tys. EVERY supported_scalar_type tys ==>
    LENGTH tys <= SUM (MAP (type_memory_bytes ce) tys)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  drule log_scalar_memory_positive >> disch_then (qspec_then `ce` assume_tac) >>
  first_x_assum drule >> decide_tac
QED

Theorem log_data_layout_input:
  EVERY supported_scalar_type tys /\
  LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                        value_has_type tv v) tys vs /\
  log_data_layout cx tys vs p mem /\
  SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) ==>
  ?avs. vyper_to_abi_list (get_tenv cx) tys vs = SOME avs /\
    abi_encoder_input (type_to_abi_enc_info sf ce (TupleT tys))
      (vyper_to_abi_type (get_tenv cx) (TupleT tys)) (ListV avs) p
      (SUM (MAP (type_memory_bytes ce) tys)) mem
Proof
  rpt gen_tac >> strip_tac >>
  drule_all log_data_layout_inputs >>
  disch_then (qspec_then `sf` strip_assume_tac) >>
  drule_all log_data_layout_typed_tuple >> strip_tac >>
  `is_abi_dynamic ce.ce_struct_fields (TupleT tys) =
     is_dynamic (vyper_to_abi_type (get_tenv cx) (TupleT tys)) /\
   type_memory_bytes ce (TupleT tys) = SUM (MAP (type_memory_bytes ce) tys) /\
   (~is_dynamic (vyper_to_abi_type (get_tenv cx) (TupleT tys)) ==>
    static_length (vyper_to_abi_type (get_tenv cx) (TupleT tys)) =
     SUM (MAP (type_memory_bytes ce) tys))` by
    (irule log_tuple_abi_metadata >> simp[]) >>
  drule log_tuple_length_bound >> disch_then (qspec_then `ce` assume_tac) >>
  `LENGTH avs = LENGTH tys` by metis_tac[LIST_REL_LENGTH] >>
  qexists_tac `avs` >> simp[] >>
  `has_type (vyper_to_abi_type (get_tenv cx) (TupleT tys)) (ListV avs)` by
    (simp[vyper_to_abi_type_def, has_type_def, vyper_to_abi_types_MAP,
          has_types_LIST_REL, LIST_REL_MAP1, combinTheory.o_DEF] >>
     gvs[dimword_def, SF ETA_ss] >> decide_tac) >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields (TupleT tys)`
  >- (simp[Once type_to_abi_enc_info_def, abi_encoder_complex_input_iff] >>
      qexists_tac `vyper_to_abi_types (get_tenv cx) tys` >>
      simp[abi_encoder_tuple_type_def, abi_encoder_member_span_def,
           vyper_to_abi_types_MAP, MAP_MAP_o, combinTheory.o_DEF,
           GSYM MAP_TAKE] >>
      conj_tac >- (gvs[has_type_def, vyper_to_abi_type_def, dimword_def] >> decide_tac) >>
      conj_tac >- gvs[has_type_def, vyper_to_abi_type_def, vyper_to_abi_types_MAP] >>
      simp[SF ETA_ss] >>
      rpt strip_tac >> gvs[EL_MAP] >>
      `supported_scalar_type (EL i tys)` by metis_tac[EVERY_EL] >>
      `is_abi_dynamic ce.ce_struct_fields (EL i tys) =
        is_dynamic (vyper_to_abi_type (get_tenv cx) (EL i tys)) /\
       abi_embedded_static_size ce.ce_struct_fields (EL i tys) =
        abi_member_head_size (vyper_to_abi_type (get_tenv cx) (EL i tys)) /\
       (~is_dynamic (vyper_to_abi_type (get_tenv cx) (EL i tys)) ==>
        static_length (vyper_to_abi_type (get_tenv cx) (EL i tys)) =
         type_memory_bytes ce (EL i tys))` by
        (irule log_scalar_abi_metadata >> simp[]) >>
      simp[]) >>
  `vyper_to_abi (get_tenv cx) (TupleT tys) (ArrayV (TupleV vs)) =
    SOME (ListV avs)` by simp[Once vyper_to_abi_def] >>
  `~is_dynamic (vyper_to_abi_type (get_tenv cx) (TupleT tys))` by metis_tac[] >>
  drule_all val_in_memory_static_abi >> strip_tac >>
  once_rewrite_tac[type_to_abi_enc_info_def] >>
  rule_assum_tac (REWRITE_RULE [vyper_to_abi_type_def]) >>
  asm_rewrite_tac[abi_encoder_input_copy_iff, LESS_EQ_REFL] >>
  conj_tac >- (first_x_assum irule >> asm_rewrite_tac[]) >>
  qpat_x_assum `type_memory_size tv = _`
    (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  first_assum ACCEPT_TAC
QED

Theorem log_data_sources_typed:
  !xs vs. LIST_REL (log_data_source cx b cap s) xs vs ==>
    LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                          value_has_type tv v) (MAP SND xs) vs
Proof
  Induct_on `xs` >- simp[] >>
  gen_tac >> PairCases_on `h` >> Cases_on `vs` >>
  simp[log_data_source_def] >> metis_tac[]
QED

Theorem compile_log_store_data_input:
  compile_log_store_data cenv xs (MAP SND xs) buf off sa = ((),sb) /\
  LIST_REL (log_data_source cx b cap s) xs vs /\
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sa x) xs /\
  (!x. buf = Var x ==> not_fresh_at sa x) /\
  eval_operand buf s = SOME (n2w b) /\
  off + SUM (MAP (type_memory_bytes cenv) (MAP SND xs)) <= cap /\
  b + cap < dimword (:256) ==>
  inst_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  ?t avs. run_inst_seq (emitted_insts sa sb) s = OK t /\
    log_data_layout cx (MAP SND xs) vs (b + off) t.vs_memory /\
    log_write_frame sa (b + off)
      (SUM (MAP (type_memory_bytes cenv) (MAP SND xs))) s t /\
    LIST_REL (log_data_source cx b cap t) xs vs /\
    eval_operand buf t = SOME (n2w b) /\
    (!op ty. MEM (op,ty) xs ==> eval_operand op t = eval_operand op s) /\
    vyper_to_abi_list (get_tenv cx) (MAP SND xs) vs = SOME avs /\
    abi_encoder_input (type_to_abi_enc_info sf cenv (TupleT (MAP SND xs)))
      (vyper_to_abi_type (get_tenv cx) (TupleT (MAP SND xs))) (ListV avs)
      (b + off) (SUM (MAP (type_memory_bytes cenv) (MAP SND xs))) t.vs_memory
Proof
  strip_tac >> drule_all compile_log_store_data_run >> strip_tac >>
  drule log_data_sources_types >> strip_tac >>
  drule log_data_sources_typed >> strip_tac >>
  `EVERY supported_scalar_type (MAP SND xs)` by gvs[EVERY_MAP, combinTheory.o_DEF] >>
  `SUM (MAP (type_memory_bytes cenv) (MAP SND xs)) < dimword (:256)` by decide_tac >>
  drule_all log_data_layout_input >>
  disch_then (qspec_then `sf` strip_assume_tac) >>
  asm_rewrite_tac[] >> qexistsl_tac [`t`, `avs`] >> asm_rewrite_tac[]
QED
