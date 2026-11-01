(* Resource-boundary diagnostics for the frozen source encoder contract.
   These concern internal runner premises, not execution counterexamples. *)
Theory abiEncoderResourceAdapter
Ancestors
  abiEncoderProps abiEncoderOpenInput abiEncoderOpenInputFrame
  abiEncoderInput abiDecodeRanges abiDecoderAllocation abiDecoderFootprint
  venomMemDefs abiDecoderReentry abiDecoderFrame compileEnv
  finite_map pred_set valueEncodingProps contractABI
  fragExec words list vyperTyping valueEncoding vyperValue vyperABI

Theorem abi_encoder_zero_source_separation_diagnostic:
  evaluate_type FEMPTY
    (TupleT [ArrayT (BaseT (BytesT (Dynamic 1))) (Fixed 0)]) =
    SOME (TupleTV [ArrayTV (BaseTV (BytesT (Dynamic 1))) (Fixed 0)]) /\
  type_memory_size
    (TupleTV [ArrayTV (BaseTV (BytesT (Dynamic 1))) (Fixed 0)]) = 0 /\
  venomMemDefs$regions_disjoint (16,0) (0,32) /\
  (!source_cap:num. ~(16 + source_cap <= 0 \/ 0 + 32 <= 16))
Proof
  simp[evaluate_type_def, type_memory_size_def, type_slot_size_def,
    wordsTheory.dimword_def, vfmConstantsTheory.word_size_def,
    venomMemDefsTheory.regions_disjoint_def]
QED

Theorem abi_encoder_zero_source_value_diagnostic:
  value_has_type
    (TupleTV [ArrayTV (BaseTV (BytesT (Dynamic 1))) (Fixed 0)])
    (ArrayV (TupleV [ArrayV (SArrayV [])])) /\
  vyper_to_abi FEMPTY
    (TupleT [ArrayT (BaseT (BytesT (Dynamic 1))) (Fixed 0)])
    (ArrayV (TupleV [ArrayV (SArrayV [])])) = SOME (ListV [ListV []]) /\
  val_in_memory
    (TupleTV [ArrayTV (BaseTV (BytesT (Dynamic 1))) (Fixed 0)])
    (ArrayV (TupleV [ArrayV (SArrayV [])])) 16 mem /\
  LENGTH (enc (vyper_to_abi_type FEMPTY
    (TupleT [ArrayT (BaseT (BytesT (Dynamic 1))) (Fixed 0)]))
    (ListV [ListV []])) = 32
Proof
  simp[value_has_type_def, vyper_to_abi_def, vyper_to_abi_type_def,
    val_in_memory_def, type_memory_size_def, enc_def, is_dynamic_def,
    REV_DEF, evaluate_type_def, type_slot_size_def,
    vfmConstantsTheory.word_size_def, wordsTheory.dimword_def]
QED

Theorem abi_encoder_zero_source_pre_diagnostic:
  enc_pre st st' ops 64 top
    (TupleTV [ArrayTV (BaseTV (BytesT (Dynamic 1))) (Fixed 0)])
    (ArrayV (TupleV [ArrayV (SArrayV [])])) 16 [(0,32)] s <=>
  ((!y. MEM (Var y) ops ==> not_fresh_at st y) /\
   enc_scratch (frag_ids st st') 64 top s)
Proof
  simp[enc_pre_def, abi_encoder_zero_source_value_diagnostic,
    type_memory_size_def, venomMemDefsTheory.regions_disjoint_def]
QED

Theorem abi_encoder_pre_memory_bounds:
  enc_pre st st' ops lo top tv v sb [(d,n)] s ==>
  sb + type_memory_size tv < dimword (:256) /\
  d + n < dimword (:256)
Proof
  simp[enc_pre_def, enc_scratch_def] >> rpt strip_tac >> decide_tac
QED

Theorem abi_encoder_zero_source_open_diagnostic:
  abi_encoder_open_input (AbiComplex [(AbiComplex [],32,0,T)])
    (Tuple [Array (SOME 0) (Bytes NONE)]) (ListV [ListV []]) 16 0 mem
Proof
  simp[abi_encoder_open_complex_iff, abi_encoder_tuple_type_def,
    abi_encoder_member_span_def] >>
  simp[abi_member_head_size_def, is_dynamic_def,
    abi_encoder_open_complex_iff, abi_encoder_tuple_type_def,
    abi_encoder_member_span_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem abi_encoder_zero_source_open_transport:
  abi_encoder_open_input (AbiComplex [(AbiComplex [],32,0,T)])
    (Tuple [Array (SOME 0) (Bytes NONE)]) (ListV [ListV []]) 16 0 mem'
Proof
  irule abi_encoder_open_input_empty_memory >>
  qexists_tac `[]` >> simp[abi_encoder_zero_source_open_diagnostic]
QED

Theorem abi_encoder_fragment_ids:
  frag_ids st st' = abi_decoder_ids st.cs_next_id st'.cs_next_id
Proof
  simp[frag_ids_def, abi_decoder_ids_def]
QED

Theorem abi_encoder_fragment_missing:
  abi_decoder_missing st.cs_next_id st'.cs_next_id s =
  {i | i IN frag_ids st st' /\ FLOOKUP s.vs_allocas i = NONE}
Proof
  simp[abi_decoder_missing_def, abi_encoder_fragment_ids,
    EXTENSION, FLOOKUP_DEF] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem abi_encoder_scratch_budget:
  enc_scratch (frag_ids st st') lo top s ==>
  abi_decoder_budget st.cs_next_id st'.cs_next_id lo (top-lo) s
Proof
  pure_rewrite_tac[enc_scratch_def, abi_decoder_budget_def,
    abi_encoder_fragment_missing, GSYM abi_encoder_fragment_ids] >>
  strip_tac >> `lo <= top` by decide_tac >>
  `lo + (top-lo) = top` by decide_tac >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `alloca_inv s` mp_tac >>
  pure_rewrite_tac[alloca_inv_def, alloca_next_valid_def,
    allocas_non_overlapping_def] >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >>
      `sz = 32 /\ lo <= off` by metis_tac[] >>
      simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem abi_encoder_scratch_footprint:
  enc_scratch (frag_ids st st') lo top s /\ p+n <= lo ==>
  abi_footprint_disjoint p n
    (abi_decoder_child_scratch (abi_decoder_ids st.cs_next_id st'.cs_next_id)
      lo (top-lo) s)
Proof
  strip_tac >> irule abi_decoder_child_scratch_disjoint >> simp[] >>
  qpat_x_assum `enc_scratch _ _ _ _` mp_tac >>
  pure_rewrite_tac[enc_scratch_def, abi_encoder_fragment_ids] >>
  strip_tac >> conj_tac
  >- (rpt strip_tac >> `lo <= q` by metis_tac[] >> decide_tac) >>
  decide_tac
QED

Theorem abi_encoder_pre_operand_live:
  enc_pre st st' ops lo top tv v sb outs s /\ MEM op ops ==>
  abi_decoder_operand_live st.cs_next_var op
Proof
  Cases_on `op` >>
  simp[enc_pre_def, abi_decoder_operand_live_def,
    abi_decoder_older_vars_def, not_fresh_at_def] >> metis_tac[]
QED

Theorem abi_encoder_pre_prune_eval:
  enc_pre st st' ops lo top tv v sb outs s /\ MEM op ops ==>
  eval_operand op (abi_decoder_prune_vars st.cs_next_var s) = eval_operand op s
Proof
  strip_tac >> irule abi_decoder_prune_eval >>
  drule_all abi_encoder_pre_operand_live >> simp[]
QED

Theorem abi_encoder_prune_scratch:
  enc_scratch ids lo top (abi_decoder_prune_vars next s) <=>
  enc_scratch ids lo top s
Proof
  simp[enc_scratch_def, abi_decoder_prune_vars_def,
    alloca_inv_def, alloca_next_valid_def, allocas_non_overlapping_def]
QED

Theorem abi_encoder_prune_pre:
  enc_pre st st' ops lo top tv v sb outs
    (abi_decoder_prune_vars next s) <=>
  enc_pre st st' ops lo top tv v sb outs s
Proof
  simp_tac bool_ss [enc_pre_def, abi_encoder_prune_scratch,
    abi_decoder_prune_vars_def] >> simp[]
QED

Theorem abi_encoder_budget_scratch:
  abi_decoder_budget st.cs_next_id st'.cs_next_id lo (top-lo) s /\
  lo <= top /\ alloca_inv s ==>
  enc_scratch (frag_ids st st') lo top s
Proof
  strip_tac >> `lo + (top-lo) = top` by decide_tac >>
  qpat_x_assum `abi_decoder_budget _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_decoder_budget_def, enc_scratch_def,
    abi_encoder_fragment_missing, GSYM abi_encoder_fragment_ids] >>
  strip_tac >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem abi_encoder_prune_entry:
  enc_pre st st' ops lo top tv v sb outs s ==>
  enc_pre st st' ops lo top tv v sb outs
    (abi_decoder_prune_vars st.cs_next_var s) /\
  fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s) /\
  abi_decoder_vars_extend s.vs_vars
    (abi_decoder_prune_vars st.cs_next_var s) s
Proof
  simp[abi_encoder_prune_pre, abi_decoder_prune_fresh,
    abi_decoder_prune_extension]
QED
