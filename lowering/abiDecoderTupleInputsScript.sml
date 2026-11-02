(* Recover tuple members and layout from a recursive decoder precondition.
   TOP-LEVEL: abi_decoder_tuple_inputs.
   Helper: tuple conversion shape. *)
Theory abiDecoderTupleInputs
Ancestors
  abiDecoderPreObservations abiDecoderMembers abiDecoderMemberInfos abiDecoderCoherence
  abiDecoderTypedContract abiDecoderContract abiDecoderReentry
  compileEnv valueEncoding vyperABI contractABI venomState words list

Theorem abi_decoder_tuple_values:
  abi_to_vyper env (TupleT tys) av = SOME v ==>
  ?avs vs. av = ListV avs /\ v = ArrayV (TupleV vs)
Proof
  Cases_on `av` >> simp[Once abi_to_vyper_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem abi_decoder_tuple_inputs:
  abi_decoder_recursive_pre ce env sf (TupleT tys) (TupleTV tvs) di av v
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) ==>
  ?avs vs. av = ListV avs /\ v = ArrayV (TupleV vs) /\
    abi_decoder_members ce env sf tys tvs avs vs /\
    type_memory_bytes ce (TupleT tys) = SUM (MAP (type_memory_bytes ce) tys) /\
    abi_decoder_ranges opc hi src dst sb
      (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
      d (SUM (MAP (type_memory_bytes ce) tys)) b cap initial /\
    mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
      (abi_decode_source opc initial) = enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var hi
Proof
  strip_tac >> drule abi_decoder_pre_observations >> strip_tac >>
  `type_memory_bytes ce (TupleT tys) = SUM (MAP (type_memory_bytes ce) tys)`
    by (simp[Once type_memory_bytes_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  drule abi_decoder_tuple_values >> strip_tac >> gvs[Excl "enc_def"] >>
  drule_all abi_decoder_tuple_members >> strip_tac >>
  gvs[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP, Excl "enc_def"]
QED
