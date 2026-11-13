(* Allocation-backed index initialization preserves the executable state interface. *)
Theory abiMalformedIndexState
Ancestors
  abiMalformedResources abiDecoderIndexInit abiDecoderArrayHeader
  exprSimAlloc exprLoweringProps emitHelperProps compileEnv
  venomState venomInst venomMemDefs venomMemProps words finite_map list arithmetic

Theorem abi_malformed_index_state:
  abi_decode_index_init st = (ip,en) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) ==>
  ?t p. run_inst_seq (emitted_insts st en) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    p + 32 < dimword (:256) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry)
Proof
  strip_tac >> drule abi_decode_index_init_trace >> strip_tac >>
  `32 < dimword (:256)` by
    simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st allocation_st) s = OK allocated` >>
  `eval_operand (Lit 0w) allocated = SOME 0w` by simp[eval_operand_def] >>
  drule_all abi_decode_store_sequence >> strip_tac >>
  `inst_extends allocation_st en` by metis_tac[inst_extends_emit_void] >>
  `inst_extends st allocation_st` by metis_tac[abi_decode_alloc_buffer_inst_extends] >>
  `run_inst_seq (emitted_insts st en) s = OK (mstore (w2n w) 0w allocated)` by
    (drule_all run_inst_seq_emit_extend >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es (mstore (w2n w) 0w allocated)` by
    (irule literal_mstore_state_rel >>
     reverse conj_tac >- simp[] >>
     qexistsl_tac [`w2n w`, `mk_inst st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString st.cs_next_var)]`, `32`] >>
     conj_tac >- (rpt strip_tac >> qpat_x_assum `!name b len. _` drule >>
       simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
     gvs[mk_inst_def]) >>
  qexistsl_tac [`mstore (w2n w) 0w allocated`, `w2n w`] >>
  gvs[mload_mstore_same, mstore_def, write_memory_with_expansion_def]
QED

(* The second site may already be allocated: neither application assumes a
   fresh site or prunes registers. The first slot's allocation entry survives. *)
Theorem abi_malformed_index_state_two_sites:
  abi_decode_index_init st = (ip,en) /\
  abi_decode_index_init st2 = (ip2,en2) /\
  st.cs_next_id < st2.cs_next_id /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st /\ local_ptrs_reserved cenv st2 /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst st2.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st2.cs_next_var)]) (fn_insts func) ==>
  ?t u p q.
    run_inst_seq (emitted_insts st en) s = OK t /\
    run_inst_seq (emitted_insts st2 en2) t = OK u /\
    stmt_state_rel ctx func cenv cx es t /\
    stmt_state_rel ctx func cenv cx es u /\
    FLOOKUP u.vs_allocas st.cs_next_id = SOME (p,32) /\
    FLOOKUP u.vs_allocas st2.cs_next_id = SOME (q,32) /\
    eval_operand ip2 u = SOME (n2w q) /\ mload q u = 0w
Proof
  strip_tac >>
  qpat_assum `abi_decode_index_init st = _`
    (mp_then Any mp_tac abi_malformed_index_state) >>
  simp[] >> disch_then drule >> simp[] >> strip_tac >>
  qpat_assum `abi_decode_index_init st2 = _`
    (mp_then Any mp_tac abi_malformed_index_state) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexistsl_tac [`t'`, `p`, `p'`] >> simp[]
QED
