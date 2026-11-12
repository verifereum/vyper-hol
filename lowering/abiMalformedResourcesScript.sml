(* Malformed input needs actual allocation room, not credit for every instruction id. *)
Theory abiMalformedResources
Ancestors
  abiDecoderIndexInit abiDecoderArrayHeader abiDecoderContract
  abiBuiltinAllocation exprSimAlloc exprLoweringProps valueEncodingProps
  emitHelperProps emitHelper compileEnv context venomExecSemantics
  venomState venomInst venomMemDefs venomMemProps words finite_map list arithmetic

Theorem abi_malformed_count_product:
  (n:num) <= maxn /\ maxn * stride < dimword (:256) ==>
  n * stride < dimword (:256)
Proof
  strip_tac >>
  `n * stride <= maxn * stride` by simp[] >> decide_tac
QED

Theorem abi_malformed_dynarray_product:
  abi_size_bound sf (ArrayT elem (Dynamic maxn)) < dimword (:256) /\
  n <= maxn ==>
  n * abi_embedded_static_size sf elem < dimword (:256)
Proof
  strip_tac >> irule abi_malformed_count_product >>
  qexists_tac `maxn` >> simp[] >>
  `maxn * abi_embedded_static_size sf elem <=
   maxn * (abi_embedded_static_size sf elem +
     (if is_abi_dynamic sf elem then abi_size_bound sf elem else 0))` by simp[] >>
  gvs[Once abi_size_bound_def] >> decide_tac
QED

(* Both first entry and ALLOCA-site reuse: a source allocation with an older
   id survives allocation and initialization of the real loop index slot. *)
Theorem abi_malformed_index_source_window:
  abi_decode_index_init st = (ip,en) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  live < st.cs_next_id /\ FLOOKUP s.vs_allocas live = SOME (B,cap) /\
  L <= cap ==>
  ?t p. run_inst_seq (emitted_insts st en) s = OK t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    p + 32 < dimword (:256) /\ alloca_room ctx func t /\
    FLOOKUP t.vs_allocas live = SOME (B,cap) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
    mem_bytes_at B L t.vs_memory = mem_bytes_at B L s.vs_memory
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
  qexistsl_tac [`mstore (w2n w) 0w allocated`, `w2n w`] >>
  `alloca_room ctx func (mstore (w2n w) 0w allocated)` by
    (irule alloca_room_fields >> qexists_tac `allocated` >>
     fs[stmt_state_rel_def, mstore_def, write_memory_with_expansion_def]) >>
  `B + L <= w2n w \/ w2n w + 32 <= B` by
    (qpat_x_assum `!aid b len. _` drule >>
     disch_then drule >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at B L (mstore (w2n w) 0w allocated).vs_memory =
   mem_bytes_at B L allocated.vs_memory` by
    (irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  gvs[mload_mstore_same, mstore_def, write_memory_with_expansion_def]
QED
