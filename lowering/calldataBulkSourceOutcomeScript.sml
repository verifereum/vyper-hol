(* Exact source decoding and physical execution share one bulk-copy witness. *)
Theory calldataBulkSourceOutcome
Ancestors
  calldataBulkPhysicalOutcome calldataStaticSourceExact calldataBulkSourceExact
  calldataReconstruction calldataSourceCorrespondence vyperCalldata vyperValue
  abiDecoderCoherence abiDecoderReentry abiDecoderContract valueEncoding
  abiEncoder venomExecSemantics venomState compileEnv words arithmetic

Theorem calldata_bulk_source_outcome:
  abi_decoder_coherent ce env sf (ArrayT ety (Dynamic maxn)) tv /\
  type_to_abi_dec_info sf ce (ArrayT ety (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\
  ~dec_info_needs_clamp ei /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ d + type_memory_size tv < dimword (:256) ==>
  ?etv n t.
    tv = ArrayTV etv (Dynamic maxn) /\
    abi_decoder_coherent ce env sf ety etv /\
    ~tv_abi_dynamic etv /\ ~tv_needs_clamp etv /\
    mem_sz = type_memory_size etv /\
    type_memory_size tv = 32+maxn*mem_sz /\
    n = w2n (abi_decode_load CALLDATALOAD p s) /\
    (if n <= maxn then
       ?v. cd_decode F s.vs_call_ctx.cc_calldata tv (w2n p) = SOME v /\
       value_has_type tv v /\ val_wf tv v /\ val_in_memory tv v d t.vs_memory /\
       32+n*mem_sz <= type_memory_size tv /\
       d+32 < dimword (:256) /\ n*mem_sz < dimword (:256) /\
       run_inst_seq (emitted_insts st st') s = OK t /\
       mem_word_at d t.vs_memory = n2w n /\
       mem_bytes_at (d+32) (n*mem_sz) t.vs_memory =
         mem_bytes_at (w2n (p+32w)) (n*mem_sz) s.vs_call_ctx.cc_calldata /\
       abi_decode_frame d (32+n*mem_sz) s t /\
       (!op. abi_decoder_operand_live st.cs_next_var op ==>
          eval_operand op t = eval_operand op s) /\
       t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
     else
       cd_decode F s.vs_call_ctx.cc_calldata tv (w2n p) = NONE /\
       maxn < n /\
       run_inst_seq (emitted_insts st st') s = Abort Revert_abort t /\
       (!op. abi_decoder_operand_live st.cs_next_var op ==>
          eval_operand op t = eval_operand op s) /\
       t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
       t.vs_data_section = s.vs_data_section /\
       t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next)
Proof
  strip_tac >> drule_all calldata_bulk_physical_outcome >> strip_tac >>
  qexistsl_tac [`etv`, `n`, `t`] >> simp[] >>
  Cases_on `n <= maxn` >> gvs[]
  >- (`?vs. cd_decode_elems T s.vs_call_ctx.cc_calldata etv (w2n (p+32w)) 0
          (w2n (abi_decode_load CALLDATALOAD p s)) = SOME vs /\
        LENGTH vs = w2n (abi_decode_load CALLDATALOAD p s) /\
        EVERY (value_has_type etv) vs /\
        elems_in_memory vs (d+32) etv t.vs_memory` by
        (irule calldata_static_elems_source_exact >>
         simp[MULT_COMM] >> metis_tac[]) >>
      qexists_tac `ArrayV (DynArrayV vs)` >> conj_tac
      >- simp[calldata_bulk_source_decode, GSYM calldata_decode_load_word] >>
      irule (REWRITE_RULE [make_array_value_def] calldata_dynamic_values_typed_memory) >>
      simp[]) >>
  simp[calldata_bulk_source_decode, GSYM calldata_decode_load_word]
QED
