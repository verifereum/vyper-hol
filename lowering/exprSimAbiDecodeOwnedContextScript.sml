(* Ownership is independent of the source/execution context. *)
Theory exprSimAbiDecodeOwnedContext
Ancestors
  exprSimAbiDecodeMemberExecute exprSimAbiDecodeSiteOwnership
  exprSimAbiDecodeScratchCover exprSimAbiDecodeSiteProvenance
  abiDecoderSiteEffect finite_map pred_set arithmetic

Definition abi_decode_owned_def:
  abi_decode_owned sites scratch d n s <=>
    abi_decode_scratch_cover sites scratch s /\ d+n <= s.vs_alloca_next /\
    (!a. d <= a /\ a < d+n ==> a NOTIN scratch)
End

Definition abi_decode_owned_child_contract_def:
  abi_decode_owned_child_contract ce env ty tv <=>
    !ctx func fn limit_st next scratch sites st last dst src base_op hi B bs pos d s.
    compile_abi_decode_to_buf dst src MLOAD base_op hi
      (type_to_abi_dec_info ce.ce_struct_fields ce ty) st = ((),last) /\
    abi_decode_code_context func fn st last /\
    last.cs_next_var <= limit_st.cs_next_var /\
    abi_decode_sites st.cs_next_id last.cs_next_id SUBSET sites /\
    abi_decode_owned sites scratch d (type_memory_bytes ce ty) s /\
    abi_decode_context_pre ctx func ce env ty tv limit_st next
      (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce ty}) sites
      st dst src base_op hi B bs pos d s ==>
    abi_decode_context_result ctx func fn tv limit_st next
      (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce ty})
      (abi_decode_sites st.cs_next_id last.cs_next_id) last
      (abi_decode_source_view (vyper_to_abi_type env ty) bs pos) env ty d s
End

Theorem abi_decode_owned_slice:
  abi_decode_owned sites scratch d n s /\ off+len <= n ==>
  abi_decode_owned sites scratch (d+off) len s
Proof
  simp_tac bool_ss [abi_decode_owned_def] >> strip_tac >>
  drule_all abi_decode_output_slice_scratch >> simp[]
QED

Theorem abi_decode_owned_sites_subset:
  abi_decode_owned sites scratch d n s /\ child SUBSET sites ==>
  abi_decode_owned child scratch d n s
Proof
  simp[abi_decode_owned_def, abi_decode_scratch_cover_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem abi_decode_owned_transport:
  abi_decode_owned sites scratch d n s /\ abi_decode_alloc_progress sites s t ==>
  abi_decode_owned sites scratch d n t
Proof
  simp_tac bool_ss [abi_decode_owned_def] >> strip_tac >> conj_tac
  >- metis_tac[abi_decode_scratch_cover_transport] >>
  fs[abi_decode_alloc_progress_def]
QED

Theorem abi_decode_owned_writes:
  abi_decode_owned sites scratch d n s ==>
  abi_decode_site_writes sites d n s SUBSET
    scratch UNION {a | d <= a /\ a < d+n}
Proof
  simp_tac bool_ss [abi_decode_owned_def] >>
  metis_tac[abi_decode_scratch_cover_writes]
QED

Theorem abi_decode_context_result_widen:
  abi_decode_context_result ctx func fn tv limit_st next writes sites last
    view env ty d s /\ writes SUBSET wider ==>
  abi_decode_context_result ctx func fn tv limit_st next wider sites last
    view env ty d s
Proof
  simp_tac bool_ss [abi_decode_context_result_def] >>
  metis_tac[decode_site_effect_weaken]
QED
