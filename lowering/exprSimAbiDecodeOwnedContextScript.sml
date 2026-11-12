(* Ownership is independent of the source/execution context. *)
Theory exprSimAbiDecodeOwnedContext
Ancestors
  exprSimAbiDecodeMemberExecute exprSimAbiDecodeSiteOwnership
  exprSimAbiDecodeScratchCover exprSimAbiDecodeSiteProvenance
  abiDecoderSiteEffect abiBuiltinDecodeSetup finite_map pred_set arithmetic

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

(* Caller audit: after setup, the registered output owns its entire region.
   No allocation-site resources are required for the executing observer. *)
Theorem abi_decode_registered_output_owned:
  alloca_inv s /\ FLOOKUP s.vs_allocas output = SOME(d,n) /\
  output NOTIN sites ==>
  abi_decode_owned sites
    ({a | s.vs_alloca_next <= a} UNION
     {a | ?id b sz. id IN sites /\
       FLOOKUP s.vs_allocas id = SOME(b,sz) /\ b <= a /\ a < b+sz}) d n s
Proof
  strip_tac >> drule_all abi_decode_registered_output_scratch >>
  simp[abi_decode_owned_def]
QED

Theorem abi_decode_setup_source_sites:
  abi_builtin_allocation_frame next output outsz s t /\ output NOTIN sites /\
  B+cnt <= s.vs_alloca_next /\
  (!id b sz. id IN sites /\ FLOOKUP s.vs_allocas id = SOME(b,sz) ==>
    abi_footprint_disjoint B cnt [(b,sz)]) ==>
  (!id b sz. id IN sites /\ FLOOKUP t.vs_allocas id = SOME(b,sz) ==>
    abi_footprint_disjoint B cnt [(b,sz)]) /\
  (!a. B <= a /\ a < B+cnt ==>
    a NOTIN ({a | t.vs_alloca_next <= a} UNION
      {a | ?id b sz. id IN sites /\
        FLOOKUP t.vs_allocas id = SOME(b,sz) /\ b <= a /\ a < b+sz}))
Proof
  strip_tac >>
  `!id. id IN sites ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id` by
    metis_tac[abiBuiltinAllocationTheory.abi_builtin_allocation_frame_outside] >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (fs[abiBuiltinAllocationTheory.abi_builtin_allocation_frame_def,
        abiBuiltinAllocationTheory.abi_builtin_allocate_state_def] >>
     Cases_on `FLOOKUP s.vs_allocas output = NONE` >> gvs[]) >>
  conj_asm1_tac >- metis_tac[] >>
  fs[abiDecoderFrameTheory.abi_footprint_disjoint_def] >>
  simp[] >> rpt strip_tac >> metis_tac[LESS_LESS_EQ_TRANS, NOT_LESS_EQUAL]
QED

Theorem abi_decode_setup_output_owned:
  abi_builtin_allocation_frame next output outsz s t /\ alloca_inv s /\
  ((FLOOKUP s.vs_allocas output = NONE /\ d = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas output = SOME(d,outsz)) /\ output NOTIN sites ==>
  abi_decode_owned sites
    ({a | t.vs_alloca_next <= a} UNION
     {a | ?id b sz. id IN sites /\
       FLOOKUP t.vs_allocas id = SOME(b,sz) /\ b <= a /\ a < b+sz}) d outsz t
Proof
  strip_tac >> irule abi_decode_registered_output_owned >>
  metis_tac[abi_decode_setup_alloca_inv, abi_decode_setup_output_registered]
QED

Theorem abi_decode_setup_output_excluded:
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) ==>
  abi_builtin_decode_output_site st min_size max_size NOTIN
    abi_decode_sites ready.cs_next_id last
Proof
  strip_tac >> drule abi_builtin_decode_setup_shape >>
  simp[abi_decode_sites_def]
QED
