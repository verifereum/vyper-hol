Theory exprSimAbiDecodeArrayInvariant
Ancestors
  exprSimAbiDecodeArrayMembers exprSimAbiDecodeTupleAssembly
  exprSimAbiDecodeOwnedMember exprSimAbiDecodeOwnedContext
  exprSimAbiDecodeSiteOwnership exprSimAbiDecodeScratchCover
  exprSimAbiDecodeChildFrame abiDecoderLoopData abiDecoderSiteEffect
  valueEncodingProps valueEncoding finite_map pred_set list rich_list arithmetic

Definition abi_array_source_prefix_def:
  abi_array_source_prefix env ty bs p j vs <=>
    LENGTH vs = j /\
    (!k. k < j ==> abi_decode_source_accepts env ty
      (abi_array_member_view (vyper_to_abi_type env ty) bs p k) (EL k vs))
End

Definition abi_array_memory_prefix_def:
  abi_array_memory_prefix tv d m j vs s <=>
    LENGTH vs = j /\
    (!k. k < j ==> val_wf tv (EL k vs) /\
      val_in_memory tv (EL k vs) (d+32+k*m) s.vs_memory)
End

Definition abi_array_cell_def:
  abi_array_cell d m j = {a | d+32+j*m <= a /\ a < d+32+(j+1)*m}
End

Theorem abi_array_prefix_zero[simp]:
  abi_array_source_prefix env ty bs p 0 [] /\
  abi_array_memory_prefix tv d m 0 [] s
Proof
  simp[abi_array_source_prefix_def, abi_array_memory_prefix_def]
QED

Theorem abi_array_source_prefix_append:
  abi_array_source_prefix env ty bs p j vs /\
  abi_decode_source_accepts env ty
    (abi_array_member_view (vyper_to_abi_type env ty) bs p j) v ==>
  abi_array_source_prefix env ty bs p (SUC j) (vs ++ [v])
Proof
  simp_tac bool_ss [abi_array_source_prefix_def] >> strip_tac >>
  conj_tac >- simp[] >> gen_tac >> strip_tac >>
  Cases_on `k < j`
  >- (asm_simp_tac (srw_ss()) [EL_APPEND1] >> metis_tac[]) >>
  `k = j` by decide_tac >> gvs[EL_APPEND2]
QED

Theorem abi_array_memory_prefix_append_frame:
  abi_array_memory_prefix tv d m j vs s /\ m = type_memory_size tv /\
  decode_site_effect ctx func next V s t /\
  (!k. k < j ==> decode_protects V {(d+32+k*m,m)}) /\
  val_wf tv v /\ val_in_memory tv v (d+32+j*m) t.vs_memory ==>
  abi_array_memory_prefix tv d m (SUC j) (vs ++ [v]) t
Proof
  simp_tac bool_ss [abi_array_memory_prefix_def] >> strip_tac >>
  conj_tac >- simp[] >> gen_tac >> strip_tac >>
  Cases_on `k < j`
  >- (asm_simp_tac (srw_ss()) [EL_APPEND1] >>
      irule abi_decode_child_completed_value >> metis_tac[]) >>
  `k = j` by decide_tac >> gvs[EL_APPEND2]
QED

Theorem abi_array_child_writes_protect_prefix:
  (!a. d <= a /\ a < d+32+n*m ==> a NOTIN scratch) /\ j < n ==>
  !k. k < j ==>
    decode_protects (scratch UNION abi_array_cell d m j) {(d+32+k*m,m)}
Proof
  simp[decode_protects_def, abi_array_cell_def] >> rpt strip_tac >>
  `k*m+m <= j*m /\ j*m <= n*m` by
    (`k*m+m = SUC k*m` by simp[MULT_CLAUSES, ADD_COMM] >>
     asm_rewrite_tac [] >> simp[LE_MULT_RCANCEL] >> decide_tac) >>
  qpat_x_assum `!a. _` (qspec_then `a` mp_tac) >>
  simp[MULT_COMM] >> decide_tac
QED

(* Canonical child-only scratch, fixed at the invariant's origin. *)
Definition abi_array_child_scratch_def:
  abi_array_child_scratch sites origin =
    {a | origin.vs_alloca_next <= a} UNION
    {a | ?id b sz. id IN sites /\
      FLOOKUP origin.vs_allocas id = SOME(b,sz) /\ b <= a /\ a < b+sz}
End

Theorem abi_array_child_scratch_cover:
  abi_decode_scratch_cover sites (abi_array_child_scratch sites origin) origin
Proof
  simp[abi_decode_scratch_cover_def, abi_array_child_scratch_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem abi_array_child_scratch_subset:
  abi_decode_scratch_cover outer scratch origin /\ sites SUBSET outer ==>
  abi_array_child_scratch sites origin SUBSET scratch
Proof
  simp[abi_decode_scratch_cover_def, abi_array_child_scratch_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem abi_array_child_scratch_slot:
  alloca_inv origin /\ FLOOKUP origin.vs_allocas idx = SOME(slot,32) /\
  idx NOTIN sites ==>
  decode_protects (abi_array_child_scratch sites origin) {(slot,32)}
Proof
  strip_tac >> drule_all abi_decode_registered_output_scratch >>
  simp[decode_protects_def, abi_array_child_scratch_def]
QED

Theorem abi_array_child_writes_protect_slot:
  alloca_inv origin /\ FLOOKUP origin.vs_allocas idx = SOME(slot,32) /\
  idx NOTIN sites /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN abi_array_cell d m j) ==>
  decode_protects (abi_array_child_scratch sites origin UNION abi_array_cell d m j)
    {(slot,32)}
Proof
  strip_tac >> irule decode_protects_union >> conj_tac
  >- metis_tac[abi_array_child_scratch_slot] >>
  simp[decode_protects_def]
QED

Theorem abi_array_child_owned:
  abi_decode_owned outer scratch d (32+n*m) origin /\ sites SUBSET outer /\
  abi_decode_alloc_progress sites origin s /\ j < n ==>
  abi_decode_owned sites (abi_array_child_scratch sites origin) (d+32+j*m) m s
Proof
  strip_tac >>
  `abi_array_child_scratch sites origin SUBSET scratch` by
    metis_tac[abi_array_child_scratch_subset, abi_decode_owned_def] >>
  `abi_decode_owned sites (abi_array_child_scratch sites origin) d (32+n*m) origin` by
    (simp[abi_decode_owned_def, abi_array_child_scratch_cover] >>
     fs[abi_decode_owned_def, SUBSET_DEF] >> metis_tac[]) >>
  `abi_decode_owned sites (abi_array_child_scratch sites origin) d (32+n*m) s` by
    metis_tac[abi_decode_owned_transport] >>
  simp_tac bool_ss [GSYM ADD_ASSOC] >>
  irule abi_decode_owned_slice >> qexists_tac `32+n*m` >> asm_rewrite_tac[] >>
  `j*m+m <= n*m` by
    (`j*m+m = SUC j*m` by simp[MULT_CLAUSES, ADD_COMM] >>
     asm_rewrite_tac [] >> simp[LE_MULT_RCANCEL] >> decide_tac) >>
  decide_tac
QED

(* Persistent facts before the runtime-indexed setup.  In particular there is
   no assumption about the next offset word or about its successful check. *)
Definition abi_array_runtime_context_def:
  abi_array_runtime_context ctx func ce env ty tv limit_st first
    scratch sites st dst src base_op hi B bs p d n s <=>
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    assignable_type env ty /\ abi_decode_bytes_widths env ty /\
    first <= st.cs_next_var /\ st.cs_next_var <= limit_st.cs_next_var /\
    EVERY (abi_decoder_operand_live st.cs_next_var) [dst;src;base_op;hi] /\
    base_op <> Lit 0w /\ hi <> Lit 0w /\
    eval_operand dst s = SOME(n2w d) /\
    eval_operand src s = SOME(n2w p) /\
    eval_operand base_op s = SOME(n2w B) /\
    eval_operand hi s = SOME(n2w(LENGTH bs)) /\
    p+32 <= LENGTH bs /\ B+LENGTH bs < dimword(:256) /\
    d+32+n*type_memory_bytes ce ty < dimword(:256) /\
    bs = mem_bytes_at B (LENGTH bs) s.vs_memory /\
    B+LENGTH bs <= s.vs_alloca_next /\
    (!a. B <= a /\ a < B+LENGTH bs ==> a NOTIN
      (scratch UNION {a | d <= a /\ a < d+32+n*type_memory_bytes ce ty})) /\
    (!id b sz. id IN sites /\ FLOOKUP s.vs_allocas id = SOME(b,sz) ==>
      abi_footprint_disjoint B (LENGTH bs) [(b,sz)]) /\
    decode_site_resources ctx func s /\ fn_inst_ids_distinct func /\
    fresh_vars_wrt limit_st s
End

(* The two counters are deliberately separate: after a child returns the
   prefix has length SUC j, while the registered index slot still holds j. *)
Definition abi_array_loop_data_def:
  abi_array_loop_data ctx func first writes origin outer scratch sites
    idx slot ip src base_op B p n j env ty tv bs d m k vs s <=>
    Ldata ctx func first writes origin idx slot ip src MLOAD base_op B p n j s /\
    alloca_inv origin /\ FLOOKUP origin.vs_allocas idx = SOME(slot,32) /\
    idx NOTIN sites /\ sites SUBSET outer /\
    abi_decode_owned outer scratch d (32+n*m) origin /\
    abi_decode_alloc_progress sites origin s /\
    (!a. slot <= a /\ a < slot+32 ==> a NOTIN {a | d <= a /\ a < d+32+n*m}) /\
    m = type_memory_size tv /\
    abi_array_source_prefix env ty bs p k vs /\
    abi_array_memory_prefix tv d m k vs s
End

Definition abi_array_ready_def:
  abi_array_ready ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s <=>
    abi_array_runtime_context ctx func ce env ty tv limit_st first
      scratch sites st dst src base_op hi B bs p d n s /\
    abi_array_loop_data ctx func first writes origin outer scratch sites
      idx slot ip src base_op B p n j env ty tv bs d
      (type_memory_bytes ce ty) j vs s /\
    abi_decoder_operand_live st.cs_next_var ip /\ abi_decode_entry st s
End

Definition abi_array_body_post_def:
  abi_array_body_post ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s <=>
    abi_array_runtime_context ctx func ce env ty tv limit_st first
      scratch sites st dst src base_op hi B bs p d n s /\
    abi_array_loop_data ctx func first writes origin outer scratch sites
      idx slot ip src base_op B p n j env ty tv bs d
      (type_memory_bytes ce ty) (SUC j) vs s /\
    abi_decoder_operand_live st.cs_next_var ip /\ abi_decode_entry st s
End

Theorem abi_array_loop_data_child_owned:
  abi_array_loop_data ctx func first writes origin outer scratch sites
    idx slot ip src base_op B p n j env ty tv bs d m k vs s /\ j < n ==>
  abi_decode_owned sites (abi_array_child_scratch sites origin) (d+32+j*m) m s
Proof
  simp_tac bool_ss [abi_array_loop_data_def] >>
  metis_tac[abi_array_child_owned]
QED

Theorem abi_array_loop_data_protect_prefix:
  abi_array_loop_data ctx func first writes origin outer scratch sites
    idx slot ip src base_op B p n j env ty tv bs d m k vs s /\ j < n ==>
  !i. i < j ==> decode_protects
    (abi_array_child_scratch sites origin UNION abi_array_cell d m j)
    {(d+32+i*m,m)}
Proof
  strip_tac >> gen_tac >> strip_tac >>
  irule abi_array_child_writes_protect_prefix >>
  fs[abi_array_loop_data_def] >>
  `abi_array_child_scratch sites origin SUBSET scratch` by
    metis_tac[abi_array_child_scratch_subset, abi_decode_owned_def] >>
  fs[abi_decode_owned_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem abi_array_loop_data_protect_slot:
  abi_array_loop_data ctx func first writes origin outer scratch sites
    idx slot ip src base_op B p n j env ty tv bs d m k vs s /\ j < n ==>
  decode_protects
    (abi_array_child_scratch sites origin UNION abi_array_cell d m j) {(slot,32)}
Proof
  simp_tac bool_ss [abi_array_loop_data_def] >> strip_tac >>
  `!a. slot <= a /\ a < slot+32 ==> a NOTIN abi_array_cell d m j` by
    (`j*m+m <= n*m` by
       (`j*m+m = SUC j*m` by simp[MULT_CLAUSES, ADD_COMM] >>
        asm_rewrite_tac [] >> simp[LE_MULT_RCANCEL] >> decide_tac) >>
     simp_tac (srw_ss()) [abi_array_cell_def] >> rpt strip_tac >>
     qpat_x_assum `!a. _` (qspec_then `a` mp_tac) >>
     gvs[LEFT_ADD_DISTRIB, MULT_CLAUSES, MULT_COMM] >> decide_tac) >>
  metis_tac[abi_array_child_writes_protect_slot]
QED

Theorem abi_array_ready_runtime_context:
  abi_array_ready ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s ==>
  abi_array_runtime_context ctx func ce env ty tv limit_st first
    scratch sites st dst src base_op hi B bs p d n s
Proof
  simp[abi_array_ready_def]
QED

Theorem abi_array_ready_loop_data:
  abi_array_ready ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s ==>
  abi_array_loop_data ctx func first writes origin outer scratch sites
    idx slot ip src base_op B p n j env ty tv bs d
    (type_memory_bytes ce ty) j vs s
Proof
  simp[abi_array_ready_def]
QED

Theorem abi_array_ready_entry:
  abi_array_ready ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s ==>
  abi_decode_entry st s /\ abi_decoder_operand_live st.cs_next_var ip
Proof
  simp[abi_array_ready_def]
QED

Theorem abi_array_ready_child_owned:
  abi_array_ready ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s /\
  j < n ==>
  abi_decode_owned sites (abi_array_child_scratch sites origin)
    (d+32+j*type_memory_bytes ce ty) (type_memory_bytes ce ty) s
Proof
  metis_tac[abi_array_ready_loop_data, abi_array_loop_data_child_owned]
QED

Theorem abi_array_loop_data_slot:
  abi_array_loop_data ctx func first writes origin outer scratch sites
    idx slot ip src base_op B p n j env ty tv bs d m k vs s ==>
  FLOOKUP s.vs_allocas idx = SOME(slot,32) /\
  eval_operand ip s = SOME(n2w slot) /\ mload slot s = n2w j
Proof
  simp[abi_array_loop_data_def, Ldata_def]
QED

Theorem abi_array_runtime_source:
  abi_array_runtime_context ctx func ce env ty tv limit_st first
    scratch sites st dst src base_op hi B bs p d n s ==>
  bs = mem_bytes_at B (LENGTH bs) s.vs_memory /\
  B+LENGTH bs <= s.vs_alloca_next /\
  (!a. B <= a /\ a < B+LENGTH bs ==> a NOTIN scratch)
Proof
  simp[abi_array_runtime_context_def] >> metis_tac[]
QED

Theorem abi_array_body_post_prefix:
  abi_array_body_post ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s ==>
  abi_array_source_prefix env ty bs p (SUC j) vs /\
  abi_array_memory_prefix tv d (type_memory_bytes ce ty) (SUC j) vs s
Proof
  simp[abi_array_body_post_def, abi_array_loop_data_def]
QED

Theorem abi_array_body_post_slot:
  abi_array_body_post ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s ==>
  mload slot s = n2w j /\ abi_decode_entry st s
Proof
  simp[abi_array_body_post_def, abi_array_loop_data_def, Ldata_def]
QED

(* A child effect may touch its cell and its own scratch, but neither the
   loop slot nor any completed cell.  This probe exercises the packaged
   invariant without assuming that the runtime setup succeeds. *)
Theorem abi_array_loop_data_append_prefix:
  abi_array_loop_data ctx func first writes origin outer scratch sites
    idx slot ip src base_op B p n j env ty tv bs d m j vs s /\ j < n /\
  abi_decode_source_accepts env ty
    (abi_array_member_view (vyper_to_abi_type env ty) bs p j) v /\
  decode_site_effect ctx func child
    (abi_array_child_scratch sites origin UNION abi_array_cell d m j) s t /\
  val_wf tv v /\ val_in_memory tv v (d+32+j*m) t.vs_memory ==>
  abi_array_source_prefix env ty bs p (SUC j) (vs ++ [v]) /\
  abi_array_memory_prefix tv d m (SUC j) (vs ++ [v]) t /\
  mload slot t = n2w j
Proof
  strip_tac >>
  `decode_protects
    (abi_array_child_scratch sites origin UNION abi_array_cell d m j)
    {(slot,32)}` by metis_tac[abi_array_loop_data_protect_slot] >>
  `!i. i < j ==> decode_protects
    (abi_array_child_scratch sites origin UNION abi_array_cell d m j)
    {(d+32+i*m,m)}` by metis_tac[abi_array_loop_data_protect_prefix] >>
  qhdtm_x_assum `abi_array_loop_data` mp_tac >> simp_tac bool_ss [abi_array_loop_data_def] >> strip_tac >> conj_tac
  >- metis_tac[abi_array_source_prefix_append] >> conj_tac
  >- metis_tac[abi_array_memory_prefix_append_frame] >>
  metis_tac[Ldata_def, decode_site_effect_mload]
QED
