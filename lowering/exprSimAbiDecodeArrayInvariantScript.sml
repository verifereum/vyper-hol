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
