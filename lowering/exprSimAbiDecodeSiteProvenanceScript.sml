(* Allocation provenance is separate from the decoder memory frame. *)
Theory exprSimAbiDecodeSiteProvenance
Ancestors
  venomState finite_map pred_set arithmetic

Definition abi_decode_sites_def:
  abi_decode_sites lo hi = {id:num | lo <= id /\ id < hi}
End

Definition abi_decode_alloc_progress_def:
  abi_decode_alloc_progress sites s t <=>
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    (!id. id NOTIN sites ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!id b sz. FLOOKUP s.vs_allocas id = NONE /\
      FLOOKUP t.vs_allocas id = SOME(b,sz) ==>
      s.vs_alloca_next <= b /\ b+sz <= t.vs_alloca_next)
End

Definition abi_decode_site_writes_def:
  abi_decode_site_writes sites d outsz s =
    {a | d <= a /\ a < d+outsz} UNION
    {a | s.vs_alloca_next <= a} UNION
    {a | ?id b sz. id IN sites /\
      FLOOKUP s.vs_allocas id = SOME(b,sz) /\ b <= a /\ a < b+sz}
End

Theorem abi_decode_alloc_progress_refl:
  abi_decode_alloc_progress sites s s
Proof
  simp[abi_decode_alloc_progress_def] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem abi_decode_alloc_progress_trans:
  abi_decode_alloc_progress sites s t /\
  abi_decode_alloc_progress sites t u ==>
  abi_decode_alloc_progress sites s u
Proof
  simp_tac bool_ss [abi_decode_alloc_progress_def] >> strip_tac >>
  conj_tac >- decide_tac >>
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP t.vs_allocas id`
  >- metis_tac[LESS_EQ_TRANS] >>
  PairCases_on `x` >>
  `FLOOKUP u.vs_allocas id = SOME(x0,x1)` by metis_tac[] >>
  gvs[] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem abi_decode_alloc_progress_widen:
  abi_decode_alloc_progress A s t /\ A SUBSET B ==>
  abi_decode_alloc_progress B s t
Proof
  simp[abi_decode_alloc_progress_def, SUBSET_DEF] >> metis_tac[]
QED
