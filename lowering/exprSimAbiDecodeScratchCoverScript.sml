(* Stable permissions for reusable decoder scratch sites. *)
Theory exprSimAbiDecodeScratchCover
Ancestors
  exprSimAbiDecodeSiteProvenance abiDecoderSiteEffect
  finite_map pred_set arithmetic

Definition abi_decode_scratch_cover_def:
  abi_decode_scratch_cover sites scratch s <=>
    {a | s.vs_alloca_next <= a} SUBSET scratch /\
    (!id b sz. id IN sites /\ FLOOKUP s.vs_allocas id = SOME(b,sz) ==>
      {a | b <= a /\ a < b+sz} SUBSET scratch)
End

Theorem abi_decode_scratch_cover_transport:
  abi_decode_scratch_cover sites scratch s /\ abi_decode_alloc_progress sites s t ==>
  abi_decode_scratch_cover sites scratch t
Proof
  simp_tac bool_ss [abi_decode_scratch_cover_def, abi_decode_alloc_progress_def] >>
  strip_tac >> conj_tac
  >- (fs[SUBSET_DEF] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (fs[SUBSET_DEF] >> rpt strip_tac >>
      `s.vs_alloca_next <= b` by metis_tac[] >>
      qpat_x_assum `!x. s.vs_alloca_next <= x ==> _` irule >> decide_tac) >>
  `FLOOKUP t.vs_allocas id = SOME x` by metis_tac[] >> gvs[] >> metis_tac[]
QED

Theorem abi_decode_scratch_cover_writes:
  abi_decode_scratch_cover sites scratch s ==>
  abi_decode_site_writes sites d n s SUBSET
    scratch UNION {a | d <= a /\ a < d+n}
Proof
  simp[abi_decode_scratch_cover_def, abi_decode_site_writes_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem abi_decode_scratch_tail_protects:
  (!a. d <= a /\ a < d+h ==> a NOTIN scratch) ==>
  decode_protects (scratch UNION {a | d+h <= a /\ a < d+h+n}) {(d,h)}
Proof
  simp[decode_protects_def] >> rpt strip_tac >> fs[] >>
  first_x_assum drule >> decide_tac
QED

Theorem abi_decode_scratch_row_source:
  (!a. B <= a /\ a < B+H ==> a NOTIN scratch) /\
  (!a. B <= a /\ a < B+H ==> ~(d <= a /\ a < d+n)) ==>
  !a. B <= a /\ a < B+H ==>
    a NOTIN (scratch UNION {a | d <= a /\ a < d+n})
Proof
  simp[]
QED

(* A cover suitable for framing an output necessarily places the entire
   nonempty output below the allocation frontier. This is a caller obligation,
   not a consequence of source/output separation. *)
Theorem abi_decode_scratch_cover_output_bound:
  abi_decode_scratch_cover sites scratch s /\ 0 < n /\
  (!a. d <= a /\ a < d+n ==> a NOTIN scratch) ==>
  d+n <= s.vs_alloca_next
Proof
  simp_tac bool_ss [abi_decode_scratch_cover_def] >> strip_tac >>
  spose_not_then assume_tac >>
  `s.vs_alloca_next <= d+n-1 /\ d <= d+n-1 /\ d+n-1 < d+n` by decide_tac >>
  fs[SUBSET_DEF] >>
  qpat_x_assum `!a. d <= a /\ a < d+n ==> _`
    (qspec_then `d+n-1` mp_tac) >> simp[]
QED

Theorem abi_decode_scratch_cover_site_separation:
  abi_decode_scratch_cover sites scratch s /\
  (!a. d <= a /\ a < d+n ==> a NOTIN scratch) /\
  id IN sites /\ FLOOKUP s.vs_allocas id = SOME(b,sz) ==>
  !a. d <= a /\ a < d+n ==> ~(b <= a /\ a < b+sz)
Proof
  simp[abi_decode_scratch_cover_def, SUBSET_DEF] >> metis_tac[]
QED
