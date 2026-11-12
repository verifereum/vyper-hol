(* Conditional exterior frames; separation is a caller obligation.
   Old pointer transport is already ptr_covers_old_transport in
   appendStorageGhostPtr, and is reused rather than duplicated here. *)
Theory storageNormalizationFramePtr
Ancestors
  storageCopyCompiledPtr appendStorageGhostPtr exprSimStorageCopy pred_set arithmetic

Theorem storage_copy_exterior_bytes:
  copy_prefix loc a b n s k t /\ (off+len <= b \/ b+32*n <= off) ==>
  mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory
Proof
  strip_tac >> fs[copy_prefix_def] >> metis_tac[]
QED

Theorem storage_copy_exterior_taint:
  M' = (M DIFF {y | b <= y /\ y < b+32*n}) UNION
    {b+32*i+r | i < n /\ r < 32 /\ P i r} /\
  ~(b <= x /\ x < b+32*n) ==>
  (x IN M' <=> x IN M)
Proof
  strip_tac >> gvs[] >>
  `!i r. i < n /\ r < 32 ==> b <= b+32*i+r /\ b+32*i+r < b+32*n` by
    (rpt strip_tac >> decide_tac) >>
  simp[] >> metis_tac[arithmeticTheory.ADD_ASSOC]
QED
