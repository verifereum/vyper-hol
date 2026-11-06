Theory placeMemoryCopyFrames
Ancestors
  valueEncodingProps valueEncoding compileEnv venomState

(* A byte frame preserves any represented value separated from the write,
   including zero-length regions. No type-specific variants are needed. *)
Theorem val_in_memory_outside_write:
  !tv v p m d n m'.
  val_in_memory tv v p m /\ val_wf tv v /\
  (p + type_memory_size tv <= d \/ d + n <= p) /\
  (!a len. a + len <= d \/ d + n <= a ==>
           mem_bytes_at a len m' = mem_bytes_at a len m) ==>
  val_in_memory tv v p m'
Proof
  rpt strip_tac >> irule val_in_memory_mem_agree >>
  simp[] >> qexistsl_tac [`type_memory_size tv`, `m`] >> simp[] >>
  metis_tac[]
QED

Theorem contained_interval_separated:
  !b p sz total d n.
  b <= p /\ p + sz <= b + total /\
  (b + total <= d \/ d + n <= b) ==>
  p + sz <= d \/ d + n <= p
Proof
  rpt strip_tac >> decide_tac
QED
