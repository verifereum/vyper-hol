Theory immutableCopyExterior
Ancestors
  immutableCopyExecution venomMemProps venomState venomExecSemantics
  words arithmetic valueEncodingProps

(* Both immutable read modes write to the same destination range. *)
Theorem immutable_copy_word_exterior:
  w2n b + off + 32 < dimword (:256) /\
  (at + len <= w2n b + off \/ w2n b + off + 32 <= at) ==>
  mem_bytes_at at len (immutable_word_transfer F ctor a b off s).vs_memory =
  mem_bytes_at at len s.vs_memory
Proof
  strip_tac >>
  `w2n (b + n2w off) = w2n b + off` by
    (Cases_on `b` >> fs[word_add_n2w]) >>
  simp[immutable_word_transfer_def, mstore_mem_bytes_at_disjoint]
QED

Theorem immutable_copy_transfers_exterior:
  !n off s.
    w2n b + off + 32*n < dimword (:256) ==>
    !at len. at + len <= w2n b + off \/ w2n b + off + 32*n <= at ==>
    mem_bytes_at at len (immutable_transfers F ctor a b n off s).vs_memory =
    mem_bytes_at at len s.vs_memory
Proof
  Induct >- simp[immutable_transfers_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  simp[Once immutable_transfers_def] >>
  `w2n b + (off + 32) + 32*n < dimword (:256) /\
   (at + len <= w2n b + (off + 32) \/ w2n b + (off + 32) + 32*n <= at)` by
    (fs[MULT_SUC] >> decide_tac) >>
  irule immutable_copy_word_exterior >> fs[MULT_SUC] >> decide_tac
QED
