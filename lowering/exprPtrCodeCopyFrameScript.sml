(* Immutable reads impose no source bound on the destination write frame. *)
Theory exprPtrCodeCopyFrame
Ancestors
  exprPtrCodeCopyPost immutableCopyExecution venomMemProps venomState
  venomExecSemantics words arithmetic valueEncodingProps exprSimCopy

Theorem immutable_word_exterior:
  w2n b + off + 32 < dimword (:256) /\
  (at+len <= w2n b+off \/ w2n b+off+32 <= at) ==>
  mem_bytes_at at len (immutable_word_transfer F F a b off s).vs_memory =
  mem_bytes_at at len s.vs_memory
Proof
  strip_tac >>
  `w2n (b+n2w off) = w2n b+off` by
    (Cases_on `b` >> fs[word_add_n2w]) >>
  simp[immutable_word_transfer_def, mstore_mem_bytes_at_disjoint]
QED

Theorem immutable_transfers_exterior:
  !n off s.
  w2n b + off + 32*n < dimword (:256) ==>
  !at len. at+len <= w2n b+off \/ w2n b+off+32*n <= at ==>
  mem_bytes_at at len (immutable_transfers F F a b n off s).vs_memory =
  mem_bytes_at at len s.vs_memory
Proof
  Induct >- simp[immutable_transfers_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  simp[Once immutable_transfers_def] >>
  `w2n b+(off+32)+32*n < dimword (:256) /\
    (at+len <= w2n b+(off+32) \/ w2n b+(off+32)+32*n <= at)` by
    (fs[MULT_SUC] >> decide_tac) >>
  irule immutable_word_exterior >> fs[MULT_SUC] >> decide_tac
QED

Theorem code_copy_endpoint_exterior:
  compile_imm_copy_to_memory F imm src dst n 0 sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  copy_runtime_frame sa s sb z /\ w2n b+32*n < dimword (:256) ==>
  !at len. at+len <= w2n b \/ w2n b+32*n <= at ==>
  mem_bytes_at at len z.vs_memory = mem_bytes_at at len s.vs_memory
Proof
  strip_tac >> drule_all code_copy_same_endpoint_memory >> strip_tac >>
  rpt gen_tac >> strip_tac >> asm_rewrite_tac[] >>
  irule immutable_transfers_exterior >> simp[]
QED
