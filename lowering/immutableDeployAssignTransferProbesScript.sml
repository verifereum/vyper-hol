(* Bounded probes of sequential immutable-store copying. *)
Theory immutableDeployAssignTransferProbes
Ancestors
  immutableCopyExecution valueEncoding venomState list

(* Padding can be corrupted by a forward overlapping copy even though
   the meaningful prefix is preserved.  This is NOT a counterexample
   to immutable assignment; it tests the snapshot proof interface. *)
Theorem immutable_padding_overlap_probe:
  let s0 = s with vs_memory :=
    ([1w] ++ REPLICATE 31 0w ++ [2w] ++ REPLICATE 63 0w) in
  let t = immutable_transfers T T 0w 32w 2 0 s0 in
    mem_bytes_at 32 1 t.vs_memory = [1w] /\
    mem_bytes_at 64 1 t.vs_memory = [1w] /\
    mem_bytes_at 32 1 s0.vs_memory = [2w]
Proof
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.WORD_EVAL_CONV) >> EVAL_TAC
QED
