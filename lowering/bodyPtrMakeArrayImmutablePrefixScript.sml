(* Semantic observations of the checked immutable one-word endpoint. *)
Theory bodyPtrMakeArrayImmutablePrefix
Ancestors
  bodyPtrMakeArrayImmutableCompose bodyPtrMakeArrayImmutableStep
  immutableCopyExecution immutableMemoryFrame typedCopyPtr valueEncodingProps
  bodyPtrDefs venomState venomExecSemantics words arithmetic pred_set


Theorem immutable_runtime_word_observations:
  u.vs_memory = (immutable_word_transfer F F a b off s).vs_memory ==>
  mem_agree_outside {i | w2n (b+n2w off) <= i /\ i < w2n (b+n2w off)+32}
    u.vs_memory s.vs_memory /\
  mem_word_at (w2n (b+n2w off)) u.vs_memory =
    immutable_copy_read F (a+n2w off) s
Proof
  simp[immutable_word_transfer_fields, mstore_memory_frame,
       mstore_mem_word_at_same]
QED

Theorem immutable_runtime_clean_prefix_extend:
  tnf.t_mem = tn.t_mem DIFF {i | at+off <= i /\ i < at+off+32} /\
  (!k. k < off ==> at+k NOTIN tn.t_mem) ==>
  (!k. k < off+32 ==> at+k NOTIN tnf.t_mem)
Proof
  rpt strip_tac >> gvs[] >> Cases_on `k < off` >>
  simp[] >> decide_tac
QED

Theorem immutable_runtime_prefix_bytes:
  u.vs_memory = (immutable_word_transfer F F a b off s).vs_memory /\
  w2n (b+n2w off) = w2n b+off ==>
  !k. k < off ==>
    mem_bytes_at (w2n b+k) 1 u.vs_memory =
    mem_bytes_at (w2n b+k) 1 s.vs_memory
Proof
  strip_tac >> drule immutable_runtime_word_observations >>
  simp[mem_agree_outside_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> decide_tac
QED

Theorem immutable_runtime_prefix_predicate:
  u.vs_memory = (immutable_word_transfer F F a b off s).vs_memory /\
  w2n (b+n2w off) = w2n b+off /\
  (!k. k < off ==> P k (mem_bytes_at (w2n b+k) 1 s.vs_memory)) ==>
  (!k. k < off ==> P k (mem_bytes_at (w2n b+k) 1 u.vs_memory))
Proof
  rpt strip_tac >>
  `mem_bytes_at (w2n b+k) 1 u.vs_memory =
   mem_bytes_at (w2n b+k) 1 s.vs_memory` by
    metis_tac[immutable_runtime_prefix_bytes] >>
  asm_rewrite_tac[] >> first_x_assum irule >> simp[]
QED

Theorem immutable_runtime_clean_window:
  tnf.t_mem = tn.t_mem DIFF {i | at <= i /\ i < at+32} ==>
  !i. at <= i /\ i < at+32 ==> i NOTIN tnf.t_mem
Proof
  simp[]
QED
