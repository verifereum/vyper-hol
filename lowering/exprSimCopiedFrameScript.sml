(* An index may change the original base, but its old-allocation frame
   protects every byte of the saved array, including its length word. *)
Theory exprSimCopiedFrame
Ancestors
  loweringPosts memoryValueFrame venomState venomInst finite_map words

Theorem copied_array_index_frame:
  expr_post ctx func ce cx idx es sn se b ee iv iop u /\
  FLOOKUP b.vs_allocas aid = SOME (off,sz) /\ aid < sn.cs_next_id /\
  (!name base len. local_region ce es.scopes b name base len ==>
     off + sz <= base \/ base + len <= off) /\
  not_fresh_at sn dst /\ eval_operand (Var dst) b = SOME (n2w off) /\
  off + sz < dimword (:256) /\
  memory_value_rel tv v off b.vs_memory /\ val_wf tv v /\
  type_memory_size tv <= sz ==>
  eval_operand (Var dst) u = SOME (n2w off) /\
  memory_value_rel tv v off u.vs_memory /\
  FLOOKUP u.vs_allocas aid = SOME (off,sz)
Proof
  strip_tac >>
  `mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz b.vs_memory` by
    (fs[expr_post_def] >> metis_tac[]) >>
  `memory_value_rel tv v off u.vs_memory` by
    (irule memory_value_rel_mem_agree_region >> simp[] >>
     qexistsl [`sz`, `b.vs_memory`] >> simp[]) >>
  fs[expr_post_def, eval_operand_def] >> metis_tac[]
QED
