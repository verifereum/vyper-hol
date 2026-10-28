(* TOP-LEVEL: the dynamic-array live copy preserves typed values outside
   the declared destination capacity, including empty and zero-size cases. *)
Theory dynCopyFrame
Ancestors
  dynCopyMemory dynCopyExec memoryValueDefs valueEncoding
  venomState list words arithmetic

Theorem dyn_copy_result_preserves_capacity:
  !tv v offset var_base elem_size dst_addr src_addr n capacity ss.
    w2n (dst_addr:bytes32) + 32 < dimword(:256) /\
    w2n (src_addr:bytes32) + 32 < dimword(:256) /\ n * elem_size < dimword(:256) /\
    n <= capacity /\ memory_value_rel tv v offset ss.vs_memory /\ val_wf tv v /\
    (offset + type_memory_size tv <= w2n dst_addr \/
      w2n dst_addr + 32 + capacity * elem_size <= offset) ==>
    memory_value_rel tv v offset (dyn_copy_result var_base elem_size dst_addr src_addr n ss).vs_memory
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `n * elem_size <= capacity * elem_size` by simp[LE_MULT_RCANCEL] >>
  mp_tac (Q.SPECL [`var_base`, `elem_size`, `dst_addr`, `src_addr`, `n`, `ss`]
    dyn_copy_result_natural_memory) >> impl_tac >- simp[] >> DISCH_TAC >>
  asm_rewrite_tac [] >>
  mp_tac (Q.SPECL [`tv`, `v`, `offset`, `w2n (dst_addr:bytes32)`, `w2n (src_addr:bytes32)`,
    `n`, `elem_size`, `ss`] dyn_copy_memory_preserves_value) >>
  impl_tac >- (simp[] >> decide_tac) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic-array copy frame theorem: " ^ name)
  end) (DB.thms "dynCopyFrame")
