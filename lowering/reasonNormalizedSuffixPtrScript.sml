(* Resource audit boundaries between tuple copying and the checked finish.
   Tuple MCOPY frames operands/coverage but not expr_post.  Slot allocation
   still needs the source-state allocation invariant and separation from the
   tuple head before its initializing MSTORE can preserve that head. *)
Theory reasonNormalizedSuffixPtr
Ancestors reasonFinishPtr reasonTupleCopyPtr reasonResourcesPtr
  representationCleanPtr valueEncoding venomMemProps bodyPtrDefs
  exprSimProps words list pred_set

Theorem reason_tuple_copy_string_head:
  ptr_mem_ok cx ty (StringV str) op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand op s = SOME a /\ val_wf tv (StringV str) /\
  val_store_size tv (StringV str) <= n /\
  sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
  tnf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + n}) UNION
    {w2n b + i | i < n /\ w2n a + i IN tn.t_mem} ==>
  (!mem. mem_agree_outside tnf.t_mem sf.vs_memory mem ==>
    val_in_memory tv (StringV str) (w2n b) mem) /\
  (!i. w2n b <= i /\ i < w2n b + 32 ==> i NOTIN tnf.t_mem) /\
  mload (w2n b) sf = n2w (LENGTH str)
Proof
  strip_tac >>
  `!mem. mem_agree_outside tnf.t_mem sf.vs_memory mem ==>
    val_in_memory tv (StringV str) (w2n b) mem` by
    (rpt strip_tac >> irule reason_tuple_copy_resources_ptr >>
     conj_tac >- simp[] >>
     qexistsl [`G`, `a`, `cx`, `n`, `op`, `s`, `sf`, `tn`, `tnf`, `ty`] >> simp[]) >>
  conj_tac >- simp[] >> conj_tac
  >- (drule robust_val_in_memory_string_clean >> simp[]) >>
  `val_in_memory tv (StringV str) (w2n b) sf.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  gvs[val_in_memory_def, venomStateTheory.mload_def, mem_word_at_def]
QED
