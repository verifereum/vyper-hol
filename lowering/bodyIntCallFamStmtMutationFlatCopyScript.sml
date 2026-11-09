(* Allocation-preserving counted flat-copy boundary. *)
Theory bodyIntCallFamStmtMutationFlatCopy
Ancestors
  placeMemoryTypedPrimitive placeMemoryCopyEffect

Theorem intcall_flat_copy_effect:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  n < dimword (:256) /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. typed_copy_effect ctx func sa sb s t (w2n dw) n /\
      mem_bytes_at (w2n dw) n t.vs_memory =
        mem_bytes_at (w2n sw) n s.vs_memory
Proof
  strip_tac >> drule_all compile_copy_memory_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[typed_copy_effect_def] >> gvs[]
QED
