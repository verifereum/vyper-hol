(* Operand boundaries for the memory-counted EC arithmetic case. *)
Theory bodyMemEcArithOperands
Ancestors
  exprSimMemDefs exprSimProps compileEnv

Theorem ec_point_read_capacity:
  expr_store_bound cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v p t /\
  eval_operand p t = SOME w /\ eval_operand p u = SOME w /\
  t.vs_alloca_next <= u.vs_alloca_next ==>
  w2n w + 64 <= u.vs_alloca_next
Proof
  Cases_on `v` >>
  simp[expr_store_bound_def, vyperValueTheory.evaluate_type_def,
       is_word_type_def, val_store_size_def, valueEncodingTheory.type_memory_size_def,
       vyperValueTheory.type_slot_size_def, wordsTheory.dimword_def] >>
  rpt strip_tac >> first_x_assum (qspec_then `w` mp_tac) >> simp[]
QED
