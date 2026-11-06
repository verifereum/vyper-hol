(* Boundary probes for pointer-safe unwrap. *)
Theory exprPtrUnwrapFacts
Ancestors
  bodyPtrDefs representationCleanPtr

Theorem ptr_mem_ok_prim_clean:
  ptr_mem_ok cx t v op G tn s /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand op s = SOME w /\
  ((?b. v = BoolV b) \/ (?n. v = IntV n) \/
   (?k. v = FlagV k) \/ (?n. v = DecimalV n)) ==>
  !i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem
Proof
  rw[ptr_mem_ok_def] >>
  irule robust_val_in_memory_prim_clean >>
  metis_tac[]
QED
