(* A checked obstruction to the frozen bop_ptr_val_ok_frame interface.
   This is not a counterexample to bop_expr_ptr_ok. *)
Theory bodyPtrBopFrameCounterexample
Ancestors bodyPtrDefs compileEnv ptrDiscipline finite_map

Theorem bop_frame_word_counterexample:
  !cx v s tv.
  (ptr_val_ok cx (BaseT BoolT) v (Var "x") FEMPTY entry_taint s /\
   eval_operand (Var "x") s = eval_operand (Var "x") s /\
   op_taint entry_taint (Var "x") = op_taint entry_taint (Var "x") /\
   (~is_word_type (BaseT BoolT) ==>
     evaluate_type (get_tenv cx) (BaseT BoolT) = SOME tv /\ val_wf tv v /\
     (!x. Var "x" = Var x ==>
       FLOOKUP (FEMPTY |+ ("x",(0,32))) x = FLOOKUP FEMPTY x) /\
     (!w. eval_operand (Var "x") s = SOME w ==>
       mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory =
         mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
       (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\
         i IN entry_taint.t_mem ==> i IN entry_taint.t_mem)))) /\
  ~ptr_val_ok cx (BaseT BoolT) v (Var "x")
     (FEMPTY |+ ("x",(0,32))) entry_taint s
Proof
  simp[ptr_val_ok_def, is_word_type_def, op_prov_def,
       op_taint_def, entry_taint_def, FLOOKUP_UPDATE]
QED
