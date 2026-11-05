(* Memory case of the body induction (bodyMemory's body_mem_mutual): for loop;
   fragLoopMemory's frag_exec_loop_mem is the loop step. *)
Theory bodyMemFor
Ancestors
  bodyMemoryPreds

Theorem body_for_mem_case:
  !cx id typ it n body.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_mem_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_mem_ok cx it) ==>
    body_stmt_mem_ok cx (For id typ it n body)
Proof
  cheat
QED
