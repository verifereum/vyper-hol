(* Memory case of the body induction: a ternary with an arm whose value the
   lowering lays out differently from its source type (a widened internal
   call), the memory twin of bodySimIfExpWidened's
   body_ifexp_widened_call_arm.

   HELD, as S1's: describing a widened internal call's value at its lowered
   type needs the posts interface (post_value_type) that this base does not
   have. *)
Theory bodyMemIfExpWidened
Ancestors
  fragGasMemoryLength bodyMemoryPreds bodyIfExpWidenedTyping bodyIfExpTypedMemory typedArrayCopyPathsMem typedFieldCopyPathsMem typedFieldCopyCuts typedFieldCopyAggregateMem

Theorem body_ifexp_widened_call_arm_mem:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_mem_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_mem_ok cx e3) /\
    body_expr_mem_ok cx e1 ==>
    !tops ctx func cenv env ty es.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (IfExp v5 e1 e2 e3) es /\
      (?e. (e = e2 \/ e = e3) /\
           ~((int_calls_expr e = [] \/
              same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
             post_value_type cenv e = expr_type e)) ==>
      expr_sim_mem ctx func cenv cx ty (IfExp v5 e1 e2 e3) es /\
      expr_vv_sim_mem ctx func cenv cx ty (IfExp v5 e1 e2 e3) es
Proof
  cheat
QED
