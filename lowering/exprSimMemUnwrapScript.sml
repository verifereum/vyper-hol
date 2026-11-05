(* The forced memory judgment from the value one: the memory twin of
   exprSimUnwrap's expr_sim_of_vv_sim, through unwrap_value's code. *)
Theory exprSimMemUnwrap
Ancestors
  exprSimMemDefs exprSimUnwrap exprSimDefs loweringPosts gasOutcome
  exprLowering compileEnv vyperInterpreter vyperState

Theorem expr_sim_mem_of_vv_sim_mem:
  !ctx func cenv cx ty e es.
    expr_vv_sim_mem ctx func cenv cx ty e es /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) /\
    (!sa t op sb. compile_expr cenv ty e sa = (StackValue t op, sb) ==>
                  is_word_type (expr_type e)) ==>
    expr_sim_mem ctx func cenv cx ty e es
Proof
  cheat
QED
