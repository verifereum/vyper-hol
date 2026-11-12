(*
 * Construct-free facts the joint (full) expression leaves share.
 *
 * TOP-LEVEL:
 *   expr_vv_sim_stack_full -- an expression that compiles to a stack value
 *     and evaluates to a value gets its vv judgment from its value judgment
 *   gas_shadow_compiles_alloc_buffer -- a static buffer allocation compiles
 *     alike on both sides of the shadow
 *)
Theory bodyFullExprGeneric
Ancestors
  bodySimFull gasShadowState gasShadow context exprLowering compileEnv
  vyperInterpreter vyperState

(* The full twin of exprStackPtr's expr_vv_sim_stack_ptr.  As in the memory
   twin (exprSimMemoryStack's body_expr_vv_sim_mem_stack), a non-word stack
   value's lowered type must take no memory: expr_sim_full bounds only the
   value's footprint, and vv_store_bound also wants the whole lowered
   type's region below the frontier. *)
Theorem expr_vv_sim_stack_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty e es.
    (~is_word_type (expr_type e) ==>
     !tvt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) =
             SOME tvt ==>
           type_memory_size tvt = 0) /\
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty e es /\
    (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
    (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty e es
Proof
  cheat
QED

Theorem gas_shadow_compiles_alloc_buffer:
  !size. gas_shadow_compiles (compile_alloc_buffer size)
           (compile_alloc_buffer size)
Proof
  simp[compile_alloc_buffer_def] >> gen_tac >>
  irule gas_shadow_compiles_bind >>
  simp[gas_shadow_compiles_emit_op, gas_shadow_compiles_return]
QED
