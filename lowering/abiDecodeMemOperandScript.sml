(* Typing and memory-simulation handoff for the abi_decode operand. *)
Theory abiDecodeMemOperand
Ancestors
  bodyMemoryPreds exprSimHypsDefs vyperTypeSystem vyperTypeCallGraph
  allocLimits vyperState vyperContext

Theorem abi_decode_mem_operand_access:
  (!s'' x t.
     type_check (type_builtin_args_length_ok (AbiDecode unwrap) (LENGTH es))
       "TypeBuiltin args" s'' = (INL x,t) ==>
     body_exprs_mem_ok cx es) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann (AbiDecode unwrap) target es) st ==>
  ?e1 n. es = [e1] /\ ann = target /\
    expr_type e1 = BaseT (BytesT (Dynamic n)) /\
    assignable_type env.type_defs target /\ abi_decode_bytes_widths env.type_defs target /\
    expr_body_pre cenv cx env e1 st /\ body_expr_mem_ok cx e1 /\
    expr_sim_mem ctx func cenv cx (expr_type e1) e1 st /\
    expr_vv_sim_mem ctx func cenv cx (expr_type e1) e1 st
Proof
  strip_tac >>
  `?e1 n. es = [e1] /\ ann = target /\
    expr_type e1 = BaseT (BytesT (Dynamic n)) /\
    assignable_type env.type_defs target /\ abi_decode_bytes_widths env.type_defs target /\
    expr_body_pre cenv cx env e1 st` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     rw[expr_body_pre_def, well_typed_expr_def, int_calls_expr_def,
        supportedExprTraverseTheory.expr_has_evm_run_thm,
        byte_widths_expr_def, alloc_limits_expr_def, type_builtin_result_ok_def,
        well_typed_type_builtin_args_def] >>
     Cases_on `es` >> gvs[] >> rename1 `h::tl` >> Cases_on `tl` >>
     gvs[well_typed_expr_def, int_calls_expr_def,
         supportedExprTraverseTheory.expr_has_evm_run_thm,
         supportedExprTraverseTheory.supported_expr_exists_def,
         supportedExprTraverseTheory.supported_exprs_exists_every,
         byte_widths_expr_def, alloc_limits_expr_def] >>
     metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left,
               listTheory.APPEND_ASSOC]) >>
  gvs[] >>
  `body_exprs_mem_ok cx [e1]` by
    (first_x_assum irule >>
     simp[type_check_def, assert_def, type_builtin_args_length_ok_def]) >>
  gvs[body_exprs_mem_ok_def] >>
  qpat_x_assum `body_expr_mem_ok _ _` mp_tac >>
  once_rewrite_tac[body_expr_mem_ok_def] >>
  metis_tac[]
QED
