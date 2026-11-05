Theory extRetNormalizeInputsPtr
Ancestors
  typedCopyPtr bodyPtrDefs vyperTypeSystem compileEnv memoryLocalRhsProps

(* Word-class preservation subsumes the source-word equality observation
   local to stmtSimReturnWiden; that local theorem is not exported. *)
Theorem arg_type_fits_word_class:
  (!sty ty. arg_type_fits sty ty ==>
     (is_word_type sty <=> is_word_type ty)) /\
  (!stys tys. arg_types_fit stys tys ==>
     (EVERY is_word_type stys <=> EVERY is_word_type tys))
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rw[arg_type_fits_def, is_word_type_def] >> gvs[]
QED

Theorem typed_return_nonword_source:
  !env ty e.
    IS_SOME (type_stmt env ty (Return (SOME e))) /\
    ~is_word_type ty ==> ~is_word_type (expr_type e)
Proof
  simp[type_stmt_return_some_iff, type_widens_to_def] >>
  metis_tac[cj 1 arg_type_fits_word_class]
QED

Theorem typed_return_ptr_buf_ok:
  !env ty e ce op G s.
    IS_SOME (type_stmt env ty (Return (SOME e))) /\
    ~is_word_type ty /\
    (~is_word_type (expr_type e) ==> ptr_buf_ok ce e op G s) ==>
    ptr_buf_ok ce e op G s
Proof
  metis_tac[typed_return_nonword_source]
QED

Theorem return_lowered_runtime_layout:
  !ce e env tops cx es v es'.
    expr_body_pre ce cx env e es /\ supported_expr tops e /\
    ce.ce_func_return_type = build_func_return_type tops /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') /\
    expr_sim_inv ce cx env es ==>
    ?stv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
      value_has_type stv v /\
      type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv
Proof
  rpt strip_tac >>
  drule_all memory_rhs_read_lowered_typed >> strip_tac >>
  drule_all memory_rhs_runtime_layout >> simp[]
QED

Theorem return_equal_lowered_robust:
  !ce e cx v op G tn s stv w.
    lowered_value_type ce e = expr_type e /\
    ~is_word_type (expr_type e) /\
    ptr_val_ok cx (expr_type e) v op G tn s /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    eval_operand op s = SOME w ==>
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory stv v (w2n w) mem
Proof
  rw[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]
QED

(* Runtime typing does not change a memory layout. The first boundary still
   requires the external frame's function-return map, module code and
   supported-expression facts, plus expr_body_pre/expr_sim_inv. The second
   boundary requires equality of lowered and annotated types: it does NOT
   cover internal calls whose declared return type differs from annotation.
   Both retain these contextual obligations explicitly for integration. *)
