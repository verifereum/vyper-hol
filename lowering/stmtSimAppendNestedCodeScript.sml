(* Compiler boundary for aggregate Append at an already resolved target. *)
Theory stmtSimAppendNestedCode
Ancestors
  stmtSimAppendResolved stmtLowering exprLowering compileEnv loweringPosts

Theorem append_nested_aggregate_code_parts:
  stmt_env cenv lctx ty (Append bt e) sa = (c,sf) /\
  compile_get_target_ptr compile_expr cenv bt sa =
    ((bop,SOME (if tr then LocTransient else LocStorage),
      SOME (ValPT (ArrayT elem (Dynamic cap)))),sp) /\
  ~is_word_type elem ==>
  c = cenv /\ ?sb raw tmp sc sd.
    lower_value compile_expr cenv elem e sp = (raw,sb) /\
    compile_alloc_buffer (type_memory_bytes cenv elem) sb = (tmp,sc) /\
    compile_store_memory cenv raw tmp.buf_operand elem
      (lowered_value_type cenv e) sc = ((),sd) /\
    compile_dynarray_append cenv bop tmp.buf_operand 1
      ((type_memory_bytes cenv elem + 31) DIV 32) elem elem cap F
      (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sd = ((),sf)
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, Once compile_stmt_def] >>
  Cases_on `tr` >>
  simp[word_scale_def, elem_size_in_location_def, is_slot_addressed_def,
       load_opc_for_def, store_opc_for_def] >>
  Cases_on `lower_value compile_expr cenv elem e sp` >>
  rename1 `lower_value _ _ _ _ _ = (raw,sb)` >> simp[] >>
  Cases_on `compile_alloc_buffer (type_memory_bytes cenv elem) sb` >>
  rename1 `compile_alloc_buffer _ _ = (tmp,sc)` >> simp[] >>
  Cases_on `compile_store_memory cenv raw tmp.buf_operand elem (lowered_value_type cenv e) sc` >>
  rename1 `compile_store_memory _ _ _ _ _ _ = (u,sd)` >>
  Cases_on `u` >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[]
QED
