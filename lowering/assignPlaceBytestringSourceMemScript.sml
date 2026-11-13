(* Source footprint for a bytestring represented by a stack pointer. *)
Theory assignPlaceBytestringSourceMem
Ancestors
  exprSimMemDefs loweringPosts valueCopyBytes exprSimProps
  memoryLocalRhsProps exprSimHyps
  valueEncodingTyping valueEncoding vyperValue compileEnv venomState

Theorem assign_bytestring_stack_source_mem[local]:
  is_bytestring_type et /\ is_bytestring_type lt /\
  vv_holds cenv cx et raw (StackValue vt op) ee s /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  vv_store_bound cx et lt ee raw (StackValue vt op) s /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) lt = SOME stv /\ value_has_type stv v ==>
  ?sw. eval_operand op s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + val_store_size stv v <= s.vs_alloca_next
Proof
  strip_tac >>
  `~is_word_type et /\ ~is_word_type lt` by
    metis_tac[is_bytestring_word_type] >>
  `?sw. eval_operand op s = SOME sw /\
     val_in_memory etv v (w2n sw) s.vs_memory` by
    (gvs[vv_holds_def, expr_val_rel_def] >> metis_tac[]) >>
  `val_in_memory stv v (w2n sw) s.vs_memory` by
    metis_tac[bytestring_val_in_memory_transfer] >>
  `0 < type_memory_size stv` by
    (drule_all bytestring_type_value >> strip_tac >>
     gvs[type_memory_size_def]) >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next` by
    (gvs[vv_store_bound_def] >> metis_tac[]) >>
  `val_wf stv v` by metis_tac[cj 1 value_has_type_val_wf] >>
  `val_store_size stv v <= type_memory_size stv` by simp[val_store_size_le] >>
  qexists_tac `sw` >> simp[] >> decide_tac
QED

Theorem assign_bytestring_post_source_mem:
  is_bytestring_type (expr_type e) /\
  is_bytestring_type (lowered_value_type cenv e) /\
  expr_body_pre cenv cx env e es /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,er) /\
  expr_sim_inv cenv cx env ee /\
  vv_post ctx func cenv cx e es sa sb s0 ee raw (StackValue vt op) s /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e)
    ee raw (StackValue vt op) s /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
  value_has_type stv v ==>
  ?sw. eval_operand op s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + val_store_size stv v <= s.vs_alloca_next
Proof
  strip_tac >>
  `value_runtime_typed env (expr_type e) v` by
    metis_tac[memory_rhs_read_annotation_typed] >>
  `?etv. evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
     value_has_type etv v /\
     type_memory_bytes cenv (expr_type e) = type_memory_size etv` by
    metis_tac[memory_rhs_runtime_layout] >>
  `vv_holds cenv cx (expr_type e) raw (StackValue vt op) ee s` by
    (gvs[vv_post_def, post_value_type_bytestring]) >>
  irule assign_bytestring_stack_source_mem >> metis_tac[]
QED
