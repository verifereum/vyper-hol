(* Consumer boundary after the destination ADD.  Compilation supplies the
   old-source premise; scalar children do not require source-buffer coverage.
   Runtime-code consumers must still retain the caller's ~ce_is_ctor premise. *)
Theory bodyPtrMakeArrayConsumerPost
Ancestors
  bodyPtrMakeArrayDispatch bodyPtrMakeArrayAddFrame exprOperandVar bodyPtrDefs emitHelper
  compileEnv context exprLowering

Theorem make_array_located_consumer_post:
  compile_expr cenv (expr_type e) e sa = (LocatedValue ty p,sm) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [buf; Lit (n2w off)] sm = (Var out,sn) /\
  vv_post ctx func cenv cx e es sa sm s0 es' tv (LocatedValue ty p) s /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue ty p) es' G tn s /\
  (~is_word_type (expr_type e) ==>
    ptr_buf_ok cenv e (vv_operand (LocatedValue ty p)) G s) ==>
  p.ptr_location <> LocCalldata /\
  vv_post ctx func cenv cx e es sa sn s0 es' tv (LocatedValue ty p)
    ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue ty p) es'
    (step_prov PG G (mk_inst sm.cs_next_id ADD [buf; Lit (n2w off)] [out])
      (update_var out w s))
    (step_taint (mk_inst sm.cs_next_id ADD [buf; Lit (n2w off)] [out]) s
      (update_var out w s) tn)
    ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  (~is_word_type (expr_type e) ==>
    ptr_buf_ok cenv e (vv_operand (LocatedValue ty p))
      (step_prov PG G (mk_inst sm.cs_next_id ADD [buf; Lit (n2w off)] [out])
        (update_var out w s))
      ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `!z. vv_operand (LocatedValue ty p) = Var z ==> not_fresh_at sm z`
    by metis_tac[cj 1 compiler_compile_var] >>
  `!z. vv_operand (LocatedValue ty p) = Var z ==> z <> out` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all located_child_after_add_not_calldata >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  simp[] >> conj_tac
  >- (irule binop_source_ptr_vv_ok >> metis_tac[]) >>
  strip_tac >> irule binop_source_ptr_buf_ok >> metis_tac[]
QED
