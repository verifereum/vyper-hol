(* Dispatch at the post-child destination ADD seam. The compiler environment
   is unchanged by emit_op; nonconstructor is a caller premise of the existing
   expr_vv_sim_ptr judgment, not a consequence of absence of dynamic allocas. *)
Theory bodyPtrMakeArrayDispatch
Ancestors
  bodyPtrMakeArrayAddFrame exprSimUnwrap context exprLowering

Theorem located_child_after_add_not_calldata:
  vv_post ctx func cenv cx e es sa sm s0 es' tv (LocatedValue ty p) s /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!z. vv_operand (LocatedValue ty p) = Var z ==> not_fresh_at sm z) /\
  emit_op opc [left;right] sm = (Var out,sn) ==>
  p.ptr_location <> LocCalldata /\
  vv_post ctx func cenv cx e es sa sn s0 es' tv (LocatedValue ty p)
    ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> conj_tac
  >- metis_tac[vv_post_calldata] >>
  irule emit_binop_vv_post >> metis_tac[]
QED

Theorem runtime_code_word_unwrap:
  ~cenv.ce_is_ctor /\ is_word_type ty /\ p.ptr_location = LocCode ==>
  unwrap_value cenv (LocatedValue ty p) sm =
    emit_op DLOAD [p.ptr_operand] sm
Proof
  simp[unwrap_value_def, compile_ptr_load_def, compile_imm_load_word_def]
QED
