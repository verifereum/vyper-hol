(* Word provenance strengthens the very same successful counted witness. *)
Theory bodyIntCallWordProducer
Ancestors
  bodyIntCallProducerInterface exprSimIfExp exprSimDefs vyperAST


Theorem gas_outcome_word_provenance:
  is_word_type t /\ gas_outcome memory tops p source start Q R ==>
  gas_outcome memory tops p source start
    (\res ee s. Q res ee s /\
      intcall_vv_provenance cenv cx t sa sb ee (raw res)
        (StackValue t' op) s) R
Proof
  simp[intcall_vv_provenance_word]
  >> alan_closer_step
QED

val _ = alan_closer_stop ();


Theorem compile_ifexp_word_provenance:
  is_word_type ann /\
  expr_vv_sim ctx func cenv cx ty (IfExp ann c a b) es /\
  compile_expr cenv ty (IfExp ann c a b) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_expr cx (IfExp ann c a b)) expr_vv_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_expr cx (IfExp ann c a b)) (es,s0)
    (\res ee t. ?raw. res = INL raw /\
      vv_post ctx func cenv cx (IfExp ann c a b) es sa sb s0 ee raw vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance cenv cx (expr_type (IfExp ann c a b))
        sa sb ee raw vv t)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `?rv. vv = StackValue ann (Var rv)` by
    (drule compile_expr_ifexp >> simp[] >> metis_tac[]) >>
  gvs[] >> simp[expr_type_def, intcall_vv_provenance_word] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_def] >> disch_then irule >> simp[]
QED
