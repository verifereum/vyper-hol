(* Semantic counted continuation for a read-only dynamic bytestring cast. *)
Theory bodyMemTbConvertDynamicCast
Ancestors
  bodyMemTbConvertCastCounted exprSimConvertBytes exprSimDefs
  exprLoweringProps loweringPosts fragGasMode compileEnv

Theorem convert_dynamic_counted_cont_mem:
  ((expr_type e1 = BaseT (BytesT (Dynamic i))) \/
    expr_type e1 = BaseT (StringT i)) /\
  ((expr_type e = BaseT (BytesT (Dynamic n))) \/
    expr_type e = BaseT (StringT n)) /\
  evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv2 /\
  value_has_type tv1 v /\
  expr_post ctx func cenv cx e1 es sa sm s0 es1 v x s /\
  compile_type_convert x (ConvBytestringCast n i) sm = (op,sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  (!p. eval_operand x s = SOME p ==> w2n p + 32 <= s.vs_alloca_next) /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  (?tt v'. gas_marked_path T ctx func s 0 (OK tt) /\
    convert_result cx (expr_type e1) (expr_type e) v = INL v' /\
    expr_post ctx func cenv cx e es sa sb s0 es1 v' op tt /\
    tt.vs_current_bb = sb.cs_current_bb /\
    tt.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func tt /\ tt.vs_alloca_next = s.vs_alloca_next /\
    tt.vs_memory = s.vs_memory /\ tt.vs_allocas = s.vs_allocas /\
    (!p. eval_operand x s = SOME p ==> eval_operand op tt = SOME p)) \/
  (?tt. gas_marked_path T ctx func s 0 (Abort Revert_abort tt) /\
    expr_exit (convert_result cx (expr_type e1) (expr_type e) v)
      (Abort Revert_abort tt))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_val_rel cx (expr_type e1) v x s /\
   stmt_state_rel ctx func cenv cx es1 s` by gvs[expr_post_def] >>
  drule_all convert_dynamic_view >> strip_tac >>
  drule convert_cast_grows >> strip_tac >>
  `w2n p + 32 <= s.vs_alloca_next` by metis_tac[] >>
  drule_all convert_cast_counted_mem >> strip_tac
  >- suspend "success" >>
  disj2_tac >> goal_assum (drule_at Any) >>
  first_x_assum drule >> strip_tac >> simp[expr_exit_def]
QED

Resume convert_dynamic_counted_cont_mem[success]:
  disj1_tac >>
  `?v'. convert_result cx (expr_type e1) (expr_type e) v = INL v'` by
    (first_x_assum irule >> simp[]) >>
  qexistsl_tac [`t`, `v'`] >> simp[] >>
  irule convert_bytestring_expr_post >>
  conj_tac >- gvs[is_bytestring_type_def] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`e1`, `tv1`, `v`] >>
  simp[] >> conj_tac >- gvs[is_bytestring_type_def] >>
  irule convert_readonly_expr_post >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`s`, `sm`, `x`] >> simp[]
QED

Finalise convert_dynamic_counted_cont_mem
