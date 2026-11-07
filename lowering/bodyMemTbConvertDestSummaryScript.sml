(* Counted bytestring destination continuation, including full capacity. *)
Theory bodyMemTbConvertDestSummary
Ancestors
  bodyMemTbConvertDynamicCast bodyMemTbConvertWidenCounted exprSimConvertBytes
  exprSimDefs exprLoweringProps compileEnv exprLowering gasSummary fragGasMode
  vyperTypeSystem valueCopyBytes loweringPosts fragExec

Theorem convert_bytestring_counted_cont_mem:
  valid_conversion (expr_type e1) (expr_type e) /\
  is_bytestring_type (expr_type e) /\
  is_bytestring_type (lowered_value_type cenv e1) /\
  evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv2 /\
  value_has_type tv1 v /\
  val_footprint tv1 v <= type_memory_bytes cenv (lowered_value_type cenv e1) /\
  type_memory_bytes cenv (expr_type e) < dimword (:256) /\
  expr_post ctx func cenv cx e1 es sa sm s0 es1 v x s /\
  (if type_memory_bytes cenv (lowered_value_type cenv e1) <
      type_memory_bytes cenv (expr_type e) then
     compile_bytestring_widen_copy (type_memory_bytes cenv (expr_type e)) x
       (type_memory_bytes cenv (lowered_value_type cenv e1)) sm
   else compile_type_convert x (mk_convert_op (expr_type e1) (expr_type e)) sm) = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ ~s.vs_halted /\
  alloca_history func s /\ alloca_inv s /\
  (!p. eval_operand x s = SOME p ==>
    w2n p + type_memory_bytes cenv (lowered_value_type cenv e1) <= s.vs_alloca_next) /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  (?tt v'. gas_marked_path T ctx func s 0 (OK tt) /\
    convert_result cx (expr_type e1) (expr_type e) v = INL v' /\
    expr_post ctx func cenv cx e es sa sb s0 es1 v' op tt /\
    tt.vs_current_bb = sb.cs_current_bb /\
    tt.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func tt /\ s.vs_alloca_next <= tt.vs_alloca_next /\
    (?w. eval_operand op tt = SOME w /\
      w2n w + type_memory_bytes cenv (expr_type e) <= tt.vs_alloca_next)) \/
  (?tt. gas_marked_path T ctx func s 0 (Abort Revert_abort tt) /\
    expr_exit (convert_result cx (expr_type e1) (expr_type e) v)
      (Abort Revert_abort tt))
Proof
  strip_tac >>
  `is_bytestring_type (expr_type e1)` by
    metis_tac[valid_conversion_to_bytestring] >>
  Cases_on `type_memory_bytes cenv (lowered_value_type cenv e1) <
              type_memory_bytes cenv (expr_type e)`
  >- (gvs[] >> drule_all convert_widen_cont_mem >> metis_tac[]) >>
  gvs[] >>
  `32 <= type_memory_bytes cenv (lowered_value_type cenv e1)` by
    gvs[bytestring_type_cases, type_memory_bytes_def] >>
  `!p. eval_operand x s = SOME p ==> w2n p + 32 <= s.vs_alloca_next` by
    (rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  qpat_x_assum `is_bytestring_type (expr_type e1)` mp_tac >>
  pure_rewrite_tac[bytestring_type_cases] >>
  CONV_TAC (LAND_CONV (HO_REWR_CONV (GSYM EXISTS_OR_THM))) >>
  disch_then (qx_choose_then `i` assume_tac) >>
  qpat_x_assum `is_bytestring_type (expr_type e)` mp_tac >>
  pure_rewrite_tac[bytestring_type_cases] >>
  CONV_TAC (LAND_CONV (HO_REWR_CONV (GSYM EXISTS_OR_THM))) >>
  disch_then (qx_choose_then `n` assume_tac) >>
  `compile_type_convert x (ConvBytestringCast n i) sm = (op,sb)` by
    gvs[mk_convert_op_to_bytestring] >>
  drule_all convert_dynamic_counted_cont_mem >> strip_tac
  >- suspend "cast_success" >>
  disj2_tac >> metis_tac[]
QED

Resume convert_bytestring_counted_cont_mem[cast_success]:
  disj1_tac >> qexistsl_tac [`tt`, `v'`] >> simp[] >>
  `?p. eval_operand x s = SOME p` by
    (gvs[expr_post_def, expr_val_rel_def, is_word_type_def] >> metis_tac[]) >>
  qexists_tac `p` >> conj_tac >- metis_tac[] >>
  qpat_x_assum `!p. eval_operand x s = SOME p ==>
    w2n p + type_memory_bytes cenv (lowered_value_type cenv e1) <= _` drule >>
  decide_tac
QED

Finalise convert_bytestring_counted_cont_mem

Theorem convert_bytestring_continuation_summary_mem:
  valid_conversion (expr_type e1) (expr_type e) /\
  is_bytestring_type (expr_type e) /\
  is_bytestring_type (lowered_value_type cenv e1) /\
  evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv2 /\
  value_has_type tv1 v /\
  val_footprint tv1 v <= type_memory_bytes cenv (lowered_value_type cenv e1) /\
  type_memory_bytes cenv (expr_type e) < dimword (:256) /\
  expr_post ctx func cenv cx e1 es sa sm s0 (ee with gas_obs := []) v x s /\
  (if type_memory_bytes cenv (lowered_value_type cenv e1) <
      type_memory_bytes cenv (expr_type e) then
     compile_bytestring_widen_copy (type_memory_bytes cenv (expr_type e)) x
       (type_memory_bytes cenv (lowered_value_type cenv e1)) sm
   else compile_type_convert x (mk_convert_op (expr_type e1) (expr_type e)) sm) = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ ~s.vs_halted /\
  alloca_history func s /\ alloca_inv s /\
  (!p. eval_operand x s = SOME p ==>
    w2n p + type_memory_bytes cenv (lowered_value_type cenv e1) <= s.vs_alloca_next) /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  expr_res_ok (convert_result cx (expr_type e1) (expr_type e) v) ==>
  gas_summary_at T (ctx,func) []
    (\vs. (convert_result cx (expr_type e1) (expr_type e) v,vs))
    (ee with gas_obs := [],s)
    (\res fin tt. ?v'. res = INL v' /\
      expr_post ctx func cenv cx e es sa sb s0 fin v' op tt /\
      tt.vs_current_bb = sb.cs_current_bb /\
      tt.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func tt /\ s.vs_alloca_next <= tt.vs_alloca_next /\
      (?w. eval_operand op tt = SOME w /\
        w2n w + type_memory_bytes cenv (expr_type e) <= tt.vs_alloca_next))
    (\res fin r. expr_exit res r)
Proof
  strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM (ee with gas_obs := []).scopes` by simp[] >>
  drule_all convert_bytestring_counted_cont_mem >> strip_tac
  >- (simp[gas_summary_at_def] >>
      qexistsl_tac [`INL v'`, `ee`, `OK tt`] >>
      simp[gas_marked_exec_def]) >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`convert_result cx (expr_type e1) (expr_type e) v`,
               `ee`, `Abort Revert_abort tt`] >>
  simp[gas_marked_exec_def, exit_result_def]
QED
