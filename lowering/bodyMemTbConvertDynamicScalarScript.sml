(* Counted memory-safe continuations for bytestring-to-scalar conversion. *)
Theory bodyMemTbConvertDynamicScalar
Ancestors
  bodyMemTbConvertReadSuffix allocaHistoryFragment exprSimConvertFromBytes
  varsExt freshWrites fragGasMode fragGasPathMem fragExec exprSimDefs loweringPosts gasSummary
  exprLoweringProps compileEnv venomState venomExecSemantics rich_list list

Theorem dynamic_scalar_counted_fragment_mem:
  is_bytestring_type src /\ ~is_bytestring_type dst /\
  valid_conversion src dst /\ well_formed_type tenv dst /\
  evaluate_type (get_tenv cx) src = SOME stv /\ value_has_type stv v /\
  convert_result cx src dst v = res /\
  compile_type_convert op (mk_convert_op src dst) sa = (r,sb) /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s0 /\ alloca_inv s0 /\
  (!z. op = Var z ==> not_fresh_at sa z) /\
  (!a. eval_operand op s0 = SOME a ==> w2n a + 64 <= s0.vs_alloca_next) /\
  stmt_state_rel ctx func cenv cx es s0 /\
  expr_val_rel cx src v op s0 /\ expr_val_at cenv cx src sarg sa0 es v op s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out. gas_marked_path T ctx func s0 0 out /\
    ((?s vout dtv. out = OK s /\ res = INL vout /\
       evaluate_type (get_tenv cx) dst = SOME dtv /\
       stmt_state_rel ctx func cenv cx es s /\
       eval_operand r s = SOME (typed_val_to_w256 dtv vout) /\
       s.vs_memory = s0.vs_memory /\ s.vs_allocas = s0.vs_allocas /\
       (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
              lookup_var x s = SOME w) /\
       ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
       s.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next) \/
     (exit_result out /\ expr_exit res out))
Proof
  strip_tac >> drule_all dynamic_operand_packet >> strip_tac >>
  `dynamic_straight_fresh (compile_type_convert op (mk_convert_op src dst))` by
    (irule dynamic_scalar_straight_read_fresh >> simp[]) >>
  `dynamic_writes_fresh sa (emitted_insts sa sb)` by
    metis_tac[dynamic_straight_fresh_def] >>
  drule dynamic_writes_fresh_path_opcodes >> strip_tac >>
  `vars_ext_result
    (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s0))
    (run_inst_seq (emitted_insts sa sb) s0)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >> fs[EVERY_MEM]) >>
  `eval_operand op (drop_fresh sa s0) = SOME a` by
    simp[eval_operand_drop_fresh] >>
  qspecl_then [`sa`,`s0`] assume_tac fresh_vars_wrt_drop_fresh >>
  `val_in_memory stv v (w2n a) (drop_fresh sa s0).vs_memory` by
    simp[drop_fresh_def] >>
  `w2n a + 64 <= s0.vs_alloca_next` by metis_tac[] >>
  drule_all convert_dynamic_scalar_paths_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all dynamic_scalar_run_exact >>
  Cases_on `res` >> simp[] >> strip_tac >> gvs[vars_ext_result_def]
  >- suspend "success" >>
  suspend "abort"
QED

Resume dynamic_scalar_counted_fragment_mem[success]:
  drule_all dynamic_run_post >> strip_tac >>
  drule_all dynamic_code_prefix >> strip_tac >>
  `LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb) =
    LENGTH sb.cs_current_insts` by
    (qpat_x_assum `dynamic_straight_fresh _` mp_tac >>
     rewrite_tac[dynamic_straight_fresh_def] >> disch_then drule >>
     strip_tac >> simp[]) >>
  `alloca_history func (t' with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (`alloca_history func
        (t' with vs_inst_idx := s0.vs_inst_idx + LENGTH (emitted_insts sa sb))`
       suffices_by simp[] >>
     irule alloca_history_run_inst_seq >> goal_assum (drule_at Any) >>
     fs[IS_PREFIX_APPEND, EVERY_MEM] >> metis_tac[]) >>
  drule_all dynamic_run_read_fresh >> strip_tac >>
  qexists_tac `OK (t' with vs_inst_idx := LENGTH sb.cs_current_insts)` >>
  simp[gas_marked_path_def] >>
  fs[vars_ext_def, drop_fresh_def] >>
  qpat_x_assum `t' = _` SUBST1_TAC >>
  qpat_x_assum `sf = _` SUBST1_TAC >> simp[]
QED

Resume dynamic_scalar_counted_fragment_mem[abort]:
  goal_assum (drule_at Any) >> simp[exit_result_def, expr_exit_def]
QED

Finalise dynamic_scalar_counted_fragment_mem

Theorem dynamic_continuation_summary_mem:
  expr_post ctx func cenv cx e1 es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  alloca_history func t0 /\ s0.vs_alloca_next <= t0.vs_alloca_next /\
  alloca_inv t0 /\ fn_inst_ids_distinct func /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  is_bytestring_type (expr_type e1) /\ ~is_bytestring_type t /\
  valid_conversion (expr_type e1) t /\ well_formed_type tenv t /\ ann = t /\
  is_word_type t /\
  evaluate_type (get_tenv cx) (expr_type e1) = SOME stv /\ value_has_type stv v1 /\
  ((lowered_value_type cenv e1 = BaseT (BytesT (Dynamic 0)) \/
    lowered_value_type cenv e1 = BaseT (StringT 0)) ==> v1 = BytesV [] \/ v1 = StringV "") /\
  (if lowered_value_type cenv e1 = BaseT (BytesT (Dynamic 0)) \/
      lowered_value_type cenv e1 = BaseT (StringT 0)
   then op = Lit 0w /\ sb = s1
   else compile_type_convert x (mk_convert_op (expr_type e1) t) s1 = (op,sb) /\
        (!a. eval_operand x t0 = SOME a ==> w2n a + 64 <= t0.vs_alloca_next)) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  fn_has_code s1 sb func /\ local_ptrs_reserved cenv s1 /\
  sa.cs_next_var <= s1.cs_next_var ==>
  gas_summary_at T (ctx,func) []
    (\vs. (convert_result cx (expr_type e1) t v1,vs))
    (ee with gas_obs := [],t0)
    (\res fin ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert t [e1]) es sa sb s0
        fin v op ss /\ ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func ss /\ s0.vs_alloca_next <= ss.vs_alloca_next)
    (\res fin out. expr_exit res out)
Proof
  strip_tac >>
  `post_value_type cenv e1 = expr_type e1` by
    (irule post_value_type_bytestring >> first_assum ACCEPT_TAC) >>
  Cases_on `lowered_value_type cenv e1 = BaseT (BytesT (Dynamic 0)) \/
            lowered_value_type cenv e1 = BaseT (StringT 0)`
  >- suspend "empty" >>
  gvs[] >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) t0 /\
   expr_val_rel cx (expr_type e1) v1 x t0 /\
   expr_val_at cenv cx (expr_type e1) sa s1 (ee with gas_obs := []) v1 x t0` by
    fs[expr_post_def] >>
  drule_all (Q.INST
    [`src` |-> `expr_type e1`, `dst` |-> `ann`, `v` |-> `v1`,
     `res` |-> `convert_result cx (expr_type e1) ann v1`]
    dynamic_scalar_counted_fragment_mem |> SIMP_RULE (srw_ss()) []) >>
  strip_tac
  >- suspend "success" >>
  suspend "abort"
QED

Resume dynamic_continuation_summary_mem[empty]:
  `?vout dtv. convert_result cx (expr_type e1) t v1 = INL vout /\
    evaluate_type (get_tenv cx) t = SOME dtv /\ typed_val_to_w256 dtv vout = 0w` by
    metis_tac[dynamic_empty_scalar_convert] >>
  gvs[] >> simp[gas_summary_at_def] >>
  qexistsl_tac [`INL vout`,`ee`,`OK t0`] >>
  simp[gas_marked_exec_def, gas_marked_path_def, gas_path_mem_rules] >>
  (irule dynamic_expr_post_convert >> simp[eval_operand_def] >>
   conj_tac >- fs[expr_post_def] >>
   qexistsl_tac [`s1`,`t0`] >> simp[] >> metis_tac[])
QED

Resume dynamic_continuation_summary_mem[success]:
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL vout`,`ee`,`OK s`] >>
  simp[gas_marked_exec_def] >>
  conj_tac >- metis_tac[] >>
  irule dynamic_expr_post_convert >> simp[] >>
  qexistsl_tac [`s1`,`t0`] >> simp[] >> metis_tac[]
QED

Resume dynamic_continuation_summary_mem[abort]:
  simp[gas_summary_at_def] >>
  qexistsl_tac [`convert_result cx (expr_type e1) ann v1`,`ee`,`out`] >>
  simp[gas_marked_exec_def]
QED

Finalise dynamic_continuation_summary_mem
