(* RawRevert's suffix, at the landing of the selected Bytes operand. *)
Theory entryCreateRawRevertSelected
Ancestors
  entryCreateTerminalFetch entryCreateFocusSpec bodyFullRawRevertCompiledTail
  exprSimHash exprSimConvertFromBytes exprSimHyps exprOperandVar
  exprSimFullBundleProps loweringPosts compileEnv fragExec vyperState
  fragGasOriginPtrExec gasSummary vyperStorageFootprint

Theorem raw_revert_selected_terminal_exit:
  expr_body_pre ce cx env e es /\ expr_type e = BaseT (BytesT (Dynamic cap)) /\
  lower_value compile_expr ce (expr_type e) e a = (op,m) /\ local_ptrs_reserved ce a /\
  compile_raw_revert op m = ((),b) /\ fn_has_code m b f /\
  (!tail. (do x <- eval_expr cx e; read_result cx x od)
    (es with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
      (res,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\ create_operand_at m t /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_sim_full_post (DF,lo,d,C,f) ce cx e (es,a,m,s,op,G,tn)
      H res mid G1 tn1 t /\
    gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) left (OK t,G1,tn1)) ==>
  ?v exc fin r G2 tn2. res = INL v /\
    (!tail. vyperState$bind (lift_option_type (dest_BytesV v) "raw_revert data")
      (\data. vyperState$raise (Error (RevertData data))) (mid with gas_obs := tail) =
      ((INR exc : 'a + exception),fin with gas_obs := tail)) /\
    storage_trace_domain cx st0 fin.storage_trace /\
    exit_result r /\ create_operand_full_scope m b E C f t [] r /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
      valid_horizon cx st0 H mid.storage_trace /\
      gas_origin_ptr_path (DF H,lo,E,C,f,PG) (t,G1,tn1) [] (r,G2,tn2) /\
      create_operand_exit_post C cx H (INR exc : 'a + exception)
        (fin with gas_obs := []) (G2,tn2) r)
Proof
  strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by
    fs[storage_trace_domain_def, Abbr `H0`] >>
  first_x_assum (qspec_then `H0` mp_tac) >>
  simp[expr_sim_full_post_def] >> strip_tac >> gvs[] >>
  `?bs. v = BytesV bs` by
    (qpat_assum `!tail. (do x <- eval_expr _ _; read_result _ x od) _ = _`
       (qspec_then `[]` (assume_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
     `expr_body_pre ce cx env e (es with gas_obs := gas_explicit left s.vs_gas_readings)` by simp[] >>
     drule_at (Pat `(do x <- eval_expr _ _; read_result _ x od) _ = _`)
       expr_body_pre_base_result >>
     simp[] >> metis_tac[dynamic_bytes_value_typed]) >> gvs[] >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap)))` by
    (drule expr_body_pre_type_evaluates >> simp[vyperValueTheory.evaluate_type_def] >>
     rw[]) >>
  `post_value_type ce e = expr_type e` by simp[is_bytestring_type_def] >>
  `!x. op = Var x ==> not_fresh_at m x` by
    (drule compile_lower_value_var >> simp[]) >>
  `~t.vs_halted` by (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  `?w G2 tn2. !D. gas_origin_ptr_path (D,lo,E,C,f,PG)
       (t,G1,tn1) [] (Abort Revert_abort w,G2,tn2)` by
    (irule (INST_TYPE [alpha |-> ``:256``] raw_revert_compiled_tail_joint) >> simp[] >>
     qhdtm_assum `expr_post` (irule_at Any) >>
     qhdtm_assum `ghost_inv_at` (irule_at Any) >>
     fs[create_operand_at_def] >> rpt (HINT_EXISTS_TAC >> simp[]) >>
     qpat_assum `expr_type e = _` (SUBST1_TAC o SYM) >> simp[]) >>
  qexistsl_tac [`Error (RevertData bs)`,`mid`,
    `Abort Revert_abort w`,`G2`,`tn2`] >>
  simp[lift_option_type_def, vyperValueTheory.dest_BytesV_def, bind_def,
       return_def, raise_def, exit_result_def, create_operand_exit_post_def,
       exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def] >>
  qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
    (qspec_then `DF H0` assume_tac) >>
  drule_all raw_revert_joint_scope >> simp[]
QED
