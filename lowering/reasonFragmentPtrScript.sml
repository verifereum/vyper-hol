(* Raw reason expression composition with a checked encoder continuation. *)
Theory reasonFragmentPtr
Ancestors
  reasonSourceProps reasonCompilerProps bodyPtrAttributeSource
  bodyPtrDefs gasSummaryComposePtr fragGasPathPtr fragGasSeqPtr stmtFragPtr fragExec
  exprSimMemorySource exprSimDefs exprSimProps loweringPosts
  gasContext gasSummary gasExemptCert gasSummaryCompose gasCount fragGasMode
  stmtSimDefs stmtSimProps vyperInterpreter vyperState vyperValue
  vyperValueOperation venomState list rich_list arithmetic
Libs
  monadsyntax

Theorem raise_reason_endpoint_string:
  gas_admissible (eval_stmt cx (Raise (RaiseReason r))) (stmt_res_ok lctx) es /\
  (!tail. eval_expr cx r (es with gas_obs := xs ++ tail) =
    (INL tv,ee with gas_obs := tail)) /\
  vv_holds cenv cx (expr_type r) tv vv (ee with gas_obs := []) t ==>
  ?str.
    (!tail. read_result cx tv (ee with gas_obs := tail) =
      (INL (StringV str),ee with gas_obs := tail)) /\
    (!tail. eval_stmt cx (Raise (RaiseReason r))
      (es with gas_obs := xs ++ tail) =
      (INR (AssertException str),ee with gas_obs := tail))
Proof
  strip_tac >> drule attribute_vv_holds_read_operand >> strip_tac >>
  drule read_result_gas_obs >> simp[] >> strip_tac >>
  qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >> fs[] >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def] >>
  disch_then (qspec_then `xs ++ []` mp_tac) >>
  simp[eval_raise_reason_bind, bind_def] >>
  Cases_on `v` >>
  simp[dest_StringV_def, lift_option_type_def, raise_def, return_def,
       stmt_res_ok_def] >>
  strip_tac >> rename1 `StringV str` >> qexists `str` >>
  simp[eval_raise_reason_bind, bind_def, dest_StringV_def,
       lift_option_type_def, raise_def, return_def]
QED

Theorem compile_raise_reason_path_frag_ptr:
  !d ctx PG func cx lctx RetQ cenv ty r es.
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_vv_sim_ptr d ctx PG func cenv cx (expr_type r) r es /\
    (!sa vv sm sb s0 ee tv t G tn str.
       compile_expr cenv (expr_type r) r sa = (vv,sm) /\
       compile_revert_with_reason cenv vv (expr_type r)
         (type_memory_bytes cenv (expr_type r)) sm = ((),sb) /\
       fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
       local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
       vv_post ctx func cenv cx r es sa sm s0 ee tv vv t /\
       ghost_inv d cenv cx ee G tn t /\
       ptr_vv_ok cx (expr_type r) tv vv ee G tn t /\
       ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
       t.vs_inst_idx = LENGTH sm.cs_current_insts /\
       read_result cx tv ee = (INL (StringV str),ee) ==>
       ?z Gf tnf. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t 0 Gf tnf
         (Abort Revert_abort z)) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Raise (RaiseReason r)))
      (eval_stmt cx (Raise (RaiseReason r))) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule compile_raise_reason_parts >> strip_tac >>
  drule_all raise_reason_compiler_code >> strip_tac >>
  drule compile_reason_message_cases >> strip_tac >- metis_tac[] >> gvs[] >>
  drule raise_reason_raw_admissible >> strip_tac >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_ptr_def]) >>
  disch_then drule >> simp[] >>
  disch_then (qspecl_then [`s0`,`G0`,`tn0`] mp_tac) >> simp[] >>
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qpat_x_assum `?res es_end G tn rr. _` strip_assume_tac >> gvs[]
      >- suspend "normal"
      >> suspend "exception") >>
  qexists `marks` >> disj2_tac >>
  pop_assum strip_assume_tac >>
  qexistsl [`err`,`ee`,`leaf`,`finish'`] >>
  drule raise_reason_raw_exempt >> simp[]
QED

Resume compile_raise_reason_path_frag_ptr[normal]:
  `~t.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  `vv_holds cenv cx (expr_type r) tv vv (es_end with gas_obs := []) t` by
    fs[vv_post_def] >>
  drule_all raise_reason_endpoint_string >> strip_tac >>
  qpat_assum `!tail. read_result _ _ _ = _` (qspec_then `[]` assume_tac) >> fs[] >>
  qpat_x_assum `!sa vv sm sb s0 ee tv t G tn str. _`
    (drule_all_then strip_assume_tac) >>
  qexists `marks` >> disj1_tac >>
  qexistsl [`INR (AssertException str)`,`es_end`,`Gf`,`tnf`,`Abort Revert_abort z`] >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[gas_path_ptr_then, ADD_CLAUSES] >>
  disj2_tac >> simp[exit_result_def, stmt_exit_ptr_def, expr_exit_def]
QED

Resume compile_raise_reason_path_frag_ptr[exception]:
  Cases_on `res` >- fs[expr_exit_def] >>
  qexists `marks` >> disj1_tac >>
  qexistsl [`INR y`,`es_end`,`G`,`tn`,`r''`] >>
  conj_tac >- (gen_tac >> simp[eval_raise_reason_bind, bind_def]) >>
  conj_tac >- simp[] >>
  disj2_tac >> simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]
QED

Finalise compile_raise_reason_path_frag_ptr
