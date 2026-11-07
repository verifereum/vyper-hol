(* Word-local assignment: reuse the checked scalar-local store continuation. *)
Theory assignBasePtrWordFragment
Ancestors assignTuplePtrLocalWordRuntime assignBasePtrScalarPost
  stmtSimAssign stmtSimAssignSource stmtSimAssignStore stmtSimDeclStore
  stmtSimProps exprSimProps exprSimDefs bodyPtrDefs stmtFragPtr
  gasSummaryComposePtr gasExemptCert fragGasPathPtr fragGasPath fragGasMode
  gasSummary gasSummaryCompose exprLoweringProps emitHelperProps emitHelper exprLowering
  stmtLowering compileEnv loweringPosts venomState venomInst
  vyperState vyperLookup finite_map list rich_list
Libs monadsyntax

Theorem compile_assign_local_stmt_frag_ptr:
  !d ctx PG func cx lctx RetQ cenv ty id e es p sz vtyp etv.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vtyp /\ is_word_type vtyp /\
    is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    (!gs v es1 entry.
       bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       store_lays_out etv entry.type v) /\
    expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_all assign_local_word_code_parts >> strip_tac >> gvs[] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (drule assign_local_admissible_rhs >> simp[]) >>
  `~block_is_terminated sb` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> Cases_on `sb'.cs_current_insts` >>
     gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
         mk_inst_def, is_terminator_def]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
    by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then drule_all >> simp[gas_outcome_ptr_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_summary_ptr_at_marked] >> strip_tac
      >- suspend "normal" >> suspend "exception") >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule assign_local_exempt >> simp[] >>
  metis_tac[gas_exempt_cert_unforce_result]
QED

Resume compile_assign_local_stmt_frag_ptr[exception]:
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[expr_exit_def]) >> gvs[] >>
  qexistsl_tac [`INR ex`, `es_end`, `G`, `tn`, `r`] >> conj_tac
  >- (drule assign_local_admissible_run >> strip_tac >>
      simp[gas_marked_exec_ptr_def] >>
      conj_tac >- (irule gas_source_bind_exception >> fs[gas_marked_exec_ptr_def]) >>
      fs[gas_marked_exec_ptr_def]) >>
  disj2_tac >> simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]
QED

Resume compile_assign_local_stmt_frag_ptr[normal]:
  gvs[] >> drule gas_marked_exec_ptr_exec >> strip_tac >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v,es_end with gas_obs := tail)` by fs[gas_marked_exec_ptr_def] >>
  drule_all assign_local_continuation_all_tails >> strip_tac >>
  `lookup_scopes id es_end.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `store_lays_out etv entry.type v` by
    (qpat_x_assum `!gs v es1 entry. _` irule >>
     qexistsl_tac [`es_end with gas_obs := []`,
       `gas_explicit marks s0.vs_gas_readings`] >>
     qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t /\
   eval_operand op t = SOME (typed_val_to_w256 etv v)` by
    (fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `?dw. lookup_var p t = SOME dw` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  `op_taint tn op = {}` by fs[ptr_val_ok_def] >>
  `stmt_state_rel ctx func cenv cx es_end t /\ ghost_inv d cenv cx es_end G tn t`
    by (fs[] >> metis_tac[ghost_inv_gas_obs]) >>
  drule_all tuple_local_word_runtime_head_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  suspend "finish"
QED

Resume compile_assign_local_stmt_frag_ptr[finish]:
  qexistsl_tac [`INL ()`,
    `es_end with scopes := pre ++ (env |+ (id,entry with <|value := v; popped := []|>)) :: rest`,
    `G`, `tn'`, `OK t'`] >> conj_tac
  >- (drule assign_local_admissible_run >> strip_tac >>
      simp[gas_marked_exec_ptr_def] >>
      conj_tac
      >- (gen_tac >> simp[Once bind_def]) >>
      metis_tac[gas_path_ptr_then, gas_marked_exec_ptr_def, arithmeticTheory.ADD_0]) >>
  disj1_tac >> simp[stmt_lands_def, cenv_top_ext_refl] >>
  conj_tac
  >- (qpat_x_assum `ghost_inv _ _ _ (_ with scopes := _) _ _ t'` mp_tac >>
      simp[ghost_inv_def] >> strip_tac >> asm_rewrite_tac[]) >>
  fs[expr_post_def, ghost_kept_def] >> metis_tac[]
QED
Finalise compile_assign_local_stmt_frag_ptr
