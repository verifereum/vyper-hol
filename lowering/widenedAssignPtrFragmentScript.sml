(* Counted composition of the RHS and the widened local write. *)
Theory widenedAssignPtrFragment
Ancestors widenedAssignPtrRead widenedAssignPtrPreparation
  widenedAssignPtrRhsInput assignBasePtrLocalBodyFacts bodyPtrPreds bodyPtrDefs
  bodySim exprSimHyps exprSimHypsDefs exprSimDefs exprSimProps
  stmtSimAssignSource stmtSimAssignMem stmtSimDeclMem stmtSimProps
  stmtLowering exprLowering exprLoweringProps exprSimUnwrap
  compileEnv context fragExec stmtFragPtr loweringPosts
  gasSummaryComposePtr gasSummary gasOutcome gasExemptCert
  fragGasMode fragGasPathPtr fragGasPath
  exprOpenTerminals assignValueMemoryOpen localPtrsProps
  vyperTypeSystem vyperAST vyperState finite_map words
Libs monadsyntax

Theorem widened_assignment_fragment_ptr:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env e es /\ supported_expr tops e /\
  body_expr_ptr_ok cx e /\
  e = Call ann (IntCall fid) args drv /\
  type_stmt env rty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
  stmt_exprs_ok ce (Assign (BaseTarget (NameTarget id)) e) /\
  FLOOKUP env.var_types id = SOME ty /\
  type_widens_to env.type_defs (expr_type e) ty /\
  ~is_word_type ty /\ 0 < type_memory_bytes ce ty /\
  type_memory_bytes ce ty < 2 ** 64 /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  ce.ce_var_type id = SOME ty ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ ce
    (stmt_env ce lctx rty (Assign (BaseTarget (NameTarget id)) e))
    (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  rename1 `stmt_env ce lctx rty (Assign (BaseTarget (NameTarget id)) e) sa =
    (ce',sf)` >>
  `~(has_length_word (expr_type e) /\ is_empty_value_expr e)` by
    metis_tac[is_empty_value_expr_def] >>
  drule_all widened_assignment_code >> strip_tac >>
  qpat_x_assum `ce' = ce` SUBST_ALL_TAC >>
  rename1 `unwrap_value ce vv sm = (op,sB)` >>
  `lower_value compile_expr ce (expr_type e) e sa = (op,sB)` by
    (pure_rewrite_tac[lower_value_def, comp_bind_def] >>
     asm_rewrite_tac[] >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (drule assign_local_admissible_rhs >> simp[]) >>
  `!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x`
    by metis_tac[ret_pc_ok_def] >>
  `expr_sim_ptr d ctx PG func ce cx (expr_type e) e es` by
    metis_tac[body_expr_ptr_ok_def] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then drule_all >> simp[gas_outcome_ptr_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >> (
qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_ptr_at_marked] >> strip_tac
  >- (
qpat_x_assum `r = OK t` SUBST_ALL_TAC >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  `sa.cs_next_var <= sB.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `local_ptrs_reserved ce sB` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `(!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sB x) /\
   (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sB x)` by
    metis_tac[not_fresh_at_mono] >>
  `~t.vs_halted` by
    (drule gas_marked_exec_ptr_exec >> strip_tac >>
     qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> metis_tac[gas_marked_path_exec,gas_path_normal]) >>
  `~is_word_type (post_value_type ce e)` by
    (qpat_assum `e = Call _ _ _ _` SUBST_ALL_TAC >>
     drule retained_intcall_physical_layout >> metis_tac[expr_type_def]) >>
  `ptr_buf_ok ce e op G t` by
    (qpat_assum `e = Call _ _ _ _` SUBST_ALL_TAC >> fs[]) >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx))
    (es,s0,G0,tn0) marks (INL v) (es_end with gas_obs := []) G tn (OK t)` by
    fs[gas_marked_exec_ptr_def] >>
  `ptr_val_ok cx (post_value_type ce e) v op G tn t` by
    (qpat_assum `e = Call _ _ _ _` SUBST_ALL_TAC >> simp[]) >>
  `expr_post ctx func ce cx e es sa sB s0
    (es_end with gas_obs := []) v op t` by metis_tac[] >>
  drule_all widened_assign_retained_read_continuation_ptr >> strip_tac >>
  rename1 `gas_marked_exec_ptr _ _ _ _ _ _ (INL ()) ee1 Gf tf (OK u)` >>
  qexistsl_tac [`INL ()`,`ee1`,`Gf`,`tf`,`OK u`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  disj1_tac >> simp[stmt_lands_def,cenv_top_ext_refl,ghost_inv_gas_obs] >>
  conj_tac
  >- (`acyclic_struct_metadata ce.ce_struct_fields` by fs[body_inv_def] >>
      `~block_is_terminated sm` by
        (qpat_assum `e = Call _ _ _ _` SUBST_ALL_TAC >>
         qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
         simp[Once compile_expr_def] >> metis_tac[compile_intcall_open]) >>
      `~block_is_terminated sB` by metis_tac[unwrap_value_open] >>
      drule_all compile_assign_value_memory_open >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sB x` by metis_tac[not_fresh_at_mono] >>
      qpat_x_assum `!x. not_fresh_at sB x ==> _` drule >>
      qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[expr_post_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `not_fresh_at sB x` by metis_tac[not_fresh_at_mono] >>
  qpat_x_assum `!x. not_fresh_at sB x ==> _` drule >>
  qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >> simp[ghost_kept_def]
  ) >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[expr_exit_def]) >>
  qpat_x_assum `res = INR ex` SUBST_ALL_TAC >>
  qexistsl_tac [`INR ex`,`es_end`,`G`,`tn`,`r`] >> conj_tac
  >- (drule assign_local_admissible_run >> strip_tac >>
      qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_ptr_def] >> strip_tac >>
      qpat_assum `e = Call _ _ _ _` SUBST_ALL_TAC >>
      simp[bind_def]) >>
  disj2_tac >> simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]
  )) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  irule assign_local_exempt >> simp[] >>
  metis_tac[gas_exempt_cert_unforce_result]
QED
