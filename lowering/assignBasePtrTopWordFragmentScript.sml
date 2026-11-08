(* Scalar storage/transient assignment through the checked single-store path. *)
Theory assignBasePtrTopWordFragment
Ancestors assignTuplePtrStorage assignBasePtrCleanStorage
  stmtSimAssignStorage stmtSimForced stmtSimProps exprSimProps exprSimDefs
  bodyPtrDefs stmtFragPtr gasSummaryComposePtr gasExemptCert fragGasPathPtr
  fragGasPath fragGasMode gasSummary gasSummaryCompose gasContext
  exprLoweringProps emitHelperProps emitHelper exprLowering stmtLowering
  compileEnv loweringPosts venomState venomInst vyperState vyperStorageBackend
  ptrDiscipline stmtSimDeclMem
  vyperStorageLayoutSafety accountsRelProps exprSimTopLevelProps finite_map list
Libs monadsyntax

Theorem compile_assign_storage_stmt_frag_ptr:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\ type_slot_size tvt = 1 /\
  cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_var_type (src,id) = SOME vtyp /\ is_word_type vtyp /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
  (!gs v es1. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gs) = (INL v,es1) ==>
     encode_value tvt v = SOME [(0,typed_val_to_w256 etv v)]) /\
  expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Assign (BaseTarget (TopLevelNameTarget (src,id))) e))
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e)) es
Proof
  strip_tac >> simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  `FLOOKUP cenv.ce_module_vars (src,id) =
    SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (irule toplevel_storage_ce_vars >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  drule_all assign_storage_word_code_parts >> strip_tac >> gvs[] >>
  drule_all eval_assign_toplevel_action >>
  disch_then (qspec_then `e` assume_tac) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule forced_then_admissible >>
     qexistsl_tac [`write_storage_slot cx tr (n2w slot) tvt`, `lctx`] >> metis_tac[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
    by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then drule_all >> simp[gas_outcome_ptr_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_summary_ptr_at_marked] >> strip_tac
      >- suspend "normal" >>
      `?ex. res = INR ex` by (Cases_on `res` >> gvs[expr_exit_def]) >> gvs[] >>
      qexistsl_tac [`INR ex`, `es_end`, `G`, `tn`, `r`] >> conj_tac
      >- (irule gas_marked_exec_ptr_bind_exception >> simp[]) >>
      disj2_tac >> simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  once_rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]
QED

Resume compile_assign_storage_stmt_frag_ptr[normal]:
  gvs[] >> drule gas_marked_exec_ptr_exec >> strip_tac >>
  `post_value_type cenv e = expr_type e` by
    metis_tac[loweringPostsTheory.post_value_type_word] >>
  `encode_value tvt v = SOME [(0,typed_val_to_w256 etv v)]` by
    (qpat_x_assum `!gs v es1. _ ==> encode_value _ _ = _` irule >>
     fs[gas_marked_exec_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t /\
   eval_operand op t = SOME (typed_val_to_w256 etv v)` by
    (fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `op_taint tn op = {}` by fs[ptr_val_ok_def] >>
  `declared_storage_region cx src id [] = SOME (tr,n2w slot,tvt)` by
    simp[declared_storage_region_def] >>
  drule_all storage_dead_update_word_region >> strip_tac >>
  Cases_on `write_storage_slot cx tr (n2w slot) tvt v (es_end with gas_obs := [])` >>
  rename1 `_ = (res,ee)` >>
  drule_all stmt_state_rel_write_storage_word >> strip_tac >> gvs[] >>
  `compile_store_at_loc cenv.ce_imm_alloca (Lit (n2w slot)) op
    (SOME (if tr then LocTransient else LocStorage)) sb' = ((),sb)` by
    (Cases_on `tr` >> gvs[compile_store_at_loc_def]) >>
  suspend "store"
QED

Resume compile_assign_storage_stmt_frag_ptr[store]:
  `eval_operand (Lit (n2w slot)) t = SOME (n2w slot) /\
   op_taint tn (Lit (n2w slot)) = {}` by simp[eval_operand_def, op_taint_def] >>
  `~t.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all emit_storage_zero_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `cx_dead cx`] assume_tac) >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by simp[] >>

  `sb.cs_current_bb = sb'.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sb'.cs_current_insts)` by
    (Cases_on `tr` >> gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, emit_def]) >>
  `~block_is_terminated sb` by
    (Cases_on `tr` >> gvs[] >> drule emit_void_nonterminator_open >>
     simp[is_terminator_def]) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ _ _ _ tf (OK u)` >>
  `~u.vs_halted /\ (!x. lookup_var x u = lookup_var x t)` by
    (Cases_on `tr` >> simp[Abbr `u`, tstore_def, sstore_def, lookup_var_def]) >>
  `!x. op_taint tf (Var x) = op_taint tn (Var x)` by
    (`tf.t_var = tn.t_var` by
       (simp[Abbr `tf`] >> irule (cj 2 clean_storage_step_taint_ptr) >>
        simp[] >>
        Cases_on `tr` >> simp[tstore_def, sstore_def]) >>
     simp[op_taint_def]) >>
  suspend "finish"
QED

Resume compile_assign_storage_stmt_frag_ptr[finish]:
  `stmt_state_rel ctx func cenv cx ee u` by
    (simp[Abbr `u`, stmt_state_rel_inst_idx]) >>
  `ghost_inv d cenv cx ee G tf u` by
    (simp[Abbr `u`, Abbr `tf`] >>
     irule (cj 2 storage_word_endpoint_inv_ptr) >>
     simp[] >> metis_tac[]) >>
  `!tail. write_storage_slot cx tr (n2w slot) tvt v (es_end with gas_obs := tail) =
    (INL (),ee with gas_obs := tail)` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     once_rewrite_tac[write_storage_slot_gas_obs] >> strip_tac >>
     gen_tac >> once_rewrite_tac[write_storage_slot_gas_obs] >> gvs[]) >>
  qexistsl_tac [`INL ()`, `ee`, `G`, `tf`, `OK u`] >> conj_tac
  >- (irule (SIMP_RULE std_ss [APPEND_NIL]
       (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal)) >>
      qexistsl_tac [`G`, `es_end`, `t`, `tn`, `v`] >>
      simp[gas_marked_exec_ptr_def]) >>
  `ghost_inv d cenv cx (ee with gas_obs := []) G tf u` by
    simp[ghost_inv_gas_obs] >>
  disj1_tac >> simp[stmt_lands_def, cenv_top_ext_refl] >>
  fs[expr_post_def, ghost_kept_def] >>
  Cases_on `tr` >> gvs[Abbr `u`, sstore_def, tstore_def] >> metis_tac[]
QED
Finalise compile_assign_storage_stmt_frag_ptr

Theorem compile_assign_storage_typed_stmt_frag_ptr:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  expr_type e = typ /\ is_word_type typ /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_var_type (src,id) = SOME vtyp /\ is_word_type vtyp /\
  (!gs v es1. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gs) = (INL v,es1) ==> value_has_type tvt v) /\
  expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Assign (BaseTarget (TopLevelNameTarget (src,id))) e))
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e)) es
Proof
  strip_tac >> irule compile_assign_storage_stmt_frag_ptr >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> irule encode_value_word_typed >> metis_tac[]) >>
  metis_tac[exprSimUnwrapTheory.word_type_slot_size]
QED
