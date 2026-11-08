(* Compiler decomposition for the supported storage assignment fragment. *)
Theory assignBasePtrStorageFragment
Ancestors assignBasePtrStorageCopyCallResidual assignBasePtrStorageTypes assignBasePtrStorageContinuation assignBasePtrStorageSemantic
  assignBasePtrStorageGhost stmtSimAssignStorage bodyPtrDefs stmtFragPtr
  stmtLowering exprLowering context compileEnv loweringPosts finite_map
  exprSimProps stmtSimProps stmtLoweringMono stmtSimForced gasSummaryComposePtr
  gasExemptCert fragGasPathPtr fragGasPath fragGasMode gasSummary exprSimHypsDefs
  exprSimDefs fragExec exprLoweringProps vyperState assignBasePtrStorageDirect
  exprOperandVar venomState vyperTyping vyperStorageBackend
  assignBasePtrStorageExtent assignBasePtrStorageLoop exprSimHyps valueEncodingProps
  list exprOpenTerminals exprOpenPrimitives emitHelperProps venomInst bodySimStmtCases exprSimSource
Libs monadsyntax

Theorem assign_base_storage_code_parts:
  stmt_env cenv lctx ty (Assign (BaseTarget (TopLevelNameTarget nid)) e)
    sa = (c,sf) /\
  FLOOKUP cenv.ce_module_vars nid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  cenv.ce_hashmap_info nid = NONE /\
  cenv.ce_module_var_type nid = SOME vtyp /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
  c = cenv /\
  ?vv sV sB op.
    compile_expr cenv (expr_type e) e sa = (vv,sV) /\
    unwrap_value cenv vv sV = (op,sB) /\
    lower_value compile_expr cenv (expr_type e) e sa = (op,sB) /\
    compile_assign_value cenv (Lit slot)
      (if tr then LocTransient else LocStorage) op (is_word_type vtyp)
      (vv_location vv) vtyp (lowered_value_type cenv e)
      (case vtyp of ArrayT elem (Dynamic _) =>
         SOME ((type_memory_bytes cenv elem + 31) DIV 32,
               type_memory_bytes cenv elem) | _ => NONE)
      (type_memory_bytes cenv vtyp) sB = ((),sf)
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
    compile_get_target_ptr_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >>
  Cases_on `tr` >> simp[comp_return_def] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `_ = (vv,sV)` >> simp[] >>
  Cases_on `unwrap_value cenv vv sV` >> rename1 `_ = (op,sB)` >>
  simp[] >> strip_tac >> gvs[] >>
  simp[lower_value_def, comp_bind_def] >>
  qpat_x_assum `(\(_0,cs'). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  Cases_on `_0` >> gvs[]
QED

Theorem assign_base_storage_no_empty_shortcut:
  supported_storage_type tops ty /\
  (!elem n. ty <> ArrayT elem (Dynamic n)) ==>
  ~has_length_word ty
Proof
  strip_tac >> drule assign_base_storage_not_bytestring >> strip_tac >>
  Cases_on `ty` >> gvs[has_length_word_def] >>
  Cases_on `b` >> gvs[has_length_word_def]
QED

Theorem assign_base_storage_model_lookup[local]:
  !n. lookup_var x (store_copy_prefix loc b k t n) = lookup_var x t
Proof
  Induct >> simp[assign_base_store_prefix_zero, assign_base_store_prefix_suc] >>
  Cases_on `loc = LocStorage` >> gvs[sstore_def, tstore_def, lookup_var_def]
QED

Theorem assign_base_storage_suffix_open[local]:
  ~is_bytestring_type ty /\ ~block_is_terminated sa /\
  compile_assign_value cenv (Lit k) (if tr then LocTransient else LocStorage)
    (Var root) F loc ty ty NONE capacity sa = (z,sb) ==>
  ~block_is_terminated sb
Proof
  strip_tac >> drule assign_base_storage_direct_code >> strip_tac >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> Cases_on `capacity <= 32` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      drule emit_void_terminated >>
      Cases_on `tr` >> simp[is_terminator_def]) >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[compile_word_copy_loop_open]
QED

Theorem compile_assign_storage_copy_eq_frag_ptr:
  post_value_type cenv e = expr_type e /\
  body_inv tops bctx cenv cx /\ expr_sim_inv cenv cx env es /\
  expr_body_pre cenv cx env e es /\ supported_expr tops e /\
  type_stmt env ret (Assign (BaseTarget (TopLevelNameTarget nid)) e) = SOME env' /\
  supported_storage_type tops (expr_type e) /\ ~is_word_type (expr_type e) /\
  (!elem n. expr_type e <> ArrayT elem (Dynamic n)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  well_formed_type_value tv /\
  (storage_vars_rel cenv cx /\ transient_vars_rel cenv cx ==>
   FLOOKUP cenv.ce_module_vars nid =
    SOME (if tr then TransientLoc k else StorageLoc k)) /\
  cenv.ce_hashmap_info nid = NONE /\ cenv.ce_module_var_type nid = SOME (expr_type e) /\
  declared_storage_region cx mid id [] = SOME (tr,k,tv) /\
  w2n k + type_slot_size tv <= dimword (:256) /\
  (!mid' id' subs' k' tv'.
     declared_storage_region cx mid' id' subs' = SOME (tr,k',tv') /\
     (k',tv') <> (k,tv) ==>
     ranges_disjoint (w2n k) (type_slot_size tv) (w2n k') (type_slot_size tv')) /\
  eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nid)) e) =
    bind (bind (eval_expr cx e) (read_result cx)) (write_storage_slot cx tr k tv) /\
  (!gs v es1. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
     (INL v,es1) ==> value_has_type tv v) /\
  expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ret (Assign (BaseTarget (TopLevelNameTarget nid)) e))
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nid)) e)) es
Proof
  strip_tac >> simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  `FLOOKUP cenv.ce_module_vars nid =
    SOME (if tr then TransientLoc k else StorageLoc k)` by
    (first_x_assum irule >> fs[stmt_state_rel_def, state_rel_def]) >>
  `~(has_length_word (expr_type e) /\ is_empty_value_expr e)` by
    metis_tac[assign_base_storage_no_empty_shortcut] >>
  drule_all assign_base_storage_code_parts >> strip_tac >>
  qpat_x_assum `~(has_length_word _ /\ _)` kall_tac >> gvs[] >>
  `cs_extends sa sB` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sB sb` by
    metis_tac[cj 1 ci_mono_stmt_helpers, ci_mono_def, pairTheory.SND] >>
  `fn_has_code sa sB func /\ fn_has_code sB sb func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule forced_then_admissible >>
     qexistsl_tac [`write_storage_slot cx tr k tv`, `lctx`] >> metis_tac[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
    by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then drule_all >> simp[gas_outcome_ptr_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >> suspend "summary") >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  once_rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]
QED

Resume compile_assign_storage_copy_eq_frag_ptr[summary]:
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_ptr_at_marked] >> strip_tac
  >- suspend "operand" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexistsl_tac [`INR ex`, `es_end`, `G`, `tn`, `r`] >> conj_tac
  >- (irule gas_marked_exec_ptr_bind_exception >> simp[]) >>
  disj2_tac >> simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]
QED

Resume compile_assign_storage_copy_eq_frag_ptr[operand]:
  gvs[] >>
  drule_all assign_base_store_expr_source >> strip_tac >>
  drule gas_marked_exec_ptr_exec >> strip_tac >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     metis_tac[gas_marked_path_exec, gas_path_normal]) >>
  `value_has_type tv v` by
    (qpat_x_assum `!gs v es1. _ ==> value_has_type _ _` irule >>
     qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> metis_tac[]) >>
  drule_all assign_base_storage_rhs_lowered_type >> strip_tac >>
  drule_all assign_base_typed_assignment_capacity_positive >> strip_tac >>
  `?root. op = Var root` by
    (fs[ptr_buf_ok_def] >> metis_tac[]) >> gvs[] >>
  `lookup_var root t = SOME b` by fs[eval_operand_def] >>
  `ptr_covers G tn root t (type_memory_bytes cenv (lowered_value_type cenv e))` by
    (fs[ptr_covers_def, ptr_buf_ok_def, ptr_val_ok_def, eval_operand_def] >>
     metis_tac[]) >>
  `not_fresh_at sB root` by metis_tac[compile_lower_value_var] >>
  `~t.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  `expr_val_at cenv cx (expr_type e) sa sB (es_end with gas_obs := [])
     v (Var root) t` by
    (qpat_assum `expr_post _ _ _ _ e _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `post_value_type cenv e = _`
       (fn th => rewrite_tac[expr_post_def, th]) >>
     rpt strip_tac >> first_assum ACCEPT_TAC) >>
  suspend "counted"
QED
Resume compile_assign_storage_copy_eq_frag_ptr[counted]:
  `(case expr_type e of ArrayT elem (Dynamic _) =>
      SOME ((type_memory_bytes cenv elem + 31) DIV 32,
            type_memory_bytes cenv elem) | _ => NONE) = NONE` by
    (Cases_on `expr_type e` >> simp[] >> Cases_on `b'` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by simp[] >>
  `compile_assign_value cenv (Lit k) (if tr then LocTransient else LocStorage)
     (Var root) F (vv_location vv) (expr_type e) (lowered_value_type cenv e)
     NONE (type_memory_bytes cenv (expr_type e)) sB = ((),sb)` by metis_tac[] >>
  drule_all assign_base_storage_typed_counted >>
  disch_then (qspecl_then [`cx_dead cx`, `PG`] strip_assume_tac) >>
  suspend "post"
QED

Resume compile_assign_storage_copy_eq_frag_ptr[post]:
  `?writes. encode_value tv v = SOME writes` by
    metis_tac[value_has_type_equiv, optionTheory.IS_SOME_EXISTS] >>
  qmatch_asmsub_abbrev_tac `execution_frame u = execution_frame model` >>
  qabbrev_tac `ee = set_storage cx (es_end with gas_obs := []) tr
    (apply_writes k writes (get_storage cx (es_end with gas_obs := []) tr))` >>
  `write_storage_slot cx tr k tv v (es_end with gas_obs := []) = (INL (),ee)` by
    (simp[Abbr `ee`, write_storage_slot_eq] >>
     fs[stmt_state_rel_def, state_rel_def]) >>
  `w2n b+32*(type_slot_size tv-1) < dimword (:256)` by
    (drule_all assign_base_storage_rhs_bound >> strip_tac >>
     drule_all expr_body_pre_copy_ok >> strip_tac >>
     gvs[type_memory_size_slots] >> decide_tac) >>
  `stmt_state_rel ctx func cenv cx ee model` by
    (simp[Abbr `model`] >> irule assign_base_store_prefix_state_region >>
     simp[] >> metis_tac[]) >>
  `local_ptrs_reserved cenv sB` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     simp[] >> drule (cj 2 compile_expr_grows) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx ee u` by
    (irule assign_base_store_endpoint_state >>
     qexistsl_tac [`model`, `sB`] >> asm_rewrite_tac[] >>
     simp[Abbr `model`, assign_base_storage_model_lookup]) >>
  `!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
     val_in_memory tv v (w2n b) m` by
    (fs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]) >>
  `stor_taint_ok cx tf u` by
    (irule assign_base_store_stor_taint_ok >>
     goal_assum (drule_at (Pat `assign_base_store_frame _ _ _ _ _ _ _ _`)) >>
     simp[] >>
     `stor_taint_ok cx tn t /\ t.vs_call_ctx.cc_address = cx.txn.target` by
       fs[ghost_inv_def, stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
     metis_tac[]) >>
  suspend "ghost"
QED
Resume compile_assign_storage_copy_eq_frag_ptr[ghost]:
  `sa.cs_next_var <= sB.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `ret_pc_ok cenv sB t` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
     fs[expr_post_def]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sB x` by metis_tac[not_fresh_at_mono] >>
  `ee.scopes = (es_end with gas_obs := []).scopes` by simp[Abbr `ee`] >>
  `!x. not_fresh_at sB x ==> FLOOKUP Gf x = FLOOKUP G x /\
     op_taint tf (Var x) = op_taint tn (Var x) /\ lookup_var x u = lookup_var x t`
    by metis_tac[] >>
  drule_all assign_base_store_ghost_post >> strip_tac >>
  suspend "open"
QED

Resume compile_assign_storage_copy_eq_frag_ptr[open]:
  `?gs rv es1. eval_expr cx e (es with gas_obs := gs) = (INL rv,es1)` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `~block_is_terminated sV` by
    (irule compile_expr_open >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     simp[] >>
     `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
       fs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  `~block_is_terminated sB` by metis_tac[unwrap_value_open] >>
  `~block_is_terminated sb` by
    (irule assign_base_storage_suffix_open >>
     goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[assign_base_storage_not_bytestring]) >>
  suspend "finish"
QED

Resume compile_assign_storage_copy_eq_frag_ptr[finish]:
  `!tail. write_storage_slot cx tr k tv v (es_end with gas_obs := tail) =
     (INL (),ee with gas_obs := tail)` by
    (gen_tac >>
     `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
     Cases_on `tr` >>
     simp[Abbr `ee`, write_storage_slot_eq, set_storage_def, get_storage_def]) >>
  qexistsl_tac [`INL ()`, `ee`, `Gf`, `tf`, `OK u`] >> conj_tac
  >- (irule (SIMP_RULE std_ss [APPEND_NIL]
        (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal)) >>
      qexistsl_tac [`G`, `es_end`, `t`, `tn`, `v`] >>
      simp[gas_marked_exec_ptr_def]) >>
  disj1_tac >> simp[stmt_lands_def, cenv_top_ext_refl] >>
  conj_tac >- metis_tac[ghost_inv_gas_obs] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sB x` by metis_tac[not_fresh_at_mono] >>
      fs[expr_post_def] >> metis_tac[]) >>
  fs[ghost_kept_def] >> metis_tac[not_fresh_at_mono]
QED
Finalise compile_assign_storage_copy_eq_frag_ptr


Theorem compile_assign_storage_copy_stmt_frag_ptr:
  body_inv tops bctx cenv cx /\ expr_sim_inv cenv cx env es /\
  expr_body_pre cenv cx env e es /\ supported_expr tops e /\
  type_stmt env ret (Assign (BaseTarget (TopLevelNameTarget nid)) e) = SOME env' /\
  supported_storage_type tops (expr_type e) /\ ~is_word_type (expr_type e) /\
  (!elem n. expr_type e <> ArrayT elem (Dynamic n)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  well_formed_type_value tv /\
  (storage_vars_rel cenv cx /\ transient_vars_rel cenv cx ==>
   FLOOKUP cenv.ce_module_vars nid =
    SOME (if tr then TransientLoc k else StorageLoc k)) /\
  cenv.ce_hashmap_info nid = NONE /\ cenv.ce_module_var_type nid = SOME (expr_type e) /\
  declared_storage_region cx mid id [] = SOME (tr,k,tv) /\
  w2n k + type_slot_size tv <= dimword (:256) /\
  (!mid' id' subs' k' tv'.
     declared_storage_region cx mid' id' subs' = SOME (tr,k',tv') /\
     (k',tv') <> (k,tv) ==>
     ranges_disjoint (w2n k) (type_slot_size tv) (w2n k') (type_slot_size tv')) /\
  eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nid)) e) =
    bind (bind (eval_expr cx e) (read_result cx)) (write_storage_slot cx tr k tv) /\
  (!gs v es1. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
     (INL v,es1) ==> value_has_type tv v) /\
  expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ret (Assign (BaseTarget (TopLevelNameTarget nid)) e))
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nid)) e)) es
Proof
  strip_tac >> Cases_on `post_value_type cenv e = expr_type e`
  >- (mp_tac (SPEC_ALL compile_assign_storage_copy_eq_frag_ptr) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  mp_tac (SPEC_ALL
    assignBasePtrStorageCopyCallResidualTheory.assign_storage_copy_call_frag_ptr) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED
