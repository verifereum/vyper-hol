(* Expression/suffix composition for pointer-safe storage append. *)
Theory stmtAppendStorageComposePtr
Ancestors
  appendStorageComposeFactsPtr appendStorageSuccessPostPtr
  bodyPtrDefs stmtFragPtr stmtAbortPtr gasSummaryComposePtr stmtSimForced
  stmtSimAppendStorageCompose exprSimProps exprOperandVar exprLoweringProps
  compileEnv loweringStateRelDefs loweringPosts stmtSimDefs stmtSimProps finite_map words
  vyperInterpreter vyperState vyperValue venomState fragGasPathPtr gasExemptCert
  gasSummary gasSummaryCompose gasStorage fragGasMode fragGasPath gasContext appendStorageGhostPtr ptrDiscipline
  vyperStorageTrace vyperStorageFootprint
  vyperFiniteStoragePreservation vyperStoragePlaceRegion
  vyperStorageBackend stmtAppendStoragePathPtr stmtSimAppendStorage
  list fragExec exprSimDefs ptrSafetyTransport

Theorem compile_append_storage_word_stmt_frag_ptr:
  eval_target_place cx (TopLevelNameTarget nid) es =
    (INL (StoragePlace tr slot (ArrayTV tv (Dynamic cap))),
     es with storage_trace := es.storage_trace ++
       [StorageRoot tr offset (ArrayTV tv (Dynamic cap))]) /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  FLOOKUP cenv.ce_module_vars nid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  cenv.ce_module_var_type nid = SOME (ArrayT elem (Dynamic cap)) /\
  cenv.ce_hashmap_info nid = NONE /\
  cenv.ce_module_dynarray_capacity nid = cap /\
  is_word_type elem /\ type_memory_bytes cenv elem = 32 /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
  type_slot_size tv = 1 /\ cap < dimword (:256) /\
  well_formed_type_value (ArrayTV tv (Dynamic cap)) /\
  (!gs v es1.
     bind (eval_expr cx e) (read_result cx)
       (es with <|gas_obs := gs; storage_trace := es.storage_trace ++
          [StorageRoot tr offset (ArrayTV tv (Dynamic cap))]|>) =
       (INL v,es1) ==>
     encode_value tv v = SOME [(0,typed_val_to_w256 etv v)] /\
     value_has_type tv v) /\
  expr_sim_ptr d ctx PG func cenv cx elem e
    (es with storage_trace := es.storage_trace ++
      [StorageRoot tr offset (ArrayTV tv (Dynamic cap))]) ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Append (TopLevelNameTarget nid) e))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  strip_tac >> simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_all append_storage_word_code_parts >> strip_tac >>
  rename1 `lower_value _ _ _ _ sa = (op,sB)` >>
  rpt (qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC) >>
  drule_all append_storage_word_code_frame >> strip_tac >>
  drule append_toplevel_place_any >> strip_tac >>
  drule eval_append_storage_bind >> disch_then (qspec_then `e` assume_tac) >>
  qmatch_asmsub_abbrev_tac
    `expr_sim_ptr d ctx PG func cenv cx elem e es_rhs` >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es_rhs` by
    (simp[Abbr `es_rhs`] >> metis_tac[append_forced_admissible]) >>
  `!x. op = Var x ==> not_fresh_at sB x` by metis_tac[compile_lower_value_var] >>
  `sa.cs_next_var <= sB.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `local_ptrs_reserved cenv sB` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `eval_stmt _ _ = _` SUBST1_TAC >>
  irule gas_outcome_ptr_record_storage_event >> simp[] >> suspend "rhs"
QED

Resume compile_append_storage_word_stmt_frag_ptr[rhs]:
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sB`, `op`, `s0`, `G0`, `tn0`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      `valid_horizon cx st0 H es.storage_trace` by
        fs[Abbr `es_rhs`, valid_horizon_def] >>
      `stmt_state_rel H ctx func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv H d cenv cx es G0 tn0 s0` by metis_tac[] >>
      `storage_well_formed_on cx es_rhs (FST H) <=>
       storage_well_formed_on cx es (FST H)` by
        (irule storage_well_formed_on_backends >> simp[Abbr `es_rhs`]) >>
      simp[Abbr `es_rhs`]) >>
  simp[gas_outcome_ptr_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      irule gas_bad_storage_at_bind_left >>
      simp[storage_trace_frame_append_place])
  >- suspend "summary" >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  once_rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]
QED

Resume compile_append_storage_word_stmt_frag_ptr[summary]:
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_ptr_at_marked] >> strip_tac >>
  Cases_on `?H. valid_horizon cx st0 H es_end.storage_trace`
  >- (pop_assum (qx_choose_then `H0` assume_tac) >>
      qpat_assum `!H. valid_horizon _ _ _ _ ==> _`
        (qspec_then `H0` mp_tac) >> simp[] >> strip_tac
      >- suspend "operand" >>
      `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
      qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      irule gas_summary_ptr_at_bind_exception >>
      qexistsl_tac [`G`, `tn`, `ex`, `es_end`, `r`] >>
      simp[] >> rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ _ _ ==> _`
        (qspec_then `H` mp_tac) >> simp[] >>
      simp[gas_marked_exec_ptr_def, stmt_exit_ptr_def] >>
      metis_tac[expr_exit_INR_type]) >>
  qexists_tac `marks` >> disj1_tac >>
  irule gas_bad_storage_at_bind_left >>
  simp[storage_trace_frame_append_place] >>
  irule gas_bad_storage_at_no_horizon >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume compile_append_storage_word_stmt_frag_ptr[operand]:
  gvs[] >>
  qpat_x_assum `!st. eval_target_place _ _ _ = _` kall_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `fn_has_code sa sb func` kall_tac >>
  qpat_x_assum `fn_has_code sa sB func` kall_tac >>
  qpat_x_assum `gas_admissible (bind _ _) _ _` kall_tac >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `eval_operand op t = SOME (typed_val_to_w256 etv v)` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  drule gas_marked_exec_ptr_exec >> strip_tac >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     metis_tac[gas_marked_path_exec, gas_path_normal]) >>
  `encode_value tv v = SOME [(0,typed_val_to_w256 etv v)] /\
   value_has_type tv v` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     disch_then (qspec_then `[]` strip_assume_tac o CONJUNCT1) >>
     metis_tac[]) >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
       MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H)` by
    (rpt strip_tac >>
     qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     `valid_horizon cx st0 H es_rhs.storage_trace` by
       (drule_all valid_horizon_frame >>
        simp[storage_trace_frame_bind, evaluate_storage_trace_frame,
             storage_trace_frame_read_result]) >>
     fs[Abbr `es_rhs`, valid_horizon_def, storage_observations_ok_def,
        storage_trace_regions_def, EVERY_MEM]) >>
  `MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H0)` by metis_tac[] >>
  `(if tr then tload slot t else sload slot t) =
   lookup_storage slot (get_storage cx (es_end with gas_obs := []) tr)` by
    (irule declared_storage_head_agree >> conj_tac
     >- (goal_assum (drule_at Any) >> simp[type_slot_size_def]) >>
     goal_assum (drule_at Any)) >>
  `~t.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `FLOOKUP cenv.ce_module_vars _ = _` kall_tac >>
  qpat_x_assum `cenv.ce_module_var_type _ = _` kall_tac >>
  qpat_x_assum `!gs v es1. bind _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` kall_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!aid b. FLOOKUP _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `!aid off sz. _ ==> mem_bytes_at _ _ _ = _` kall_tac >>
  qpat_x_assum `locals_kept _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` kall_tac >>
  `stor_taint_ok H0 cx tn t` by metis_tac[ghost_inv_def] >>
  `t.vs_call_ctx.cc_address = cx.txn.target` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `key_taint (if tr then tn.t_trans else tn.t_stor) slot = {}` by
    (irule declared_header_key_taint_empty >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`mid`, `n`, `[]`,
       `ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid))`] >>
     simp[type_slot_size_def]) >>
  `op_taint tn op = {}` by metis_tac[ptr_val_ok_def] >>
  suspend "suffix"
QED

Resume compile_append_storage_word_stmt_frag_ptr[suffix]:
  Cases_on `append_place cx (StoragePlace tr slot
    (ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid)))) v
    (es_end with gas_obs := [])` >>
  rename1 `_ = (res1, ee1)` >>
  `!tail. append_place cx (StoragePlace tr slot
      (ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid)))) v
      (es_end with gas_obs := tail) = (res1, ee1 with gas_obs := tail)` by
    (gen_tac >> drule append_storage_place_gas_obs >>
     disch_then (qspec_then `tail` mp_tac) >> simp[]) >>
  `ee1 with gas_obs := [] = ee1` by
    (qpat_assum `!tail. append_place _ _ _ _ = _`
       (qspec_then `[]` mp_tac) >> simp[] >> metis_tac[]) >>
  Cases_on `w2n (if tr then tload slot t else sload slot t) <
    cenv.ce_module_dynarray_capacity nid`
  >- suspend "stored" >>
  suspend "full"
QED

Resume compile_append_storage_word_stmt_frag_ptr[full]:
  `cenv.ce_module_dynarray_capacity nid <=
    w2n (if tr then tload slot t else sload slot t)` by decide_tac >>
  drule_all append_storage_word_abort_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`,
    `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>`] strip_assume_tac) >>
  `res1 = INR (Error (RuntimeError "append full storage array"))` by
    (`cenv.ce_module_dynarray_capacity nid <= w2n
       (lookup_storage slot (get_storage cx (es_end with gas_obs := []) tr))`
       by metis_tac[] >>
     drule append_storage_full >>
     disch_then (qspecl_then [`v`, `tv`] mp_tac) >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INR (Error (RuntimeError "append full storage array"))`,
    `ee1`, `G'`, `tn'`, `Abort Revert_abort t'`] >> conj_tac
  >- (irule (SIMP_RULE std_ss [APPEND_NIL]
        (Q.INST [`right` |-> `[]`] gas_marked_source_bind_normal)) >>
      qexistsl_tac [`es_end`, `t`, `v`] >>
      simp[gas_marked_exec_def]) >>
  gen_tac >> strip_tac >>
  `valid_horizon cx st0 H es_end.storage_trace` by
    (`valid_horizon cx st0 H (es_end with gas_obs := []).storage_trace` by
       metis_tac[valid_horizon_frame, storage_trace_frame_append_place] >> fs[]) >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _`
    (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  conj_tac
  >- (irule (SIMP_RULE std_ss [APPEND_NIL]
        (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal)) >>
      qexistsl_tac [`G`, `es_end`, `t`, `tn`, `v`] >>
      simp[gas_marked_exec_ptr_def] >>
      irule gas_path_ptr_from_no_dead >> goal_assum (drule_at Any)) >>
  simp[exit_result_def, stmt_exit_ptr_def, expr_exit_def]
QED

Resume compile_append_storage_word_stmt_frag_ptr[stored]:
  qmatch_asmsub_abbrev_tac `len < cenv.ce_module_dynarray_capacity nid` >>
  `len = w2n (if tr then tload slot t else sload slot t)` by simp[Abbr `len`] >>
  drule_all append_storage_word_success_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`,
    `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>`] strip_assume_tac) >>
  rename1 `state_frame u = _` >>
  `len = w2n (lookup_storage slot
    (get_storage cx (es_end with gas_obs := []) tr))` by metis_tac[] >>
  `!x a. not_fresh_at sB x /\ lookup_var x t = SOME a ==>
    lookup_var x u = SOME a` by metis_tac[] >>
  drule_all append_storage_word_success_post >> strip_tac >>
  `ret_pc_ok cenv sB t` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sB x` by metis_tac[not_fresh_at_mono] >>
  `len = w2n (lookup_storage slot
    (if tr then contract_transient t else contract_storage t))` by
    (qpat_x_assum `len = w2n (if tr then _ else _)` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `tr` >>
     simp[tload_def, sload_def]) >>
  `!x. not_fresh_at sB x ==> FLOOKUP G' x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x) /\
     lookup_var x u = lookup_var x t` by metis_tac[] >>
  drule_all append_storage_word_ghost_post >> strip_tac >>
  suspend "stored_finish"
QED

Resume compile_append_storage_word_stmt_frag_ptr[stored_finish]:
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`res1`, `ee1`, `G'`, `tn'`,
    `OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)`] >> conj_tac
  >- (irule (SIMP_RULE std_ss [APPEND_NIL]
        (Q.INST [`right` |-> `[]`] gas_marked_source_bind_normal)) >>
      qexistsl_tac [`es_end`, `t`, `v`] >>
      simp[gas_marked_exec_def]) >>
  gen_tac >> strip_tac >>
  `valid_horizon cx st0 H es_end.storage_trace` by
    (`valid_horizon cx st0 H (es_end with gas_obs := []).storage_trace` by
       metis_tac[valid_horizon_frame, storage_trace_frame_append_place] >> fs[]) >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _`
    (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  conj_tac
  >- (irule (SIMP_RULE std_ss [APPEND_NIL]
        (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal)) >>
      qexistsl_tac [`G`, `es_end`, `t`, `tn`, `v`] >>
      simp[gas_marked_exec_ptr_def] >>
      irule gas_path_ptr_from_no_dead >> goal_assum (drule_at Any)) >>
  qpat_x_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H)` by metis_tac[] >>
  drule_all append_storage_word_success_post >> strip_tac >>
  drule_all append_storage_word_ghost_post >> strip_tac >>
  `storage_well_formed_on cx ee1 (FST H)` by
    (mp_tac (Q.INST
       [`cx` |-> `cx`,
        `regions` |-> `FST (H : (bool # 256 word # type_value) list # num list)`,
        `st` |-> `es_end with gas_obs := []`,
        `st'` |-> `ee1`, `b` |-> `tr`, `root` |-> `slot`,
        `tv` |-> `ArrayTV tv (Dynamic cap)`, `path` |-> `[]`,
        `delta` |-> `0`, `slot` |-> `slot`, `etv` |-> `tv`,
        `n` |-> `cap`, `v` |-> `v`, `res` |-> `res1`]
       append_subregion_preserves_storage_well_formed_on) >>
     fs[storage_subregion_def, valid_horizon_def]) >>
  disj1_tac >> simp[] >>
  `sb.cs_current_bb = sB.cs_current_bb` by
    (drule append_storage_word_suffix_structure >> simp[same_blocks_def]) >>
  `~block_is_terminated sb` by
    (irule primitive_append_nonterminator_open >> goal_assum (drule_at Any) >>
     Cases_on `tr` >> simp[venomInstTheory.is_terminator_def]) >>
  simp[stmt_lands_def, stmt_state_rel_inst_idx, cenv_top_ext_refl] >>
  conj_tac
  >- (qpat_x_assum `ghost_inv H d cenv cx ee1 G' tn' u` mp_tac >>
      rpt (pop_assum kall_tac) >>
      `u with vs_inst_idx := LENGTH sb.cs_current_insts =
       u with <|vs_prev_bb := u.vs_prev_bb;
                vs_current_bb := u.vs_current_bb;
                vs_inst_idx := LENGTH sb.cs_current_insts|>` by
        simp[venom_state_component_equality] >>
      metis_tac[ghost_inv_jump_to]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sB x` by metis_tac[not_fresh_at_mono] >>
      simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `ghost_kept cenv es sa G0 tn0 s0 G' tn'` by metis_tac[] >>
  pop_assum mp_tac >> rpt (pop_assum kall_tac) >>
  simp[ghost_kept_def]
QED

Finalise compile_append_storage_word_stmt_frag_ptr
