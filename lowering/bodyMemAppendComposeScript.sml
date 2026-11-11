(* Counted RHS composition for word storage Append. *)
Theory bodyMemAppendCompose
Ancestors
  bodyMemAppendPath bodyMemAppendFacts stmtSimAppendStorageCompose
  stmtSimForced exprSimMemDefs exprSimDefs stmtSimDefs stmtSimProps
  loweringPosts exprSimProps exprOperandVar exprLoweringProps emitHelperProps
  compileEnv exprLowering emitHelper freshWrites gasOutcome gasSummary fragGasMode
  vyperInterpreter vyperState venomState venomInst venomExecSemantics
  bodyMemoryDefs vyperStorage vyperStorageBackend list finite_map
Libs
  monadsyntax

Theorem append_registers_compose_mem[local]:
  sa.cs_next_var <= sm.cs_next_var /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x s1 = SOME w) /\
  (!x w. not_fresh_at sm x /\ lookup_var x s1 = SOME w ==>
    lookup_var x s2 = SOME w) ==>
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x s2 = SOME w)
Proof
  rpt strip_tac >>
  `not_fresh_at sm x` by fs[not_fresh_at_def] >>
  first_x_assum irule >> simp[] >> first_x_assum irule >> simp[]
QED

Theorem compile_append_storage_word_stmt_frag_mem:
  eval_target_place cx (TopLevelNameTarget nid) es =
    (INL (StoragePlace tr slot (ArrayTV tv (Dynamic cap))),es) /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  FLOOKUP cenv.ce_module_vars nid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  cenv.ce_module_var_type nid = SOME (ArrayT elem (Dynamic cap)) /\
  cenv.ce_module_dynarray_capacity nid = cap /\
  is_word_type elem /\ type_memory_bytes cenv elem = 32 /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
  type_slot_size tv = 1 /\ cap < dimword (:256) /\
  (!gs v es1. (do result <- eval_expr cx e; read_result cx result od)
      (es with gas_obs := gs) = (INL v,es1) ==>
    encode_value tv v = SOME [(0,typed_val_to_w256 etv v)]) /\
  expr_sim_mem ctx func cenv cx elem e es ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Append (TopLevelNameTarget nid) e))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all append_storage_word_code_parts >> strip_tac >> gvs[] >>
  rename1 `lower_value _ _ _ _ sa = (op,sB)` >>
  drule_all append_storage_word_code_frame >> strip_tac >>
  drule append_toplevel_place_any >>
  disch_then (mp_tac o MATCH_MP eval_append_storage_bind) >>
  disch_then (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  drule forced_then_admissible >> strip_tac >>
  `~block_is_terminated sb` by metis_tac[append_storage_word_suffix_open_mem] >>
  irule forced_then_outcome >> conj_tac
  >- (rpt strip_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]) >>
  qexists_tac `\v ee t.
    expr_post ctx func cenv cx e es sa sB s0 ee v op t /\
    expr_store_bound cx elem v op t /\
    t.vs_current_bb = sB.cs_current_bb /\ t.vs_inst_idx = LENGTH sB.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` >>
  conj_tac
  >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
      `encode_value tv v = SOME [(0,typed_val_to_w256 etv v)]` by metis_tac[] >>
      qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
      `eval_operand op t = SOME (typed_val_to_w256 etv v)` by
        (gvs[expr_val_rel_def] >> metis_tac[]) >>
      `sB.cs_next_var <= sb.cs_next_var /\ sa.cs_next_var <= sB.cs_next_var` by
        (drule (cj 2 compile_expr_grows) >> strip_tac >>
         drule append_storage_word_suffix_grows_mem >> simp[]) >>
      `local_ptrs_reserved cenv sB` by
        (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
      `!x. op = Var x ==> not_fresh_at sB x` by
        metis_tac[compile_lower_value_var] >>
      `alloca_inv t` by fs[stmt_state_rel_def] >>
      Cases_on `append_place cx (StoragePlace tr slot
        (ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid)))) v ee` >>
      rename1 `_ = (res,ee')` >>
      drule_all append_storage_word_value_path_mem >>
      disch_then (qspecl_then [`lctx`, `RetQ`] mp_tac) >>
      disch_then (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
      `ee'.gas_obs = []` by
        (drule append_storage_place_preserves_gas >> simp[]) >>
      `ee' with gas_obs := [] = ee'` by
        simp[evaluation_state_component_equality] >>
      disch_then DISJ_CASES_TAC
      >- (pop_assum strip_assume_tac >>
          `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t' = SOME w` by
            (rpt strip_tac >> irule append_registers_compose_mem >>
             qexistsl_tac [`s0`, `t`, `sa`, `sB`] >> simp[]) >>
          qexistsl_tac [`res`, `ee'`, `r`] >>
          conj_tac >- metis_tac[append_storage_place_gas_obs] >>
          simp[cenv_top_ext_refl] >> disj1_tac >>
          irule return_buf_frame_frame >>
          qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]) >>
      pop_assum strip_assume_tac >>
      qexistsl_tac [`res`, `ee'`, `r`] >>
      conj_tac >- metis_tac[append_storage_place_gas_obs] >>
      simp[] >> disj2_tac >> gen_tac >>
      drule_all append_storage_place_exit_transport >> simp[]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sB`, `op`, `s0`] mp_tac) >>
  simp[expr_store_bound_def]
QED
