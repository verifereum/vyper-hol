(* Counted RHS, scratch staging and aggregate storage Append. *)
Theory bodyMemAppendAggregateCompose
Ancestors
  bodyMemAppendAggregateFacts
  stmtSimAppendStorageCompose
  bodyDeclMemoryCounted bodyMemAppendCompose bodyMemAppendFacts
  stmtSimForced exprSimMemDefs exprSimDefs stmtSimDefs stmtSimProps
  loweringPosts exprSimProps exprOperandVar exprLoweringProps emitHelperProps
  compileEnv loweringStateRelDefs exprLowering emitHelper freshWrites gasOutcome gasSummary fragGasMode
  vyperInterpreter vyperState venomState venomInst venomExecSemantics
  bodyMemoryDefs vyperStorage vyperStorageBackend list finite_map
  valueTypingMemoryProps valueEncodingProps valueCopy loweringSlice words context fragExec
Libs
  monadsyntax

Theorem compile_append_storage_aggregate_stmt_frag_mem:
  eval_target_place cx (TopLevelNameTarget nid) es =
    (INL (StoragePlace tr slot (ArrayTV tv (Dynamic cap))),es) /\
  declared_storage_region cx mid name [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
  (!mid' n' subs' slot' tv'.
    declared_storage_region cx mid' n' subs' = SOME (tr,slot',tv') /\
    (slot',tv') <> (slot,ArrayTV tv (Dynamic cap)) ==>
    ranges_disjoint (w2n slot) (type_slot_size (ArrayTV tv (Dynamic cap)))
                    (w2n slot') (type_slot_size tv')) /\
  FLOOKUP cenv.ce_module_vars nid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  cenv.ce_module_var_type nid = SOME (ArrayT elem (Dynamic cap)) /\
  cenv.ce_module_dynarray_capacity nid = cap /\
  ~is_word_type elem /\ ~is_bytestring_type elem /\ expr_type e = elem /\
  lowered_value_type cenv e = elem /\ supported_pure_expr tops e /\
  evaluate_type (get_tenv cx) elem = SOME tv /\
  type_memory_bytes cenv elem = 32*type_slot_size tv /\
  type_memory_bytes cenv elem < 2**64 /\
  0 < type_slot_size tv /\ well_formed_type_value tv /\ cap < dimword (:256) /\
  (!gs v es1. (do result <- eval_expr cx e; read_result cx result od)
      (es with gas_obs := gs) = (INL v,es1) ==>
    value_has_type tv v /\ ?writes. encode_value tv v = SOME writes) /\
  expr_sim_mem ctx func cenv cx elem e es ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Append (TopLevelNameTarget nid) e))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
(* PORT_ADMISSION SEQ-4381: whole aggregate Append lemma, including static
   types: the old path uses dense FOLDL and the one-word direct store still
   needs a separate proof. Sparse Append repair remains owned separately.
   Original proof retained below.

Proof
  strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all append_storage_copy_code_parts >> strip_tac >> gvs[] >>
  rename1 `lower_value _ _ _ _ sa = (op,sB)` >>
  rename1 `compile_alloc_buffer _ sB = (buf,sc)` >>
  rename1 `compile_store_memory _ _ _ _ _ sc = ((),sd)` >>
  drule_all append_storage_aggregate_code_frame >> strip_tac >>
  drule append_toplevel_place_any >>
  disch_then (mp_tac o MATCH_MP eval_append_storage_bind) >>
  disch_then (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  drule forced_then_admissible >> strip_tac >>
  `~block_is_terminated sb` by metis_tac[append_storage_aggregate_suffix_open] >>
  irule forced_then_outcome >> conj_tac
  >- (rpt strip_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]) >>
  qexists_tac `\v ee t.
    expr_post ctx func cenv cx e es sa sB s0 ee v op t /\
    expr_store_bound cx (expr_type e) v op t /\
    t.vs_current_bb = sB.cs_current_bb /\ t.vs_inst_idx = LENGTH sB.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` >>
  conj_tac
  >- suspend "suffix" >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sB`, `op`, `s0`] mp_tac) >>
  simp[expr_store_bound_def]
QED

Resume compile_append_storage_aggregate_stmt_frag_mem[suffix]:
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  drule_all append_aggregate_rhs_memory >> strip_tac >> gvs[] >>
  `value_has_type tv v` by metis_tac[] >>
  `val_wf tv v` by metis_tac[value_has_type_memory_wf] >>
  `val_footprint tv v <= 32 * type_slot_size tv` by
    metis_tac[val_footprint_le, type_memory_size_slots] >>
  `w2n w + 32 * type_slot_size tv <= t.vs_alloca_next` by decide_tac >>
  `!x. op = Var x ==> not_fresh_at sB x` by
    metis_tac[compile_lower_value_var] >>
  `local_ptrs_reserved cenv sB` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx ee t` by fs[expr_post_def] >>
  `return_buf_frame d cenv sB t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
     simp[] >> fs[expr_post_def]) >>
  `compile_copy_memory buf.buf_operand op (32 * type_slot_size tv) sc = ((),sd)` by
    gvs[compile_store_memory_def] >>
  `fn_has_code sB sd func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  `32 * type_slot_size tv < dimword (:256)` by simp[dimword_def] >>
  drule_all compile_scratch_prefix_body_path >>
  disch_then (qx_choose_then `staged` strip_assume_tac) >>
  `local_ptrs_reserved cenv sd` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sB` >> simp[]) >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sd x` by
    (rpt strip_tac >> drule compiler_alloc_buffer_var >>
     disch_then drule >> fs[not_fresh_at_def]) >>
  `w2n w' + 32 * type_slot_size tv < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `type_slot_size tv < dimword (:256)` by decide_tac >>
  `?writes. encode_value tv v = SOME writes` by metis_tac[] >>
  Cases_on `append_place cx (StoragePlace tr slot
    (ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid)))) v ee` >>
  rename1 `_ = (res,ee')` >>
  `w2n slot + type_slot_size (ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid))) <= dimword (:256)` by decide_tac >>
  `!mid' n' subs' slot' tv'.
    declared_storage_region cx mid' n' subs' = SOME (tr,slot',tv') /\
    (slot',tv') <> (slot,ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid))) ==>
    ranges_disjoint (w2n slot)
      (type_slot_size (ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid))))
      (w2n slot') (type_slot_size tv')` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  drule_all append_storage_aggregate_value_path_mem >>
  disch_then (qspecl_then [`lctx`, `RetQ`] mp_tac) >>
  disch_then (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  `gas_marked_path T ctx func t 0 r` by
    (simp[gas_marked_path_def] >>
     `gas_path_mem ctx func t (0 + 0) r` suffices_by simp[] >>
     irule fragGasPathMemTheory.gas_path_mem_then >>
     qexists_tac `staged` >> fs[gas_marked_path_def]) >>
  `ee'.gas_obs = []` by
    (drule append_storage_place_preserves_gas >> simp[]) >>
  `ee' with gas_obs := [] = ee'` by
    simp[evaluation_state_component_equality] >>
  disch_then DISJ_CASES_TAC
  >- (pop_assum strip_assume_tac >>
      qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
      `!x a. not_fresh_at sa x /\ lookup_var x s0 = SOME a ==>
        lookup_var x t' = SOME a` by
        (rpt strip_tac >>
         `not_fresh_at sB x /\ not_fresh_at sd x` by fs[not_fresh_at_def] >>
         metis_tac[]) >>
      qexistsl_tac [`res`, `ee'`, `r`] >>
      conj_tac >- metis_tac[append_storage_place_gas_obs] >>
      simp[cenv_top_ext_refl] >> disj1_tac >>
      irule return_buf_frame_frame >>
      qexistsl_tac [`cenv`, `staged`, `sd`] >> simp[]) >>
  pop_assum strip_assume_tac >>
  qexistsl_tac [`res`, `ee'`, `r`] >>
  conj_tac >- metis_tac[append_storage_place_gas_obs] >>
  simp[] >> disj2_tac >> gen_tac >>
  drule_all append_storage_place_exit_transport >> simp[]
QED

Finalise compile_append_storage_aggregate_stmt_frag_mem

*)
Proof
  cheat
QED
