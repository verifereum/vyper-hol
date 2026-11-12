(* Counted RHS, scratch staging and aggregate storage Append. *)
Theory bodyMemAppendAggregateCompose
Ancestors
  bodyMemAppendAggregateCode bodyMemAppendAggregateValuePath bodyMemAppendAggregateFacts
  stmtSimAppendStorageCompose
  bodyDeclMemoryCounted bodyMemAppendCompose bodyMemAppendFacts
  stmtSimForced exprSimMemDefs exprSimDefs stmtSimDefs stmtSimProps
  loweringPosts exprSimProps exprOperandVar exprLoweringProps emitHelperProps
  compileEnv loweringStateRelDefs exprLowering emitHelper freshWrites gasOutcome gasStorage gasSummary fragGasMode
  vyperStorageTrace vyperStorageFootprint
  vyperFiniteStoragePreservation vyperStoragePlaceRegion
  vyperInterpreter vyperState venomState venomInst venomExecSemantics
  bodyMemoryDefs vyperStorage vyperStorageBackend list finite_map
  valueTypingMemoryProps valueEncodingProps valueCopy loweringSlice words context fragExec
Libs
  monadsyntax

Theorem compile_append_storage_aggregate_stmt_frag_mem:
  eval_target_place cx (TopLevelNameTarget nid) es =
    (INL (StoragePlace tr slot (ArrayTV tv (Dynamic cap))),
     es with storage_trace := es.storage_trace ++
       [StorageRoot tr offset (ArrayTV tv (Dynamic cap))]) /\
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
  cenv.ce_hashmap_info nid = NONE /\
  cenv.ce_module_dynarray_capacity nid = cap /\
  ~is_word_type elem /\ ~is_bytestring_type elem /\ expr_type e = elem /\
  lowered_value_type cenv e = elem /\ supported_pure_expr tops e /\
  evaluate_type (get_tenv cx) elem = SOME tv /\
  type_memory_bytes cenv elem = 32*type_slot_size tv /\
  type_memory_bytes cenv elem < 2**64 /\
  0 < type_slot_size tv /\ well_formed_type_value tv /\ cap < dimword (:256) /\
  well_formed_type_value (ArrayTV tv (Dynamic cap)) /\
  (!gs v es1. (do result <- eval_expr cx e; read_result cx result od)
      (es with <|gas_obs := gs; storage_trace := es.storage_trace ++
         [StorageRoot tr offset (ArrayTV tv (Dynamic cap))]|>) = (INL v,es1) ==>
    value_has_type tv v /\ ?writes. encode_value tv v = SOME writes) /\
  expr_sim_mem ctx func cenv cx elem e
    (es with storage_trace := es.storage_trace ++
      [StorageRoot tr offset (ArrayTV tv (Dynamic cap))]) ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Append (TopLevelNameTarget nid) e))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all append_storage_copy_code_parts >> strip_tac >> gvs[] >>
  rename1 `lower_value _ _ _ _ sa = (op,sB)` >>
  rename1 `compile_alloc_buffer _ sB = (buf,sc)` >>
  rename1 `compile_store_memory _ _ _ _ _ sc = ((),sd)` >>
  drule_all append_storage_aggregate_code_frame >> strip_tac >>
  drule append_toplevel_place_any >> strip_tac >>
  drule eval_append_storage_bind >> disch_then (qspec_then `e` assume_tac) >>
  qmatch_asmsub_abbrev_tac
    `expr_sim_mem ctx func cenv cx _ e es_rhs` >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es_rhs` by
    (simp[Abbr `es_rhs`] >> metis_tac[append_forced_admissible]) >>
  qpat_x_assum `eval_stmt _ _ = _` SUBST1_TAC >>
  irule gas_outcome_record_storage_event >> simp[] >> suspend "rhs"
QED

Resume compile_append_storage_aggregate_stmt_frag_mem[rhs]:
  `~block_is_terminated sb` by metis_tac[append_storage_aggregate_suffix_open] >>
  irule forced_then_outcome >> conj_tac
  >- (rpt strip_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]) >>
  qexists_tac `\H v ee t.
    expr_post H ctx func cenv cx e es_rhs sa sB s0 ee v op t /\
    expr_store_bound cx (expr_type e) v op t /\
    t.vs_current_bb = sB.cs_current_bb /\ t.vs_inst_idx = LENGTH sB.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` >>
  conj_tac >- simp[storage_trace_frame_append_place] >> conj_tac
  >- suspend "suffix" >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sB`, `op`, `s0`] mp_tac) >>
  impl_tac
  >- (simp[expr_store_bound_def] >> rpt strip_tac >>
      `valid_horizon cx st0 H es.storage_trace` by
        fs[Abbr `es_rhs`, valid_horizon_def] >>
      `stmt_state_rel H ctx func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H)` by metis_tac[] >>
      `storage_well_formed_on cx es_rhs (FST H) <=>
       storage_well_formed_on cx es (FST H)` by
        (irule storage_well_formed_on_backends >> simp[Abbr `es_rhs`]) >>
      simp[Abbr `es_rhs`]) >> simp[expr_store_bound_def]
QED

Resume compile_append_storage_aggregate_stmt_frag_mem[suffix]:
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  rename1 `(bind (eval_expr cx e) (read_result cx)) _ = (INL v, ee)` >>
  `?H0. valid_horizon cx st0 H0 ee.storage_trace` by metis_tac[] >>
  pop_assum (qx_choose_then `H0` assume_tac) >>
  `expr_post H0 ctx func cenv cx e es_rhs sa sB s0 ee v op t /\
   expr_store_bound cx (expr_type e) v op t /\
   t.vs_current_bb = sB.cs_current_bb /\
   t.vs_inst_idx = LENGTH sB.cs_current_insts /\
   alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` by
    metis_tac[] >>
  qpat_x_assum `?gs. bind _ _ _ = _` (qx_choose_then `gs` assume_tac) >>
  `value_has_type tv v /\ ?writes. encode_value tv v = SOME writes` by
    (qpat_x_assum `!gs v es1. _` (qspecl_then [`gs`, `v`, `ee`] mp_tac) >>
     simp[Abbr `es_rhs`] >> disch_then irule >>
     qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[Abbr `es_rhs`] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  pop_assum (qx_choose_then `writes` assume_tac) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    simp[storage_trace_frame_bind, evaluate_storage_trace_frame,
         storage_trace_frame_read_result] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       MEM (tr,slot,ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid))) (FST H) /\
       storage_locks_separated (FST H) (SND H) /\
       (!slot' tv'.
          MEM (tr,slot',tv') (FST H) /\
          (slot',tv') <> (slot,ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid))) ==>
          ranges_disjoint (w2n slot)
            (type_slot_size (ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid))))
            (w2n slot') (type_slot_size tv'))` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H (es_rhs with gas_obs := gs).storage_trace` by
       metis_tac[valid_horizon_frame] >>
     `MEM (tr,slot,ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid))) (FST H)` by
       fs[Abbr `es_rhs`, valid_horizon_def, storage_observations_ok_def,
          storage_trace_regions_def, EVERY_MEM] >>
     `regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H)` by
       fs[valid_horizon_def] >>
     simp[] >> rpt strip_tac >>
     fs[regions_consistent_def] >> metis_tac[]) >>
  qpat_x_assum `expr_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `expr_store_bound _ _ _ _ _` mp_tac >>
  rpt strip_tac >>
  drule_all append_aggregate_rhs_memory >> strip_tac >>
  qpat_x_assum `expr_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `val_wf tv v` by metis_tac[value_has_type_memory_wf] >>
  `val_footprint tv v <= 32 * type_slot_size tv` by
    metis_tac[val_footprint_le, type_memory_size_slots] >>
  `w2n w + 32 * type_slot_size tv <= t.vs_alloca_next` by decide_tac >>
  `!x. op = Var x ==> not_fresh_at sB x` by
    metis_tac[compile_lower_value_var] >>
  `local_ptrs_reserved cenv sB` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `return_buf_frame d cenv sB t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
     simp[]) >>
  `compile_copy_memory buf.buf_operand op (32 * type_slot_size tv) sc = ((),sd)` by
    gvs[compile_store_memory_def] >>
  `fn_has_code sB sd func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  `32 * type_slot_size tv < dimword (:256)` by simp[dimword_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee t` by
    (rpt strip_tac >>
     `expr_post H ctx func cenv cx e es_rhs sa sB s0 ee v op t` by
       metis_tac[] >>
     pop_assum (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     first_assum ACCEPT_TAC) >>
  drule_all (compile_scratch_prefix_body_path
             |> Q.SPECL [`\H. valid_horizon cx st0 H ee.storage_trace`, `H0`]
             |> SIMP_RULE bool_ss []) >>
  disch_then (qx_choose_then `staged` strip_assume_tac) >>
  `stmt_state_rel H0 ctx func cenv cx ee staged` by metis_tac[] >>
  `local_ptrs_reserved cenv sd` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sB` >> simp[]) >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sd x` by
    (rpt strip_tac >> drule compiler_alloc_buffer_var >>
     disch_then drule >> fs[not_fresh_at_def]) >>
  `w2n w' + 32 * type_slot_size tv < dimword (:256)` by
    (qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ staged` mp_tac >>
     qpat_x_assum `w2n w' + _ <= staged.vs_alloca_next` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `type_slot_size tv < dimword (:256)` by decide_tac >>
  Cases_on `append_place cx (StoragePlace tr slot
    (ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid)))) v ee` >>
  rename1 `_ = (res,ee')` >>
  `w2n slot + type_slot_size (ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid))) <= dimword (:256)` by decide_tac >>
  qspec_then `\H. valid_horizon cx st0 H ee.storage_trace /\
                  stmt_state_rel H ctx func cenv cx ee staged`
    (drule_at (Pat `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ _ _ = _`) o SRULE [])
    (Q.GEN `P` (SPEC_ALL append_storage_aggregate_value_path_mem)) >>
  disch_then (qspecl_then [`lctx`, `\v st r. F`, `H0`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
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
      `!x a. not_fresh_at sa x /\ lookup_var x s0 = SOME a ==>
        lookup_var x t' = SOME a` by
        (rpt strip_tac >>
         `not_fresh_at sB x /\ not_fresh_at sd x` by fs[not_fresh_at_def] >>
         metis_tac[]) >>
      qexistsl_tac [`res`, `ee'`, `r`] >>
      conj_tac >- metis_tac[append_storage_place_gas_obs] >>
      conj_tac >- simp[] >>
      disj1_tac >> simp[] >> gen_tac >> strip_tac >>
      `valid_horizon cx st0 H ee.storage_trace` by
        metis_tac[valid_horizon_frame, storage_trace_frame_append_place] >>
      `expr_post H ctx func cenv cx e es_rhs sa sB s0 ee v op t` by
        metis_tac[] >>
      `stmt_state_rel H ctx func cenv cx ee staged` by metis_tac[] >>
      `stmt_state_rel H ctx func cenv cx ee' t'` by metis_tac[] >>
      `MEM (tr,slot,ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid))) (FST H)` by
        metis_tac[] >>
      `storage_well_formed_on cx ee' (FST H)` by
        (mp_tac (Q.INST
           [`cx` |-> `cx`,
            `regions` |-> `FST (H : (bool # 256 word # type_value) list # num list)`,
            `st` |-> `ee`,
            `st'` |-> `ee'`, `b` |-> `tr`, `root` |-> `slot`,
            `tv` |-> `ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid))`,
            `path` |-> `[]`, `delta` |-> `0`, `slot` |-> `slot`, `etv` |-> `tv`,
            `n` |-> `cenv.ce_module_dynarray_capacity nid`, `v` |-> `v`,
            `res` |-> `res`]
           append_subregion_preserves_storage_well_formed_on) >>
         fs[storage_subregion_def, valid_horizon_def]) >>
      simp[cenv_top_ext_refl] >>
      irule return_buf_frame_frame >>
      qexistsl_tac [`cenv`, `staged`, `sd`] >> simp[]) >>
  pop_assum strip_assume_tac >>
  qexistsl_tac [`res`, `ee'`, `r`] >>
  conj_tac >- metis_tac[append_storage_place_gas_obs] >>
  conj_tac >- simp[] >>
  disj2_tac >> simp[] >> rpt strip_tac >>
  fs[stmt_exit_def]
QED

Finalise compile_append_storage_aggregate_stmt_frag_mem
