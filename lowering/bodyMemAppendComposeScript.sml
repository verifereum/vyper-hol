(* Counted RHS composition for word storage Append. *)
Theory bodyMemAppendCompose
Ancestors
  bodyMemAppendPath bodyMemAppendFacts stmtSimAppendStorageCompose
  stmtSimForced exprSimMemDefs exprSimDefs stmtSimDefs stmtSimProps
  loweringPosts exprSimProps exprOperandVar exprLoweringProps emitHelperProps
  compileEnv loweringStateRelDefs exprLowering emitHelper freshWrites gasOutcome gasStorage gasSummary fragGasMode
  vyperStorageTrace vyperStorageFootprint
  vyperFiniteStoragePreservation vyperStoragePlaceRegion
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
  (!gs v es1. (do result <- eval_expr cx e; read_result cx result od)
      (es with <|gas_obs := gs; storage_trace := es.storage_trace ++
         [StorageRoot tr offset (ArrayTV tv (Dynamic cap))]|>) = (INL v,es1) ==>
    encode_value tv v = SOME [(0,typed_val_to_w256 etv v)] /\
    value_has_type tv v) /\
  expr_sim_mem ctx func cenv cx elem e
    (es with storage_trace := es.storage_trace ++
      [StorageRoot tr offset (ArrayTV tv (Dynamic cap))]) ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Append (TopLevelNameTarget nid) e))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all append_storage_word_code_parts >> strip_tac >> gvs[] >>
  rename1 `lower_value _ _ _ _ sa = (op,sB)` >>
  drule_all append_storage_word_code_frame >> strip_tac >>
  drule append_toplevel_place_any >> strip_tac >>
  drule eval_append_storage_bind >> disch_then (qspec_then `e` assume_tac) >>
  qmatch_asmsub_abbrev_tac
    `expr_sim_mem ctx func cenv cx elem e es_rhs` >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es_rhs` by
    (simp[Abbr `es_rhs`] >> metis_tac[append_forced_admissible]) >>
  qpat_x_assum `eval_stmt _ _ = _` SUBST1_TAC >>
  irule gas_outcome_record_storage_event >> simp[] >> suspend "rhs"
QED

Resume compile_append_storage_word_stmt_frag_mem[rhs]:
  `~block_is_terminated sb` by metis_tac[append_storage_word_suffix_open_mem] >>
  match_mp_tac (Q.INST [`P` |-> `\H v ee t.
      expr_post H ctx func cenv cx e es_rhs sa sB s0 ee v op t /\
      expr_store_bound cx elem v op t /\
      t.vs_current_bb = sB.cs_current_bb /\
      t.vs_inst_idx = LENGTH sB.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next`]
    (SPEC_ALL forced_then_outcome)) >>
  conj_tac
  >- (qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
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
          simp[Abbr `es_rhs`]) >> simp[expr_store_bound_def]) >>
  conj_tac >- simp[storage_trace_frame_append_place] >>
  conj_tac >- suspend "operand" >>
  rpt strip_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]
QED

Resume compile_append_storage_word_stmt_frag_mem[operand]:
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `?H0. valid_horizon cx st0 H0 ee.storage_trace` by metis_tac[] >>
  pop_assum (qx_choose_then `H0` assume_tac) >>
  `expr_post H0 ctx func cenv cx e es_rhs sa sB s0 ee v op t /\
   expr_store_bound cx elem v op t /\
   t.vs_current_bb = sB.cs_current_bb /\
   t.vs_inst_idx = LENGTH sB.cs_current_insts /\
   alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` by
    metis_tac[] >>
  `encode_value tv v = SOME [(0,typed_val_to_w256 etv v)] /\
   value_has_type tv v` by metis_tac[] >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    simp[storage_trace_frame_bind, evaluate_storage_trace_frame,
         storage_trace_frame_read_result] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H)` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H (es_rhs with gas_obs := gs).storage_trace` by
       metis_tac[valid_horizon_frame] >>
     fs[Abbr `es_rhs`, valid_horizon_def, storage_observations_ok_def,
        storage_trace_regions_def, EVERY_MEM]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
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
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee t /\
       MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H)` by
    (rpt strip_tac >>
     `expr_post H ctx func cenv cx e es_rhs sa sB s0 ee v op t` by
       metis_tac[] >> fs[expr_post_def]) >>
  Cases_on `append_place cx (StoragePlace tr slot
    (ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid)))) v ee` >>
  rename1 `_ = (res,ee')` >>
  drule_all (Q.INST
    [`P` |-> `\H. valid_horizon cx st0 H ee.storage_trace`,
     `H0` |-> `H0`] append_storage_word_value_path_mem) >>
  disch_then (qspecl_then [`lctx`, `\v st r. F`] mp_tac) >>
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
      conj_tac >- simp[] >>
      disj1_tac >> simp[] >> gen_tac >> strip_tac >>
      `valid_horizon cx st0 H ee.storage_trace` by
        metis_tac[valid_horizon_frame, storage_trace_frame_append_place] >>
      `expr_post H ctx func cenv cx e es_rhs sa sB s0 ee v op t` by
        metis_tac[] >>
      qpat_x_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
      `MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H)` by metis_tac[] >>
      `stmt_state_rel H ctx func cenv cx ee' t'` by metis_tac[] >>
      `storage_well_formed_on cx ee' (FST H)` by
        (mp_tac (Q.INST
           [`cx` |-> `cx`,
            `regions` |-> `FST (H : (bool # 256 word # type_value) list # num list)`,
            `st` |-> `ee`,
            `st'` |-> `ee'`, `b` |-> `tr`, `root` |-> `slot`,
            `tv` |-> `ArrayTV tv (Dynamic cap)`, `path` |-> `[]`,
            `delta` |-> `0`, `slot` |-> `slot`, `etv` |-> `tv`,
            `n` |-> `cap`, `v` |-> `v`, `res` |-> `res`]
           append_subregion_preserves_storage_well_formed_on) >>
         fs[storage_subregion_def, valid_horizon_def]) >>
      simp[cenv_top_ext_refl] >>
      irule return_buf_frame_frame >>
      qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]) >>
  pop_assum strip_assume_tac >>
  qexistsl_tac [`res`, `ee'`, `r`] >>
  conj_tac >- metis_tac[append_storage_place_gas_obs] >>
  conj_tac >- simp[] >>
  disj2_tac >> simp[] >> rpt strip_tac >>
  fs[stmt_exit_def]
QED

Finalise compile_append_storage_word_stmt_frag_mem
