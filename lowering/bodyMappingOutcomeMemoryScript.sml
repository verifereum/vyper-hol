(* Counted semantic sequencing for mapping subscripts. *)
Theory bodyMappingOutcomeMemory
Ancestors
  mappingSubscriptCode mappingSubscriptSemantics exprSimSubscriptMap
  bodyMemMapBase bodyMemoryPreds
  exprSimMemDefs exprSimMapMemDefs exprSimMapKey exprSimSubscriptArraySource
  exprSimWordArgs exprSimProps exprBopSimProps stmtSimProps exprOperandVar
  fragGasMode fragGasPath gasSummary

Theorem mapping_index_sim_mem[local]:
  (!s res t. eval_expr cx obj s = (INL res,t) ==>
     body_expr_mem_ok cx idx) /\
  body_inv tops ctx cenv cx /\
  (expr_body_pre cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre cenv cx env (Subscript ann obj idx) es) /\
  place_type cenv obj = MapPT kt vt /\
  gas_marked_exec T (ctx,func) (eval_expr cx obj)
    (es,s0) marks (INL tv) mid (OK t) ==>
  expr_sim_mem ctx func cenv cx (expr_type idx) idx (mid with gas_obs := [])
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac strip_assume_tac))) >>
  drule_all mapping_subscript_marked_index_pre >> strip_tac >>
  `body_expr_mem_ok cx idx` by metis_tac[] >>
  qpat_x_assum `body_expr_mem_ok cx idx`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [body_expr_mem_ok_def]) >>
  disch_then (qspecl_then
    [`tops`, `ctx`, `func`, `cenv`, `env`, `expr_type idx`,
     `mid with gas_obs := []`] mp_tac) >> simp[]
QED

Theorem compile_mapping_subscript_outcome_mem_given_tail:
  (!ctx func cenv cx idx em sm sn s1 en kv key t kt tv hashed sp base_op slot sb base_slot st0 H0.
    valid_horizon cx st0 H0 en.storage_trace /\
    (!H. valid_horizon cx st0 H en.storage_trace ==>
      expr_post H ctx func cenv cx idx em sm sn s1 en kv key t /\
      stmt_state_rel H ctx func cenv cx em s1) /\
    expr_type idx = kt /\ hashmap_key_type kt /\
    evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv kv /\
    (if is_bytestring_type kt then compile_keccak256_key key F sn
     else (key,sn)) = (hashed,sp) /\
    compile_mapping_subscript base_op hashed sp = (slot,sb) /\
    (!x. key = Var x ==> not_fresh_at sn x) /\
    (!x. base_op = Var x ==> not_fresh_at sm x) /\ (!l. base_op <> Label l) /\
    eval_operand base_op s1 = SOME base_slot /\
    fn_inst_ids_distinct func /\ fn_has_code sp sb func /\ fn_has_code sn sb func /\
    local_ptrs_reserved cenv sm /\
    MAP FDOM em.scopes = MAP FDOM en.scopes /\
    sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    expr_store_bound cx (expr_type idx) kv key t /\ alloca_history func t ==>
    ?u. gas_marked_path T ctx func t 0 (OK u) /\
        eval_operand slot u = SOME (hashmap_slot base_slot (encode_hashmap_key kt kv)) /\
        (!H. valid_horizon cx st0 H en.storage_trace ==>
          stmt_state_rel H ctx func cenv cx en u) /\ wb_frame cenv em en sm s1 u /\
        (~expr_has_effect idx ==> pure_frame cenv func em sm s1 u) /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next) /\
  body_expr_mem_ok cx obj /\
  (!s tv t. eval_expr cx obj s = (INL tv,t) ==> body_expr_mem_ok cx idx) /\
  body_inv tops ctx cenv cx /\
  (expr_body_pre cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre cenv cx env (Subscript ann obj idx) es) /\
  place_type cenv obj = MapPT kt vt /\
  compile_expr cenv ty (Subscript ann obj idx) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H)) /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (eval_expr cx (Subscript ann obj idx)) A es /\
  (!ex. A (INR ex) ==> expr_map_res_ok (INR ex)) ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (eval_expr cx (Subscript ann obj idx)) (es,s0)
    (\H res ee t. ?tr base_slot kv tv tp p ef.
       res = INL tv /\
       storage_mapping_region cx tr base_slot (HashMapT kt vt) /\
       select_result cx (expr_type obj) (HashMapRef tr base_slot kt vt)
         (ValueSubscript kv) ef = (INL tv,ee) /\
       valid_horizon cx st0 H ee.storage_trace /\
       storage_well_formed_on cx ee (FST H) /\
       expr_type idx = kt /\ hashmap_key_type kt /\
       (?key_ty. evaluate_type (get_tenv cx) kt = SOME key_ty /\
                 value_has_type key_ty kv) /\
       expr_sim_inv cenv cx env ee /\ vv = LocatedValue tp p /\
       p.ptr_location = slot_loc tr /\
       eval_operand p.ptr_operand t =
         SOME (hashmap_slot base_slot (encode_hashmap_key kt kv)) /\
       stmt_state_rel H ctx func cenv cx ee t /\ wb_frame cenv es ee sa s0 t /\
       (~expr_has_effect (Subscript ann obj idx) ==>
          pure_frame cenv func es sa s0 t) /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\H res ee r. expr_exit res r)
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "tail") strip_assume_tac) >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_initial >> simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by
    (qexists_tac `storage_trace_horizon es.storage_trace` >>
     fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by simp[] >>
  `expr_map_pre cenv cx env obj es` by
    metis_tac[expr_body_pre_map_subscript_base, expr_map_pre_subscript_base] >>
  `type_place_expr env obj = SOME (HashMapT kt vt)` by
    (drule_all expr_map_pre_checked_type >> simp[]) >>
  qpat_assum `type_place_expr _ obj = _`
    (strip_assume_tac o Q.SPECL [`cenv`, `idx`, `cx`] o
     MATCH_MP map_base_no_overlap) >>
  drule_all mapping_subscript_code_parts >> strip_tac >>
  drule exprOperandVarTheory.compile_lower_value_var >>
  simp[] >> disch_then assume_tac >>
  qpat_assum `compile_expr _ _ obj _ = _`
    (mp_then Any mp_tac (cj 1 exprOperandVarTheory.compiler_compile_var)) >>
  simp[] >> disch_then assume_tac >>
  `type_place_expr env obj = SOME (HashMapT kt vt)` by
    (drule_all expr_map_pre_checked_type >> simp[]) >>
  drule_all compile_mapping_operand_not_label >> disch_then assume_tac >>
  `gas_admissible (eval_expr cx obj) expr_map_res_ok es` by
    (irule subscript_result_base_admissible >>
     qexistsl_tac [`A`, `ann`, `idx`] >> simp[]) >>
  `expr_map_sim_mem ctx func cenv cx ty obj es` by
    (drule_all body_expr_mem_ok_map >> simp[]) >>
  qpat_x_assum `expr_map_sim_mem _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_map_sim_mem_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `bvv`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    rewrite_tac[MATCH_MP eval_expr_subscript_bind th]) >>
  disch_then (mp_then Any match_mp_tac gas_outcome_bind_result_exec) >>
  conj_tac
  >- (rpt gen_tac >> simp[] >> rpt strip_tac >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]) >>
  reverse conj_tac
  >- simp[vyperStorageTraceTheory.storage_trace_frame_bind_all, vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_read_result, vyperStorageTraceTheory.storage_trace_frame_select] >>
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 mid.storage_trace`)
  >- (rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_initial >>
      simp[vyperStorageTraceTheory.storage_trace_frame_bind_all, vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_read_result, vyperStorageTraceTheory.storage_trace_frame_select]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  BETA_TAC >> pure_rewrite_tac[sumTheory.INL_11] >> strip_tac >>
  rename1 `v = HashMapRef tr base_slot bkt bvt` >>
  `wb_frame cenv es (mid with gas_obs := []) sa s0 t` by
    (pure_rewrite_tac[loweringPostsTheory.wb_frame_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!x w. not_fresh_at sa x /\ _ ==> _` kall_tac >>
  qpat_x_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _` kall_tac >>
  qpat_x_assum `!aid off sz. _ ==> mem_bytes_at _ _ t.vs_memory = _` kall_tac >>
  qpat_x_assum `locals_kept cenv es (mid with gas_obs := []) s0 t` kall_tac >>
  `expr_body_pre cenv cx env idx (mid with gas_obs := []) /\
   ?s u. eval_expr cx obj s = (INL v,u)` by
    (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)
       mapping_subscript_marked_index_pre >>
     disch_then irule >> simp[] >>
     qexists `ann` >> simp[]) >>
  `eval_expr cx obj
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, mid with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >>
     disch_then (CONJUNCTS_THEN2 (qspec_then `[]` mp_tac) kall_tac) >> simp[]) >>
  `type_place_expr env obj = SOME (HashMapT kt vt)` by
    (drule_all expr_map_pre_checked_type >> simp[]) >>
  `bkt = kt /\ bvt = vt` by
    (qpat_assum `eval_expr _ _ (_ with gas_obs := _) = _`
       (mp_then Any mp_tac expr_map_pre_eval_result) >>
     disch_then (qspecl_then [`cenv`, `env`] mp_tac) >>
     simp[] >> strip_tac >>
     first_x_assum (qspec_then `HashMapT kt vt` mp_tac) >>
     simp[eval_result_typed_def]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) t /\
     storage_well_formed_on cx (mid with gas_obs := []) (FST H)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     BETA_TAC >> strip_tac >> gvs[]) >>
  `gas_admissible (bind (eval_expr cx idx) (read_result cx))
     expr_res_ok (mid with gas_obs := [])` by
    (qpat_assum `~subscript_reads_base _ _ _`
       (irule o MATCH_MP subscript_result_index_admissible) >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`A`, `ann`] >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >>
     drule gas_path_normal >> simp[]) >>
  `expr_sim_mem ctx func cenv cx (expr_type idx) idx (mid with gas_obs := [])` by
    (irule mapping_index_sim_mem >> simp[] >> metis_tac[]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_mem_def] >>
  disch_then (qspecl_then [`st0`, `sm`, `sn`, `key`, `t`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then assume_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ _ _ _ (start,t)` >>
  match_mp_tac (BETA_RULE (Q.SPEC
    `\H kv ee u. expr_post H ctx func cenv cx idx
       (mid with gas_obs := []) sm sn t ee kv key u /\
       expr_store_bound cx (expr_type idx) kv key u /\
       u.vs_current_bb = sn.cs_current_bb /\
       u.vs_inst_idx = LENGTH sn.cs_current_insts /\
       alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next`
    (Q.GEN `P` forced_then_outcome_exec))) >>
  conj_tac >- (simp[Abbr `start`] >> first_assum ACCEPT_TAC) >>
  reverse conj_tac
  >- (simp[vyperStorageTraceTheory.storage_trace_frame_select] >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  simp[Abbr `start`] >>
  map_every qx_gen_tac [`imarks`, `kv`, `fin`, `it`] >> strip_tac >>
  `expr_sim_inv cenv cx env (fin with gas_obs := []) /\
   expr_type idx = kt /\ hashmap_key_type kt /\
   (?key_ty. evaluate_type (get_tenv cx) kt = SOME key_ty /\
             value_has_type key_ty kv) /\
   MAP FDOM es.scopes = MAP FDOM mid.scopes /\
   MAP FDOM mid.scopes = MAP FDOM fin.scopes` by
    (drule_all mapping_subscript_marked_success >> simp[]) >>
  `?selected selected_state. selected_state = fin with storage_trace := selected_state.storage_trace /\
   !tail.
     select_result cx (expr_type obj) (HashMapRef tr base_slot kt vt)
       (ValueSubscript kv) (fin with gas_obs := tail) =
     (INL selected,selected_state with gas_obs := tail)` by
    (irule mapping_subscript_selection_success >>
     qexistsl_tac [`ann`, `cenv`, `env`, `es`, `idx`] >> simp[]) >>

  `fn_has_code sn sb func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `~it.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ imarks _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >>
     drule gas_path_normal >> simp[]) >>
  `eval_operand (vv_operand bvv) t = SOME base_slot` by
    gvs[contextTheory.vv_operand_def] >>
  `bind (eval_expr cx idx) (read_result cx)
     (mid with gas_obs := gas_explicit imarks t.vs_gas_readings) =
     (INL kv,fin with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ _ _ imarks _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >>
     disch_then (CONJUNCTS_THEN2 (qspec_then `[]` mp_tac) kall_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
     expr_post H ctx func cenv cx idx (mid with gas_obs := []) sm sn t
       (fin with gas_obs := []) kv key it /\
     stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) t` by
    (gen_tac >> disch_tac >>
     `valid_horizon cx st0 H mid.storage_trace` by
       (qpat_assum `vyperState$bind _ _ _ = _`
          (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame) >>
        simp[vyperStorageTraceTheory.storage_trace_frame_bind_all, vyperStorageTraceTheory.evaluate_storage_trace_frame,
             vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
     conj_tac
     >- (qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
           (qspec_then `H` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         BETA_TAC >> strip_tac >> gvs[]) >>
     simp[]) >>
  `?out. gas_marked_path T ctx func it 0 (OK out) /\
     eval_operand slot out = SOME (hashmap_slot base_slot (encode_hashmap_key kt kv)) /\
     (!H. valid_horizon cx st0 H fin.storage_trace ==>
       stmt_state_rel H ctx func cenv cx (fin with gas_obs := []) out) /\
     wb_frame cenv (mid with gas_obs := []) (fin with gas_obs := []) sm t out /\
     (~expr_has_effect idx ==>
        pure_frame cenv func (mid with gas_obs := []) sm t out) /\
     out.vs_current_bb = sb.cs_current_bb /\
     out.vs_inst_idx = LENGTH sb.cs_current_insts /\
     alloca_history func out /\ it.vs_alloca_next <= out.vs_alloca_next` by
    (simp[] >> asm "tail" (fn th => match_mp_tac (SRULE [] (Q.INST
       [`en` |-> `fin with gas_obs := []`,
        `em` |-> `mid with gas_obs := []`,
        `H0` |-> `storage_trace_horizon fin.storage_trace`,
        `base_op` |-> `vv_operand bvv`, `tv` |-> `key_ty`]
       (SPEC_ALL th)))) >> fs[] >> metis_tac[]) >>
  `wb_frame cenv es (fin with gas_obs := []) sa s0 out` by
    (irule (Q.INST [`H` |-> `H0`]
       (INST_TYPE [alpha |-> ``:256``] exprSimWordArgsTheory.wb_frame_trans)) >>
     qpat_assum `wb_frame cenv es (mid with gas_obs := []) sa s0 t`
       (irule_at Any) >>
     qpat_assum `wb_frame cenv (mid with gas_obs := []) _ sm t out`
       (irule_at Any) >>
     qpat_assum `stmt_state_rel H0 _ _ _ _ es s0` (irule_at Any) >> simp[]) >>
  `~expr_has_effect (Subscript ann obj idx) ==> pure_frame cenv func es sa s0 out` by
    (rewrite_tac[loweringPostsTheory.expr_has_effect_thm, DE_MORGAN_THM] >>
     strip_tac >>
     `pure_frame cenv func es sa s0 t` by
       (qpat_x_assum `~expr_has_effect obj ==> _` mp_tac >> simp[]) >>
     `pure_frame cenv func (mid with gas_obs := []) sm t out` by
       (qpat_x_assum `~expr_has_effect idx ==> _` mp_tac >> simp[]) >>
     `!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
              FLOOKUP out.vs_allocas aid = SOME b` by
       (qpat_assum `wb_frame cenv _ _ sm t out` mp_tac >>
        pure_rewrite_tac[loweringPostsTheory.wb_frame_def] >>
        strip_tac >> first_assum ACCEPT_TAC) >>
     `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
            lookup_var x t = SOME w` by
       (qpat_assum `wb_frame cenv es _ sa s0 t` mp_tac >>
        pure_rewrite_tac[loweringPostsTheory.wb_frame_def] >>
        strip_tac >> first_assum ACCEPT_TAC) >>
     match_mp_tac exprSimPropsTheory.pure_frame_trans >>
     qexistsl_tac [`mid with gas_obs := []`, `sm`, `t`] >> simp[]) >>
  `storage_mapping_region cx tr base_slot (HashMapT kt vt)` by
    (qpat_x_assum `storage_mapping_region _ _ _ _` mp_tac >> simp[]) >>
  `s0.vs_alloca_next <= out.vs_alloca_next` by decide_tac >>
  qexistsl_tac [`INL selected`, `selected_state`, `OK out`] >>
  conj_tac >- simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  disj1_tac >> qexists_tac `out` >> simp[] >> rpt strip_tac >>
  `select_result cx (expr_type obj) (HashMapRef tr base_slot kt vt)
     (ValueSubscript kv) (fin with gas_obs := []) =
     (INL selected,selected_state with gas_obs := [])` by simp[] >>
  `valid_horizon cx st0 H fin.storage_trace` by
    (qpat_assum `select_result _ _ _ _ _ = _`
       (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame) >>
     simp[vyperStorageTraceTheory.storage_trace_frame_select]) >>
  `stmt_state_rel H ctx func cenv cx (fin with gas_obs := []) out /\
   storage_well_formed_on cx (fin with gas_obs := []) (FST H)` by
    (conj_tac >- simp[] >>
     `expr_post H ctx func cenv cx idx (mid with gas_obs := []) sm sn t
       (fin with gas_obs := []) kv key it` by simp[] >>
     fs[loweringPostsTheory.expr_post_def]) >>
  qexistsl_tac [`tr`, `base_slot`, `kv`, `fin with gas_obs := []`] >>
  simp[contextTheory.mk_ptr_def, contextTheory.vv_location_def] >>
  qpat_x_assum `selected_state = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  fs[loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def,
     loweringPostsTheory.popped_kept_def, vyperStorageFootprintTheory.storage_well_formed_on_def,
     boolTheory.FORALL_BOOL, vyperStorageBackendTheory.get_storage_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
