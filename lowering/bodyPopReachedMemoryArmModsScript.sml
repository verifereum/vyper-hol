(* Finish linked Pop at the actual reached mutable-memory place. *)
Theory bodyPopReachedMemoryArmMods
Ancestors
  bodyPopInputsMods bodyPopSourceMods bodyPopReachedMemoryMods
  bodyPopMemoryRunMods bodyPopMemoryPostMods bodyPopExitPathsMods
  bodyWriteTargetStageMods gasOutcomeFullPostMods gasOutcomeFull
  exprSimPopNestedBase exprSimPopNestedLocalRun exprSimPopNestedLocalProps
  exprSimHypsDefs exprBodyPreProps stmtReasonLitFragMemory stmtPoppedKeys
  typedMemoryCopy vyperTypeEvalCaseProofs vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState vyperAST vyperLookup bodyFullTargetDefs freshWrites
  immutableRegionFrameProps exprLowering compileEnv context fragExec rich_list list arithmetic words

Theorem memory_arm_pre_obs[local]:
  expr_body_pre_mods mods ce cx env e (es with gas_obs := gs) <=>
  expr_body_pre_mods mods ce cx env e es
Proof
  simp[expr_body_pre_mods_def,expr_sim_inv_mods_def]
QED

Theorem memory_arm_source_horizon[local]:
  eval_target_place cx bt (es with gas_obs := gs) = (INL p,ee) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  valid_horizon cx st0 H es.storage_trace
Proof
  strip_tac >>
  `storage_trace_frame (eval_target_place cx bt)` by
    simp[cj 8 evaluate_storage_trace_frame] >>
  drule_all storage_trace_frame_prefix >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[valid_horizon_append]
QED

Theorem memory_arm_provenance[local]:
  ptr_covers G tn root t sz /\ lookup_var root t = SOME b /\
  FLOOKUP G p = FLOOKUP G root ==>
  ?base span. FLOOKUP G p = SOME (base,span) /\ w2n b + sz <= base+span
Proof
  rw[bodyPtrDefsTheory.ptr_covers_def] >> fs[] >>
  goal_assum (drule_at Any) >> decide_tac
QED

Theorem memory_arm_clean_header[local]:
  mem_word_taint M off = {} ==> M DIFF {i | off <= i /\ i < off+32} = M
Proof
  simp[ptrDisciplineTheory.mem_word_taint_def, pred_setTheory.EXTENSION] >>
  strip_tac >> gen_tac >> eq_tac >- simp[] >>
  disch_tac >> simp[] >> CCONTR_TAC >> fs[] >>
  qpat_x_assum `!x. _` (qspec_then `x-off` mp_tac) >>
  `off + (x-off) = x /\ x-off < 32` by decide_tac >> simp[]
QED

Theorem memory_arm_compile[local]:
  compile_get_target_ptr compile_expr ce bt sa =
    ((hdr,SOME LocMemory,SOME (value_type_place (Type (ArrayT ann (Dynamic cap))))),sm) /\
  compile_expr ce ty (Pop ann bt) sa = (vv,sb) /\
  type_memory_bytes ce ann = esz ==>
  ?x0 x1 x2 x3 x4 x5 x6.
    ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6] /\
    EVERY (\x. ~not_fresh_at sm x) [x0;x1;x2;x3;x4;x5;x6] /\
    vv = LocatedValue ann (mk_ptr (Var x6) LocMemory) /\
    sb.cs_current_bb = sm.cs_current_bb /\
    sb.cs_current_insts = sm.cs_current_insts ++
      memory_pop_insts hdr sm.cs_next_id esz x0 x1 x2 x3 x4 x5 x6
Proof
  strip_tac >>
  qpat_x_assum `compile_expr ce ty (Pop ann bt) sa = _` mp_tac >>
  simp[Once nested_pop_compile_eq, value_type_place_def, word_scale_def,
       elem_size_in_location_def, is_slot_addressed_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_then strip_assume_tac memory_pop_shape >>
  qexistsl_tac [`x0`,`x1`,`x2`,`x3`,`x4`,`x5`,`x6`] >>
  fs[]
QED

Theorem pop_reached_memory_arm_mods:
  contract_inv mods exps ctx cenv cx /\
  expr_body_pre_mods mods cenv cx env (Pop ann bt) es /\
  compile_expr cenv ty (Pop ann bt) sa = (vv,sb) /\
  ci_mono sa sm /\ ci_mono sm sb /\ fn_has_code sm sb func /\
  gas_admissible (eval_expr cx (Pop ann bt)) expr_vv_res_ok es /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt es st0 sa sm shadow_sa shadow_sm dst s0 G0 tn0 /\
  (!tail. eval_target_place cx bt
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL (MemoryPlace id path),ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
  (?entry v. lookup_scopes id ee.scopes = SOME entry /\
            evaluate_subscripts entry.type entry.value path = INL v) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sm s0
       ee (PlaceR (MemoryPlace id path)) (Type (ArrayT ann (Dynamic cap))) dst G0 tn0 G tn t) /\
  (!mods cenv cx env es id root_ty root_tv path k etv n.
     expr_sim_inv_mods mods cenv cx env es /\
     cenv.ce_var_type id = SOME root_ty /\
     evaluate_type (get_tenv cx) root_ty = SOME root_tv /\
     mutable_place_path root_tv path /\
     mem_path_offset root_tv path = SOME (k,ArrayTV etv (Dynamic n)) ==>
     dynarray_len_untupled cenv id k) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (pop_place cx (MemoryPlace id path)) (ee,t,G,tn)
    (\H res ef G' tn' u. ?tv. res = INL tv /\
      vv_post_mods H ctx func cenv cx (Pop ann bt) es sa sb s0 ef tv vv u /\
      vv_store_bound cx (post_value_type cenv (Pop ann bt))
        (lowered_value_type cenv (Pop ann bt)) ef tv vv u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ef G' tn' u /\
      ptr_vv_ok cx (post_value_type cenv (Pop ann bt)) tv vv ef G' tn' u /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv (Pop ann bt)) /\
           ~is_bytestring_type (post_value_type cenv (Pop ann bt)) ==>
           vv_own cenv cx (post_value_type cenv (Pop ann bt)) sa sb ef tv vv u /\
           (!t' ptr. vv = LocatedValue t' ptr ==> ptr.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?v. read_result cx tv ef = (INL v,ef) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Pop ann bt)) = SOME rt /\
                  eval_operand (vv_operand vv) u = SOME w ==>
                  w2n w + type_memory_size rt <= lo /\
                  (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
                         val_in_memory rt v (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv (Pop ann bt)) ==>
                ptr_buf_ok cenv (Pop ann bt) op G' u) /\
      (!t' ptr. vv = LocatedValue t' ptr /\ ptr.ptr_location = LocMemory ==>
                ptr_buf_ok cenv (Pop ann bt) ptr.ptr_operand G' u) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
    (\H res ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac pop_target_inputs_mods >>
  qabbrev_tac `gs = gas_explicit marks s0.vs_gas_readings` >>
  `eval_target_place cx bt (es with gas_obs := gs) =
     (INL (MemoryPlace id path),ee)` by
    (`ee with gas_obs := [] = ee` by
       (qpat_assum `ee.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
     qpat_assum `!tail. eval_target_place _ _ _ = _`
       (qspec_then `[]` assume_tac) >>
     fs[Abbr `gs`]) >>
  `expr_body_pre_mods mods cenv cx env (Pop ann bt) (es with gas_obs := gs)` by
    simp[memory_arm_pre_obs] >>
  drule_all_then strip_assume_tac pop_memory_live_array_mods >>
  drule_all_then strip_assume_tac pop_target_source_facts_mods >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (qspec_then `H0` (drule_then assume_tac)) >>
  PairCases_on `dst` >>
  drule_all_then strip_assume_tac pop_reached_memory_header_mods >>
  `evaluate_type (get_tenv cx) ann = SOME etv` by
    (drule_then (SUBST_ALL_TAC o SYM) env_consistent_type_defs_get_tenv >> simp[]) >>
  qpat_x_assum `evaluate_type (get_tenv cx) (ArrayT ann (Dynamic cap)) = _`
    (mp_tac o ONCE_REWRITE_RULE [vyperValueTheory.evaluate_type_def]) >>
  simp_tac (srw_ss()) [AllCaseEqs()] >> strip_tac >> gvs[] >>
  `type_memory_bytes cenv ann = type_memory_size etv` by
    (irule typed_copy_memory_size >> qexists `get_tenv cx` >>
     qpat_assum `expr_sim_inv_mods mods cenv cx env es`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >> simp[] >> metis_tac[]) >>
  qhdtm_assum `write_target_entry_mods`
    (strip_assume_tac o REWRITE_RULE [write_target_entry_mods_def]) >>
  `?x0 x1 x2 x3 x4 x5 x6.
     ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6] /\
     EVERY (\x. ~not_fresh_at sm x) [x0;x1;x2;x3;x4;x5;x6] /\
     vv = LocatedValue ann (mk_ptr (Var x6) LocMemory) /\
     sb.cs_current_bb = sm.cs_current_bb /\
     sb.cs_current_insts = sm.cs_current_insts ++
      memory_pop_insts (Var p) sm.cs_next_id (type_memory_size etv) x0 x1 x2 x3 x4 x5 x6` by
    (irule memory_arm_compile >> goal_assum (drule_at (Pat `compile_get_target_ptr _ _ _ _ = _`)) >>
     qexists `ty` >> asm_rewrite_tac[]) >>
  pop_assum strip_assume_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (qspec_then `H0` (drule_then (strip_assume_tac o MATCH_MP write_target_post_view_mods))) >>
  drule_all_then strip_assume_tac fn_has_code_code >>
  Cases_on `vs = []`
  >- suspend "empty" >>
  suspend "live"
QED

Resume pop_reached_memory_arm_mods[empty]:
  qpat_x_assum `vs = []` SUBST_ALL_TAC >>
  rename1 `isPREFIX (memory_pop_insts (Var p) _ _ x0 x1 x2 x3 x4 x5 x6) _` >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `w2n (b + n2w k) + 32 <= t.vs_alloca_next` by decide_tac >>
  `mload (w2n (b+n2w k)) t = 0w` by simp[] >>
  `mem_word_taint tn.t_mem (w2n (b+n2w k)) = {}` by simp[] >>
  `ALL_DISTINCT [x0;x1;x2]` by fs[] >>
  `isPREFIX [mk_inst sm.cs_next_id MLOAD [Var p] [x0];
     mk_inst (sm.cs_next_id+1) ISZERO [Var x0] [x1];
     mk_inst (sm.cs_next_id+2) ISZERO [Var x1] [x2]]
     (DROP t.vs_inst_idx bb.bb_instructions)` by
    (irule isPREFIX_TRANS >>
     qexists `memory_pop_insts (Var p) sm.cs_next_id (type_memory_size etv) x0 x1 x2 x3 x4 x5 x6` >>
     reverse conj_tac >- asm_rewrite_tac[] >> simp[memory_pop_insts_def]) >>
  `get_instruction bb (t.vs_inst_idx+3) =
    SOME (mk_inst (sm.cs_next_id+3) ASSERT [Var x2] [])` by
    (drule_all_then strip_assume_tac fn_has_code_same_block >>
     qpat_assum `!i. i < LENGTH (memory_pop_insts _ _ _ _ _ _ _ _ _ _) ==> _`
       (qspec_then `3` mp_tac) >> fs[memory_pop_insts_def]) >>
  drule_all pop_memory_empty_exit_mods >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  `!tail. pop_place cx (MemoryPlace id path) (ee with gas_obs := tail) =
    (INR (Error (RuntimeError "pop empty memory array")),ee with gas_obs := tail)` by
    (drule_then strip_assume_tac lookup_scopes_find_containing_scope >>
     gen_tac >> irule pop_memory_place_live_empty >> simp[] >>
     goal_assum (drule_at (Pat `find_containing_scope _ _ = _`)) >> simp[]) >>
  irule gas_outcome_full_mods_exit_revert >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G'`,`ee`,`INR (Error (RuntimeError "pop empty memory array"))`,`tn'`,`v`] >>
  simp[exit_result_def,exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def]
QED

Resume pop_reached_memory_arm_mods[live]:
  rename1 `isPREFIX (memory_pop_insts (Var p) _ _ x0 x1 x2 x3 x4 x5 x6) _` >>
  qabbrev_tac `esz = type_memory_size etv` >>
  qabbrev_tac `addr = w2n (b+n2w k) + 32 + (LENGTH vs-1)*esz` >>
  `addr + esz <= w2n b + sz` by (fs[Abbr `addr`,MULT_COMM] >> decide_tac) >>
  `addr < dimword (:256)` by decide_tac >>
  `?base span. FLOOKUP G p = SOME (base,span) /\ w2n b + sz <= base+span` by
    (irule memory_arm_provenance >> qexistsl_tac [`root`,`t`,`tn`] >> asm_rewrite_tac[]) >>
  rename1 `w2n b + sz <= addr_bound_base + addr_bound_span` >>
  `addr + esz <= addr_bound_base + addr_bound_span` by decide_tac >>
  `ALL_DISTINCT [p;x0;x1;x2;x3;x4;x5;x6]` by
    (qpat_assum `ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6]` mp_tac >>
     qpat_assum `not_fresh_at sm p` mp_tac >>
     qpat_assum `EVERY (\x. ~not_fresh_at sm x) _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]) >>
  `0 < LENGTH vs` by
    (qpat_assum `vs <> []` mp_tac >> rpt (pop_assum kall_tac) >> Cases_on `vs` >> simp[]) >>
  `w2n (b+n2w k) + 32 <= t.vs_alloca_next` by decide_tac >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  mp_tac (Q.INST [`k` |-> `LENGTH sm.cs_current_insts`,
    `s` |-> `t`, `w` |-> `b+n2w k`, `len` |-> `LENGTH (vs:value list)`,
    `root_base` |-> `addr_bound_base`, `span` |-> `addr_bound_span`,
    `id` |-> `sm.cs_next_id`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (SIMP_RULE bool_ss [LET_THM] pop_memory_positive_run_mods)) >>
  impl_tac >-
    (asm_rewrite_tac[] >> conj_tac
     >- (irule LESS_EQ_LESS_TRANS >> qexists_tac `cap` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `w2n (b+n2w k) = _` (pure_once_rewrite_tac o single o SYM) >>
     qpat_assum `addr < dimword (:256)` mp_tac >>
     qpat_assum `addr + esz <= addr_bound_base + addr_bound_span` mp_tac >>
     simp_tac bool_ss [Abbr `addr`]) >>
  disch_then (qx_choose_then `q` (qx_choose_then `Gf` (qx_choose_then `tf` strip_assume_tac))) >>
  qabbrev_tac `u = q with vs_inst_idx := LENGTH sm.cs_current_insts + 9` >>
  `u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (conj_tac
     >- (qpat_assum `u = t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>`
           (mp_tac o Q.AP_TERM `\z. z.vs_current_bb`) >> simp[]) >>
     simp[Abbr `u`,memory_pop_insts_def]) >>
  `popped_keys_indexed ee.scopes` by
    (irule eval_target_place_popped_keys_indexed >>
     goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
     qpat_assum `expr_sim_inv_mods mods cenv cx env es`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >> simp[]) >>
  `dynarray_len_untupled cenv id k` by
    (qpat_assum `!m ce c en st i ty tv ps j el n. _ ==> dynarray_len_untupled ce i j`
       irule >> goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
     goal_assum (drule_at (Pat `expr_sim_inv_mods _ _ _ _ _`)) >> simp[]) >>
  `!z cap. cenv.ce_return_buf = SOME (PtrVar (Var z) cap) ==> not_fresh_at sm z` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sa` >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `!z cap. cenv.ce_return_pc = SOME (PtrVar (Var z) cap) ==> not_fresh_at sm z` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sa` >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `!z. not_fresh_at sm z ==> lookup_var z u = lookup_var z t /\
     FLOOKUP Gf z = FLOOKUP G z /\ op_taint tf (Var z) = op_taint tn (Var z)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. ~MEM x _ ==> _` irule >>
     qpat_assum `not_fresh_at sm z` mp_tac >>
     qpat_assum `EVERY (\x. ~not_fresh_at sm x) _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]) >>
  suspend "source"
QED

Resume pop_reached_memory_arm_mods[source]:
  drule_then strip_assume_tac lookup_scopes_find_containing_scope >>
  drule_all pop_memory_live_transition >>
  disch_then (qspec_then `cx` (qx_choose_then `updated` strip_assume_tac)) >>
  rename1 `find_containing_scope id ee.scopes = SOME (pre,sc,entry,rest)` >>
  qabbrev_tac `tv = PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV &(LENGTH vs-1))]))` >>
  qabbrev_tac `ef = ee with scopes := pre ++ sc |+ (id,entry with <|value := updated;
        popped := record_pop path (ArrayV (DynArrayV vs)) (LAST vs) entry.popped|>) :: rest` >>
  `!tail. pop_place cx (MemoryPlace id path) (ee with gas_obs := tail) =
          (INL tv,ef with gas_obs := tail)` by
    (gen_tac >> simp[Abbr `ef`,Abbr `tv`] >> irule pop_memory_place_live >> simp[] >>
     goal_assum (drule_at (Pat `find_containing_scope _ _ = _`)) >> simp[]) >>
  `ef.storage_trace = ee.storage_trace /\ (ef with gas_obs := []) = ef /\
   (ee with gas_obs := []) = ee` by
    simp[Abbr `ef`,evaluation_state_component_equality] >>
  `pop_place cx (MemoryPlace id path) ee = (INL tv,ef)` by
    (qpat_assum `let fin = _ in _` (mp_tac o SIMP_RULE bool_ss [LET_THM]) >>
     simp[Abbr `ef`,Abbr `tv`]) >>
  irule gas_outcome_full_mods_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`,`ef`,`INL tv`,`u`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `H` >> simp_tac bool_ss [] >> strip_tac >>
  conj_tac >- qpat_assum `!D. gas_origin_ptr_path (D,_,_,_,_,_) _ _ _` irule >>
  suspend "post"
QED

Resume pop_reached_memory_arm_mods[post]:
  `valid_horizon cx st0 H ee.storage_trace` by gvs[] >>
  `valid_horizon cx st0 H es.storage_trace` by
    (irule memory_arm_source_horizon >>
     goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (qpat_assum `!h. _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `immutable_decl_sep_mods cenv cx ee.scopes t.vs_vars t.vs_allocas t.vs_alloca_next` by
    (qpat_x_assum `immutable_frame_mods func cenv cx ee t`
       (mp_tac o CONJUNCT2 o REWRITE_RULE [bodyFullPostsModsTheory.immutable_frame_mods_def]) >>
     simp_tac (srw_ss()) [bodyInvSplitTheory.immutable_alloca_sep_mods_def,
          bodyInvSplitTheory.immutable_decl_sep_mods_def,
          exprLoweringPropsTheory.immutable_alloca_sep_def] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `tf.t_mem = tn.t_mem DIFF {i | w2n b+k <= i /\ i < w2n b+k+32}` by
    (qpat_assum `tf.t_mem = tn.t_mem` (pure_once_rewrite_tac o single) >>
     sym_tac >> irule memory_arm_clean_header >> simp[Once ADD_COMM]) >>
  qpat_assum `!h. _ ==> write_target_post_mods h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` (drule_then assume_tac)) >>
  `(!z cap. cenv.ce_return_buf = SOME (PtrVar (Var z) cap) ==> not_fresh_at sm z) /\
   (!z cap. cenv.ce_return_pc = SOME (PtrVar (Var z) cap) ==> not_fresh_at sm z)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `type_memory_bytes cenv ann = type_memory_size etv` by
    (irule typed_copy_memory_size >> qexists `get_tenv cx` >>
     qpat_assum `expr_sim_inv_mods mods cenv cx env es`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >> simp[] >> metis_tac[]) >>
  `k + 32 + (LENGTH vs - 1) * type_memory_size etv + type_memory_size etv <= sz` by
    (qpat_assum `type_memory_bytes cenv ann = type_memory_size etv`
       (pure_once_rewrite_tac o single o SYM) >>
     qpat_assum `type_memory_bytes cenv ann = esz` (pure_once_rewrite_tac o single) >>
     qpat_assum `vs <> [] ==> _` (drule_then mp_tac) >>
     rpt (pop_assum kall_tac) >>
     pure_once_rewrite_tac [Q.SPECL [`esz`,`LENGTH vs - 1`] MULT_COMM] >>
     decide_tac) >>
  mp_tac (Q.INST [`H` |-> `H`,
    `mid` |-> `ee`, `s` |-> `t`, `x` |-> `x6`,
    `G'` |-> `Gf`, `tn'` |-> `tf`, `w` |-> `n2w addr : bytes32`,
    `dst` |-> `(Var p,SOME LocMemory,SOME (value_type_place (Type (ArrayT ann (Dynamic cap)))))`]
    (SIMP_RULE bool_ss [LET_THM]
       (INST_TYPE [alpha |-> ``:256``] pop_memory_positive_post_mods))) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qpat_assum `!h. dead_lo_ok_mods h _ _ _ _` (qspec_then `H` ACCEPT_TAC))
     >- (pure_once_rewrite_tac [Q.SPECL [`w2n b`,`sz`] ADD_COMM] >>
         first_assum ACCEPT_TAC)
     >- (qpat_assum `u = t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>` mp_tac >>
         rpt (pop_assum kall_tac) >> simp[venomStateTheory.venom_state_component_equality])
     >- (pure_once_rewrite_tac [Q.SPECL [`w2n b`,`k`] ADD_COMM] >>
         qpat_assum `w2n (b+n2w k) = _` (pure_once_rewrite_tac o single o SYM) >>
         first_assum ACCEPT_TAC)
     >- (simp_tac bool_ss [Abbr `addr`] >> first_assum ACCEPT_TAC)
     >- (qpat_assum `type_memory_bytes cenv ann = type_memory_size etv`
           (pure_once_rewrite_tac o single o SYM) >>
         qpat_assum `type_memory_bytes cenv ann = esz` (pure_once_rewrite_tac o single) >>
         qpat_assum `addr < dimword (:256)` mp_tac >>
         simp_tac bool_ss [wordsTheory.w2n_n2w, LESS_MOD] >>
         simp_tac bool_ss [Abbr `addr`] >>
         qpat_assum `w2n (b+n2w k) = _` (pure_once_rewrite_tac o single) >>
         pure_rewrite_tac [ADD_ASSOC] >>
         pure_once_rewrite_tac [Q.SPECL [`k`,`w2n b`] ADD_COMM] >>
         simp_tac bool_ss []) >>
     qpat_assum `type_memory_bytes cenv ann = type_memory_size etv`
       (pure_once_rewrite_tac o single o SYM) >>
     qpat_assum `type_memory_bytes cenv ann = esz` (pure_once_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `ef1` strip_assume_tac) >>
  `ef1 = ef` by
    (qpat_assum `pop_place _ _ _ = (INL _,ef1)` mp_tac >>
     qpat_assum `pop_place _ _ _ = (INL tv,ef)` (pure_once_rewrite_tac o single) >>
     simp_tac (srw_ss()) [Abbr `tv`]) >>
  qpat_x_assum `ef1 = ef` SUBST_ALL_TAC >>
  qexists_tac `tv` >>
  qpat_assum `(ef with gas_obs := []) = ef` (pure_once_rewrite_tac o single) >>
  qpat_assum `vv = LocatedValue ann _` (pure_once_rewrite_tac o single) >>
  simp_tac (srw_ss()) [Abbr `tv`,contextTheory.vv_location_def,contextTheory.mk_ptr_def] >>
  rpt conj_tac >> FIRST
    [first_assum ACCEPT_TAC,
     qhdtm_assum `vv_post_mods`
       (ACCEPT_TAC o SIMP_RULE (srw_ss()) [contextTheory.mk_ptr_def]),
     qhdtm_assum `vv_store_bound`
       (ACCEPT_TAC o SIMP_RULE (srw_ss()) [loweringPostsTheory.post_value_type_def,
                                         contextTheory.mk_ptr_def]),
     qhdtm_assum `ptr_vv_ok`
       (ACCEPT_TAC o SIMP_RULE (srw_ss()) [loweringPostsTheory.post_value_type_def,
                                         contextTheory.mk_ptr_def])]
QED

Finalise pop_reached_memory_arm_mods
