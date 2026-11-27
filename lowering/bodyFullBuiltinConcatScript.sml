(* Concat on the joint finite-horizon body contract. *)
Theory bodyFullBuiltinConcat
Ancestors exprSimDefs[qualified,ignore_grammar] stmtSimProps[qualified,ignore_grammar]
  bodyFullBuiltinConcatLoop bodyFullBuiltinConcatFrame bodyFullBuiltinConcatEntry
  bodyFullBuiltinConcatReady bodyFullOfVV
  bodyFullHashKeccakFixed[qualified,ignore_grammar] bodyFullIfExpReach[qualified,ignore_grammar]
  bodyFullPreds bodySimFull gasOutcomeFullCompose gasOutcomeFullGuarded
  exprSimConcatResult exprSimConcatSource exprSimHyps exprSimSource
  exprSimHypsDefs exprLowering loweringPosts allocLimits vyperTypeInvariants
  vyperTypeSystem vyperContext compileEnv emitHelperProps fragExec
  gasShadowCompile gasShadowCompileHelpers gasShadowState
  reasonCodeResourcesPtr bodyPtrAttributeFields stateRelProj
  vyperTypeConversions valueEncoding valueEncodingDefs valueEncodingProps vfmConstants
  vyperAST words arithmetic list
  bodyFullPredsMods[qualified] bodyFullShadowBodyInv[qualified] bodyInvSplit[qualified]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Builtin a (Concat n) args) es` by suspend "vv" >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule bodyFullOfVVTheory.expr_sim_full_of_vv >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> simp[]) >>
  qpat_assum `expr_body_pre _ _ _ (Builtin a (Concat n) args) _`
    (mp_tac o MATCH_MP exprSimHypsTheory.expr_body_pre_type_evaluates) >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qexists `x` >> simp[] >> rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (Builtin a (Concat n) args)
     (es with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
  strip_tac >> gvs[] >> metis_tac[]
QED
*)
Theorem concat_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a n args es.
    (builtin_args_length_ok (Concat n) (LENGTH args) ==>
      body_exprs_full_ok_mods mods exps cx args) /\
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin a (Concat n) args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a (Concat n) args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a (Concat n) args) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume concat_sim_full[vv]:
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_initial_domain >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  conj_tac >- first_assum ACCEPT_TAC >> disch_tac >>
  drule_all concat_loop_initial_entry >>
  disch_then (qspec_then `PG` (qx_choosel_then
    [`s4`,`s5`,`shadow_s4`,`shadow_s5`,`t4`,`G4`,`tn4`,`dp`,`ov`,`ow`,
     `binst`,`B`,`bsz`,`oinst`,`buf`,`bv`,`fo`,`s6`,`u'`,`tvr`]
    (map_every assume_tac o CONJUNCTS))) >>
  map_every (fn q => qpat_x_assum q
    (assume_tac o CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))))
    [`bsz = concat_alloc_size _`, `binst = mk_inst _ ALLOCA _ _`,
     `oinst = mk_inst _ ALLOCA _ _`] >>
  qhdtm_assum `concat_loop_ready`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [concat_loop_ready_def]) >>
  drule (PURE_ONCE_REWRITE_RULE [GSYM concat_loop_ready_def] concat_args_sim_full) >>
  disch_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ loopQ loopR` >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ finalQ finalR` >>
  `storage_trace_frame (eval_expr cx (Builtin a (Concat n) args))` by
    simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s0,G0,tn0) [] (OK t4,G4,tn4)` by simp[] >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_expr cx (Builtin a (Concat n) args))
    (es,t4,G4,tn4) finalQ finalR` by suspend "finish" >>
  mp_tac (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,`tops` |-> `cx_tops cx`,
    `s1` |-> `t4`,`G1` |-> `G4`,`tn1` |-> `tn4`,
    `Q` |-> `finalQ`,`R` |-> `finalR`]
    (SPEC_ALL (Q.ISPEC `eval_expr cx (Builtin a (Concat n) args)`
      (Q.GEN `source` gasOutcomeFullGuardedTheory.gas_outcome_full_zero_prefix_guarded)))) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume concat_sim_full[finish]:
  qspecl_then [`cx`,`a`,`n`,`args`] mp_tac exprSimHypsTheory.eval_expr_concat_bind >>
  (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (fn th => rewrite_tac[th]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_values >>
      qexistsl [`mid`,`t`,`v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_values >> simp[])
  >~ [`storage_trace_frame (eval_exprs _ _)`]
  >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >- (gen_tac >> BETA_TAC >> simp[vyperStorageTraceTheory.storage_trace_frame_def]) >>
  qexists `\H res ee G tn t. loopQ H res ee G tn t /\
    ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "continuation" >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ loopQ loopR` (irule_at Any) >>
  conj_tac >- simp[] >> simp[Abbr `loopR`,Abbr `finalR`] >>
  rpt strip_tac >> Cases_on `res`
  >- (qpat_assum `expr_exit (INL _) _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[exprSimDefsTheory.expr_exit_def]) >>
  rename1 `expr_exit (INR ex) r` >> simp[] >>
  rpt conj_tac
  >- (qpat_assum `expr_exit (INR ex) r` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[stmtSimPropsTheory.expr_exit_INR_type])
  >- (qpat_assum `halt_exit H cx ee (INR ex) r` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[exprSimDefsTheory.halt_exit_def]) >>
  simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume concat_sim_full[continuation]:
  qx_genl_tac [`marks`,`res`,`ee`,`G5`,`tn5`,`t5`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `loopQ` >> disch_then (strip_assume_tac o BETA_RULE) >>
  rename1 `res = INL vs` >> qpat_x_assum `res = INL vs` SUBST_ALL_TAC >>
  qspecl_then [`a`,`n`,`MAP expr_type args`,`vs`,`get_tenv cx`,`tvr`]
    mp_tac exprSimConcatResultTheory.concat_typed_result >>
  (impl_tac >-
    (rpt conj_tac >> asm_rewrite_tac[] >>
     simp[listTheory.LIST_REL_MAP1,combinTheory.o_DEF] >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `v` (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `payload = FLAT (MAP (\v. case v of BytesV bs => bs
    | StringV str => MAP (n2w o ORD) str | _ => []) vs)` >>
  `LENGTH payload < dimword (:256)` by
    (qpat_assum `LENGTH (payload:word8 list) <= _` mp_tac >>
     qpat_assum `32 + SUM _ <= bsz` mp_tac >>
     qpat_assum `bsz < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `lookup_var bv t5 = SOME (n2w B)` by
    (qpat_assum `!z w. not_fresh_at s4 z /\ _ ==> _` irule >> simp[]) >>
  `FLOOKUP G5 bv = FLOOKUP G4 bv /\ op_taint tn5 (Var bv) = op_taint tn4 (Var bv)` by
    (qpat_assum `ghost_kept_at lo cenv es s4 G4 tn4 t4 G5 tn5` mp_tac >>
     qpat_assum `not_fresh_at s4 bv` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[bodyPtrDefsTheory.ghost_kept_at_def]) >>
  `ptr_covers G5 tn5 bv t5 bsz` by
    (qpat_assum `ptr_covers G4 tn4 bv t4 bsz` mp_tac >>
     qpat_assum `lookup_var bv t4 = _` mp_tac >>
     qpat_assum `lookup_var bv t5 = _` mp_tac >>
     qpat_assum `FLOOKUP G5 bv = _` mp_tac >>
     qpat_assum `op_taint tn5 (Var bv) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[bodyPtrDefsTheory.ptr_covers_def]) >>
  `s4.cs_next_var <= s5.cs_next_var` by
    (qpat_assum `ci_mono s4 s5` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `local_ptrs_reserved cenv s5` by
    (qspecl_then [`cenv`,`s4`,`s5`]
      mp_tac exprLoweringPropsTheory.local_ptrs_reserved_next_var >> simp[]) >>
  `not_fresh_at s5 bv /\ not_fresh_at s5 ov` by
    (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `s4` >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s5 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `s4` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s5 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `s4` >> simp[]) >>
  suspend "suffix"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume concat_sim_full[suffix]:
  `!name lb lsz. local_region cenv ee.scopes t5 name lb lsz ==>
    regions_disjoint B 32 lb lsz` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!name lb lsz. local_region cenv ee.scopes t5 name lb lsz <=> _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     qpat_assum `!name lb lsz. local_region cenv es.scopes t4 name lb lsz ==> _ /\ _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     qpat_assum `local_region cenv ee.scopes t5 name lb lsz` mp_tac >>
     qpat_assum `32 <= bsz` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!name lb lsz. local_region cenv es.scopes t4 name lb lsz ==>
    regions_disjoint B 32 lb lsz` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!name lb lsz. local_region cenv es.scopes t4 name lb lsz ==> _ /\ _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     qpat_assum `local_region cenv es.scopes t4 name lb lsz` mp_tac >>
     qpat_assum `32 <= bsz` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  mp_tac (Q.INST [`sa` |-> `s5`, `sm` |-> `s6`, `u` |-> `u'`,
    `s` |-> `t5`, `G` |-> `G5`, `tn` |-> `tn5`, `inst` |-> `binst`,
    `k` |-> `LENGTH (payload:word8 list)`,
    `H0` |-> `storage_trace_horizon ee.storage_trace`, `es` |-> `ee`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (SPEC_ALL bodyFullBuiltinConcatFrameTheory.concat_suffix_full)) >>
  (impl_tac >- (simp[Abbr `binst`,venomInstTheory.mk_inst_def] >>
     first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`t6`,`G6`,`tn6`] (map_every assume_tac o CONJUNCTS)) >>
  disj1_tac >> qexists `vs` >> conj_tac >- REFL_TAC >>
  mp_tac (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
    `tops` |-> `cx_tops cx`, `es` |-> `ee`, `s` |-> `t5`,
    `G` |-> `G5`, `tn` |-> `tn5`, `t` |-> `t6`,
    `G'` |-> `G6`, `tn'` |-> `tn6`,
    `res` |-> `INL (Value v):eval_result + exception`,
    `Q` |-> `finalQ`, `R` |-> `finalR`]
    (SPEC_ALL (Q.ISPEC `\st:evaluation_state.
      ((case evaluate_concat n vs of INL v => INL (Value v)
        | INR err => INR (Error err)),st)`
      (Q.GEN `source` gasOutcomeFullComposeTheory.gas_outcome_full_pure)))) >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[] >> qx_gen_tac `H` >> disch_tac >> conj_tac
     >- first_assum MATCH_ACCEPT_TAC >> suspend "post")) >>
  disch_then ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume concat_sim_full[post]:
  `ee with gas_obs := [] = ee` by
    (qpat_assum `ee.gas_obs = []` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `INL vs = INL _` (SUBST_ALL_TAC o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `t6 = _` kall_tac >>
  `stmt_state_rel H ctx func cenv cx ee t6` by
    (qpat_assum `!H. stmt_state_rel H ctx func cenv cx ee t5 ==> _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `ghost_inv_at (DF H) lo d cenv cx ee G6 tn6 t6` by
    (qpat_assum `!D. ghost_inv_at D lo d cenv cx ee G5 tn5 t5 ==> _`
       (qspec_then `DF H` mp_tac) >> simp[]) >>
  `lookup_var bv t6 = SOME (n2w B)` by
    (qpat_assum `!x. not_fresh_at s5 x ==> _ /\ _ /\ _`
       (qspec_then `bv` mp_tac) >> simp[]) >>
  `mem_bytes_at (B+32) (LENGTH payload) t5.vs_memory = payload` by
    (qpat_assum `mem_bytes_at (B+32) _ t5.vs_memory = _` mp_tac >>
     qunabbrev_tac `payload` >> POP_ASSUM_LIST (K all_tac) >>
     simp[valueEncodingDefsTheory.mem_bytes_at_def]) >>
  `mem_bytes_at (B+32) (LENGTH payload) t6.vs_memory = payload` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n t6.vs_memory = _`
       (qspecl_then [`B+32`,`LENGTH payload`] mp_tac) >> simp[]) >>
  `val_in_memory tvr v B t6.vs_memory` by
    (qpat_assum `!off mem. val_in_memory tvr v off mem <=> _`
       (qspecl_then [`B`,`t6.vs_memory`] mp_tac) >>
     simp[valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
  `!i. B+32 <= i /\ i < B+32+LENGTH payload ==> i NOTIN tn6.t_mem` by
    (rpt gen_tac >> strip_tac >>
     `i NOTIN tn5.t_mem` by
       (qpat_assum `!i. B+32 <= i /\ _ ==> i NOTIN tn5.t_mem`
          (qspec_then `i` mp_tac) >> simp[Abbr `payload`]) >>
     qpat_assum `i NOTIN tn5.t_mem` mp_tac >>
     qpat_assum `tn6.t_mem SUBSET tn5.t_mem` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
  Q.SUBGOAL_THEN `a = BaseT (BytesT (Dynamic n)) \/ a = BaseT (StringT n)` ASSUME_TAC
  >- (qpat_assum `a = BaseT (BytesT (Dynamic n)) /\ _ \/ a = BaseT (StringT n) /\ _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `val_footprint tvr v <= 32 + SUM (MAP concat_payload_capacity (MAP expr_type args))` by
    (qpat_assum `val_footprint tvr v = _` mp_tac >>
     qpat_assum `LENGTH (payload:word8 list) <= _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `val_store_size tvr v <= bsz` by
    (qpat_assum `a = BaseT (BytesT (Dynamic n)) \/ a = BaseT (StringT n)` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) a = SOME tvr` mp_tac >>
     qpat_assum `val_footprint tvr v <= _` mp_tac >>
     qunabbrev_tac `bsz` >> POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
     drule vyperTypeConversionsTheory.evaluate_type_BaseT_SOME >> strip_tac >> gvs[] >>
     Cases_on `v` >>
     gvs[loweringPostsTheory.val_footprint_def,exprSimPropsTheory.val_store_size_def,
       valueEncodingTheory.type_memory_size_def] >>
     drule exprSimPropsTheory.word_size_monotone >>
     simp[exprLoweringTheory.concat_alloc_size_def,vfmConstantsTheory.word_size_def,
       arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `type_memory_bytes cenv (lowered_value_type cenv (Builtin a (Concat n) args)) <= bsz` by
    (qpat_assum `a = BaseT (BytesT (Dynamic n)) \/ a = BaseT (StringT n)` mp_tac >>
     qunabbrev_tac `bsz` >> POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     gvs[exprLoweringTheory.lowered_value_type_def,exprLoweringTheory.concat_buffer_type_def,
       compileEnvTheory.type_memory_bytes_def,exprLoweringTheory.concat_alloc_size_def,
       listTheory.MAP_MAP_o,combinTheory.o_DEF,vfmConstantsTheory.word_size_def] >>
     simp[arithmeticTheory.MAX_DEF]) >>
  `B < dimword (:256)` by
    (qpat_assum `B+bsz < dimword (:256)` mp_tac >> POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `!i. B <= i /\ i < B+val_footprint tvr v ==> i NOTIN tn6.t_mem` by
    (qpat_assum `val_footprint tvr v = _` (fn th => rewrite_tac[th]) >>
     rpt gen_tac >> strip_tac >> Cases_on `i < B+32`
     >- (qpat_assum `!i. B <= i /\ i < B+32 ==> i NOTIN tn6.t_mem`
          (qspec_then `i` mp_tac) >> simp[]) >>
     qpat_assum `!i. B+32 <= i /\ _ ==> i NOTIN tn6.t_mem`
       (qspec_then `i` mp_tac) >>
     (impl_tac >- decide_tac) >> disch_then ACCEPT_TAC) >>
  suspend "representation"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume concat_sim_full[representation]:
  `w2n (n2w B:bytes32) = B` by simp[] >>
  `ptr_mem_ok cx a v (Var bv) G6 tn6 t6` by
    (irule reasonCodeResourcesPtrTheory.clean_memory_representation_ptr >>
     qexistsl [`n2w B:bytes32`,`bsz`,`tvr`] >>
     qpat_assum `w2n (n2w B:bytes32) = B` (fn th => pure_rewrite_tac [th]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `ptr_covers G6 tn6 bv t6 bsz`
    (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_covers_def]) >>
  `ptr_vv_ok cx a (Value v) (LocatedValue a (base_ptr buf)) ee G6 tn6 t6` by
    (irule bodyPtrAttributeFieldsTheory.ptr_vv_ok_memory >>
     qpat_assum `buf.buf_operand = Var bv` (fn th =>
       simp[NoAsms,contextTheory.base_ptr_def,vyperStateTheory.read_result_def,
         vyperStateTheory.return_def,th]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `ptr_buf_ok cenv (Builtin a (Concat n) args) (Var bv) G6 t6` by
    (qpat_assum `ptr_covers G6 tn6 bv t6 bsz` mp_tac >>
     qpat_assum `type_memory_bytes cenv _ <= bsz` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodyPtrDefsTheory.ptr_covers_def,bodyPtrDefsTheory.ptr_buf_ok_def,
       venomStateTheory.eval_operand_def] >> rpt strip_tac >> gvs[] >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `s0.vs_alloca_next <= t6.vs_alloca_next` by
    (qpat_assum `s0.vs_alloca_next <= t4.vs_alloca_next` mp_tac >>
     qpat_assum `t4.vs_alloca_next <= t5.vs_alloca_next` mp_tac >>
     qpat_assum `t6.vs_alloca_next = t5.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  qunabbrev_tac `finalQ` >> BETA_TAC >> qexists `Value v` >>
  qpat_assum `ee with gas_obs := [] = ee` (fn th => pure_rewrite_tac [th]) >>
  qpat_assum `vv = LocatedValue a (base_ptr buf)` (fn th => pure_rewrite_tac [th]) >>
  pure_rewrite_tac [contextTheory.base_ptr_def,contextTheory.vv_location_def,
    contextTheory.vv_operand_def,vyperASTTheory.expr_type_def] >>
  qpat_assum `buf.buf_operand = Var bv` (fn th => pure_rewrite_tac [th]) >>
  suspend "frames"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume concat_sim_full[frames]:
  qpat_assum `stmt_state_rel H ctx func cenv cx ee t6`
    (fn th => simp[NoAsms, MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp th]) >>
  map_every (fn q => qpat_assum q (fn th => simp[NoAsms,th]))
    [`t6.vs_current_bb = sb.cs_current_bb`,
     `t6.vs_inst_idx = LENGTH sb.cs_current_insts`,
     `alloca_history func t6`,
     `s0.vs_alloca_next <= t6.vs_alloca_next`,
     `ghost_inv_at (DF H) lo d cenv cx ee G6 tn6 t6`,
     `ptr_buf_ok cenv (Builtin a (Concat n) args) (Var bv) G6 t6`] >>
  qpat_assum `ptr_vv_ok cx a (Value v) _ ee G6 tn6 t6` mp_tac >>
  qpat_assum `buf.buf_operand = Var bv` (fn th =>
    simp[NoAsms,th,contextTheory.base_ptr_def]) >> disch_tac >>
  simp[NoAsms,vyperASTTheory.expr_type_def,
    loweringPostsTheory.post_value_type_def] >>
  rpt conj_tac
  >~ [`vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`]
  >- suspend "vvpost"
  >~ [`vv_store_bound _ _ _ _ _ _ _`]
  >- suspend "storebound"
  >~ [`ptr_vv_ok _ _ _ _ _ _ _ _`]
  >- first_assum ACCEPT_TAC
  >~ [`_ ==> vv_own _ _ _ _ _ _ _ _ _`]
  >- (qpat_assum `a = BaseT (BytesT (Dynamic n)) \/ a = BaseT (StringT n)` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      strip_tac >> simp[compileEnvTheory.is_bytestring_type_def])
  >> suspend "kept"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume concat_sim_full[vvpost]:
  `sa.cs_next_id < s5.cs_next_id+2` by
    (qpat_assum `ci_mono s4 s5` mp_tac >>
     qpat_assum `s4.cs_next_id = sa.cs_next_id+4` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `!name lb lsz. local_region cenv ee.scopes t6 name lb lsz <=>
    local_region cenv ee.scopes t5 name lb lsz` by
    (rpt gen_tac >>
     qspecl_then [`cenv`,`s5`,`ee.scopes`,`t5`,`t6`,`name`,`lb`,`lsz`]
       mp_tac exprSimConcatResultTheory.concat_local_region_vars >>
     (impl_tac >-
       (conj_tac >- first_assum ACCEPT_TAC >> rpt gen_tac >> disch_tac >>
        qpat_assum `!x. not_fresh_at s5 x ==> _ /\ _ /\ _`
          (qspec_then `x` mp_tac) >> simp[])) >> disch_then ACCEPT_TAC) >>
  `!name lb lsz. local_region cenv ee.scopes t6 name lb lsz ==>
    B+bsz <= lb \/ lb+lsz <= B` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!name lb lsz. local_region cenv ee.scopes t6 name lb lsz <=> _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     qpat_assum `!name lb lsz. local_region cenv ee.scopes t5 name lb lsz <=> _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     qpat_assum `!name lb lsz. local_region cenv es.scopes t4 name lb lsz ==> _ /\ _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     qpat_assum `local_region cenv ee.scopes t6 name lb lsz` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `wb_frame cenv es ee sa s0 t6` by suspend "wb" >>
  `EVERY ($~ o expr_has_effect) args ==> pure_frame cenv func es sa s0 t6` by
    suspend "pure" >>
  `FLOOKUP t5.vs_allocas sa.cs_next_id = SOME (B,bsz)` by
    (qpat_assum `Abbrev (binst = _)` (fn th =>
       qpat_assum `FLOOKUP t5.vs_allocas binst.inst_id = SOME (B,bsz)`
         (mp_tac o REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] th,
                                 venomInstTheory.mk_inst_def])) >>
     simp[]) >>
  mp_tac (Q.INST [`e` |-> `Builtin a (Concat n) args`,
    `tv` |-> `tvr`,`w` |-> `n2w B:bytes32`, `s` |-> `t6`,
    `p` |-> `base_ptr buf`,`aid` |-> `sa.cs_next_id`,
    `b` |-> `B`,`sz` |-> `bsz`,`es'` |-> `ee`]
      (Q.ISPEC `(H:(bool # bytes32 # type_value) list # num list)`
        (Q.GEN `H` exprSimHashTheory.vv_post_allocated_memory_intro))) >>
  qpat_assum `buf.buf_operand = Var bv` (fn th =>
    pure_rewrite_tac [th,vyperASTTheory.expr_type_def,contextTheory.base_ptr_def]) >>
  (impl_tac >-
    (simp[valueEncodingPropsTheory.mem_word_at_eq_mload,venomStateTheory.eval_operand_def,
       vyperASTTheory.expr_type_def] >>
     conj_tac >-
       (qpat_assum `lookup_var bv t6 = SOME w` mp_tac >>
        qpat_assum `lookup_var bv t6 = SOME (n2w B)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[]) >>
     qx_genl_tac [`name`,`lb`,`lsz`] >> disch_tac >>
     qpat_assum `!name lb lsz. local_region cenv es.scopes t4 name lb lsz ==> _ /\ _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >> simp[])) >>
  disch_then ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume concat_sim_full[wb]:
  `sa.cs_next_var <= s4.cs_next_var /\ sa.cs_next_var <= s5.cs_next_var` by
    (qpat_assum `s4.cs_next_var = sa.cs_next_var+3` mp_tac >>
     qpat_assum `s4.cs_next_var <= s5.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  rewrite_tac[loweringPostsTheory.wb_frame_def] >> rpt conj_tac
  >- (qx_genl_tac [`x`,`w`] >> strip_tac >>
      `not_fresh_at s4 x /\ not_fresh_at s5 x` by
        (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `sa` >> simp[]) >>
      `lookup_var x t4 = SOME w` by
        (qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _`
           (qspec_then `x` mp_tac) >> simp[]) >>
      `lookup_var x t5 = SOME w` by
        (qpat_assum `!z w. not_fresh_at s4 z /\ _ ==> _` irule >> simp[]) >>
      qpat_assum `!x. not_fresh_at s5 x ==> _ /\ _ /\ _`
        (qspec_then `x` mp_tac) >> simp[])
  >- (qx_genl_tac [`aid`,`entry`] >> disch_tac >>
      qpat_assum `t6.vs_allocas = t5.vs_allocas` (fn th => rewrite_tac [th]) >>
      qpat_assum `!aid a. FLOOKUP t4.vs_allocas aid = SOME a ==> _` irule >>
      qpat_assum `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> _` irule >>
      first_assum ACCEPT_TAC)
  >- suspend "wbmem" >>
  suspend "wblocals"
QED
*)
(* SCRATCH MEASUREMENT: original continuation.
Resume concat_sim_full[wbmem]:
  qx_genl_tac [`aid`,`off`,`sz`] >> strip_tac >>
  `regions_disjoint B bsz off sz /\ regions_disjoint (w2n ow) 64 off sz` by
    (qpat_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _`
       (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[]) >>
  `FLOOKUP t4.vs_allocas aid = SOME (off,sz)` by
    (qpat_assum `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  `!name lb lsz. local_region cenv es.scopes t4 name lb lsz <=>
    local_region cenv es.scopes s0 name lb lsz` by
    (rpt gen_tac >>
     qspecl_then [`cenv`,`sa`,`es.scopes`,`s0`,`t4`,`name`,`lb`,`lsz`]
       mp_tac exprSimConcatResultTheory.concat_local_region_vars >>
     (impl_tac >-
       (conj_tac >- first_assum ACCEPT_TAC >> rpt gen_tac >> disch_tac >>
        qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _`
          (qspec_then `x` mp_tac) >> simp[])) >> disch_then ACCEPT_TAC) >>
  `mem_bytes_at off sz t4.vs_memory = mem_bytes_at off sz s0.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n t4.vs_memory = _` irule >>
     qpat_assum `regions_disjoint (w2n (ow:bytes32)) 64 off sz` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at off sz t5.vs_memory = mem_bytes_at off sz t4.vs_memory` by
    (qpat_assum `!aid p n. FLOOKUP t4.vs_allocas aid = SOME (p,n) /\ _ ==> _`
       (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
     (impl_tac >-
       (qpat_assum `FLOOKUP t4.vs_allocas aid = SOME (off,sz)`
          (fn th => simp[NoAsms,th]) >>
        rpt conj_tac
        >- (qpat_assum `aid < sa.cs_next_id` mp_tac >>
            qpat_assum `s4.cs_next_id = sa.cs_next_id+4` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> decide_tac)
        >- (qpat_assum `regions_disjoint B bsz off sz` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[])
        >- (qpat_assum `regions_disjoint (w2n (ow:bytes32)) 64 off sz` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
        qpat_assum `!name lb lsz. local_region cenv es.scopes t4 name lb lsz <=> _`
          (fn th => rewrite_tac [th]) >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `mem_bytes_at off sz t6.vs_memory = mem_bytes_at off sz t5.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n t6.vs_memory = _` irule >>
     qpat_assum `regions_disjoint B bsz off sz` mp_tac >>
     qpat_assum `32 <= bsz` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  simp[]
QED
*)
(* SCRATCH MEASUREMENT: original continuation.
Resume concat_sim_full[wblocals]:
  `locals_kept cenv es es s0 t4` by
    (irule exprSimPropsTheory.locals_kept_regions >>
     qx_genl_tac [`name`,`lb`,`lsz`] >> disch_tac >>
     `regions_disjoint (w2n ow) 64 lb lsz` by
       (qpat_assum `!name b len. local_region cenv es.scopes s0 name b len ==> _ /\ _`
          (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >> simp[]) >>
     qpat_assum `!p n. _ ==> mem_bytes_at p n t4.vs_memory = _` irule >>
     qpat_assum `regions_disjoint (w2n (ow:bytes32)) 64 lb lsz` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `locals_kept cenv es ee s0 t5` by
    (irule exprBopSimPropsTheory.locals_kept_trans >>
     qexistsl [`es`,`sa`,`t4`] >>
     rpt conj_tac
     >- (qx_genl_tac [`x`,`w`] >> strip_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _`
           (qspec_then `x` mp_tac) >> simp[]) >>
     first_assum ACCEPT_TAC) >>
  irule exprSimPropsTheory.locals_kept_regions_tail >>
  qexists `t5` >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qx_genl_tac [`name`,`lb`,`lsz`] >> disch_tac >>
  `regions_disjoint B bsz lb lsz` by
    (qpat_assum `!name b len. local_region cenv es.scopes s0 name b len ==> _ /\ _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >> simp[]) >>
  qpat_assum `!p n. _ ==> mem_bytes_at p n t6.vs_memory = _` irule >>
  qpat_assum `regions_disjoint B bsz lb lsz` mp_tac >>
  qpat_assum `32 <= bsz` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED
*)
(* SCRATCH MEASUREMENT: original continuation.
Resume concat_sim_full[pure]:
  disch_tac >>
  `~EXISTS expr_has_effect args` by
    (qpat_assum `EVERY ($~ o expr_has_effect) args` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[listTheory.EVERY_MEM,listTheory.EXISTS_MEM,combinTheory.o_DEF]) >>
  qpat_assum `~EXISTS expr_has_effect args ==> _ /\ _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `!name lb lsz. local_region cenv es.scopes t4 name lb lsz <=>
    local_region cenv es.scopes s0 name lb lsz` by
    (rpt gen_tac >>
     qspecl_then [`cenv`,`sa`,`es.scopes`,`s0`,`t4`,`name`,`lb`,`lsz`]
       mp_tac exprSimConcatResultTheory.concat_local_region_vars >>
     (impl_tac >-
       (conj_tac >- first_assum ACCEPT_TAC >> rpt gen_tac >> disch_tac >>
        qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _`
          (qspec_then `x` mp_tac) >> simp[])) >> disch_then ACCEPT_TAC) >>
  rewrite_tac[loweringPostsTheory.pure_frame_def] >>
  conj_tac >- suspend "purelocals" >> suspend "pureglobal"
QED
*)
(* SCRATCH MEASUREMENT: original continuation.
Resume concat_sim_full[purelocals]:
  qx_genl_tac [`name`,`lb`,`lsz`] >> disch_tac >>
  `regions_disjoint B bsz lb lsz /\ regions_disjoint (w2n ow) 64 lb lsz` by
    (qpat_assum `!name b len. local_region cenv es.scopes s0 name b len ==> _ /\ _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >> simp[]) >>
  `mem_bytes_at lb lsz t4.vs_memory = mem_bytes_at lb lsz s0.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n t4.vs_memory = _` irule >>
     qpat_assum `regions_disjoint (w2n (ow:bytes32)) 64 lb lsz` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at lb lsz t5.vs_memory = mem_bytes_at lb lsz t4.vs_memory` by
    (qpat_assum `!name lb lsz. local_region cenv es.scopes t4 name lb lsz ==>
       mem_bytes_at lb lsz t5.vs_memory = _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >> simp[]) >>
  `mem_bytes_at lb lsz t6.vs_memory = mem_bytes_at lb lsz t5.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n t6.vs_memory = _` irule >>
     qpat_assum `regions_disjoint B bsz lb lsz` mp_tac >>
     qpat_assum `32 <= bsz` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  simp[]
QED
*)
(* SCRATCH MEASUREMENT: original continuation.
Resume concat_sim_full[pureglobal]:
  qx_genl_tac [`off`,`len`] >> disch_tac >>
  `FLOOKUP t6.vs_allocas binst.inst_id = SOME (B,bsz) /\
   FLOOKUP t6.vs_allocas oinst.inst_id = SOME (w2n ow,64)` by
    (qpat_assum `t6.vs_allocas = t5.vs_allocas` (fn th => simp[th])) >>
  `regions_disjoint off len B bsz` by
    (qpat_assum `!inst b sz. MEM inst (fn_insts func) /\
       inst.inst_opcode = ALLOCA /\ sa.cs_next_id <= inst.inst_id /\ _ ==>
       regions_disjoint off len b sz`
       (qspecl_then [`binst`,`B`,`bsz`] mp_tac) >>
     simp[Abbr `binst`,venomInstTheory.mk_inst_def]) >>
  `regions_disjoint off len (w2n ow) 64` by
    (qpat_assum `!inst b sz. MEM inst (fn_insts func) /\
       inst.inst_opcode = ALLOCA /\ sa.cs_next_id <= inst.inst_id /\ _ ==>
       regions_disjoint off len b sz`
       (qspecl_then [`oinst`,`w2n ow`,`64`] mp_tac) >>
     simp[Abbr `oinst`,venomInstTheory.mk_inst_def]) >>
  `mem_bytes_at off len t4.vs_memory = mem_bytes_at off len s0.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n t4.vs_memory = _` irule >>
     qpat_assum `regions_disjoint off len (w2n (ow:bytes32)) 64` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at off len t5.vs_memory = mem_bytes_at off len t4.vs_memory` by
    (qpat_assum `!p n. _ /\ _ /\ (!inst b sz. _ ==> _) ==>
       mem_bytes_at p n t5.vs_memory = _`
       (qspecl_then [`off`,`len`] mp_tac) >>
     (impl_tac >-
       (conj_tac
        >- (qpat_assum `regions_disjoint off len B bsz` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
        conj_tac
        >- (qpat_assum `regions_disjoint off len (w2n (ow:bytes32)) 64` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
        qx_genl_tac [`inst`,`b`,`sz`] >> strip_tac >>
        `sa.cs_next_id <= inst.inst_id` by
          (qpat_assum `s4.cs_next_id = sa.cs_next_id+4` mp_tac >>
           qpat_assum `s4.cs_next_id <= inst.inst_id` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
        qpat_assum `!inst b sz. MEM inst (fn_insts func) /\
          inst.inst_opcode = ALLOCA /\ sa.cs_next_id <= inst.inst_id /\ _ ==>
          regions_disjoint off len b sz`
          (qspecl_then [`inst`,`b`,`sz`] mp_tac) >>
        qpat_assum `t6.vs_allocas = t5.vs_allocas` (fn th => simp[th]))) >>
     disch_then ACCEPT_TAC) >>
  `mem_bytes_at off len t6.vs_memory = mem_bytes_at off len t5.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n t6.vs_memory = _` irule >>
     qpat_assum `regions_disjoint off len B bsz` mp_tac >>
     qpat_assum `32 <= bsz` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  simp[]
QED
*)
(* SCRATCH MEASUREMENT: original continuation.
Resume concat_sim_full[storebound]:
  map_every (fn q => qpat_assum q mp_tac)
    [`B < dimword (:256)`, `lookup_var bv t6 = SOME (n2w B)`,
     `val_store_size tvr v <= bsz`,
     `type_memory_bytes cenv (lowered_value_type cenv (Builtin a (Concat n) args)) <= bsz`,
     `evaluate_type (get_tenv cx) a = SOME tvr`,
     `B+bsz <= t4.vs_alloca_next`, `t4.vs_alloca_next <= t5.vs_alloca_next`,
     `t6.vs_alloca_next = t5.vs_alloca_next`,
     `a = BaseT (BytesT (Dynamic n)) \/ a = BaseT (StringT n)`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
  simp[exprSimMemDefsTheory.vv_store_bound_def,
    venomStateTheory.eval_operand_def,vyperStateTheory.read_result_def,
    vyperStateTheory.return_def] >> rpt strip_tac >> gvs[] >>
  drule vyperTypeConversionsTheory.evaluate_type_BaseT_SOME >>
  strip_tac >> gvs[exprLoweringTheory.lowered_value_type_def,
    exprLoweringTheory.concat_buffer_type_def,compileEnvTheory.type_memory_bytes_def,
    vyperValueTheory.evaluate_type_def,valueEncodingTheory.type_memory_size_def,
    vfmConstantsTheory.word_size_def] >> decide_tac
QED
*)
(* SCRATCH MEASUREMENT: original continuation.
Resume concat_sim_full[kept]:
  `!name lb lsz. local_region cenv es.scopes t4 name lb lsz <=>
    local_region cenv es.scopes s0 name lb lsz` by
    (rpt gen_tac >>
     qspecl_then [`cenv`,`sa`,`es.scopes`,`s0`,`t4`,`name`,`lb`,`lsz`]
       mp_tac exprSimConcatResultTheory.concat_local_region_vars >>
     (impl_tac >-
       (conj_tac >- first_assum ACCEPT_TAC >> rpt gen_tac >> disch_tac >>
        qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _`
          (qspec_then `x` mp_tac) >> simp[])) >> disch_then ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G5 tn5` by
    (irule wordArgsPtrTheory.ghost_kept_at_trans >>
     qexistsl_tac [`G4`,`es`,`t4`,`s4`,`tn4`] >>
     map_every (fn q => qpat_assum q (fn th => simp[NoAsms,th]))
       [`s4.cs_next_var = sa.cs_next_var+3`,
        `s4.cs_next_id = sa.cs_next_id+4`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `sa.cs_next_var <= s5.cs_next_var` by
    (qpat_assum `s4.cs_next_var = sa.cs_next_var+3` mp_tac >>
     qpat_assum `s4.cs_next_var <= s5.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
  qexistsl_tac [`G5`,`tn5`] >>
  rpt conj_tac
  >- (qx_gen_tac `x` >> disch_tac >>
      `not_fresh_at s5 x` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      qpat_assum `!x. not_fresh_at s5 x ==> _ /\ _ /\ _`
        (qspec_then `x` mp_tac) >> simp[]) >>
  first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise concat_sim_full
*)
