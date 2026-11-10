(* Typed result packaging for Concat. *)
Theory bodyPtrBytestringBuiltinsConcatResult
Ancestors
  bodyPtrBytestringBuiltinsConcatSuffix bodyPtrEnvBuiltinsBoundary
  exprSimConcatResult exprSimHyps exprSimProps exprLowering
  compileEnv loweringPosts bodyPtrDefs words list arithmetic vfmConstants
  vyperTypeConversions valueEncoding bodyPtrBytestringBuiltinsCalldataOutcome
  exprSimHash exprSimSource exprSimHypsDefs exprSimDefs vyperTyping
  vyperTypeSystem allocLimits vyperTypeInvariants gasSummaryComposePtr gasExemptCert
  vyperState vyperContext bodyPtrBytestringBuiltinsConcatCompile
  bodyPtrBytestringBuiltinsConcatArgs annAssignPtrSetup freshWrites exprLoweringProps
  bodyPtrBytestringBuiltinsConcatPostFrame wordArgsPtr valueEncodingProps venomState

Theorem concat_buffer_capacity:
  ann = BaseT (BytesT (Dynamic n)) \/ ann = BaseT (StringT n) ==>
  type_memory_bytes ce (lowered_value_type ce (Builtin ann (Concat n) args)) <=
    concat_alloc_size (MAP expr_type args)
Proof
  strip_tac >> gvs[lowered_value_type_def, concat_buffer_type_def,
    type_memory_bytes_def, concat_alloc_size_def, MAP_MAP_o,
    combinTheory.o_DEF, word_size_def] >>
  simp[MAX_DEF]
QED

Theorem concat_value_store_bound:
  (ann = BaseT (BytesT (Dynamic n)) \/ ann = BaseT (StringT n)) /\
  evaluate_type tenv ann = SOME tv /\
  val_footprint tv v <= 32 + SUM (MAP concat_payload_capacity ts) ==>
  val_store_size tv v <= concat_alloc_size ts
Proof
  strip_tac >> gvs[] >>
  drule evaluate_type_BaseT_SOME >> strip_tac >> gvs[] >>
  Cases_on `v` >>
  gvs[val_footprint_def, val_store_size_def, type_memory_size_def] >>
  drule word_size_monotone >>
  simp[concat_alloc_size_def, word_size_def, MAX_DEF] >> decide_tac
QED

Theorem concat_result_endpoint_ptr:
  2 <= LENGTH args /\
  SUM (MAP bytelike_type_bound (MAP expr_type args)) <= n /\
  ((ann = BaseT (BytesT (Dynamic n)) /\
    EVERY (\t. ?bd. t = BaseT (BytesT bd)) (MAP expr_type args)) \/
   (ann = BaseT (StringT n) /\
    EVERY (\t. ?m. t = BaseT (StringT m)) (MAP expr_type args))) /\
  LIST_REL (\t v. ?tv. evaluate_type (get_tenv cx) t = SOME tv /\
    value_has_type tv v) (MAP expr_type args) vs /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  bs = FLAT (MAP (\v. case v of BytesV bs => bs
    | StringV str => MAP ((n2w : num -> word8) o ORD) str | _ => []) vs) /\
  mem_word_at (w2n w) s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (w2n w+32) (LENGTH bs) s.vs_memory = bs /\
  (!i. w2n w <= i /\ i < w2n w+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
  ptr_covers G tn p s (concat_alloc_size (MAP expr_type args)) /\
  eval_operand (Var p) s = SOME w /\
  stmt_state_rel ctx fn ce cx es' s /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  b <= w2n w /\ w2n w + concat_alloc_size (MAP expr_type args) <= b+sz /\
  (!name lb lsz. local_region ce es'.scopes s name lb lsz ==>
    b+sz <= lb \/ lb+lsz <= b) /\
  wb_frame ce es sa s0 s ==>
  ?v. evaluate_concat n vs = INL v /\
    vv_post ctx fn ce cx (Builtin ann (Concat n) args) es sa sb s0 es'
      (Value v) (LocatedValue ann <|ptr_operand := Var p; ptr_location := LocMemory|>) s /\
    ptr_vv_ok cx (post_value_type ce (Builtin ann (Concat n) args)) (Value v)
      (LocatedValue ann <|ptr_operand := Var p; ptr_location := LocMemory|>) es' G tn s /\
    ptr_buf_ok ce (Builtin ann (Concat n) args) (Var p) G s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `2 <= LENGTH (MAP expr_type args)` by simp[] >>
  drule_all concat_typed_result >> strip_tac >>
  `ann = BaseT (BytesT (Dynamic n)) \/ ann = BaseT (StringT n)` by metis_tac[] >>
  `val_store_size tv v <= concat_alloc_size (MAP expr_type args)` by
    (irule concat_value_store_bound >> conj_tac >- simp[] >>
     qexistsl_tac [`ann`,`n`,`get_tenv cx`] >> simp[]) >>
  `val_in_memory tv v (w2n w) s.vs_memory` by metis_tac[] >>
  `type_memory_bytes ce (lowered_value_type ce (Builtin ann (Concat n) args)) <=
    concat_alloc_size (MAP expr_type args)` by (irule concat_buffer_capacity >> simp[]) >>
  `!i. w2n w <= i /\ i < w2n w + val_footprint tv v ==> i NOTIN tn.t_mem` by
    (rpt strip_tac >> first_x_assum irule >> gvs[]) >>
  drule_all covered_clean_memory_result >>
  disch_then (qspecl_then [`es'`] strip_assume_tac) >>
  (qexists_tac `v` >>
  simp[post_value_type_not_int_call, vyperASTTheory.expr_type_def] >>
  conj_tac >- (
    irule (vv_post_allocated_memory_intro |> Q.INST
      [`e` |-> `Builtin ann (Concat n) args`] |>
      SRULE[vyperASTTheory.expr_type_def]) >>
    simp[post_value_type_not_int_call, vyperASTTheory.expr_type_def] >>
    conj_tac >- gvs[] >>
    qexistsl_tac [`aid`,`b`,`sz`,`tv`] >> simp[] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    assume_tac (Q.SPEC `MAP expr_type args` concat_alloc_size_bounds) >>
    gvs[] >> decide_tac) >>
  gvs[])
QED

Theorem concat_body_pre_facts:
  expr_body_pre ce cx env (Builtin ann (Concat n) args) es ==>
  expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  2 <= LENGTH args /\
  SUM (MAP bytelike_type_bound (MAP expr_type args)) <= n /\
  ((ann = BaseT (BytesT (Dynamic n)) /\
    EVERY (\t. ?bd. t = BaseT (BytesT bd)) (MAP expr_type args)) \/
   (ann = BaseT (StringT n) /\
    EVERY (\t. ?m. t = BaseT (StringT m)) (MAP expr_type args))) /\
  (?tv. evaluate_type (get_tenv cx) ann = SOME tv) /\
  EVERY (\e. is_bytestring_type (expr_type e) \/
    ?m. expr_type e = BaseT (BytesT (Fixed m))) args /\
  concat_alloc_size (MAP expr_type args) < dimword (:256)
Proof
  strip_tac >>
  `!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st` by
    (rpt strip_tac >> irule expr_body_pre_builtin_arg >>
     conj_tac >- simp[] >>
     qexistsl_tac [`ann`,`args`,`Concat n`,`es`] >> simp[]) >>
  `expr_sim_inv ce cx env es /\ well_typed_expr env (Builtin ann (Concat n) args) /\
    alloc_limits_expr ce (Builtin ann (Concat n) args)` by fs[expr_body_pre_def] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `2 <= LENGTH args /\ SUM (MAP bytelike_type_bound (MAP expr_type args)) <= n /\
    well_formed_type env.type_defs ann` by
    (qpat_x_assum `well_typed_expr _ _` mp_tac >>
     simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
     rpt strip_tac >> fs[]) >>
  Q.SUBGOAL_THEN
    `((ann = BaseT (BytesT (Dynamic n)) /\
       EVERY (\t. ?bd. t = BaseT (BytesT bd)) (MAP expr_type args)) \/
      (ann = BaseT (StringT n) /\
       EVERY (\t. ?m. t = BaseT (StringT m)) (MAP expr_type args)))` assume_tac
  >- (qpat_x_assum `well_typed_expr _ _` mp_tac >>
      simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
      rpt strip_tac >> fs[]) >>
  `?tv. evaluate_type (get_tenv cx) ann = SOME tv` by
    (fs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >> gvs[]) >>
  `concat_alloc_size (MAP expr_type args) < 2 ** 64` by
    fs[alloc_limits_expr_def] >>
  simp[] >> conj_tac
  >- (qpat_x_assum `(_ /\ _) \/ (_ /\ _)` strip_assume_tac >>
      fs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >> res_tac >>
      fs[is_bytestring_type_def] >> rename1 `BytesT bd` >>
      Cases_on `bd` >> fs[is_bytestring_type_def]) >>
  irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** 64` >> simp[dimword_def]
QED

Theorem gas_outcome_ptr_values_bind:
  gas_outcome_ptr D tops (ctx,fn) PG
    (source : evaluation_state -> value list evaluation_result)
    (es,s0,G0,tn0) P E /\
  (!res ee G tn t. P res ee G tn t ==>
    ?vs. res = INL vs /\
      gas_outcome_ptr D tops (ctx,fn) PG (next vs) (ee,t,G,tn) Q R) /\
  (!res ee gt r. E res ee gt r ==>
    ?exc. res = INR exc /\ R (INR exc) ee gt r) ==>
  gas_outcome_ptr D tops (ctx,fn) PG (vyperState$bind source next)
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >> irule gas_outcome_ptr_bind >> rpt conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_values >>
      goal_assum (drule_at Any) >> simp[]) 
  >- (rpt strip_tac >> irule gas_exempt_cert_error_values >> simp[]) >>
  irule gas_outcome_ptr_conseq >> qexistsl_tac [`P`,`E`] >> simp[]
QED

Theorem concat_result_vv_sim_ptr:
  (builtin_args_length_ok (Concat n) (LENGTH args) ==> body_exprs_ptr_ok cx args) /\
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (Builtin ann (Concat n) args) es ==>
  expr_vv_sim_ptr d ctx PG fn ce cx ty (Builtin ann (Concat n) args) es
Proof
  strip_tac >> drule concat_body_pre_facts >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `body_exprs_ptr_ok cx args` by fs[builtin_args_length_ok_def] >>
  simp[expr_vv_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_all concat_ptr_compile_cuts >> strip_tac >>
  `32 <= concat_alloc_size (MAP expr_type args)` by
    (assume_tac (Q.SPEC `MAP expr_type args` concat_alloc_size_bounds) >> decide_tac) >>
  drule_all concat_prefix_args_ready >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`]
    (qx_choosel_then [`r`,`p`,`off`,`a`,`ow`,`Gf`,`tnf`,`t`,`binst`,`oinst`]
      (map_every assume_tac o CONJUNCTS))) >>
  suspend "traversal"
QED

Resume concat_result_vv_sim_ptr[traversal]:
  qpat_x_assum `data = Var p` SUBST_ALL_TAC >>
  qpat_x_assum `buf.buf_operand = Var r`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  qpat_assum `ob.buf_operand = Var off` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `32 + 0 + SUM (MAP concat_payload_capacity (MAP expr_type args)) <=
     concat_alloc_size (MAP expr_type args) /\
   32 + concat_data_bound 0 (MAP expr_type args) <=
     concat_alloc_size (MAP expr_type args)` by
    (mp_tac (Q.SPEC `MAP expr_type args` concat_alloc_size_bounds) >> simp[]) >>
  `mload (w2n ow) t = n2w 0 /\ (0:num) <= 0 /\
   (!i. w2n a+32 <= i /\ i < w2n a+32+0 ==> i NOTIN tnf.t_mem)` by simp[] >>
  drule_all (concat_args_sim_ptr |> Q.SPEC `args` |> Q.SPEC `0` |> Q.SPEC `0`) >>
  disch_then (qspec_then `PG` assume_tac) >>
  irule gas_outcome_ptr_prefix >>
  first_assum (irule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  `builtin_args_length_ok (Concat n) (LENGTH args)` by simp[builtin_args_length_ok_def] >>
  qspecl_then [`cx`,`ann`,`n`,`args`] mp_tac eval_expr_concat_bind >>
  (impl_tac >- first_assum ACCEPT_TAC) >> disch_then SUBST1_TAC >>
  irule gas_outcome_ptr_values_bind >>
  first_assum (irule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)) >>
  reverse conj_tac >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> disch_then (qx_choose_then `vs` (map_every assume_tac o CONJUNCTS) o BETA_RULE) >>
  suspend "continuation"
QED

Resume concat_result_vv_sim_ptr[continuation]:
  qexists_tac `vs` >> conj_tac >- first_assum ACCEPT_TAC >>
  `lookup_var r t' = SOME a /\ lookup_var off t' = SOME ow` by metis_tac[] >>
  `lookup_var r t' = lookup_var r t` by simp[] >>
  `ptr_covers G tn r t' (concat_alloc_size (MAP expr_type args))` by
    (irule annassign_declared_pointer_after_rhs_ptr >>
     qexistsl_tac [`Gf`,`ce`,`es`,`t`,`s4`,`tnf`] >> simp[]) >>
  `not_fresh_at s5 r` by
    (irule not_fresh_at_mono >> qexists_tac `s4` >> fs[ci_mono_def]) >>
  drule_all concat_suffix_path_ptr >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`]
    (qx_choosel_then [`out`,`H`,`tm`,`u`,`tf`,`un`]
      (map_every assume_tac o CONJUNCTS))) >>
  `FLOOKUP t'.vs_allocas binst.inst_id =
     SOME (w2n a,concat_alloc_size (MAP expr_type args))` by metis_tac[] >>
  `!name b k. local_region ce ee.scopes t' name b k ==>
     w2n a + concat_alloc_size (MAP expr_type args) <= b \/ b+k <= w2n a` by
    (rpt strip_tac >>
     `local_region ce es.scopes t name b k` by
       (irule local_region_frame >> conj_tac >-
          (qexists_tac `fn` >>
           qpat_x_assum `stmt_state_rel ctx fn ce cx es t` mp_tac >>
           simp[stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`s4`,`ee.scopes`,`t'`] >> simp[]) >> metis_tac[]) >>
  `!x. not_fresh_at s4 x ==> lookup_var x tf = lookup_var x t' /\
     FLOOKUP H x = FLOOKUP G x /\ op_taint un (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at s5 x` by
       (irule not_fresh_at_mono >> qexists_tac `s4` >> fs[ci_mono_def]) >>
     first_assum (qspec_then `x` mp_tac) >> simp[]) >>
  `un.t_mem SUBSET tn.t_mem` by simp[] >>
  drule_all (concat_suffix_frame |> Q.INST [`sa` |-> `s4`]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "endpoint"
QED

Resume concat_result_vv_sim_ptr[endpoint]:
  qmatch_asmsub_abbrev_tac `mload (w2n ow) t' = n2w (0 + LENGTH bs)` >>
  `tf = (mstore (w2n a) (n2w (LENGTH bs)) u)
     with vs_inst_idx := SUC u.vs_inst_idx` by simp[] >>
  `!i. w2n a+32 <= i /\ i < w2n a+32+LENGTH bs ==> i NOTIN tn.t_mem` by
    (qpat_x_assum `!i. w2n a+32 <= i /\ i < w2n a+32+0+_ ==> _` mp_tac >> simp[]) >>
  drule_all concat_suffix_memory_post >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!b k. b+k <= w2n a \/ w2n a+32 <= b ==>
     mem_bytes_at b k tf.vs_memory = mem_bytes_at b k t'.vs_memory` by
    (rpt strip_tac >> simp[mstore_mem_bytes_at_disjoint]) >>
  `sa.cs_next_id <= s4.cs_next_id /\ sa.cs_next_var <= s4.cs_next_var` by
    fs[ci_mono_def] >>
  `!name b k. local_region ce es.scopes t name b k <=>
     local_region ce es.scopes s0 name b k` by metis_tac[] >>
  `!aid b k. FLOOKUP s0.vs_allocas aid = SOME (b,k) /\ aid < sa.cs_next_id /\
     (!name lo sz. local_region ce es.scopes s0 name lo sz ==> b+k <= lo \/ lo+sz <= b) ==>
     mem_bytes_at b k tf.vs_memory = mem_bytes_at b k s0.vs_memory` by
    (rpt gen_tac >> strip_tac >> drule_all concat_original_site_memory >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0` by metis_tac[] >>
  `!x. not_fresh_at s4 x ==> lookup_var x tf = lookup_var x t'` by metis_tac[] >>
  `!name b k. local_region ce es.scopes s0 name b k <=>
     local_region ce es.scopes t name b k` by metis_tac[] >>
  `wb_frame ce es sa s0 tf` by (drule_all concat_original_wb_frame >> simp[]) >>
  `ghost_kept ce es sa G0 tn0 s0 G tn` by
    (drule_all wordArgsPtrTheory.ghost_kept_trans >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s4 x` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `ghost_kept ce es sa G0 tn0 s0 H un` by
    (irule bodyPtrHashBuiltinsAllocFrameTheory.hash_ghost_kept_clean_tail >>
     qexistsl_tac [`G`,`tn`] >> simp[] >> metis_tac[]) >>
  suspend "package"
QED

Resume concat_result_vv_sim_ptr[package]:
  `lookup_var r tf = SOME a` by metis_tac[] >>
  `eval_operand (Var r) tf = SOME a` by simp[eval_operand_def] >>
  `mem_word_at (w2n a) tf.vs_memory = n2w (LENGTH bs)` by
    simp[mem_word_at_eq_mload] >>
  `mem_bytes_at (w2n a+32) (LENGTH bs) tf.vs_memory = bs` by
    (qpat_x_assum `mem_bytes_at (w2n a+32) _ t'.vs_memory = _` mp_tac >>
     qpat_x_assum `mem_bytes_at (w2n a+32) _ tf.vs_memory = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[valueEncodingTheory.mem_bytes_at_def]) >>
  `!name b k. local_region ce ee.scopes tf name b k ==>
     w2n a+concat_alloc_size (MAP expr_type args) <= b \/ b+k <= w2n a` by
    (rpt strip_tac >>
     `local_region ce ee.scopes t' name b k` by
       (drule_all exprSimCopyTheory.copy_buffer_local_region_frame >> metis_tac[]) >>
     metis_tac[]) >>
  `FLOOKUP tf.vs_allocas binst.inst_id = SOME
     (w2n a,concat_alloc_size (MAP expr_type args))` by metis_tac[] >>
  `sa.cs_next_id <= binst.inst_id /\ binst.inst_id < sb.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `LIST_REL (\t v. ?tv. evaluate_type (get_tenv cx) t = SOME tv /\ value_has_type tv v)
     (MAP expr_type args) vs` by
    (qpat_x_assum `LIST_REL _ args vs` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[LIST_REL_MAP1, combinTheory.o_DEF]) >>
  `bs = FLAT (MAP (\v. case v of BytesV bs => bs
     | StringV str => MAP ((n2w : num -> word8) o ORD) str | _ => []) vs)` by
    simp[Abbr `bs`] >>
  qpat_x_assum `?tv. evaluate_type (get_tenv cx) ann = SOME tv` strip_assume_tac >>
  `w2n a <= w2n a /\
   w2n a + concat_alloc_size (MAP expr_type args) <=
     w2n a + concat_alloc_size (MAP expr_type args)` by simp[] >>
  drule_all concat_result_endpoint_ptr >>
  strip_tac >> suspend "outcome"
QED

Resume concat_result_vv_sim_ptr[outcome]:
  simp[fragGasPathPtrTheory.gas_outcome_ptr_def,
    fragGasPathPtrTheory.gas_summary_ptr_at_def] >>
  qexists_tac `[]` >> disj1_tac >>
  qexistsl_tac [`INL (Value v)`,`ee`,`H`,`un`,`OK tf`] >>
  simp[NoAsms, gasSummaryTheory.gas_explicit_nil] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ tf` mp_tac >>
     qpat_x_assum `buf.buf_operand = Var r` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     simp[vv_post_def, vv_holds_def, vv_at_def, vv_own_def,
       contextTheory.base_ptr_def, read_result_def, vyperStateTheory.return_def] >>
     metis_tac[]) >>
  simp[NoAsms, stmtFragPtrTheory.ghost_inv_gas_obs] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >-
    (qpat_x_assum `buf.buf_operand = Var r` mp_tac >>
     qpat_x_assum `ptr_buf_ok _ _ _ H tf` mp_tac >>
     qpat_x_assum `ghost_kept _ _ _ G0 tn0 s0 H un` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[contextTheory.base_ptr_def]) >>
  (qpat_x_assum `ptr_vv_ok _ _ _ _ _ H un tf` mp_tac >>
     qpat_x_assum `buf.buf_operand = Var r` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     simp[ptr_vv_ok_def, post_value_type_not_int_call, contextTheory.base_ptr_def,
       read_result_def, vyperStateTheory.return_def])
QED

Finalise concat_result_vv_sim_ptr
