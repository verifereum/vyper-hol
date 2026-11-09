(* Typed result packaging for Concat. *)
Theory bodyPtrBytestringBuiltinsConcatResult
Ancestors
  bodyPtrBytestringBuiltinsConcatSuffix bodyPtrEnvBuiltinsBoundary
  exprSimConcatResult exprSimHyps exprSimProps exprLowering
  compileEnv loweringPosts bodyPtrDefs words list arithmetic vfmConstants
  vyperTypeConversions valueEncoding bodyPtrBytestringBuiltinsCalldataOutcome
  exprSimHash exprSimSource exprSimHypsDefs exprSimDefs vyperTyping
  vyperTypeSystem allocLimits vyperTypeInvariants gasSummaryComposePtr gasExemptCert
  vyperState

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
