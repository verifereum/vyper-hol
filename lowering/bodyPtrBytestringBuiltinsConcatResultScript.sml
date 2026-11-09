(* Typed result packaging for Concat. *)
Theory bodyPtrBytestringBuiltinsConcatResult
Ancestors
  bodyPtrBytestringBuiltinsConcatSuffix bodyPtrEnvBuiltinsBoundary
  exprSimConcatResult exprSimHyps exprSimProps exprLowering
  compileEnv loweringPosts bodyPtrDefs words list arithmetic vfmConstants
  vyperTypeConversions valueEncoding bodyPtrBytestringBuiltinsCalldataOutcome
  exprSimHash

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
