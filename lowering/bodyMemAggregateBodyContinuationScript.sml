(* Physical-post aggregate relayout with the child's rebased frame. *)
Theory bodyMemAggregateBodyContinuation
Ancestors
  bodyMemAggregatePhysicalRead bodyMemAggregateTypedStore
  exprSimAggregateChildren exprSimHyps exprSimHypsDefs typedMemoryCopy
  exprLoweringProps loweringPosts compileEnv context venomState externalNormalizePremises
  vyperInterpreter vyperState fragGasPathMem

Theorem aggregate_body_physical_store_path_mem:
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  post_value_type ce e <> expr_type e /\
  compile_store_memory ce op dst (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME dtv /\
  value_has_type dtv v /\ val_wf dtv v /\
  (!stv sw. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    eval_operand op s = SOME sw ==>
    w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  eval_operand dst s = SOME dw /\
  FLOOKUP s.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n dw /\ w2n dw + type_memory_size dtv <= b+k /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv < dimword(:256) /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts /\
  (!x. dst = Var x \/ op = Var x ==> not_fresh_at su x) /\
  sm.cs_next_var <= su.cs_next_var /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  (!name a n. local_region ce es'.scopes s name a n ==>
    a+n <= w2n dw \/ w2n dw + type_memory_size dtv <= a) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) (w2n dw) (type_memory_size dtv)) /\
  alloca_history func s ==>
  ?q. gas_path_mem ctx func s 0 (OK q) /\
    val_in_memory dtv v (w2n dw) q.vs_memory /\
    stmt_state_rel ctx func ce cx es' q /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
    (!aid a. FLOOKUP r.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
    (!aid off sz a len.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!name b k. local_region ce es'.scopes r name b k ==>
        off+sz <= b \/ b+k <= off) /\
      off <= a /\ a+len <= off+sz /\
      (a+len <= w2n dw \/ w2n dw+type_memory_size dtv <= a) ==>
      mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
    locals_kept ce es' r q /\ alloca_history func q /\
    q.vs_alloca_next = s.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    metis_tac[post_value_type_word, post_value_type_bytestring] >>
  `~is_word_type (post_value_type ce e)` by
    (fs[expr_body_pre_def] >>
     metis_tac[post_value_type_widens, return_source_word_widens_eq]) >>
  drule_all aggregate_child_physical_encoding >> strip_tac >>
  `~is_bytestring_type (post_value_type ce e)` by
    metis_tac[externalNormalizePremisesTheory.normalize_return_source_kinds] >>
  `post_value_type ce e = lowered_value_type ce e` by
    (Cases_on `e` >> gvs[post_value_type_def, vyperASTTheory.expr_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >> gvs[post_value_type_def, vyperASTTheory.expr_type_def]) >>
  `expr_val_at ce cx (post_value_type ce e)
     (sa with cs_next_var := sm.cs_next_var) su es' v op s /\
   stmt_state_rel ctx func ce cx es' s` by fs[expr_post_def] >>
  `did < (sa with cs_next_var := sm.cs_next_var).cs_next_id` by simp[] >>
  drule_all aggregate_physical_source_slot_bounds >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_store_memory_typed ce dst (expr_type e) op
     (post_value_type ce e) su = ((),sb)` by
    gvs[compile_store_memory_def] >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next` by metis_tac[] >>
  drule_all aggregate_typed_store_path_mem >> simp[]
QED
