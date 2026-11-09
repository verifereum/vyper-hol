(* Counted typed stores preserve the rebased aggregate child frame. *)
Theory bodyMemAggregateTypedStore
Ancestors
  typedCopyRankPathMem fragGasPathFrameMem exprSimAggregateChildren
  bodyMemAggregatePath loweringPosts exprLoweringProps compileEnv venomState

Theorem aggregate_typed_store_path_mem:
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  compile_store_memory_typed ce dst dty src sty su = ((),sb) /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n sw + type_memory_size stv < dimword(:256) /\
  w2n dw + type_memory_size dtv < dimword(:256) /\
  (w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n sw) /\
  fn_has_code su sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = su.cs_current_bb /\ s.vs_inst_idx = LENGTH su.cs_current_insts /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at su x) /\
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  sm.cs_next_var <= su.cs_next_var /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  (!name b k. local_region ce es'.scopes s name b k ==>
    b+k <= w2n dw \/ w2n dw + type_memory_size dtv <= b) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) (w2n dw) (type_memory_size dtv)) /\
  fn_inst_ids_distinct fn /\ alloca_history fn s ==>
  ?q. gas_path_mem ctx fn s 0 (OK q) /\
    val_in_memory dtv v (w2n dw) q.vs_memory /\
    stmt_state_rel ctx func ce cx es' q /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
    (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==> FLOOKUP q.vs_allocas aid = SOME b) /\
    (!aid off sz a len.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!name b k. local_region ce es'.scopes r name b k ==>
        off+sz <= b \/ b+k <= off) /\
      off <= a /\ a+len <= off+sz /\
      (a+len <= w2n dw \/ w2n dw+type_memory_size dtv <= a) ==>
      mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
    locals_kept ce es' r q /\ alloca_history fn q /\
    q.vs_alloca_next = s.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_store_memory_typed_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    metis_tac[gas_path_mem_memory_length] >>
  `(t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
    vs_inst_idx := s.vs_inst_idx|>) = s` by fs[] >>
  drule_all aggregate_store_rebased_control_frame >> strip_tac >>
  `alloca_inv s` by gvs[expr_post_def, stmt_state_rel_def, state_rel_def] >>
  `alloca_history fn t` by
    (irule gas_path_mem_zero_history >> simp[] >>
     metis_tac[aggregate_mem_path_alloca_inv]) >>
  qexists `t` >> simp[] >>
  gvs[venom_state_component_equality, arithmeticTheory.ADD_COMM] >>
  first_assum ACCEPT_TAC
QED
