Theory aggregateCountedTypedStore
Ancestors
  aggregateTypedCopyRawShape aggregateCodeTrace aggregateCountedRenamedStore
  aggregateCountedRawRelabel aggregateCountedCutBridge exprSimAggregateChildren
  exprSimAbiGasBridge context compileEnv vyperAST venomExecSemantics
  emitHelper emitHelperProps list rich_list fragExec exprLoweringProps
  loweringPosts venomState venomInst venomMemDefs exprSimHash
  aggregateCountedStraightExec aggregateCountedStraightStore

Theorem aggregate_typed_store_renamed_body_run:
  compile_store_memory_typed ce (Var x) (expr_type e) op
    (post_value_type ce e) su = ((),sb) /\
  su.cs_blocks <> sb.cs_blocks /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  ~is_word_type (post_value_type ce e) /\
  ~is_bytestring_type (post_value_type ce e) /\
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  stmt_state_rel ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (!name a len. local_region ce es'.scopes r name a len ==>
    a+len <= w2n w \/ w2n w + type_memory_size tv <= a) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  ~s.vs_halted /\ s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  !L ids fn'. LENGTH ids = LENGTH su.cs_current_insts /\
    fn_has_code (start_relabel L ids su) (start_swap su L ids sb) fn' ==>
  ?q. val_in_memory tv v (w2n w) q.vs_memory /\
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
      (a+len <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
      mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
    locals_kept ce es' r q /\
    (!fuel rr. run_from fuel ctx fn' q = rr /\ (!err. rr <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn' (s with vs_current_bb := L) = rr)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `cs_extends su sb` by metis_tac[aggregate_typed_store_extends] >>
  `compile_store_memory_typed ce (Var x) (expr_type e) op (post_value_type ce e)
     (start_relabel L ids su) = ((),start_swap su L ids sb)` by
    (mp_tac (cj 1 compile_typed_copy_start_oblivious_family) >>
     simp[frag_start_oblivious_def] >> metis_tac[]) >>
  drule_all start_swap_fields >>
  disch_then (qspecl_then [`ids`, `L`] strip_assume_tac) >>
  drule aggregate_store_body_typed_run >>
  simp[aggregate_expr_post_start_relabel] >>
  disch_then irule >>
  simp[aggregate_expr_post_start_relabel, start_relabel_def,
       local_ptrs_reserved_def, not_fresh_at_def] >>
  fs[local_ptrs_reserved_def, not_fresh_at_def] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem typed_store_relabel_counted_normal:
  (!L ids fn'.
     LENGTH ids = LENGTH su.cs_current_insts /\
     fn_has_code (start_relabel L ids su) (start_swap su L ids sb) fn' /\
     fn_inst_ids_distinct fn' /\ fn'.fn_name = fn.fn_name /\
     (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\
          i.inst_opcode <> NOP ==> MEM i (fn_insts fn)) /\
     (!i. MEM i (fn_insts fn') ==> i.inst_opcode <> INVOKE) /\
     (sb.cs_current_insts <> [] \/
      !bb. lookup_block sb.cs_current_bb fn'.fn_blocks = SOME bb ==>
           phi_prefix_length bb.bb_instructions = 0) ==>
     ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts /\
         !fuel rr. run_from fuel ctx fn' t = rr /\ (!err. rr <> Error err) ==>
           ?fuel'. run_from fuel' ctx fn' (s with vs_current_bb := L) = rr) /\
  cs_extends su sb /\ frag_ops_free su sb /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code su sb)) /\
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks su sb))) /\
  su.cs_blocks <> sb.cs_blocks /\
  (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
  (!t p. Q t ==> Q (t with vs_prev_bb := p)) /\
  fn_has_code su sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  irule (SRULE [] (Q.INST [`R` |-> `\r. F`]
    (SPEC_ALL frag_exec_gas_path_relabel_raw))) >>
  simp[] >> qexists_tac `su` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!L ids fn'. _` drule >> simp[]
QED

Theorem aggregate_stmt_state_rel_prev_bb:
  stmt_state_rel ctx func ce cx es (s with vs_prev_bb := p) <=>
  stmt_state_rel ctx func ce cx es s
Proof
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
       local_region_def, local_backed_def, lookup_var_def, storage_rel_def,
       transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       contract_storage_def, contract_transient_def, alloca_inv_def,
       allocas_non_overlapping_def, alloca_next_valid_def, alloca_room_def,
       pending_alloca_size_def, fmp_room_def, immutable_alloca_sep_def,
       immutable_base_zero_alt, accounts_rel_def]
QED

Theorem aggregate_store_body_typed_counted:
  compile_store_memory_typed ce (Var x) (expr_type e) op
    (post_value_type ce e) su = ((),sb) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  ~is_word_type (post_value_type ce e) /\
  ~is_bytestring_type (post_value_type ce e) /\
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  stmt_state_rel ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (!name a len. local_region ce es'.scopes r name a len ==>
    a+len <= w2n w \/ w2n w + type_memory_size tv <= a) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  fn_has_code su sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = su.cs_current_bb /\ s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?q. gas_marked_path F ctx fn s 0 (OK q) /\
    (val_in_memory tv v (w2n w) q.vs_memory /\
     stmt_state_rel ctx func ce cx es' q /\
     (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
     (!aid a. FLOOKUP r.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
     (!aid off sz a len.
       FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
       (!name b k. local_region ce es'.scopes r name b k ==>
         off+sz <= b \/ b+k <= off) /\
       off <= a /\ a+len <= off+sz /\
       (a+len <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
       mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
     locals_kept ce es' r q) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `su.cs_blocks = sb.cs_blocks`
  >- suspend "straight" >>
  drule aggregate_typed_store_extends >> strip_tac >>
  drule aggregate_typed_store_raw_shape >> strip_tac >>
  ho_match_mp_tac typed_store_relabel_counted_normal >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all aggregate_typed_store_renamed_body_run >>
      strip_tac >> qexists_tac `q` >>
      gvs[arithmeticTheory.ADD_COMM] >> first_assum MATCH_ACCEPT_TAC) >>
  simp[hash_returndata_state_rel, aggregate_stmt_state_rel_prev_bb,
       lookup_var_def, locals_kept_def] >>
  rpt gen_tac >> strip_tac >> conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Resume aggregate_store_body_typed_counted[straight]:
  drule aggregate_typed_store_extends >> strip_tac >>
  drule aggregate_typed_store_raw_shape >> strip_tac >>
  drule_all compile_store_memory_typed_same_block_nonterminators >> strip_tac >>
  drule_all aggregate_store_body_typed_sim >>
  disch_then (qspec_then `\r. F` assume_tac) >>
  ho_match_mp_tac frag_exec_same_block_gas_path >>
  qexists_tac `su` >>
  goal_assum (drule_at Any) >>
  simp[arithmeticTheory.ADD_COMM] >>
  simp[hash_returndata_state_rel, lookup_var_def, locals_kept_def] >>
  rpt gen_tac >> strip_tac >> conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Finalise aggregate_store_body_typed_counted
