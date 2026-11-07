(* Counted source boundary for body-aware aggregate child stores. *)
Theory exprSimAggregateBodyCountedChildren
Ancestors
  exprSimAggregateChildren exprSimSource exprSimMemorySource gasSummary vyperState exprSimHypsDefs
  exprSimUnwrap exprSimHyps exprSimProps aggregateCountedStraightExec exprSimAbiGasBridge
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  loweringPosts venomInst list rich_list exprSimHash exprLowering fragExec venomState fragGasPath fragGasMode
  aggregateCountedTypedStore typedMemoryCopy vyperAST vyperTypeCallGraph
Libs
  monadsyntax

(* A marked execution replays at the explicit observations selected by its
   target path.  It need not replay at the original state's observations. *)
Theorem aggregate_body_marked_read_source:
  gas_marked_exec memory (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tv) mid r /\
  read_result cx tv (mid with gas_obs := []) =
    (INL v,mid with gas_obs := []) ==>
  (do res <- eval_expr cx e; read_result cx res od)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL v,mid with gas_obs := [])
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  gvs[] >> simp[bind_def]
QED

Theorem aggregate_body_pre_gas_obs:
  expr_body_pre ce cx env e (es with gas_obs := gs) <=>
  expr_body_pre ce cx env e es
Proof
  simp[expr_body_pre_def, expr_sim_inv_gas_obs]
QED

Theorem aggregate_unwrap_memory_straight[local]:
  (!t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory) /\
  unwrap_value ce vv sm = (op,su) ==>
  cs_extends sm su /\ sm.cs_blocks = su.cs_blocks /\
  frag_ops_free sm su /\
  EVERY (\i. ~is_terminator i.inst_opcode) (frag_code sm su)
Proof
  Cases_on `vv` >> simp[unwrap_value_def] >> strip_tac
  >- (gvs[comp_return_def] >>
      simp[cs_extends_refl, frag_ops_free_def, frag_code_def,
           emitted_blocks_def, emitted_insts_def]) >>
  gvs[compile_ptr_load_def] >>
  Cases_on `is_word_type t` >> gvs[comp_return_def] >>
  simp[cs_extends_refl, frag_ops_free_def, frag_code_def,
       emitted_blocks_def, emitted_insts_def] >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def,
      emit_def, mk_inst_def, cs_extends_def, frag_ops_free_def,
      frag_code_def, emitted_blocks_def, emitted_insts_def, is_terminator_def,
      DROP_LENGTH_APPEND]
QED

Theorem aggregate_expr_post_returndata[local]:
  expr_post ctx func ce cx e es sa sb s0 es' v op
    (s with vs_returndata := rd) <=>
  expr_post ctx func ce cx e es sa sb s0 es' v op s
Proof
  Cases_on `op` >>
  simp[expr_post_def, hash_returndata_state_rel, expr_val_rel_def,
       expr_val_at_def, expr_val_own_def, eval_operand_def, lookup_var_def,
       local_region_def, local_backed_def, locals_kept_def, popped_kept_def]
QED

Theorem aggregate_body_unwrap_marked:
  compile_expr ce ty e si = (vv,sj) /\
  expr_body_pre ce cx env e es /\
  unwrap_value ce vv sm = (op,su) /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= sm.cs_next_id /\
  read_result cx tv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
         ~is_word_type (post_value_type ce e) ==>
         type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
         type_memory_size tvt < 2 ** 64) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func r 0 (OK u) /\
    expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
      su r es' v op u /\
    ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
    u.vs_inst_idx = LENGTH su.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `post_value_type ce e = expr_type e`
  >- suspend "equal" >>
  `!t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory` by
    metis_tac[aggregate_unequal_post_result_location] >>
  drule_all aggregate_unwrap_memory_straight >> strip_tac >>
  drule_all unwrap_value_body_rebased_sim >>
  disch_then (qspec_then `\r. F` assume_tac) >>
  ho_match_mp_tac frag_exec_same_block_gas_path >>
  qexists_tac `sm` >> goal_assum (drule_at Any) >>
  simp[aggregate_expr_post_returndata]
QED

Resume aggregate_body_unwrap_marked[equal]:
  drule vv_post_rebase >> strip_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_marked_read >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> (impl_tac
  >- (fs[local_ptrs_reserved_def, not_fresh_at_def] >> metis_tac[])) >>
  strip_tac >> gvs[gas_marked_exec_def] >>
  qpat_x_assum `!tail. read_result _ _ _ = _`
    (qspec_then `es'.gas_obs` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  drule gas_marked_path_exec >> strip_tac >>
  drule gas_path_normal >> strip_tac >>
  qexists_tac `u` >> simp[]
QED

Finalise aggregate_body_unwrap_marked

Theorem aggregate_store_ordinary_certificate[local]:
  compile_store_memory ce src dst ty sty sa = ((),sb) /\
  (is_word_type ty \/ is_bytestring_type ty \/ ty = sty) ==>
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks /\
  frag_ops_free sa sb /\
  EVERY (\i. ~is_terminator i.inst_opcode) (frag_code sa sb)
Proof
  simp[compile_store_memory_def] >>
  Cases_on `is_word_type ty` >> simp[]
  >- (simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def,
           comp_ignore_bind_def, comp_return_def, mk_inst_def] >> strip_tac >>
      gvs[cs_extends_def, frag_ops_free_def, frag_code_def, emitted_blocks_def,
          emitted_insts_def, DROP_LENGTH_APPEND, is_terminator_def]) >>
  Cases_on `is_bytestring_type ty` >> simp[]
  >- (simp[compile_store_bytestring_def, compile_bytestring_copy_len_def,
           emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def, fresh_var_def, fresh_id_def, emit_def, mk_inst_def] >>
      strip_tac >>
      gvs[cs_extends_def, frag_ops_free_def, frag_code_def, emitted_blocks_def,
          emitted_insts_def, DROP_LENGTH_APPEND, is_terminator_def] >>
      pure_rewrite_tac [GSYM APPEND_ASSOC] >>
      simp[DROP_LENGTH_APPEND, is_terminator_def]) >>
  strip_tac >> gvs[] >> Cases_on `type_memory_bytes ce sty` >>
  gvs[compile_copy_memory_def, emit_void_def, comp_bind_def, fresh_id_def,
       emit_def, comp_ignore_bind_def, comp_return_def, mk_inst_def] >>
  gvs[cs_extends_def, frag_ops_free_def, frag_code_def, emitted_blocks_def,
      emitted_insts_def, DROP_LENGTH_APPEND, is_terminator_def]
QED

Theorem aggregate_unequal_post_calls[local]:
  post_value_type ce e <> expr_type e ==>
  int_calls_expr e <> [] /\ lowered_value_type ce e <> expr_type e
Proof
  strip_tac >> conj_tac
  >- (Cases_on `e` >> gvs[post_value_type_def] >>
      rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
      gvs[post_value_type_def, int_calls_expr_def]) >>
  metis_tac[post_value_type_lowered]
QED

Theorem aggregate_store_body_rebased_slice_marked:
  compile_store_memory ce op (Var x) (expr_type e) (lowered_value_type ce e)
    su = ((),sb) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  (int_calls_expr e <> [] /\ lowered_value_type ce e <> expr_type e ==>
    acyclic_struct_metadata ce.ce_struct_fields) /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  stmt_state_rel ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (!name a len. local_region ce es'.scopes r name a len ==>
    a+len <= w2n w \/ w2n w+type_memory_size tv <= a) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  fn_has_code su sb func /\ ~s.vs_halted /\
  s.vs_current_bb = su.cs_current_bb /\ s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
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
     locals_kept ce es' es' r q) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  drule compile_store_memory_post_type >>
  disch_then (qspecl_then [`ce`, `op`, `Var x`] assume_tac) >>
  `compile_store_memory ce op (Var x) (expr_type e) (post_value_type ce e)
      su = ((),sb)` by metis_tac[] >>
  Cases_on `is_word_type (expr_type e) \/ is_bytestring_type (expr_type e) \/
             expr_type e = post_value_type ce e`
  >- suspend "ordinary" >>
  `compile_store_memory_typed ce (Var x) (expr_type e) op (post_value_type ce e)
      su = ((),sb)` by fs[compile_store_memory_def] >>
  `acyclic_struct_metadata ce.ce_struct_fields` by
    metis_tac[aggregate_unequal_post_calls] >>
  Cases_on `is_word_type (post_value_type ce e)`
  >- (`expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
      drule_all post_value_type_widens >>
      metis_tac[return_source_word_widens_eq]) >>
  drule_all aggregate_child_physical_encoding >> strip_tac >>
  `~is_bytestring_type (post_value_type ce e)` by
    metis_tac[type_widens_from_bytestring] >>
  drule aggregate_store_body_typed_counted >>
  disch_then irule >> simp[] >>
  fs[arithmeticTheory.ADD_COMM] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (qexistsl_tac [`b`, `did`, `k`] >> simp[]) >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`env`, `es`] >> simp[]
QED

Resume aggregate_store_body_rebased_slice_marked[ordinary]:
  drule_all aggregate_store_ordinary_certificate >> strip_tac >>
  drule_all aggregate_store_body_rebased_slice_sim >>
  disch_then (qspec_then `\rr. F` assume_tac) >>
  drule frag_exec_same_block_gas_path >>
  disch_then (qspecl_then [`func`, `s`] mp_tac) >>
  simp[] >> impl_tac
  >- (POP_ASSUM_LIST (K all_tac) >>
      simp[hash_returndata_state_rel, lookup_var_def, locals_kept_def, popped_kept_def] >>
      rpt gen_tac >> strip_tac >> fs[arithmeticTheory.ADD_COMM] >>
      rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  simp[]
QED

Finalise aggregate_store_body_rebased_slice_marked

Theorem aggregate_body_child_store_slice_marked:
  compile_expr ce ty e si = (vv,sj) /\
  unwrap_value ce vv sm = (op,su) /\
  compile_store_memory ce op (Var x) (expr_type e) (lowered_value_type ce e)
    su = ((),sb) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  (int_calls_expr e <> [] /\ lowered_value_type ce e <> expr_type e ==>
    acyclic_struct_metadata ce.ce_struct_fields) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  read_result cx tvv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  fn_has_code sm su func /\ fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
    ~is_word_type (post_value_type ce e) ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
    type_memory_size tvt < 2 ** 64) /\
  stmt_state_rel ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (!name a len. local_region ce es'.scopes r name a len ==>
    a+len <= w2n w \/ w2n w+type_memory_size tv <= a) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?q. gas_marked_path F ctx func r 0 (OK q) /\
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
     locals_kept ce es' es' r q) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  drule_all aggregate_body_unwrap_marked >> strip_tac >>
  drule_all aggregate_store_body_rebased_slice_marked >> strip_tac >>
  qexists_tac `q` >> simp[] >>
  conj_tac
  >- (drule_all gas_marked_path_then >> simp[]) >>
  fs[arithmeticTheory.ADD_COMM] >> first_assum MATCH_ACCEPT_TAC
QED

(* Replay supplies the semantic premise of the slice continuation without
   identifying the original observation stream with the marked one. *)
Theorem aggregate_body_child_replay:
  expr_body_pre ce cx env e es /\
  gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tv) mid (OK r) /\
  read_result cx tv (mid with gas_obs := []) =
    (INL v,mid with gas_obs := []) /\
  vv_post ctx func ce cx e es sa sm s0 (mid with gas_obs := []) tv vv r ==>
  ?replay.
    expr_body_pre ce cx env e replay /\
    (do res <- eval_expr cx e; read_result cx res od) replay =
      (INL v,mid with gas_obs := []) /\
    vv_post ctx func ce cx e replay sa sm s0
      (mid with gas_obs := []) tv vv r
Proof
  rpt strip_tac >>
  drule_all aggregate_body_marked_read_source >> strip_tac >>
  qexists_tac `es with gas_obs := gas_explicit marks s0.vs_gas_readings` >>
  simp[aggregate_body_pre_gas_obs, vv_post_initial_gas]
QED

Theorem aggregate_body_marked_read_suffix:
  gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tv) mid (OK r) /\
  read_result cx tv (mid with gas_obs := []) =
    (INL v,mid with gas_obs := []) /\
  gas_marked_path F ctx func r 0 (OK q) ==>
  gas_marked_exec F (ctx,func)
    (do res <- eval_expr cx e; read_result cx res od) (es,s0)
    marks (INL v) mid (OK q)
Proof
  rpt strip_tac >>
  drule read_result_gas_obs >> simp[] >> strip_tac >>
  fs[gas_marked_exec_def] >> conj_tac
  >- (gen_tac >> simp[bind_def]) >>
  drule_all gas_marked_path_then >> simp[]
QED
