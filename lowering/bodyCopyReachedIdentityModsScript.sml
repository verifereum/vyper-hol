(* A stack or nonword memory unwrap leaves the reached raw state intact. *)
Theory bodyCopyReachedIdentityMods
Ancestors
  bodyLocalCopyPhysicalRhsMods bodyCopyReadPhysicalTypeMods
  bodyFullPostsMods loweringPosts exprSimMemorySource
  gasContext vyperInterpreter vyperState vyperStorageFootprint context
  fragGasOriginPtr exprLowering ptrDiscipline stateRelProj exprLoweringProps words

Theorem copy_identity_vv_at[local]:
  ((?ty. vv = StackValue ty op) \/
   (?ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory /\
           ~is_word_type ty /\ p.ptr_operand = op)) /\
  ~is_word_type tag /\ vv_at ce cx tag a b ee tv vv s ==>
  vv_at ce cx tag a b ee tv (LocatedValue tag (mk_ptr op LocMemory)) s
Proof
  strip_tac >> gvs[vv_at_def,mk_ptr_def,expr_val_at_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[local_place_at_def] >> metis_tac[]
QED

Theorem local_copy_reached_identity_mods:
  compile_expr ce (expr_type e) e a = (vv,sm) /\
  unwrap_value ce vv sm = (op,b) /\
  ((?ty. vv = StackValue ty op) \/
   (?ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory /\
           ~is_word_type ty /\ p.ptr_operand = op)) /\
  expr_body_pre_mods mods ce cx env e es /\ ~is_word_type (expr_type e) /\
  local_ptrs_reserved ce a /\
  (!tail. eval_expr cx e
     (es with gas_obs := gas_explicit marks entry.vs_gas_readings ++ tail) =
     (INL tv,ee with gas_obs := tail)) /\
  read_result cx tv ee = (INL v,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (entry,Gi,ti) marks (OK s,G,tn) /\
     vv_post_mods H ctx func ce cx e es a sm entry ee tv vv s /\
     ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  (!tag x. vv = StackValue tag x /\ ~is_word_type (post_value_type ce e) ==>
           ptr_buf_ok ce e x G s) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
           ptr_buf_ok ce e p.ptr_operand G s) /\
  ghost_kept_at lo ce es a Gi ti entry G tn /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ entry.vs_alloca_next <= s.vs_alloca_next ==>
  b = sm /\ lower_value compile_expr ce (expr_type e) e a = (op,b) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks entry.vs_gas_readings ++ tail) =
     (INL v,ee with gas_obs := tail)) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK s,G,tn)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (entry,Gi,ti) marks (OK s,G,tn) /\
     expr_post_mods H ctx func ce cx e es a b entry ee v op s /\
     ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = b.cs_current_bb /\
  s.vs_inst_idx = LENGTH b.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ entry.vs_alloca_next <= s.vs_alloca_next /\
  ghost_kept_at lo ce es a Gi ti entry G tn /\
  ~is_word_type (post_value_type ce e) /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\
  ptr_buf_ok ce e op G s /\ expr_store_bound cx (post_value_type ce e) v op s /\
  vv_at ce cx (post_value_type ce e) a b ee tv
    (LocatedValue (post_value_type ce e) (mk_ptr op LocMemory)) s /\
  (post_value_type ce e <> expr_type e ==>
    vv_own ce cx (post_value_type ce e) a b ee tv vv s) /\
  (!dst cap dw aid chunk. not_fresh_at a dst /\ lookup_var dst entry = SOME dw /\
     ptr_covers Gi ti dst entry cap /\ FLOOKUP entry.vs_allocas aid = SOME chunk ==>
     lookup_var dst s = SOME dw /\ ptr_covers G tn dst s cap /\
     FLOOKUP s.vs_allocas aid = SOME chunk) /\
  ?pt rt w.
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
    value_has_type pt v /\ value_has_type rt v /\ val_wf rt v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
    eval_operand op s = SOME w /\ op_taint tn op = {} /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory rt v (w2n w) mem) /\
    (val_store_size rt v = 0 \/ w2n w + val_store_size rt v <= s.vs_alloca_next) /\
    (type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= s.vs_alloca_next) /\
    w2n w + type_memory_size rt < dimword (:256) /\
    (~is_bytestring_type (lowered_value_type ce e) ==>
      expr_val_at ce cx (lowered_value_type ce e) a b ee v op s) /\
    (0 < type_memory_size rt ==>
       ?src. op = Var src /\ not_fresh_at b src /\ ptr_covers G tn src s (type_memory_size rt))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks entry.vs_gas_readings ++ tail) =
     (INL v,ee with gas_obs := tail)` by
    (drule read_result_gas_obs >> simp[bind_def]) >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks entry.vs_gas_readings) =
     (INL v,ee with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [listTheory.APPEND_NIL]))) >>
  drule_all copy_read_physical_type_gas_obs_mods >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (qx_choosel_then [`pt`,`rt`] strip_assume_tac))) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  `b = sm /\ ptr_val_ok cx (post_value_type ce e) v op G tn s /\
   expr_store_bound cx (post_value_type ce e) v op s /\
   (!rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
           eval_operand op s = SOME w ==>
           type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= s.vs_alloca_next)` by
    (drule_all local_copy_rhs_identity_unwrap_mods >>
     disch_then (qspecl_then [`lo`,`explicit`,`PG`,`DF (storage_trace_horizon ee.storage_trace)`]
       strip_assume_tac) >> asm_rewrite_tac[]) >>
  `ptr_buf_ok ce e op G s` by metis_tac[] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK s,G,tn)` by
    simp[cj 1 gas_origin_ptr_path_rules] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (entry,Gi,ti) marks (OK s,G,tn) /\
     expr_post_mods H ctx func ce cx e es a b entry ee v op s /\
     ghost_inv_at_mods (DF H) lo d ce cx ee G tn s` by
    (qx_gen_tac `h` >> disch_tac >>
     qpat_x_assum `vv_post_mods (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
     qpat_assum `!H. valid_horizon _ _ _ _ ==> _`
       (qspec_then `h` (drule_then strip_assume_tac)) >>
     drule_all local_copy_rhs_identity_unwrap_mods >>
     disch_then (strip_assume_tac o SPEC_ALL) >> asm_rewrite_tac[]) >>
  `s.vs_current_bb = b.cs_current_bb /\ s.vs_inst_idx = LENGTH b.cs_current_insts` by simp[] >>
  drule_all_then strip_assume_tac local_copy_physical_rhs_mods >>
  `vv_at ce cx (post_value_type ce e) a sm ee tv vv s /\
   (post_value_type ce e <> expr_type e ==>
    vv_own ce cx (post_value_type ce e) a sm ee tv vv s)` by
    fs[vv_post_mods_def] >>
  drule_all_then assume_tac copy_identity_vv_at >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee s` by
    fs[vv_post_mods_def] >>
  `s.vs_alloca_next < dimword (:256)` by
    (drule stmt_state_rel_alloca_room >>
     disch_then (ACCEPT_TAC o MATCH_MP alloca_room_next_lt)) >>
  `~is_bytestring_type (lowered_value_type ce e) ==>
   expr_val_at ce cx (lowered_value_type ce e) a b ee v op s` by
    (strip_tac >> `post_value_type ce e = lowered_value_type ce e` by metis_tac[] >>
     qpat_assum `!H. valid_horizon _ _ _ _ ==> _ /\ expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_x_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
     qpat_assum `post_value_type ce e = lowered_value_type ce e` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= s.vs_alloca_next` by
    (qpat_assum `!r x. evaluate_type _ (lowered_value_type ce e) = SOME r /\ _ ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  `w2n w + type_memory_size rt < dimword (:256)` by
    (Cases_on `type_memory_size rt = 0` >- simp[wordsTheory.w2n_lt] >> decide_tac) >>
  qpat_x_assum `b = sm` SUBST_ALL_TAC >>
  asm_rewrite_tac[] >> qexistsl [`pt`,`rt`,`w`] >> simp[] >> metis_tac[]
QED
