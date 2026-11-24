(* Attach the materializing unwrap to the very raw execution that produced
   the source read. The allocation and copy witnesses do not depend on H. *)
Theory bodyCopyReachedMaterializedMods
Ancestors
  bodyLocalCopyPhysicalRhsMods bodyCopyMaterializedRhsPostMods
  vyperEvalExprPreservesScopesDom assignTuplePtrCopyLen bodyFullHashKeccakFixed
  valueTypingMemoryProps exprLoweringProps vyperStorageFootprint fragGasOriginPtr
  bodyPtrDefs loweringPosts loweringStateRelDefs bodyFullPostsMods
  arithmetic finite_map words

Theorem local_copy_reached_materialized_mods:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  unwrap_value ce vv sm = (Var root,sb) /\
  (!tail. eval_expr cx e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (INL tv,ee with gas_obs := tail)) /\
  read_result cx tv ee = (INL v,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,Gi,ti) marks (OK s,G,tn) /\
     vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
     ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~is_word_type (post_value_type ce e) /\
  post_value_type ce e = lowered_value_type ce e /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
  value_has_type rt v /\ nb = type_memory_size rt /\
  type_memory_bytes ce (lowered_value_type ce e) = nb /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
  ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
  z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func z /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ s.vs_alloca_next <= z.vs_alloca_next /\
  sm.cs_next_id < sb.cs_next_id /\ sm.cs_next_var < sb.cs_next_var /\
  fn_inst_ids_distinct func /\ w2n w + nb < dimword (:256) /\
  root = STRING #"%" (toString sm.cs_next_var) /\
  MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts func) /\
  exec_alloca (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s (n2w nb : bytes32) = OK u /\
  FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,nb) /\
  copy_static z = copy_static u /\ LENGTH s.vs_memory <= LENGTH z.vs_memory /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint (w2n w) nb b len) /\
  (!off len. off+len <= w2n w \/ w2n w+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!j. j < w2n w \/ w2n w+nb <= j ==> j IN tf.t_mem ==> j IN tn.t_mem) /\
  z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
  z.vs_call_ctx = s.vs_call_ctx /\ z.vs_immutables = s.vs_immutables /\
  z.vs_data_section = s.vs_data_section /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  eval_operand (Var root) z = SOME w /\ ptr_covers Gf tf root z nb /\
  (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==>
    val_in_memory rt v (w2n w) mem) ==>
  lower_value compile_expr ce (expr_type e) e sa = (Var root,sb) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (INL v,ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,Gi,ti) marks (OK z,Gf,tf) /\
     expr_post_mods H ctx func ce cx e es sa sb s0 ee v (Var root) z /\
     ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z) /\
  ghost_kept_at lo ce es sa Gi ti s0 Gf tf /\
  ptr_val_ok cx (post_value_type ce e) v (Var root) Gf tf z /\
  ptr_buf_ok ce e (Var root) Gf z /\ expr_store_bound cx (post_value_type ce e) v (Var root) z /\
  ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
  z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func z /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ s0.vs_alloca_next <= z.vs_alloca_next /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
  value_has_type rt v /\ val_wf rt v /\ allocas_from lo z /\
  expr_val_at ce cx (lowered_value_type ce e) sa sb ee v (Var root) z /\
  lookup_var root z = SOME w /\ not_fresh_at sb root /\
  op_taint tf (Var root) = {} /\ ptr_covers Gf tf root z nb /\
  (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==>
    val_in_memory rt v (w2n w) mem) /\
  FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n w,nb) /\
  lo <= w2n w /\ w2n w + nb <= z.vs_alloca_next /\ w2n w + nb < dimword (:256) /\
  (!dst cap dw aid chunk. not_fresh_at sa dst /\ lookup_var dst s0 = SOME dw /\
    ptr_covers Gi ti dst s0 cap /\ FLOOKUP s0.vs_allocas aid = SOME chunk ==>
    lookup_var dst z = SOME dw /\ ptr_covers Gf tf dst z cap /\
    FLOOKUP z.vs_allocas aid = SOME chunk) /\
  (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint (w2n w) nb b len) /\
  wb_frame ce ee ee sm s z /\ ghost_kept_at lo ce ee sm G tn s Gf tf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (drule (cj 1 compile_expr_grows) >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `val_wf rt v` by (irule value_has_type_memory_wf >> first_assum ACCEPT_TAC) >>
  `nb < dimword (:256)` by decide_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func ce cx e es sa sb s0 ee v (Var root) z /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z /\
    ghost_kept_at lo ce es sa Gi ti s0 Gf tf /\
    ptr_val_ok cx (post_value_type ce e) v (Var root) Gf tf z /\
    ptr_buf_ok ce e (Var root) Gf z /\ expr_store_bound cx (post_value_type ce e) v (Var root) z /\
    FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n w,nb) /\
    lo <= w2n w /\ w2n w + nb <= z.vs_alloca_next /\ not_fresh_at sb root /\
    wb_frame ce ee ee sm s z /\ ghost_kept_at lo ce ee sm G tn s Gf tf /\
    (!x cap. not_fresh_at sm x /\ ptr_covers G tn x s cap ==> ptr_covers Gf tf x z cap)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` (drule_then strip_assume_tac) >>
     match_mp_tac copy_materialized_rhs_post_mods >> asm_rewrite_tac[LESS_EQ_REFL]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf) /\
     expr_post_mods H ctx func ce cx e es sa sb s0 ee v (Var root) z /\
     ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ z /\ _`
       (drule_then strip_assume_tac) >>
     asm_rewrite_tac[]) >>
  `lower_value compile_expr ce (expr_type e) e sa = (Var root,sb) /\
   (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (INL v,ee with gas_obs := tail)) /\
   (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,Gi,ti) marks (OK z,Gf,tf) /\
     expr_post_mods H ctx func ce cx e es sa sb s0 ee v (Var root) z /\
     ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z)` by
    (match_mp_tac (local_copy_rhs_unwrap_cut_mods
       |> Q.INST [`s` |-> `z`, `G` |-> `Gf`, `tn` |-> `tf`]
       |> Q.INST [`u` |-> `s`, `Gu` |-> `G`, `tu` |-> `tn`]) >>
     qpat_x_assum `root = _` kall_tac >>
     asm_rewrite_tac[] >> gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ (OK s,_,_) /\ _`
       (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ z /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ z`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def, expr_post_def]) >>
  drule stmt_state_rel_allocas_below_fmp >> disch_tac >>
  `allocas_from lo z` by
    (qpat_assum `ghost_inv_at_mods _ lo _ _ _ _ _ _ z`
       (strip_assume_tac o REWRITE_RULE [bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >>
     first_assum ACCEPT_TAC) >>
  `lookup_var root z = SOME w` by fs[venomStateTheory.eval_operand_def] >>
  `op_taint tf (Var root) = {}` by fs[ptr_covers_def] >>
  `s0.vs_alloca_next <= z.vs_alloca_next` by decide_tac >>
  `evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
   expr_val_at ce cx (lowered_value_type ce e) sa sb ee v (Var root) z` by
    (qpat_assum `post_value_type ce e = _` (fn th => pure_once_rewrite_tac [GSYM th]) >>
     asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> simp[] >>
      irule ptr_covers_lookup_frame >> qexistsl_tac [`Gi`,`s0`,`ti`] >>
      qpat_assum `ghost_kept_at _ _ _ _ Gi ti s0 Gf tf`
        (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ (OK s,_,_) /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ s`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `nb = _` (SUBST1_TAC o SYM) >>
  qpat_assum `!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = _ ==> _`
    irule >> qexists_tac `aid` >> simp[]
QED
