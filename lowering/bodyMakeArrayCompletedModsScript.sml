(* Package the recorded MakeArray result at its own memory allocation. *)
Theory bodyMakeArrayCompletedMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodySimStmtFacts exprBodyPreProps
  exprSimAggregateChildren exprSimBuffer exprSimProps exprSimMemDefs
  exprSimHypsDefs bodyFullHashKeccakFixed valueEncodingTyping
  exprLoweringProps loweringPosts loweringStateRelDefs bodyPtrDefs
  vyperTypeEvalCaseProofs vyperTypeExprSoundness vyperTypeInvariants
  context compileEnv vyperInterpreter vyperState vyperAST venomState words

val _ = Parse.hide "base";

Triviality completed_value_wf:
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e (es with gas_obs := gs) = (INL (Value v),ee) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  val_wf tv v
Proof
  strip_tac >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
    simp[bind_def, read_result_def, return_def] >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs) <=>
   expr_body_pre_mods mods ce cx env e es` by
    simp_tac (srw_ss()) [expr_body_pre_mods_def, expr_sim_inv_mods_def] >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_at (Pat `bind _ _ _ = _`)
    (SIMP_RULE (srw_ss() ++ ETA_ss) [] expr_body_pre_eval_mods) >>
  disch_then (drule_then strip_assume_tac) >>
  drule expr_sim_inv_mods_env >>
  disch_then (strip_assume_tac o MATCH_MP
    (SPEC_ALL env_consistent_type_defs_get_tenv)) >>
  fs[value_runtime_typed_def] >>
  metis_tac[cj 1 value_has_type_val_wf, optionTheory.SOME_11]
QED

Triviality completed_memory_post:
  vv_post H ctx func ce cx e es sa sb s0 ee (Value v)
    (LocatedValue a (mk_ptr op LocMemory)) t /\
  immutable_frame_mods func ce cx ee t ==>
  vv_post_mods H ctx func ce cx e es sa sb s0 ee (Value v)
    (LocatedValue a (mk_ptr op LocMemory)) t
Proof
  simp[vv_post_mods_def, vv_post_def, vv_holds_mods_def,
       vv_place_ptr_mods_def, vv_place_ptr_def, mk_ptr_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

(* The capacity, source result and physical/ghost landing describe the
   same run. No assumption about the active module being the main module. *)
Theorem make_array_completed_mods:
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e (es with gas_obs := gs) = (INL (Value v),ee) /\
  lowered_value_type ce e = expr_type e /\ ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  cap = type_memory_bytes ce (expr_type e) /\ cap = type_memory_size tv /\
  (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory tv v base m) /\
  ci_mono sa sm /\ ci_mono sm sb /\ sa.cs_next_id < sm.cs_next_id /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)] [q]) (fn_insts func) /\
  si.vs_memory = s0.vs_memory /\
  (!n b k. local_region ce es.scopes si n b k <=> local_region ce es.scopes s0 n b k) /\
  base + cap < dimword (:256) /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (base,cap) /\
  lookup_var q t = SOME (n2w base) /\ ptr_covers G tn q t cap /\
  base + cap <= t.vs_alloca_next /\
  (!n b k. local_region ce ee.scopes t n b k ==>
    loweringStateRelDefs$regions_disjoint base cap b k) /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  wb_frame ce es ee sa s0 t /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  return_buf_frame d ce sb t /\ ~t.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  stmt_state_rel H ctx func ce cx ee t /\ immutable_frame_mods func ce cx ee t /\
  storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods D lo d ce cx ee G tn t /\
  (~expr_has_effect e ==>
    (!n b k. local_region ce es.scopes si n b k ==>
      mem_bytes_at b k t.vs_memory = mem_bytes_at b k si.vs_memory) /\
    (!p n. (p+n <= base \/ base+cap <= p) /\
      (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        sm.cs_next_id <= inst.inst_id /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
        loweringStateRelDefs$regions_disjoint p n b sz) ==>
      mem_bytes_at p n t.vs_memory = mem_bytes_at p n si.vs_memory)) ==>
  vv_post_mods H ctx func ce cx e es sa sb s0 ee (Value v)
    (LocatedValue (expr_type e) (mk_ptr (Var q) LocMemory)) t /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee (Value v)
    (LocatedValue (expr_type e) (mk_ptr (Var q) LocMemory)) t /\
  ptr_vv_ok cx (post_value_type ce e) (Value v)
    (LocatedValue (expr_type e) (mk_ptr (Var q) LocMemory)) ee G tn t /\
  vv_own ce cx (post_value_type ce e) sa sb ee (Value v)
    (LocatedValue (expr_type e) (mk_ptr (Var q) LocMemory)) t /\
  ptr_buf_ok ce e (Var q) G t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods D lo d ce cx ee G tn t /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\ return_buf_frame d ce sb t /\ ~t.vs_halted
Proof
  strip_tac >>
  `post_value_type ce e = expr_type e` by simp[post_value_type_lowered] >>
  `base < dimword (:256)` by decide_tac >>
  `w2n (n2w base : 256 word) = base` by simp[w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `val_wf tv v` by (drule_all completed_value_wf >> simp[]) >>
  `val_footprint tv v <= cap /\ val_store_size tv v <= cap` by
    metis_tac[val_footprint_le,val_store_size_le] >>
  `sa.cs_next_id < sb.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
  `~expr_has_effect e ==> pure_frame ce func es sa s0 t` by
    (strip_tac >>
     qpat_assum `~expr_has_effect e ==> _` drule >> strip_tac >>
     irule aggregate_pure_frame_buffer >> conj_tac
     >- (qexistsl [`cap`,`base`,`sm`,`si`] >>
         pure_asm_rewrite_tac[] >>
         `sa.cs_next_id <= sm.cs_next_id` by decide_tac >> simp[]) >>
     qexistsl [`[Lit (n2w cap)]`,`[q]`] >> simp[]) >>
  `val_in_memory tv v base t.vs_memory` by
    (qpat_x_assum `!m. mem_agree_outside _ _ _ ==> _` irule >> simp[mem_agree_outside_def]) >>
  `vv_post H ctx func ce cx e es sa sb s0 ee (Value v)
     (LocatedValue (expr_type e) (mk_ptr (Var q) LocMemory)) t` by
    (irule buffer_memory_vv_post_general >>
     simp[mk_ptr_def, eval_operand_def] >>
     fs[wb_frame_def, ci_mono_def, loweringStateRelDefsTheory.regions_disjoint_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  simp[completed_memory_post] >>
  conj_tac
  >- (asm_rewrite_tac[] >> drule vv_store_bound_capacity >> disch_then irule >>
      simp[mk_ptr_def, eval_operand_def]) >>
  conj_tac
  >- (simp[ptr_vv_ok_def, mk_ptr_def, read_result_def, return_def,
           ptr_mem_ok_def, eval_operand_def] >>
      gvs[ptr_covers_def] >> decide_tac) >>
  conj_tac
  >- (simp[vv_own_def, mk_ptr_def, read_result_def, return_def, eval_operand_def] >>
      disj1_tac >> qexistsl [`sa.cs_next_id`,`base`,`cap`] >>
      simp[] >> gvs[loweringStateRelDefsTheory.regions_disjoint_def] >>
      rpt gen_tac >> strip_tac >> first_x_assum drule >> simp[]) >>
  gvs[ptr_buf_ok_def, ptr_covers_def, eval_operand_def]
QED
