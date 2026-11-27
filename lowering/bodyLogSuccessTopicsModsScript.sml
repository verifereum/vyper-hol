Theory bodyLogSuccessTopicsMods
Ancestors
  bodyLogTopicRunnerReadyMods abiLogSourceEncoding eventLogSplitProps
  eventLoweringStructure stmtSimLogTopics stmtLowering list pair words

Theorem log_success_topics_mods:
  let atys = MAP (lowered_value_type ce) args in
  let topic_rows = FST (split_log_ops (ZIP (saved,atys)) flags) in
  let T = (LENGTH flags = LENGTH args /\ LENGTH flags = LENGTH saved /\
    LENGTH flags = LENGTH vs /\ LENGTH (FILTER I flags) <= 3 /\
    encode_indexed_event_topics flags atys vs = SOME topics /\
    EVERY (\(ty,f). f ==> supported_event_leaf_type ty) (ZIP (atys,flags)) /\
    (!j. j < LENGTH flags ==>
      (expr_body_pre_mods mods ce cx env (EL j args) entry /\
       ?rt. evaluate_type (get_tenv cx) (EL j atys) = SOME rt /\
       value_has_type rt (EL j vs) /\
       type_memory_bytes ce (EL j atys) = type_memory_size rt /\
       type_memory_size rt < 2**64))) in
  let P0 = (contract_inv mods exps ctx ce cx /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      abi_encode_packed_post_mods ce.ce_modules DF lo d ctx func ce cx env
        args saved sa sm es s0 G0 tn0 H (INL vs) mid G1 tn1 t /\
      (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) t)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> dead_lo_ok_mods H (DF H) lo ce cx) /\
    ci_mono sa sm /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    compile_log_saved_topics ce topic_rows sm = (ops,se) /\ fn_has_code sm se func) in
  T /\ P0 ==>
  ?u Gu tu.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK u,Gu,tu)) /\
    ~u.vs_halted /\ u.vs_current_bb = se.cs_current_bb /\ u.vs_inst_idx = LENGTH se.cs_current_insts /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    sm.cs_next_id <= se.cs_next_id /\ sm.cs_next_var <= se.cs_next_var /\
    s0.vs_alloca_next <= t.vs_alloca_next /\ t.vs_alloca_next <= u.vs_alloca_next /\
    local_ptrs_reserved ce se /\ return_buf_frame d ce se u /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      stmt_state_rel H ctx func ce cx mid u /\ storage_well_formed_on cx mid (FST H) /\
      ghost_inv_at_mods (DF H) lo d ce cx mid Gu tu u /\ immutable_frame_mods func ce cx mid u) /\
    MAP FDOM mid.scopes = MAP FDOM es.scopes /\
    wb_frame ce es mid sa s0 u /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gu tu /\
    EVERY (safe_operand se) (Lit (n2w h)::ops) /\
    EVERY (\op. op_taint tu op = {}) (Lit (n2w h)::ops) /\
    eval_operands (Lit (n2w h)::ops) u = SOME (n2w h::topics) /\
    LENGTH (Lit (n2w h)::ops) < dimword (:256) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      LIST_REL (\(e,sv) v. ?si sm0 ss vv copy.
        abi_encode_saved_row_mods lo ce cx sa se e sv v si sm0 ss vv copy H mid Gu tu u)
      (select_log_args F flags (ZIP (args,saved))) (select_log_args F flags vs))
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (fn hyp =>
    (map_every assume_tac (CONJUNCTS hyp)) >>
    mp_tac (MP log_topic_runner_specialized_mods
            (MP (BETA_RULE (PURE_REWRITE_RULE [LET_THM] log_topic_runner_ready_mods)) hyp))) >>
  disch_then (qx_choosel_then [`u`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`u`,`Gu`,`tu`] >> asm_rewrite_tac[] >>
  `LENGTH args = LENGTH saved` by decide_tac >>
  qabbrev_tac `atys = MAP (lowered_value_type ce) args` >>
  `LENGTH atys = LENGTH args` by simp[Abbr `atys`] >>
  conj_tac >-
    (`!rs a os b. compile_log_saved_topics ce rs a = (os,b) ==> LENGTH os = LENGTH rs` by
       (Induct >> simp[compile_log_saved_topics_def, compileEnvTheory.comp_return_def,
                       Once compile_log_saved_topics_cons] >>
        rpt strip_tac >> first_x_assum drule >> simp[]) >>
     first_x_assum (drule_then assume_tac) >>
     `LENGTH flags = LENGTH (ZIP (saved,atys))` by simp[LENGTH_ZIP] >>
     drule_then strip_assume_tac
       (Q.SPECL [`ZIP (saved,atys)`, `flags`] split_log_ops_lengths) >>
     `4 < dimword (:256)` by simp[dimword_def] >>
     simp[] >> decide_tac) >>
  qabbrev_tac `rows = ZIP (ZIP (args,saved),atys)` >>
  `LENGTH (ZIP (args,saved)) = LENGTH atys` by simp[LENGTH_ZIP] >>
  `LENGTH flags = LENGTH rows` by simp[Abbr `rows`, LENGTH_ZIP] >>
  `MAP FST rows = ZIP (args,saved)` by simp[Abbr `rows`, MAP_ZIP] >>
  gen_tac >> disch_tac >>
  `SND (split_log_ops rows flags) = select_log_args F flags rows` by
    simp[eventLogSplitPropsTheory.split_log_ops_select] >>
  qpat_assum `SND (split_log_ops rows flags) = _` (fn eq =>
    qpat_assum `LIST_REL _ (SND (split_log_ops rows flags)) _`
      (mp_tac o PURE_REWRITE_RULE [eq, log_non_indexed_values_select])) >>
  qpat_assum `MAP FST rows = _` (fn eq => pure_once_rewrite_tac[GSYM eq]) >>
  pure_rewrite_tac[select_log_args_MAP, LIST_REL_MAP1] >>
  disch_then (fn rel => irule LIST_REL_mono >> irule_at Any rel) >>
  PairCases >> simp[combinTheory.o_DEF]
QED
