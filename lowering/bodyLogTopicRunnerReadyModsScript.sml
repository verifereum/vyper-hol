(* Instantiate the saved-topic traversal at the actual packed Log cut. *)
Theory bodyLogTopicRunnerReadyMods
Ancestors
  bodyLogTopicListMods bodyLogTopicRowMods bodyLogTopicAnchorFramesMods
  bodyInvCodeProps eventLoweringStructure exprLoweringProps wordArgsPtr
  exprSimWordArgs vyperStorageFootprint finite_map freshWrites list pair
  bodyAbiEncodePackedPostMods

val log_row_type = ``\e v.
  ?rt. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
       value_has_type rt v /\
       type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
       type_memory_size rt < 2**64``;

val log_cut = ``\a u Gu tu.
  ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\
  u.vs_inst_idx = LENGTH a.cs_current_insts /\ alloca_history func u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  sm.cs_next_id <= a.cs_next_id /\ sm.cs_next_var <= a.cs_next_var /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ t.vs_alloca_next <= u.vs_alloca_next /\
  local_ptrs_reserved ce a /\ return_buf_frame d ce a u /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func ce cx mid u /\ storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx mid Gu tu u /\ immutable_frame_mods func ce cx mid u) /\
  MAP FDOM mid.scopes = MAP FDOM es.scopes /\
  wb_frame ce mid mid sm t u /\ ghost_kept_at lo ce mid sm G1 tn1 t Gu tu /\
  wb_frame ce es mid sa s0 u /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gu tu``;

val topic_runner =
  log_topic_list_with_row_facts_mods
  |> Q.INST [`rows` |-> `ZIP (ZIP (args,saved),MAP (lowered_value_type ce) args)`,
      `origin` |-> `sa`, `front` |-> `sm`, `last` |-> `se`, `ee` |-> `mid`,
      `s` |-> `t`, `G` |-> `G1`, `tn` |-> `tn1`, `hash` |-> `h`,
      `A` |-> `^log_row_type`, `P` |-> `^log_cut`]
  |> BETA_RULE;

Theorem log_topic_runner_specialized_mods:
  ^(concl topic_runner)
Proof
  ACCEPT_TAC topic_runner
QED

(* Move both anchors using the same successor as the singleton topic run. *)
Theorem log_runner_row_step[local]:
  expr_sim_inv_mods mods ce cx env mid /\ storage_trace_domain cx st0 mid.storage_trace /\
  fn_inst_ids_distinct func /\ ci_mono sa sm /\ local_ptrs_reserved ce sa /\
  ty = lowered_value_type ce e /\ hashed = is_bytestring_type ty /\
  supported_event_leaf_type ty /\ encode_event_topic ty v = SOME w /\
  (^log_row_type) e v /\ expr_body_pre_mods mods ce cx env e entry /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     ?si sm ss vv copy. abi_encode_saved_row_mods lo ce cx sa a
       e sv v si sm ss vv copy H mid Gu tu u) /\
  (^log_cut) a u Gu tu /\ fn_has_code a b func /\
  compile_log_saved_topics ce [(sv,hashed)] a = ([op],b) ==>
  ?z Gz tz. (^log_cut) b z Gz tz /\ ~z.vs_halted /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
    safe_operand b op /\ eval_operand op z = SOME w /\ op_taint tz op = {} /\
    (!x. not_fresh_at a x ==> lookup_var x z = lookup_var x u /\
      FLOOKUP Gz x = FLOOKUP Gu x /\ op_taint tz (Var x) = op_taint tu (Var x))
Proof
  simp_tac bool_ss [] >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func ce cx mid u /\ immutable_frame_mods func ce cx mid u /\
    storage_well_formed_on cx mid (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx mid Gu tu u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  qpat_x_assum `ty = lowered_value_type ce e` SUBST_ALL_TAC >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`ty` |-> `lowered_value_type ce e`] log_topic_row_mods)) >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choosel_then [`z`, `Gz`, `tz`] (map_every assume_tac o CONJUNCTS))) >>
  `ci_mono a b` by
    (qspecl_then [`[(sv,hashed)]`, `ce`, `a`] mp_tac compile_log_saved_topics_ci_mono >> simp[]) >>
  `a.cs_next_var <= b.cs_next_var /\ a.cs_next_id <= b.cs_next_id` by
    (qpat_assum `ci_mono a b` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     asm_rewrite_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (qpat_assum `ci_mono sa sm` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     asm_rewrite_tac[]) >>
  `local_ptrs_reserved ce sm` by (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `wb_frame ce mid mid sm t z /\ ghost_kept_at lo ce mid sm G1 tn1 t Gz tz` by
    (irule log_topic_anchor_frames_mods >> asm_simp_tac bool_ss [] >>
     qexistsl [`Gu`, `a`, `tu`, `u`] >> asm_rewrite_tac[]) >>
  `wb_frame ce es mid sa s0 z /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gz tz` by
    (`sa.cs_next_var <= a.cs_next_var /\ sa.cs_next_id <= a.cs_next_id` by decide_tac >>
     irule log_topic_anchor_frames_mods >> asm_simp_tac bool_ss [] >>
     qexistsl [`Gu`, `a`, `tu`, `u`] >> asm_rewrite_tac[]) >>
  `sm.cs_next_var <= b.cs_next_var /\ sm.cs_next_id <= b.cs_next_id /\
    t.vs_alloca_next <= z.vs_alloca_next` by decide_tac >>
  `local_ptrs_reserved ce b` by (irule local_ptrs_reserved_next_var >> qexists `a` >> simp[]) >>
  qexistsl [`z`, `Gz`, `tz`] >> asm_rewrite_tac[] >>
  conj_tac >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists `a` >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists `a` >> simp[]) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ z /\ _`
    (drule_then strip_assume_tac) >> asm_rewrite_tac[]
QED

(* The two projections and both row relations use the same zipped indices. *)
Theorem log_runner_aligned_rows[local]:
  let atys = MAP (lowered_value_type ce) args in
  let rows = ZIP (ZIP (args,saved),atys) in
  LENGTH flags = LENGTH args /\ LENGTH flags = LENGTH saved /\ LENGTH flags = LENGTH vs /\
  EVERY (\(ty,f). f ==> supported_event_leaf_type ty) (ZIP (atys,flags)) /\
  (!j. j < LENGTH flags ==> expr_body_pre_mods mods ce cx env (EL j args) entry /\
    (^log_row_type) (EL j args) (EL j vs)) /\
  EVERY (\sv. !x. vv_operand sv = Var x ==> not_fresh_at sm x) saved /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    LIST_REL (\(e,sv) v. ?si sm' ss vv copy.
      abi_encode_saved_row_mods lo ce cx sa sm e sv v si sm' ss vv copy H mid G1 tn1 t)
      (ZIP (args,saved)) vs) ==>
  LENGTH flags = LENGTH rows /\ MAP SND rows = atys /\
  MAP (\((e,sv),ty). (sv,ty)) rows = ZIP (saved,atys) /\
  LIST_REL (\((e,sv),ty) v. ty = lowered_value_type ce e /\ (^log_row_type) e v /\
    expr_body_pre_mods mods ce cx env e entry /\
    (!x. vv_operand sv = Var x ==> not_fresh_at sm x) /\
    !H. valid_horizon cx st0 H mid.storage_trace ==>
      ?si sm' ss vv copy. abi_encode_saved_row_mods lo ce cx sa sm e sv v si sm' ss vv copy H mid G1 tn1 t)
    rows vs /\
  LIST_REL (\(flag,row) v. flag ==> supported_event_leaf_type (SND row)) (ZIP (flags,rows)) vs
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH args = LENGTH saved` by decide_tac >>
  `LENGTH (ZIP (args,saved)) = LENGTH args` by simp[LENGTH_ZIP] >>
  `LENGTH (ZIP (ZIP (args,saved),MAP (lowered_value_type ce) args)) = LENGTH args` by
    simp[LENGTH_ZIP] >>
  conj_tac >- decide_tac >>
  conj_tac >- simp[MAP_ZIP] >>
  conj_tac >-
    (simp[Once LIST_EQ_REWRITE, LENGTH_ZIP, EL_MAP, EL_ZIP, UNCURRY] >>
     rpt strip_tac >> `n < LENGTH saved` by decide_tac >> simp[EL_MAP, EL_ZIP, UNCURRY]) >>
  conj_tac
  >- suspend "saved"
  >> suspend "supported"
QED

Resume log_runner_aligned_rows[saved]:
  simp[LIST_REL_EL_EQN] >> gen_tac >> disch_tac >>
  `n < LENGTH flags /\ n < LENGTH args /\ n < LENGTH saved` by decide_tac >>
  qpat_assum `!j. j < LENGTH flags ==> expr_body_pre_mods _ _ _ _ _ _ /\ _`
    (qspec_then `n` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) []) >>
  qpat_assum `EVERY _ saved` (qspec_then `n` mp_tac o REWRITE_RULE [EVERY_EL]) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (assume_tac o BETA_RULE) >> simp[EL_ZIP, EL_MAP, UNCURRY] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> LIST_REL _ _ _`
    (drule_then (qspec_then `n` mp_tac o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN])) >>
  simp[EL_ZIP, UNCURRY]
QED

Resume log_runner_aligned_rows[supported]:
  simp[LIST_REL_EL_EQN, LENGTH_ZIP] >> gen_tac >> disch_tac >>
  `n < LENGTH flags /\ n < LENGTH args /\ n < LENGTH saved` by decide_tac >>
  qpat_assum `EVERY _ (ZIP (MAP (lowered_value_type ce) args,flags))`
    (qspec_then `n` mp_tac o REWRITE_RULE [EVERY_EL]) >>
  simp[LENGTH_ZIP, EL_ZIP, EL_MAP, UNCURRY]
QED

Finalise log_runner_aligned_rows

Theorem log_topic_runner_ready_mods:
  let atys = MAP (lowered_value_type ce) args in
  let topic_rows = FST (split_log_ops (ZIP (saved,atys)) flags) in
  let typed = (LENGTH flags = LENGTH args /\ LENGTH flags = LENGTH saved /\
    LENGTH flags = LENGTH vs /\ LENGTH (FILTER I flags) <= 3 /\
    encode_indexed_event_topics flags atys vs = SOME topics /\
    EVERY (\(ty,f). f ==> supported_event_leaf_type ty) (ZIP (atys,flags)) /\
    (!j. j < LENGTH flags ==>
      expr_body_pre_mods mods ce cx env (EL j args) entry /\
      ?rt. evaluate_type (get_tenv cx) (EL j atys) = SOME rt /\
        value_has_type rt (EL j vs) /\ type_memory_bytes ce (EL j atys) = type_memory_size rt /\
        type_memory_size rt < 2**64)) in
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
  typed /\ P0 ==> ^(fst (dest_imp (concl topic_runner)))
Proof
  simp_tac bool_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ce.ce_modules = mods` by (drule_then ACCEPT_TAC contract_inv_cenv_modules) >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==>
      abi_encode_packed_post_mods _ DF lo d ctx func ce cx env args saved
        sa sm es s0 G0 tn0 H (INL vs) mid G1 tn1 t /\ _`
    (assume_tac o SIMP_RULE (srw_ss()) [abi_encode_packed_post_mods_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> (LENGTH saved = LENGTH args /\ _) /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS o CONJUNCT1) >>
  `expr_sim_inv_mods mods ce cx env mid` by
    (qpat_assum `ce.ce_modules = mods` (fn eq =>
       qhdtm_assum `expr_sim_inv_mods` (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    LIST_REL (\(e,sv) v. ?si sm' ss vv copy.
      abi_encode_saved_row_mods lo ce cx sa sm e sv v si sm' ss vv copy H mid G1 tn1 t)
      (ZIP (args,saved)) vs` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> (LENGTH saved = LENGTH args /\ _) /\ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS o CONJUNCT1) >>
     first_assum ACCEPT_TAC) >>
  `!j. j < LENGTH flags ==> expr_body_pre_mods mods ce cx env (EL j args) entry /\
    (^log_row_type) (EL j args) (EL j vs)` by
    (simp_tac bool_ss [] >> gen_tac >> disch_tac >>
     `EL j (MAP (lowered_value_type ce) args) = lowered_value_type ce (EL j args)` by
       (irule EL_MAP >> decide_tac) >>
     qpat_assum `!j. j < LENGTH flags ==> expr_body_pre_mods _ _ _ _ _ _ /\ _`
       (qspec_then `j` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (fn th => qpat_assum `EL j (MAP _ args) = _`
       (fn eq => ACCEPT_TAC (REWRITE_RULE [eq] th)))) >>
  qpat_x_assum `!j. j < LENGTH flags ==> _ /\ (^log_row_type) (EL j args) (EL j vs)`
    (assume_tac o BETA_RULE) >>
  drule_all_then (map_every assume_tac o CONJUNCTS)
    (SIMP_RULE bool_ss [LET_THM] log_runner_aligned_rows) >>
  suspend "landing"
QED

Resume log_topic_runner_ready_mods[landing]:
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func ce cx mid t /\ storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx mid G1 tn1 t /\ immutable_frame_mods func ce cx mid t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> (LENGTH saved = LENGTH args /\ _) /\ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS o CONJUNCT1) >> asm_rewrite_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved ce sm` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> asm_rewrite_tac[]) >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `(^log_cut) sm t G1 tn1` by
    (simp_tac bool_ss [] >>
     asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL, ghost_kept_at_refl] >>
     irule wb_frame_refl >> REFL_TAC) >>
  qpat_x_assum `(^log_cut) sm t G1 tn1` (assume_tac o BETA_RULE) >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE asm_rewrite_tac[])) >>
  conj_tac >-
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ t /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  conj_tac >-
    (rpt gen_tac >> disch_then (map_every strip_assume_tac o CONJUNCTS) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  suspend "callback"
QED

Resume log_topic_runner_ready_mods[callback]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule (SIMP_RULE bool_ss [] (Q.INST
    [`ty` |-> `lowered_value_type ce e`,
     `hashed` |-> `is_bytestring_type (lowered_value_type ce e)`] log_runner_row_step)) >>
  asm_rewrite_tac[] >> qexistsl [`e`, `entry`, `env`, `mods`, `sv`, `v`] >>
  asm_rewrite_tac[]
QED

Finalise log_topic_runner_ready_mods
