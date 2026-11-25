(* Lift the observed ExtCall packing prefix, before issuing the request. *)
Theory bodyExtPackingFrameMods
Ancestors
  bodyCalldataSliceLinkedFrameMods bodyMemoryDefs stateRelProj
  bodyFullShadowBodyInv abiEncoderWindowContract loweringPosts
  loweringStateRelDefs compileEnv venomState finite_map pred_set

Theorem ext_packing_frame_mods:
  stmt_state_rel H ctx func ce cx ke zg /\
  ghost_inv_at_mods D lo d ce cx ke Gg tng zg /\
  immutable_frame_mods func ce cx ke zg /\
  local_ptrs_reserved ce s5 /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s5 x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s5 x) /\
  pure_frame ce func ke s5 zg t /\
  window_alloca_growth zg t /\
  (!aid row. FLOOKUP zg.vs_allocas aid = SOME row ==>
             FLOOKUP t.vs_allocas aid = SOME row) /\
  (!x. not_fresh_at s5 x ==>
       lookup_var x t = lookup_var x zg /\ FLOOKUP Gf x = FLOOKUP Gg x /\
       op_taint tf (Var x) = op_taint tng (Var x)) /\
  (!i. i < zg.vs_alloca_next /\ i IN tf.t_mem ==> i IN tng.t_mem) /\
  tf.t_stor = tng.t_stor /\ tf.t_trans = tng.t_trans /\ tf.t_imm = tng.t_imm /\
  t.vs_accounts = zg.vs_accounts /\ t.vs_transient = zg.vs_transient /\
  t.vs_call_ctx = zg.vs_call_ctx /\ t.vs_immutables = zg.vs_immutables /\
  t.vs_data_section = zg.vs_data_section /\ LENGTH zg.vs_memory <= LENGTH t.vs_memory ==>
  ghost_inv_at_mods D lo d ce cx ke Gf tf t /\ immutable_frame_mods func ce cx ke t
Proof
  strip_tac >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `lo <= zg.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >>
     first_assum ACCEPT_TAC) >>
  `!i. i < lo /\ i IN tf.t_mem ==> i IN tng.t_mem` by
    (rpt strip_tac >>
     `i < zg.vs_alloca_next` by decide_tac >> simp[]) >>
  `!nm b len. local_region ce ke.scopes zg nm b len ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len zg.vs_memory /\
       (!i. b <= i /\ i < b+len /\ i IN tf.t_mem ==> i IN tng.t_mem)` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (qpat_assum `pure_frame _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE[pure_frame_def]) >>
         qpat_assum `!n b sz. local_region _ _ _ n b sz ==> _`
           (drule_then ACCEPT_TAC)) >>
     drule_all_then assume_tac body_local_region_frontier >>
     rpt strip_tac >> `i < zg.vs_alloca_next` by decide_tac >> simp[]) >>
  qpat_x_assum `window_alloca_growth _ _`
    (strip_assume_tac o REWRITE_RULE[window_alloca_growth_def]) >>
  `!aid a len. FLOOKUP t.vs_allocas aid = SOME (a,len) ==>
       FLOOKUP zg.vs_allocas aid = SOME (a,len) \/ zg.vs_alloca_next <= a` by
    (rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP zg.vs_allocas aid`
     >- (disj2_tac >>
         qpat_assum `!i b sz. FLOOKUP zg.vs_allocas i = NONE /\ _ ==> _`
           (qspecl_then [`aid`,`a`,`len`] mp_tac) >> simp[]) >>
     disj1_tac >>
     qpat_assum `!aid row. FLOOKUP zg.vs_allocas aid = SOME row ==> _`
       (drule_then assume_tac) >>
     qpat_assum `FLOOKUP t.vs_allocas aid = SOME (a,len)`
       (fn th => fs[th])) >>
  irule calldata_slice_linked_frame_mods >>
  qexistsl [`Gg`, `zg`, `s5`, `tng`] >> asm_rewrite_tac[]
QED
