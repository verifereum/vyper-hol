Theory bodyIntCallStorePost
Ancestors
  bodyIntCallRestoreResults bodyIntCallReturnLayout exprSimProps
  loweringPosts compileEnv exprLoweringProps intCallResult
  finite_map arithmetic list venomMemDefs exprSimHash valueTypingMemoryProps
  fragExec venomState

(* A write inside a fresh owned allocation preserves the original frame.
   Source scopes need not be identical: transport the original regions. *)
Theorem wb_frame_owned_memory_tail:
  wb_frame ce es0 sa s0 s /\ alloca_inv s /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid /\
  sa.cs_next_var <= si.cs_next_var /\
  (!x. not_fresh_at si x ==> lookup_var x u = lookup_var x s) /\
  u.vs_allocas = s.vs_allocas /\
  (!a len. a + len <= b \/ b + sz <= a ==>
    mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory) /\
  (!n lb lsz. local_region ce es0.scopes s0 n lb lsz ==>
    lb + lsz <= b \/ b + sz <= lb) ==>
  wb_frame ce es0 sa s0 u
Proof
  strip_tac >> fs[wb_frame_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at si x` by
        (fs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
      metis_tac[])
  >- (rpt strip_tac >> rename1 `FLOOKUP s0.vs_allocas old = SOME (off,len)` >>
      `FLOOKUP s.vs_allocas old = SOME (off,len)` by metis_tac[] >>
      `old <> aid` by decide_tac >>
      `off + len <= b \/ b + sz <= off` by
        (fs[alloca_inv_def, allocas_non_overlapping_def,
            regions_disjoint_def] >> metis_tac[ADD_COMM]) >>
      metis_tac[]) >>
  irule locals_kept_regions_tail >> qexists_tac `s` >> simp[] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem owned_buffer_result_post:
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  stmt_state_rel ctx func ce cx es' s /\
  stmt_state_rel ctx func ce cx es' u /\
  vv_holds ce cx (expr_type e) (Value v)
    (LocatedValue (expr_type e) (base_ptr buf)) es' u /\
  wb_frame ce es0 sa s0 s /\
  local_ptrs_reserved ce si /\ sa.cs_next_var <= si.cs_next_var /\
  (!x. not_fresh_at si x ==> lookup_var x u = lookup_var x s) /\
  u.vs_allocas = s.vs_allocas /\
  eval_operand buf.buf_operand u = SOME w /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
  (!n lb lsz. local_region ce es'.scopes s n lb lsz ==>
    b + sz <= lb \/ lb + lsz <= b) /\
  (!n lb lsz. local_region ce es0.scopes s0 n lb lsz ==>
    local_region ce es'.scopes s n lb lsz) /\
  (!a len. a + len <= b \/ b + sz <= a ==>
    mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory) ==>
  vv_post ctx func ce cx e es0 sa sb s0 es' (Value v)
    (LocatedValue (expr_type e) (base_ptr buf)) u
Proof
  strip_tac >> irule vv_post_frame_intro >> simp[] >> reverse conj_tac
  >- (irule allocated_value_vv_at >>
      qexistsl_tac [`aid`,`b`,`sz`,`tv`,`w`] >>
      simp[contextTheory.base_ptr_def] >> reverse conj_tac
      >- metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
      rpt strip_tac >>
      `local_region ce es'.scopes s n lb lsz` by
        (irule local_region_frame >> conj_tac
         >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
         qexistsl_tac [`si`,`es'.scopes`,`u`] >> simp[]) >> metis_tac[]) >>
  irule wb_frame_owned_memory_tail >>
  goal_assum (drule_at Any) >> qexistsl_tac [`aid`,`si`] >>
  fs[stmt_state_rel_def] >> metis_tac[]
QED

(* The result stores upgrade their representation post to an owned value
   post, retaining the frame from before the whole expression. *)
Theorem stack_buffer_suffix_post:
  store_multi_results buf.buf_operand results 0 si = ((),sb) /\
  local_ptrs_reserved ce si /\
  buf.buf_operand = Var p /\ not_fresh_at si p /\
  (!x. MEM (Var x) results ==> not_fresh_at si x) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  0 < returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name))
    (expr_type e) /\
  intret_vals_match tv v ws /\ ws <> [] /\
  stmt_state_rel ctx func ce cx es' s /\ wb_frame ce es0 sa s0 s /\
  sa.cs_next_var <= si.cs_next_var /\
  eval_operand buf.buf_operand s = SOME w /\
  MAP (\op. eval_operand op s) results = MAP SOME ws /\
  w2n w + 32 * LENGTH results < dimword (:256) /\
  FLOOKUP s.vs_allocas aid = SOME (w2n w,32 * LENGTH results) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  val_footprint tv v <= 32 * LENGTH results /\
  (!n lb lsz. local_region ce es'.scopes s n lb lsz ==>
    w2n w + 32 * LENGTH results <= lb \/ lb + lsz <= w2n w) /\
  (!n lb lsz. local_region ce es0.scopes s0 n lb lsz ==>
    local_region ce es'.scopes s n lb lsz) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name =
      SOME (itv,iv) ==>
    regions_disjoint (w2n w) (32 * LENGTH results) off
      (type_memory_size itv)) ==>
  frag_exec ctx si sb (\u. u = s)
    (\u. vv_post ctx func ce cx e es0 sa sb s0 es' (Value v)
      (LocatedValue (expr_type e) (base_ptr buf)) u) (\r. F)
Proof
  strip_tac >>
  drule_all stack_return_value_layout >> disch_then assume_tac >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at si x` by simp[] >>
  drule_all store_multi_results_frag >>
  strip_tac >> irule frag_exec_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >>
  rename1 `vv_post _ _ _ _ _ _ _ _ _ _ _ _ out` >>
  `eval_operand buf.buf_operand out = SOME w` by
    (simp[eval_operand_def] >>
     qpat_x_assum `eval_operand _ s = SOME w` mp_tac >>
     simp[eval_operand_def]) >>
  irule owned_buffer_result_post >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`aid`,`w2n w`,`s`,`si`,`32 * LENGTH results`] >>
  simp[] >> metis_tac[ADD_COMM]
QED
