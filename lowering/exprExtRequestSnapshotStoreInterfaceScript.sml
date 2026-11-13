(* Current-value cells expose unwrap execution, independently of producers. *)
Theory exprExtRequestSnapshotStoreInterface
Ancestors
  exprExtRequestTupleFold exprExtRequestHistoryCompose exprSafeOperand
  exprLowering compileEnv vyperInterpreter valueTypingMemoryProps
  valueEncodingProps gasSummary fragGasMode fragExec

Definition extrequest_snapshot_cell_def:
  extrequest_snapshot_cell ctx func ce cx eb cb tb (vv,ty,tv,v) <=>
    evaluate_type (get_tenv cx) ty = SOME tv /\
    value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes ce ty = type_memory_size tv /\
    type_memory_size tv < dimword (:256) /\
    (!ee sm su s op.
      extrequest_history_frame ce cx eb cb tb ee sm s /\
      stmt_state_rel ctx func ce cx ee s /\ ee.gas_obs = [] /\
      unwrap_value ce vv sm = (op,su) /\
      fn_has_code sm su func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved ce sm /\ ~s.vs_halted /\
      s.vs_current_bb = sm.cs_current_bb /\
      s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
      ?u. gas_marked_path F ctx func s 0 (OK u) /\
        stmt_state_rel ctx func ce cx ee u /\
        expr_val_rel cx ty v op u /\ safe_operand su op /\
        extrequest_history_frame ce cx ee sm s ee su u /\
        ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
        u.vs_inst_idx = LENGTH su.cs_current_insts /\
        (!aid p k. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
          mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory))
End

Theorem extrequest_snapshot_cell_history:
  extrequest_snapshot_cell ctx func ce cx eb cb tb cell /\
  stmt_state_rel ctx func ce cx eb tb /\
  extrequest_history_frame ce cx eb cb tb ec sc tc ==>
  extrequest_snapshot_cell ctx func ce cx ec sc tc cell
Proof
  PairCases_on `cell` >> simp[extrequest_snapshot_cell_def] >>
  rpt strip_tac >>
  `extrequest_history_frame ce cx eb cb tb ee sm s` by
    (drule_all extrequest_history_frame_trans >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

(* The fold contract is shared by independent execution and prefix proofs. *)
Definition extrequest_snapshot_store_contract_def:
  extrequest_snapshot_store_contract ctx func ce cx <=>
  !cells off sm sb s eb cb tb ee buf live tuple_base sz w.
    EVERY (extrequest_snapshot_cell ctx func ce cx eb cb tb) cells /\
    compile_extcall_store_values ce
      (MAP (\(vv,ty,tv,v). (vv,ty)) cells) buf off sm = ((),sb) /\
    stmt_state_rel ctx func ce cx eb tb /\
    stmt_state_rel ctx func ce cx ee s /\
    extrequest_history_frame ce cx eb cb tb ee sm s /\
    cb.cs_next_id <= live /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    ee.gas_obs = [] /\ safe_operand sm buf /\ eval_operand buf s = SOME w /\
    FLOOKUP s.vs_allocas live = SOME (tuple_base,sz) /\ live < sm.cs_next_id /\
    tuple_base <= w2n w + off /\
    w2n w + off + SUM (MAP (\(vv,ty,tv,v). type_memory_size tv) cells) <=
      tuple_base + sz /\
    tuple_base + sz < dimword (:256) /\
    (!name b len. local_region ce ee.scopes s name b len ==>
       regions_disjoint tuple_base sz b len) /\
    (ce.ce_is_ctor ==> !name itv iv io.
       FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
       FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
       regions_disjoint io (type_memory_size itv) tuple_base sz) /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?q. gas_marked_path F ctx func s 0 (OK q) /\
      stmt_state_rel ctx func ce cx ee q /\
      tuple_in_memory (MAP (\(vv,ty,tv,v). v) cells)
        (MAP (\(vv,ty,tv,v). tv) cells) (w2n w + off) q.vs_memory /\
      extrequest_history_frame ce cx eb cb tb ee sb q /\
      FLOOKUP q.vs_allocas live = SOME (tuple_base,sz) /\
      (!a k. tuple_base <= a /\ a + k <= tuple_base + sz /\
         regions_disjoint a k (w2n w + off)
           (SUM (MAP (\(vv,ty,tv,v). type_memory_size tv) cells)) ==>
         mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
      ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x z. not_fresh_at sm x /\ lookup_var x s = SOME z ==>
         lookup_var x q = SOME z) /\
      (!aid p k. aid < sm.cs_next_id /\ aid <> live /\
         FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
         mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory) /\
      (!name b len. local_region ce ee.scopes s name b len ==>
         mem_bytes_at b len q.vs_memory = mem_bytes_at b len s.vs_memory) /\
      (ce.ce_is_ctor ==> !name itv iv io.
         FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
         FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
           | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
         mem_bytes_at io (type_memory_size itv) q.vs_memory =
         mem_bytes_at io (type_memory_size itv) s.vs_memory)
End
