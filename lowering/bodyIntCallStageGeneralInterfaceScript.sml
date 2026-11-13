(* Caller-general spatial resources.  These predicates package a traversal's
   fixed parameters, not an internal caller or a joint-induction frame. *)
Theory bodyIntCallStageGeneralInterface
Ancestors
  bodySim bodyIntCallJointContract exprSimWordArgs exprLoweringProps
  freshWrites intCallFrame exprSimProps bodyMemoryDefs exprSimAggregateChildren
  bodyPtrAttributeSource exprSimMemDefs exprSimDefs loweringPosts

(* Reuse audit (caller-general lower boundaries):
   - bodyIntCallForcing.protected_value_forcing takes explicit lo, protected
     windows and reserved operands; its upper joint wrappers and the word
     endpoint still require intcall_frame_ok and cannot be applied directly.
   - bodyIntCallWindowLanding.materialization_alloc_landing needs no fresh
     register bindings.  It preserves memory, old variables/allocations and
     reserved operands and proves disjointness from live locals.  Its window
     variant also separates any window inside an earlier allocation.
   - bodyIntCallFamCallIntStageStore.intcall_stage_store_effect gives a
     typed_copy_effect and stmt_state_rel; local and constructor-immutable
     separation are explicit premises.  Incompatible layouts additionally
     require source/destination geometry and metadata consistency.
   - ret_pc_ok_frame and return_buf_frame_frame transport conditional caller
     resources using old-variable preservation, compile-frontier monotonicity
     and (for the buffer) allocation-frontier monotonicity.  Neither requires
     an internal return-PC equality.
   The body adapter below validates the zero-low-water value-window clause,
   not the entire stage_producer.  In particular arbitrary prot/reserved and
   the post local-region authorization need a separate preservation argument.
   The stage tower's local completed-transport, compiler-tag and incompatible
   geometry lemmas have not been copied or used here. *)

Definition stage_resources_def:
  stage_resources ctx func cx lo prot staged reserved morig oorig rb
      ce env es sa s <=>
    stmt_state_rel ctx func ce cx es s /\
    expr_sim_inv ce cx env es /\ locals_alloc_ok ce env /\
    local_ptrs_reserved ce sa /\ allocas_above lo s /\
    (!a k. prot a k ==>
      mem_bytes_at a k s.vs_memory = mem_bytes_at a k morig.vs_memory) /\
    (!op. reserved op ==> eval_operand op s = eval_operand op oorig) /\
    (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) /\
    (!n p k. local_region ce es.scopes s n p k ==>
      lo <= p \/ ?b z. staged b z /\ b <= p /\ p + k <= b + z) /\
    ret_pc_ok ce sa s /\ return_buf_frame rb ce sa s /\
    (!bw cap. rb = SOME (bw,cap) /\ ce.ce_is_ctor ==>
      !nm tv iv io.
        FLOOKUP ce.ce_module_vars (ce.ce_module,nm) = SOME (ImmutableLoc io) /\
        FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
                   NONE => FEMPTY
                 | SOME imms => get_source_immutables ce.ce_module imms) nm =
          SOME (tv,iv) ==>
        regions_disjoint io (type_memory_size tv) (w2n bw) cap)
End

Definition stage_cont_def:
  stage_cont ctx func cx lo prot staged reserved morig oorig rb
      ce env es sa s ee sb u <=>
    stage_resources ctx func cx lo prot staged reserved morig oorig rb
      ce env ee sb u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    s.vs_alloca_next <= u.vs_alloca_next /\ wb_frame ce es ee sa s u
End

Definition stage_producer_def:
  stage_producer tops ctx func cx lo prot staged reserved morig oorig rb e <=>
    !ce env es sa sb s ty vv.
      body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
      compile_expr ce ty e sa = (vv,sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
      stage_resources ctx func cx lo prot staged reserved morig oorig rb
        ce env es sa s /\ ~s.vs_halted /\
      s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s)
        (\res ee u. ?tv. res = INL tv /\
          vv_holds ce cx (post_value_type ce e) tv vv ee u /\
          vv_at ce cx (post_value_type ce e) sa sb ee tv vv u /\
          (post_value_type ce e <> expr_type e ==>
            vv_own ce cx (post_value_type ce e) sa sb ee tv vv u) /\
          (~expr_has_effect e ==> vv_storage_live cx vv ee u) /\
          (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
          (post_value_type ce e <> NoneT /\
           ~is_word_type (post_value_type ce e) /\
           ~is_bytestring_type (post_value_type ce e) /\
           (case vv of StackValue _ _ => T
                     | LocatedValue _ p => p.ptr_location = LocMemory) ==>
           !tv'. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv' ==>
             ?w a k. eval_operand (vv_operand vv) u = SOME w /\
               a <= w2n w /\ w2n w + type_memory_size tv' <= a + k /\
               a + k < dimword (:256) /\
               (lo <= a \/ ?b z. staged b z /\ b <= a /\ a + k <= b + z)) /\
          (~expr_has_effect e ==> pure_frame ce func es sa s u) /\
          stage_cont ctx func cx lo prot staged reserved morig oorig rb
            ce env es sa s ee sb u)
        (\res ee r. expr_exit res r)
End

Theorem stage_cont_refl:
  stage_resources ctx func cx lo prot staged reserved morig oorig rb
    ce env es sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  stage_cont ctx func cx lo prot staged reserved morig oorig rb
    ce env es sa s es sa s
Proof
  simp[stage_cont_def, wb_frame_refl]
QED

Theorem stage_cont_trans:
  stage_resources ctx func cx lo prot staged reserved morig oorig rb
    ce env es sa s /\
  stage_cont ctx func cx lo prot staged reserved morig oorig rb
    ce env es sa s em sm t /\
  stage_cont ctx func cx lo prot staged reserved morig oorig rb
    ce env em sm t ee sb u /\
  MAP FDOM es.scopes = MAP FDOM em.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id ==>
  stage_cont ctx func cx lo prot staged reserved morig oorig rb
    ce env es sa s ee sb u
Proof
  simp[stage_cont_def] >> rpt strip_tac >> simp[] >>
  fs[stage_resources_def] >> drule_all wb_frame_trans >> simp[]
QED

(* Positive-size memory values need only the allocation and local windows;
   no return address or internal-call graph occurs in this boundary. *)
Theorem stage_positive_value_window:
  vv_at ce cx ty sa sb es r vv s /\
  read_result cx r es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ~is_word_type ty /\ 0 < type_memory_size tv /\
  val_footprint tv v = type_memory_size tv /\
  (!aid a k. FLOOKUP s.vs_allocas aid = SOME (a,k) ==>
    a + k < dimword (:256) /\ lo <= a) /\
  (!n a k. local_region ce es.scopes s n a k ==>
    a + k < dimword (:256) /\
    (lo <= a \/ ?b z. staged b z /\ b <= a /\ a + k <= b + z)) /\
  (case vv of StackValue _ _ => T
            | LocatedValue _ p => p.ptr_location = LocMemory) ==>
  ?w a k. eval_operand (vv_operand vv) s = SOME w /\
    a <= w2n w /\ w2n w + type_memory_size tv <= a + k /\
    a + k < dimword (:256) /\
    (lo <= a \/ ?b z. staged b z /\ b <= a /\ a + k <= b + z)
Proof
  Cases_on `vv` >>
  simp[loweringPostsTheory.vv_at_def, loweringPostsTheory.expr_val_at_def,
       contextTheory.vv_operand_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem stage_resources_initial:
  stmt_state_rel ctx func ce cx es s /\ expr_sim_inv ce cx env es /\
  locals_alloc_ok ce env /\ local_ptrs_reserved ce sa /\
  ret_pc_ok ce sa s /\ ce.ce_return_buf = NONE ==>
  stage_resources ctx func cx 0 (\a k. F) (\b z. F) (\op. F) s s NONE
    ce env es sa s
Proof
  simp[stage_resources_def, intCallFrameTheory.allocas_above_def,
       loweringPostsTheory.return_buf_frame_def]
QED

(* The zero low-water mark is a genuine caller-general instance: ordinary
   vv_post suffices, including dynamic values and zero-sized aggregates. *)
Theorem stage_memory_window_zero:
  stmt_state_rel ctx func ce cx es s /\
  vv_holds ce cx ty r vv es s /\ vv_at ce cx ty sa sb es r vv s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  (case vv of StackValue _ _ => T
            | LocatedValue _ p => p.ptr_location = LocMemory) ==>
  ?w a k. eval_operand (vv_operand vv) s = SOME w /\
    a <= w2n w /\ w2n w + type_memory_size tv <= a + k /\
    a + k < dimword (:256) /\ 0 <= a
Proof
  strip_tac >> drule attribute_vv_holds_read_operand >> strip_tac >>
  Cases_on `type_memory_size tv = 0`
  >- (qexistsl [`w`, `w2n w`, `0`] >> simp[wordsTheory.w2n_lt]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[exprLoweringPropsTheory.stmt_state_rel_def,
        exprLoweringPropsTheory.alloca_room_def] >> decide_tac) >>
  `!aid a k. FLOOKUP s.vs_allocas aid = SOME (a,k) ==>
     a + k < dimword (:256) /\ 0 <= a` by
    (rpt strip_tac >>
     `a + k <= s.vs_alloca_next` by
       (fs[exprLoweringPropsTheory.stmt_state_rel_def,
           venomMemDefsTheory.alloca_inv_def,
           venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
     decide_tac) >>
  `!n a k. local_region ce es.scopes s n a k ==>
     a + k < dimword (:256)` by
    (rpt strip_tac >> drule_all body_local_region_frontier >> decide_tac) >>
  drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`) stage_positive_value_window >>
  disch_then (qspecl_then [`v`, `tv`, `\b z. F`, `0`] mp_tac) >>
  simp[] >> disch_then irule >> simp[evaluated_nonbytes_footprint] >>
  metis_tac[evaluated_nonbytes_footprint]
QED

(* Representative body-simulation instantiation of the producer's difficult
   memory-window clause.  The resource-preservation adapter is separate:
   this lemma does not pretend that ordinary vv_post preserves arbitrary
   protected windows or arbitrary reserved operands. *)
Theorem body_stage_window_outcome:
  body_expr_ok cx e /\ body_inv tops ctx ce cx /\
  expr_body_pre ce cx env e es /\
  compile_expr ce ty e sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s)
    (\res ee u. ?r. res = INL r /\
      vv_post ctx func ce cx e es sa sb s ee r vv u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (~is_word_type (post_value_type ce e) /\
       ~is_bytestring_type (post_value_type ce e) /\
       (case vv of StackValue _ _ => T
                 | LocatedValue _ p => p.ptr_location = LocMemory) ==>
       !tv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv ==>
         ?w a k. eval_operand (vv_operand vv) u = SOME w /\
           a <= w2n w /\ w2n w + type_memory_size tv <= a + k /\
           a + k < dimword (:256) /\ 0 <= a))
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `expr_vv_sim ctx func ce cx ty e es` by
    (fs[Once body_expr_ok_def] >> metis_tac[]) >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_def] >> disch_then drule_all >> strip_tac >>
  irule gas_outcome_post_mono >> goal_assum (drule_at Any) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  rpt strip_tac >> fs[vv_post_def] >>
  drule_all stage_memory_window_zero >> simp[arithmeticTheory.ADD_COMM]
QED
