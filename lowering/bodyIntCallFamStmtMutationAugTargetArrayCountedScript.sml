(* Counted array target suffixes and constructor. *)
Theory bodyIntCallFamStmtMutationAugTargetArrayCounted
Ancestors
  bodyIntCallFamStmtMutationAugTargetArray bodyIntCallFamStmtMutationLoad
  bodyIntCallJointContract bodyIntCallJointAggCore targetSubscriptMemory targetSubscriptStorage
  context emitHelperProps exprLowering exprLoweringProps compileEnv venomInst pair
  gasSummaryCompose fragGasMode exprSimDefs loweringStateRelDefs
  vyperInterpreter vyperValue vyperTypeSystem loweringPosts vyperStorage
  exprSimHypsDefs

Theorem intcall_target_array_cont:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  compile_array_subscript base_op idx dyn cnt ws esz sgn
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc) sa = (dst,sb) /\
  (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient) /\
  fn_has_code sa sb fp.jc_func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. idx = Var x ==> not_fresh_at sa x) /\
  (!l. base_op <> Label l) /\ (!l. idx <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx s = SOME i /\
  idx_in_range sgn i (if dyn then
    (case loc of LocMemory => mload (w2n b) s
               | LocTransient => tload b s | _ => sload b s)
    else n2w cnt) ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      intcall_expr_cont fp ce env es sa s es sb u /\
      u.vs_memory = s.vs_memory /\
      eval_operand dst u = SOME ((if dyn then b + n2w ws else b) + i * n2w esz)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `local_ptrs_reserved ce sa /\ stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s`
    by fs[intcall_expr_res_def] >>
  `?t. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
       eval_operand dst t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
       stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es t /\
       (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==>
          lookup_var x t = SOME v) /\
       (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
       t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
       t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (qpat_x_assum `loc = _ \/ _` strip_assume_tac >> gvs[]
     >- (drule_all target_memory_array_path >> simp[])
     >- (drule_all (Q.INST [`tr` |-> `F`] target_storage_array_path
                 |> SIMP_RULE std_ss []) >> simp[]) >>
     drule_all (Q.INST [`tr` |-> `T`] target_storage_array_path
                 |> SIMP_RULE std_ss []) >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  irule bodyIntCallFamStmtMutationBinopTheory.intcall_expr_cont_readonly_path >>
  `ci_mono sa sb` by metis_tac[ci_mono_compile_array_subscript,
      ci_mono_compile_ptr_load, SND] >>
  fs[ci_mono_def] >>
  metis_tac[local_ptrs_reserved_next_var]
QED

Theorem intcall_target_memory_array_suffix:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sm s /\
  target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es0 sa sm s0 es
    (PlaceR (MemoryPlace id path))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  evaluate_type (get_tenv fp.jc_cx) (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)) =
    SOME (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  evaluate_type (get_tenv fp.jc_cx) ity = SOME itv /\ value_has_type itv (IntV i) /\
  eval_operand idx s = SOME (i2w i) /\
  compile_array_subscript (FST rb) idx dyn cnt 32 (type_memory_bytes ce ety)
    (is_signed_type ity)
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocMemory) sm = (dst,sb) /\
  fn_has_code sm sb fp.jc_func /\ sa.cs_next_var <= sm.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. idx = Var x ==> not_fresh_at sm x) /\
  (!l. idx <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. dst = Var x ==> not_fresh_at sb x) /\
  extend_place fp.jc_cx (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i)) es =
    (INL pv',es') ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es0 sa sb s0 es' pv' (Type ety)
        (dst,SOME LocMemory,SOME (ValPT ety)) u /\
      intcall_expr_cont fp ce env es sm s es' sb u
Proof
  strip_tac >>
  `expr_sim_inv ce fp.jc_cx env es /\ local_ptrs_reserved ce sm /\
   stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s` by
    fs[intcall_expr_res_def] >>
  `(?b. eval_operand (FST rb) s = SOME b /\
        place_ptr_rel ce fp.jc_cx s (PlaceR (MemoryPlace id path)) b
          (FST (SND rb)) (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)))) /\
   (!x. FST rb = Var x ==> not_fresh_at sm x)` by fs[target_post_def] >>
  drule_all place_ptr_rel_memory_current >> strip_tac >>
  drule_all extend_place_memory_array_index >>
  disch_then (qspecl_then [`i`, `fp.jc_cx`] assume_tac) >>
  `0 <= i /\ Num i < array_length (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) av /\
   es' = es` by gvs[AllCaseEqs()] >> gvs[] >>
  drule_all target_memory_array_range >> strip_tac >>
  `idx_in_range (is_signed_type ity) (i2w i)
     (if dyn then mload (w2n b) s else n2w cnt)` by metis_tac[] >>
  drule_at (Pat `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`)
    intcall_target_array_cont >> simp[] >>
  disch_then drule_all >> strip_tac >>
  drule_all target_memory_array_offset >>
  disch_then (qspec_then `b` strip_assume_tac) >>
  `eval_operand dst u = SOME (b + n2w k)` by metis_tac[] >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
   (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==> lookup_var x u = SOME w) /\
   (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP u.vs_allocas aid = SOME a)` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  drule_all target_post_memory_step >> strip_tac >>
  qexists_tac `u` >> simp[]
QED

Theorem intcall_target_storage_array_suffix:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sm s /\
  target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es0 sa sm s0 es
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  (dyn ==> w2n (lookup_storage slot (get_storage fp.jc_cx es tr)) <= cnt) /\
  storage_read_live fp.jc_cx tr (get_storage fp.jc_cx es tr) slot
    (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  w2n slot + type_slot_size (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) <= dimword(:256) /\
  evaluate_type (get_tenv fp.jc_cx) ity = SOME itv /\ value_has_type itv (IntV i) /\
  eval_operand idx s = SOME (i2w i) /\
  compile_array_subscript (FST rb) idx dyn cnt 1 (type_slot_size etv)
    (is_signed_type ity)
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca
      (if tr then LocTransient else LocStorage)) sm = (dst,sb) /\
  fn_has_code sm sb fp.jc_func /\ sa.cs_next_var <= sm.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. idx = Var x ==> not_fresh_at sm x) /\ (!l. idx <> Label l) /\
  (!l. FST rb <> Label l) /\ (!x. dst = Var x ==> not_fresh_at sb x) /\
  extend_place fp.jc_cx
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (ValueSubscript (IntV i)) es = (INL pv',es') ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es0 sa sb s0 es' pv' (Type ety)
        (dst,SOME (slot_loc tr),SOME (ValPT ety)) u /\
      intcall_expr_cont fp ce env es sm s es' sb u
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sm /\
   eval_operand (FST rb) s = SOME slot /\
   evaluate_type (get_tenv fp.jc_cx) (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)) =
     SOME (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
   (!x. FST rb = Var x ==> not_fresh_at sm x)` by
    fs[intcall_expr_res_def, target_post_def, place_ptr_rel_def] >>
  drule_all target_storage_array_live_range >> strip_tac >>
  qspecl_then [`fp.jc_cx`, `tr`, `slot`, `etv`,
    `if dyn then Dynamic cnt else Fixed cnt`, `i`, `es`]
    assume_tac extend_place_storage_array_index >>
  `0 <= i /\ es' = es /\
   pv' = PlaceR (StoragePlace tr
     (slot + n2w ((if dyn then 1 else 0) + Num i * type_slot_size etv)) etv) /\
   idx_in_range (is_signed_type ity) (i2w i)
     (if dyn then (if tr then tload slot s else sload slot s) else n2w cnt)` by
    (Cases_on `dyn` >> gvs[AllCaseEqs()]) >>
  gvs[] >>
  drule_at (Pat `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`)
    intcall_target_array_cont >>
  simp[] >> Cases_on `tr` >> fs[] >> disch_then drule_all >> strip_tac >>
  drule_all target_storage_array_type_bound >> strip_tac >>
  `eval_operand dst u = SOME
     (slot + n2w ((if dyn then 1 else 0) + Num i * type_slot_size etv))` by
    metis_tac[target_storage_array_offset] >>
  qexists_tac `u` >> simp[] >>
  irule (SRULE [value_type_place_def]
    (Q.INST [`vt'` |-> `Type ety`] target_post_suffix_frame)) >>
  gvs[place_ptr_rel_def, place_readable_def, value_type_place_def,
      intcall_expr_cont_def, intcall_expr_res_def] >>
  goal_assum (drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]
QED
