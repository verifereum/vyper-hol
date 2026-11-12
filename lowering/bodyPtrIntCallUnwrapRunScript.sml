Theory bodyPtrIntCallUnwrapRun
Ancestors
  bodyPtrIfExpAllocSource loweringPosts exprSimProps exprPtrUnwrapMarked
  bodyPtrDefs gasSummaryComposePtr logGhostFramePtr exprPtrUnwrapCode exprPtrUnwrapCodeCopyMarked
  exprPtrUnwrapStorage exprPtrUnwrapStorageMarked exprPtrUnwrapLoad
  exprSimPtrProps exprLowering emitHelper venomState finite_map exprSimMemorySource
  exprSimMemoryPath context bodyPtrIfExpNoopPost exprSimUnwrapProps
  exprSimUnwrap fragGasPathPtr compileEnv

(* A delayed operand retains its original allocation lower bound. *)
Theorem intcall_delayed_vv_post:
  post_value_type ce e = expr_type e /\
  stmt_state_rel ctx fn ce cx ee s /\
  vv_holds ce cx (expr_type e) raw vv ee s /\
  vv_at ce cx (expr_type e) si sm ee raw vv s /\
  vv_storage_live cx vv ee s /\ sm.cs_next_id <= sc.cs_next_id ==>
  vv_post ctx fn ce cx e ee si sc s ee raw vv s
Proof
  strip_tac >>
  `vv_at ce cx (expr_type e) si sc ee raw vv s` by
    (irule vv_at_alloc_map_frame >> qexistsl [`s`, `sm`] >> simp[]) >>
  simp[vv_post_def]
QED

(* External locations carry no allocation-interval obligation.  Their
   materialisation therefore starts its preservation frame at the cursor. *)
Theorem intcall_delayed_external_vv_post[local]:
  post_value_type ce e = expr_type e /\
  stmt_state_rel ctx fn ce cx ee s /\
  vv_holds ce cx (expr_type e) raw (LocatedValue t p) ee s /\
  vv_at ce cx (expr_type e) si sm ee raw (LocatedValue t p) s /\
  vv_storage_live cx (LocatedValue t p) ee s /\
  p.ptr_location <> LocMemory ==>
  vv_post ctx fn ce cx e ee sc sc s ee raw (LocatedValue t p) s
Proof
  simp[vv_post_def, vv_at_def] >> metis_tac[]
QED

Theorem intcall_delayed_external_unwrap:
  post_value_type ce e = expr_type e /\
  lowered_value_type ce e = expr_type e /\
  unwrap_value ce (LocatedValue t p) sc = (op,sb) /\
  p.ptr_location <> LocMemory /\
  stmt_state_rel ctx fn ce cx ee s /\
  vv_holds ce cx (expr_type e) raw (LocatedValue t p) ee s /\
  vv_at ce cx (expr_type e) si sm ee raw (LocatedValue t p) s /\
  vv_storage_live cx (LocatedValue t p) ee s /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue t p) ee G tn s /\
  local_ptrs_reserved ce sc /\ fn_has_code sc sb fn /\
  fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sc x) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!rt. evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
    ~is_word_type (expr_type e) ==>
    type_memory_bytes ce (expr_type e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ ghost_inv d ce cx ee G tn s ==>
  ?v H un q.
    gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG (read_result cx raw)
      (ee,s,G,tn) [] (INL v) ee H un (OK q) /\
    expr_post ctx fn ce cx e ee sc sb s ee v op q /\
    q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d ce cx ee H un q /\
    ptr_val_ok cx (expr_type e) v op H un q /\
    (~is_word_type (expr_type e) ==> ptr_buf_ok ce e op H q) /\
    ghost_kept ce ee sc G tn s H un
Proof
  strip_tac >>
  `vv_post ctx fn ce cx e ee sc sc s ee raw (LocatedValue t p) s` by
    (irule intcall_delayed_external_vv_post >> metis_tac[]) >>
  `t = expr_type e` by
    (drule vv_post_located_type >> simp[] >> metis_tac[]) >>
  `p.ptr_location <> LocCalldata` by metis_tac[vv_post_not_calldata] >>
  `ghost_kept ce ee sc G tn s G tn` by simp[ghost_kept_refl] >>
  Cases_on `p.ptr_location = LocCode`
  >- (Cases_on `is_word_type t`
      >- suspend "code_word"
      >> suspend "code_copy") >>
  `?tr. p.ptr_location = slot_loc tr` by
    (Cases_on `p.ptr_location` >> gvs[slot_loc_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  Cases_on `is_word_type t`
  >- suspend "slot_word"
  >> suspend "slot_copy"
QED

Resume intcall_delayed_external_unwrap[code_word]:
  qpat_assum `post_value_type ce e = expr_type e`
    (fn th => rewrite_tac[GSYM th]) >>
  irule unwrap_code_word_marked_read_ptr >> simp[] >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]
QED

Resume intcall_delayed_external_unwrap[code_copy]:
  `~is_word_type (expr_type e)` by metis_tac[] >> simp[] >>
  irule unwrap_code_marked_read_ptr >> simp[] >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]
QED

Resume intcall_delayed_external_unwrap[slot_word]:
  qpat_assum `post_value_type ce e = expr_type e`
    (fn th => rewrite_tac[GSYM th]) >>
  irule unwrap_storage_word_marked_read_ptr >> simp[] >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexists `tr` >> simp[]
QED

Resume intcall_delayed_external_unwrap[slot_copy]:
  `~is_word_type (expr_type e)` by metis_tac[] >> simp[] >>
  `?w. eval_operand p.ptr_operand s = SOME w /\
       storage_holds cx tr (expr_type e) raw w ee s /\
       op_taint tn p.ptr_operand = {}` by
    (Cases_on `tr` >>
     fs[vv_holds_def, ptr_vv_ok_def, slot_loc_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  irule unwrap_storage_marked_read_ptr >> simp[] >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `storage_holds _ _ _ _ _ _ _`)) >> simp[]
QED

Finalise intcall_delayed_external_unwrap

(* A memory word uses its original ownership witness, but the load preserves
   every byte, not merely the bytes outside allocations since that witness. *)
Theorem intcall_delayed_memory_word_unwrap[local]:
  unwrap_value ce (LocatedValue t p) sc = (op,sb) /\
  p.ptr_location = LocMemory /\ is_word_type t /\
  vv_post ctx fn ce cx e ee si sc s ee raw (LocatedValue t p) s /\
  local_ptrs_reserved ce si /\ si.cs_next_var <= sc.cs_next_var /\
  fn_has_code sc sb fn /\ ~ctx_has_dalloca ctx /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  ghost_inv d ce cx ee G tn s /\
  ptr_vv_ok cx (post_value_type ce e) raw (LocatedValue t p) ee G tn s /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty /\
  (!v. read_result cx raw ee = (INL v,ee) ==> value_has_type rty v) ==>
  ?v H un q.
    gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 H un (OK q) /\
    read_result cx raw ee = (INL v,ee) /\
    expr_post ctx fn ce cx e ee si sb s ee v op q /\
    q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d ce cx ee H un q /\
    ptr_val_ok cx (post_value_type ce e) v op H un q /\
    ghost_kept ce ee sc G tn s H un /\ pure_frame ce fn ee sc s q /\
    (!x w. not_fresh_at sc x /\ lookup_var x s = SOME w ==>
      lookup_var x q = SOME w) /\
    (!aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
      FLOOKUP q.vs_allocas aid = SOME site)
Proof
  strip_tac >> drule_all unwrap_memory_word_input >> strip_tac >>
  `emit_op MLOAD [Var src] sc = (op,sb)` by
    gvs[unwrap_value_def, contextTheory.compile_ptr_load_def] >>
  drule_all emit_mload_ptr_path >>
  disch_then (qspecl_then [`cx_dead cx`, `PG`] strip_assume_tac) >>
  drule_all emit_mload_endpoint >> strip_tac >>
  `emit_op MLOAD [p.ptr_operand] sc = (op,sb)` by simp[] >>
  `eval_operand p.ptr_operand s = SOME w` by simp[] >>
  drule_all unwrap_mload_post >> strip_tac >>
  qabbrev_tac `q = update_var out (mload (w2n w) s) s
                    with vs_inst_idx := SUC s.vs_inst_idx` >>
  `local_ptrs_reserved ce sc` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists `si` >> simp[]) >>
  `ghost_inv d ce cx ee G' tn' q` by
    (irule ghost_inv_fresh_frame >>
     qexistsl [`G`, `ee`, `s`, `sc`, `tn`] >>
     simp[Abbr `q`, update_var_def] >> rpt strip_tac >>
     `x <> out` by metis_tac[] >>
     gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  qexistsl [`v`, `G'`, `tn'`, `q`] >>
  gvs[Abbr `q`, ptr_val_ok_def, pure_frame_def, update_var_def] >>
  rpt conj_tac
  >- (gvs[ghost_kept_def] >> metis_tac[]) >>
  rpt strip_tac >> `x <> out` by metis_tac[] >>
  simp[lookup_var_def, FLOOKUP_UPDATE]
QED

(* The execution cursor is independent of the interval witnessing the delayed
   value.  The output frame protects all values already present at sc. *)
Theorem intcall_delayed_unwrap_run:
  unwrap_value ce vv sc = (op,sb) /\
  post_value_type ce e = expr_type e /\ vv_type vv = expr_type e /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location <> LocMemory ==>
     lowered_value_type ce e = expr_type e) /\
  ~expr_has_effect e /\
  stmt_state_rel ctx fn ce cx ee s /\
  vv_holds ce cx (expr_type e) raw vv ee s /\
  vv_at ce cx (expr_type e) si sm ee raw vv s /\
  vv_storage_live cx vv ee s /\ sm.cs_next_id <= sc.cs_next_id /\
  local_ptrs_reserved ce si /\ si.cs_next_var <= sc.cs_next_var /\
  local_ptrs_reserved ce sc /\ fn_has_code sc sb fn /\
  fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sc x) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!rt. evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
    ~is_word_type (expr_type e) ==>
    type_memory_bytes ce (expr_type e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\
  read_result cx raw ee = (INL v,ee) /\ value_has_type rty v /\
  ptr_vv_ok cx (expr_type e) raw vv ee G tn s /\
  (!t op. vv = StackValue t op /\ ~is_word_type (expr_type e) ==>
     ptr_buf_ok ce e op G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok ce e p.ptr_operand G s) /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ ghost_inv d ce cx ee G tn s ==>
  ?H un q.
    gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 H un (OK q) /\
    q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx fn ce cx ee q /\
    expr_val_rel cx (expr_type e) v op q /\
    ghost_inv d ce cx ee H un q /\
    ptr_val_ok cx (expr_type e) v op H un q /\
    (~is_word_type (expr_type e) ==> ptr_buf_ok ce e op H q) /\
    ghost_kept ce ee sc G tn s H un /\ pure_frame ce fn ee sc s q /\
    (!x w. not_fresh_at sc x /\ lookup_var x s = SOME w ==>
      lookup_var x q = SOME w) /\
    (!aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
      FLOOKUP q.vs_allocas aid = SOME site)
Proof
  strip_tac >>
  `vv_post ctx fn ce cx e ee si sc s ee raw vv s` by
    (irule intcall_delayed_vv_post >> metis_tac[]) >>
  Cases_on `vv`
  >- suspend "stack" >>
  rename1 `LocatedValue t p` >>
  Cases_on `p.ptr_location = LocMemory`
  >- (Cases_on `is_word_type t`
      >- suspend "memory_word"
      >> suspend "memory_value") >>
  suspend "external"
QED

Resume intcall_delayed_unwrap_run[stack]:
  gvs[unwrap_value_def, comp_return_def, vv_operand_def] >>
  drule_all vv_post_read_result >> strip_tac >>
  drule expr_post_of_vv_post_stack >> strip_tac >>
  qexistsl [`G`, `tn`, `s`] >>
  simp[ghost_kept_refl, pure_frame_def] >>
  conj_tac >- (irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  gvs[ptr_vv_ok_def, expr_post_def]
QED

Resume intcall_delayed_unwrap_run[memory_word]:
  `ptr_vv_ok cx (post_value_type ce e) raw (LocatedValue t p) ee G tn s` by simp[] >>
  `evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty` by simp[] >>
  `!v. read_result cx raw ee = (INL v,ee) ==> value_has_type rty v` by simp[] >>
  drule_all intcall_delayed_memory_word_unwrap >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl [`H`, `un`, `q`] >> gvs[expr_post_def, vv_type_def]
QED

Resume intcall_delayed_unwrap_run[memory_value]:
  `~is_word_type (expr_type e)` by gvs[vv_type_def] >>
  gvs[unwrap_value_def, comp_return_def] >>
  drule_all vv_post_read_result >> strip_tac >>
  drule_all expr_post_of_vv_post_memory >> strip_tac >>
  `ptr_val_ok cx (expr_type e) v p.ptr_operand G tn s` by
    gvs[ptr_vv_ok_def, ptr_val_ok_def] >>
  qexistsl [`G`, `tn`, `s`] >>
  simp[ghost_kept_refl, pure_frame_def] >>
  conj_tac >- (irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  gvs[expr_post_def]
QED

Resume intcall_delayed_unwrap_run[external]:
  `lowered_value_type ce e = expr_type e` by metis_tac[] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sc x` by
    gvs[vv_operand_def] >>
  drule_all intcall_delayed_external_unwrap >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `v' = v` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_ptr_def] >> strip_tac >>
     first_x_assum (qspec_then `ee.gas_obs` mp_tac) >> simp[]) >>
  qexistsl [`H`, `un`, `q`] >>
  gvs[gas_marked_exec_ptr_def, expr_post_def]
QED

Finalise intcall_delayed_unwrap_run
