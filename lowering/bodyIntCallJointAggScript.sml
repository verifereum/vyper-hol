(* Seam 2 joint induction step: aggregate constructors and memory subplaces. *)
Theory bodyIntCallJointAgg
Ancestors
  bodyIntCallJointContract loweringPosts exprSimWordArgs
  compileEnv stmtSimProps bodyMemoryDefs freshWrites
  placeMemoryCopyEffect exprSimCopy bodyIntCallCopySharpDynamic
  venomState intCallFrame context emitHelper emitHelperProps
  exprLoweringProps venomExecSemantics venomInst venomMemProps
  bodyIntCallStorePost bodyIntCallProtectedAlloc exprSimAlloc
  placeMemoryPrimitiveForward instIdxIndep exprSimProps exprSimUnwrap
  exprSimAggregateChildren

(* The continuation uses the standard write-back frame, so its composition
   and old-allocation interface are shared with other expression proofs. *)
Theorem intcall_expr_cont_frame:
  intcall_expr_cont fp ce env es sa s ee sb u <=>
  intcall_joint_res fp ce env ee sb u /\ ~u.vs_halted /\
  u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  wb_frame ce es sa s u
Proof
  simp[intcall_expr_cont_def, wb_frame_def] >> metis_tac[]
QED

Theorem intcall_expr_cont_trans:
  intcall_joint_res fp ce env es sa s /\
  intcall_expr_cont fp ce env es sa s em sm t /\
  intcall_expr_cont fp ce env em sm t ee sb u /\
  MAP FDOM es.scopes = MAP FDOM em.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id ==>
  intcall_expr_cont fp ce env es sa s ee sb u
Proof
  simp[intcall_expr_cont_frame] >> rpt strip_tac >>
  `wb_frame ce es sa s u` by
    (irule wb_frame_trans >>
     gvs[intcall_joint_res_def] >> metis_tac[]) >>
  simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* Transport the fixed-source resources across an operational suffix.  The
   state relation is supplied at that suffix's actual counted endpoint. *)
Theorem intcall_joint_res_frame:
  intcall_frame_ok fp /\
  intcall_joint_res fp ce env es sa s /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  sa.cs_next_var <= sb.cs_next_var /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  allocas_above fp.jc_lo u /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
         lookup_var x u = SOME w) /\
  (!a k. fp.jc_prot a k ==>
     mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op s) /\
  (!n b k. local_region ce es.scopes u n b k ==>
           local_region ce es.scopes s n b k) ==>
  intcall_joint_res fp ce env es sb u
Proof
  rpt strip_tac >>
  `local_ptrs_reserved ce sb` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     gvs[intcall_joint_res_def] >> metis_tac[]) >>
  `ret_pc_ok ce sb u` by
    (irule ret_pc_ok_frame >>
     gvs[intcall_joint_res_def] >> metis_tac[]) >>
  `return_buf_frame fp.jc_rb ce sb u` by
    (irule return_buf_frame_frame >>
     gvs[intcall_joint_res_def] >> metis_tac[]) >>
  `fp.jc_reserved fp.jc_rpc` by
    fs[intcall_frame_ok_def] >>
  gvs[intcall_joint_res_def] >>
  conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >>
      qexists_tac `sa` >> simp[]) >>
  conj_tac
  >- metis_tac[] >>
  gvs[]
QED

(* A store effect carries resources at its own operational endpoint. *)
Theorem intcall_joint_res_copy:
  intcall_frame_ok fp /\
  intcall_joint_res fp ce env es sa s /\
  typed_copy_effect fp.jc_ctx fp.jc_func sa sb s u dst len /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  sa.cs_next_var <= sb.cs_next_var /\
  (!a k. fp.jc_prot a k ==> regions_disjoint a k dst len) ==>
  intcall_joint_res fp ce env es sb u
Proof
  rpt strip_tac >>
  `local_ptrs_reserved ce sa` by fs[intcall_joint_res_def] >>
  `!n b k. local_region ce es.scopes u n b k <=>
           local_region ce es.scopes s n b k` by
    (irule copy_buffer_local_region_frame >>
     qexists_tac `sa` >> fs[typed_copy_effect_def]) >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    (drule typed_copy_effect_record >>
     simp[venom_state_component_equality]) >>
  `allocas_above fp.jc_lo u` by
    (fs[intcall_joint_res_def, allocas_above_def, typed_copy_effect_def] >>
     metis_tac[]) >>
  irule intcall_joint_res_frame >> simp[] >>
  qexistsl_tac [`s`, `sa`] >> simp[] >>
  conj_tac
  >- (fs[typed_copy_effect_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule typed_copy_effect_bytes >>
      goal_assum (drule_at Any) >> fs[regions_disjoint_def]) >>
  rpt strip_tac >> irule typed_copy_effect_operand_preserved >>
  goal_assum (drule_at Any) >> fs[intcall_joint_res_def] >> metis_tac[]
QED

(* Allocation fields do not require fresh_vars_wrt: ALLOCA overwrites only
   its own output even when stale temporary variables remain in the state. *)
Theorem intcall_alloc_run_frame:
  compile_alloc_buffer sz sa = (buf,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  (u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
            vs_alloca_next := s.vs_alloca_next|>) = s /\
  s.vs_alloca_next <= u.vs_alloca_next
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >>
  gvs[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, run_inst_seq_def,
      step_inst_base_def, mk_inst_def] >>
  conj_tac
  >- (gvs[exec_alloca_def, AllCaseEqs(), update_var_def,
          venom_state_component_equality]) >>
  gvs[AllCaseEqs()] >> drule exec_alloca_alloca_next_mono >> simp[]
QED

(* Store into a root allocated since the expression began.  The existing
   owned-memory tail theorem supplies the old-allocation byte frame. *)
Theorem intcall_expr_cont_copy:
  intcall_expr_cont fp ce env es0 sa s0 es si s /\
  typed_copy_effect fp.jc_ctx fp.jc_func si sb s u dst len /\
  intcall_joint_res fp ce env es sb u /\
  alloca_inv s /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid /\
  sa.cs_next_var <= si.cs_next_var /\
  b <= dst /\ dst + len <= b + sz /\
  (!n lb lsz. local_region ce es0.scopes s0 n lb lsz ==>
             lb + lsz <= b \/ b + sz <= lb) ==>
  intcall_expr_cont fp ce env es0 sa s0 es sb u
Proof
  rpt strip_tac >>
  `typed_copy_effect fp.jc_ctx fp.jc_func si sb s u b sz` by
    (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> simp[]) >>
  `wb_frame ce es0 sa s0 u` by
    (irule wb_frame_owned_memory_tail >> goal_assum (drule_at Any) >>
     qexistsl_tac [`aid`, `s`, `si`] >>
     fs[intcall_expr_cont_frame, typed_copy_effect_def] >> metis_tac[]) >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    (drule typed_copy_effect_record >>
     simp[venom_state_component_equality]) >>
  fs[intcall_expr_cont_frame, typed_copy_effect_def]
QED

(* Project the resource invariant onto the supplied allocation run. *)
Theorem intcall_joint_res_alloc:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  compile_alloc_buffer sz sa = (buf,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  sz < dimword (:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  intcall_joint_res fp ce env es sb u
Proof
  rpt strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa /\ allocas_above fp.jc_lo s` by
    fs[intcall_joint_res_def] >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  gvs[] >> rename1 `run_inst_seq _ s = OK u` >>
  drule_all intcall_alloc_run_frame >> strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
         comp_return_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
         emit_def]) >>
  `allocas_above fp.jc_lo u` by
    (drule_all alloc_buffer_allocas_above >> simp[]) >>
  `!n b k. local_region ce es.scopes u n b k <=>
           local_region ce es.scopes s n b k` by
    (irule copy_buffer_local_region_frame >> qexists_tac `sa` >> simp[]) >>
  `u.vs_labels = s.vs_labels` by fs[venom_state_component_equality] >>
  irule intcall_joint_res_frame >> simp[] >>
  qexistsl_tac [`s`, `sa`] >> simp[] >>
  rpt strip_tac >> Cases_on `op` >>
  gvs[eval_operand_def, lookup_var_def, intcall_joint_res_def] >> metis_tac[]
QED

Theorem intcall_joint_res_inst_idx[simp]:
  intcall_joint_res fp ce env es sa (s with vs_inst_idx := n) <=>
  intcall_joint_res fp ce env es sa s
Proof
  Cases_on `fp.jc_rb` >>
  simp[intcall_joint_res_def, exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       allocas_above_def, eval_operand_def, lookup_var_def,
       local_region_def, ret_pc_ok_def, return_buf_frame_def] >>
  rename1 `fp.jc_rb = SOME rb` >> Cases_on `rb` >>
  simp[return_buf_frame_def, lookup_var_def]
QED

(* Allocate at the actual counted endpoint, keeping the joint resources. *)
Theorem intcall_alloc_landing:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  compile_alloc_buffer sz sa = (buf,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  sz < dimword (:256) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es sa s es sb u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\ u.vs_memory = s.vs_memory /\
    sa.cs_next_id < sb.cs_next_id /\
    (!name b len. local_region ce es.scopes u name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sb p)
Proof
  rpt strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa` by fs[intcall_joint_res_def] >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq _ s = OK t` >>
  drule_all intcall_joint_res_alloc >> strip_tac >>
  drule_all intcall_alloc_run_frame >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >>
     gvs[fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def, emitted_insts_def,
         rich_listTheory.DROP_APPEND, mk_inst_def, is_terminator_def]) >>
  drule_all straight_line_zero_gas_path >> strip_tac >>
  `~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb` by
    fs[venom_state_component_equality] >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `w`] >>
  simp[intcall_expr_cont_frame, eval_op_inst_idx, local_region_def,
       lookup_var_def, wb_frame_def, locals_kept_def] >>
  fs[local_region_def, lookup_var_def] >> metis_tac[]
QED

(* A non-writing reader suffix changes only temporaries and control. *)
Theorem intcall_expr_cont_readonly:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es0 sa s0 es si s /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  sa.cs_next_var <= si.cs_next_var /\ si.cs_next_var <= sb.cs_next_var /\
  (u with <|vs_vars := s.vs_vars; vs_prev_bb := s.vs_prev_bb;
            vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at si x ==> lookup_var x u = lookup_var x s) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  intcall_expr_cont fp ce env es0 sa s0 es sb u
Proof
  rpt strip_tac >>
  `intcall_joint_res fp ce env es si s /\ wb_frame ce es0 sa s0 s` by
    fs[intcall_expr_cont_frame] >>
  `local_ptrs_reserved ce si` by fs[intcall_joint_res_def] >>
  `!n b k. local_region ce es.scopes u n b k <=>
           local_region ce es.scopes s n b k` by
    (irule copy_buffer_local_region_frame >> qexists_tac `si` >> simp[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\ u.vs_labels = s.vs_labels` by
    fs[venom_state_component_equality] >>
  `allocas_above fp.jc_lo u` by
    (fs[intcall_joint_res_def, allocas_above_def] >> metis_tac[]) >>
  `intcall_joint_res fp ce env es sb u` by
    (irule intcall_joint_res_frame >> simp[] >>
     qexistsl_tac [`s`, `si`] >> simp[] >>
     rpt strip_tac >> Cases_on `op` >>
     gvs[intcall_joint_res_def, eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  `wb_frame ce es0 sa s0 u` by
    (irule wb_frame_readonly_tail >>
     qexistsl_tac [`si`, `s`] >> simp[]) >>
  fs[intcall_expr_cont_frame]
QED

Theorem intcall_map_producer_other:
  (!ty id. e <> TopLevelName ty id) /\
  (!ty e1 e2. e <> Subscript ty e1 e2) ==>
  intcall_map_producer fp e
Proof
  rw[intcall_map_producer_def, exprSimMapDefsTheory.expr_map_pre_def] >>
  Cases_on `e` >> gvs[vyperTypeSystemTheory.well_typed_expr_def]
QED

(* ADD's run and resource landing are the same counted endpoint. *)
Theorem intcall_add_landing:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es0 sa s0 ee sm s /\
  sa.cs_next_var <= sm.cs_next_var /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  local_ptrs_reserved ce si /\ si.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
  fn_has_code sm sn fp.jc_func /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es si sm t0 ee tv vv s /\
  eval_operand buf s = SOME w ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es0 sa s0 ee sn u /\
    vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es si sn t0 ee tv vv u /\
    eval_operand dst u = SOME (w + n2w off) /\
    u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels /\
    (!x. dst = Var x ==> not_fresh_at sn x)
Proof
  rpt strip_tac >>
  drule_all buffer_emit_add_vv_post >> strip_tac >>
  rename1 `run_inst_seq _ s = OK q` >>
  `sn.cs_current_bb = sm.cs_current_bb /\
   sn.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sn /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sn) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sm sn) /\
   sm.cs_next_var <= sn.cs_next_var` by
    (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def, comp_ignore_bind_def,
          emitted_insts_def, rich_listTheory.DROP_APPEND, mk_inst_def,
          is_terminator_def] >> strip_tac >> gvs[] >>
     simp[rich_listTheory.DROP_APPEND, mk_inst_def, is_terminator_def]) >>
  `!x. dst = Var x ==> not_fresh_at sn x` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_fresh] >>
  `~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
   s.vs_inst_idx = LENGTH sm.cs_current_insts` by fs[intcall_expr_cont_def] >>
  drule_all straight_line_zero_gas_path >> strip_tac >>
  `q.vs_labels = s.vs_labels /\ q.vs_memory = s.vs_memory /\ ~q.vs_halted /\
   q.vs_current_bb = sn.cs_current_bb` by
    fs[venom_state_component_equality] >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee q` by fs[vv_post_def] >>
  qexists_tac `q with vs_inst_idx := LENGTH sn.cs_current_insts` >>
  simp[exprSimVVFrameTheory.vv_post_inst_idx, eval_op_inst_idx] >>
  irule intcall_expr_cont_readonly >>
  simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
  qexistsl_tac [`s`, `sm`] >>
  fs[venom_state_component_equality, lookup_var_def]
QED

(* Materialization uses the child's allocation frontier, even after ADD has
   advanced the variable frontier.  Win includes every old allocation. *)
Theorem intcall_unwrap_landing:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  unwrap_value ce vv sa = (op,sb) /\
  vv_holds ce fp.jc_cx ty r vv es s /\
  read_result fp.jc_cx r es = (INL v,es) /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (ty <> NoneT /\ ~is_word_type ty /\ ~is_bytestring_type ty /\
   (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
   ?w a k. eval_operand (vv_operand vv) s = SOME w /\
     a <= w2n w /\ w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
     (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z)) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es sa s es sb u /\
    expr_val_rel fp.jc_cx ty v op u /\
    (!sv. sv.cs_next_id <= sa.cs_next_id /\
      vv_at ce fp.jc_cx ty sv sa es r vv s ==>
      expr_val_at ce fp.jc_cx ty sv sb es v op u) /\
    (!sv. sv.cs_next_id <= sa.cs_next_id /\
      vv_own ce fp.jc_cx ty sv sa es r vv s ==>
      expr_val_own ce fp.jc_cx ty sv sb es v op u) /\
    (!aid b k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
      mem_bytes_at b k u.vs_memory = mem_bytes_at b k s.vs_memory)
Proof
  rpt strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa /\ allocas_above fp.jc_lo s` by
    fs[intcall_joint_res_def] >>
  drule (Q.INST
    [`reserved` |-> `fp.jc_reserved`, `P` |-> `fp.jc_prot`,
     `Win` |-> `\p k. ?aid. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,k)`,
     `scopes` |-> `es.scopes`, `staged` |-> `fp.jc_staged`]
    bodyIntCallWindowForcingTheory.protected_value_window_forcing) >>
  disch_then (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_above _ _`)) >>
  disch_then (qspecl_then [`tv`, `fp`] mp_tac) >>
  (impl_tac >-
    (simp[] >> conj_tac
     >- fs[intcall_frame_ok_def, intcall_joint_res_def] >>
     conj_tac >- (fs[intcall_frame_ok_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
     rpt strip_tac >> qexistsl_tac [`aid`, `p`, `k`] >> simp[arithmeticTheory.ADD_COMM])) >>
  strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qspec_then `ce` (qspec_then `vv` (qspec_then `sa` mp_tac)) ci_mono_unwrap_value >>
     simp[ci_mono_def]) >>
  `intcall_joint_res fp ce env es sb u` by
    (irule intcall_joint_res_frame >> simp[] >> qexistsl_tac [`s`, `sa`] >> simp[]) >>
  qexists_tac `u` >> simp[intcall_expr_cont_def] >> metis_tac[]
QED

(* Counted ADD followed by materialization, at the literal child's original
   allocation frontier.  This is uniform in word, memory and other locations. *)
Theorem intcall_add_unwrap_landing:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env ee sm s /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  local_ptrs_reserved ce si /\
  si.cs_next_var <= sm.cs_next_var /\ si.cs_next_id <= sm.cs_next_id /\
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  fn_has_code sm sn fp.jc_func /\ fn_has_code sn su fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es si sm t0 ee raw vv s /\
  read_result fp.jc_cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv /\
  type_memory_bytes ce (post_value_type ce e) = type_memory_size tv /\
  type_memory_size tv < 2**64 /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (post_value_type ce e <> NoneT /\ ~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e) /\
   (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
   ?w a k. eval_operand (vv_operand vv) s = SOME w /\
     a <= w2n w /\ w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
     (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z)) /\
  eval_operand buf s = SOME bw /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env ee sm s ee su u /\
    expr_val_rel fp.jc_cx (post_value_type ce e) v op u /\
    expr_val_at ce fp.jc_cx (post_value_type ce e) si su ee v op u /\
    (post_value_type ce e <> expr_type e ==>
      expr_val_own ce fp.jc_cx (post_value_type ce e) si su ee v op u) /\
    eval_operand dst u = SOME (bw + n2w off) /\
    (!x. dst = Var x ==> not_fresh_at su x) /\
    (!aid b k. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
      mem_bytes_at b k u.vs_memory = mem_bytes_at b k s.vs_memory)
Proof
  rpt strip_tac >>
  `intcall_expr_cont fp ce env ee sm s ee sm s` by
    simp[intcall_expr_cont_def] >>
  `sm.cs_next_var <= sm.cs_next_var` by simp[] >>
  drule_all intcall_add_landing >> strip_tac >>
  rename1 `intcall_expr_cont fp ce env ee sm s ee sn t` >>
  `sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `!w. eval_operand (vv_operand vv) s = SOME w ==>
       eval_operand (vv_operand vv) t = SOME w` by
    (Cases_on `vv_operand vv` >> fs[intcall_expr_cont_def, eval_operand_def] >>
     metis_tac[]) >>
  `intcall_joint_res fp ce env ee sn t /\ ~t.vs_halted /\
   t.vs_current_bb = sn.cs_current_bb /\
   t.vs_inst_idx = LENGTH sn.cs_current_insts /\
   vv_holds ce fp.jc_cx (post_value_type ce e) raw vv ee t` by
    fs[intcall_expr_cont_def, vv_post_def] >>
  drule_at (Pat `vv_holds _ _ _ _ _ _ _`) intcall_unwrap_landing >>
  disch_then (drule_at (Pat `intcall_joint_res _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (qspecl_then [`v`, `tv`] mp_tac) >>
  (impl_tac >-
    (simp[] >> strip_tac >>
     qpat_x_assum `_ ==> ?w a k. _` mp_tac >> simp[] >> strip_tac >>
     qexistsl_tac [`w`, `a`, `k`] >> simp[] >>
     disj2_tac >> qexistsl_tac [`b`, `z`] >> simp[])) >> strip_tac >>
  `intcall_expr_cont fp ce env ee sm s ee su u` by
    (irule intcall_expr_cont_trans >> simp[] >> qexistsl_tac [`ee`, `sn`, `t`] >> simp[]) >>
  `sn.cs_next_var <= su.cs_next_var` by
    (qspec_then `ce` (qspec_then `vv` (qspec_then `sn` mp_tac)) ci_mono_unwrap_value >>
     simp[ci_mono_def]) >>
  `eval_operand dst u = SOME (bw + n2w off)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     fs[intcall_expr_cont_def, eval_operand_def] >> metis_tac[]) >>
  qexists_tac `u` >> simp[] >> conj_tac
  >- (drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
  conj_tac
  >- (first_x_assum irule >> fs[vv_post_def]) >>
  conj_tac
  >- (strip_tac >> first_x_assum irule >> fs[vv_post_def]) >>
  conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sn` >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `t.vs_memory = _` SUBST_ALL_TAC >>
  qpat_x_assum `!aid b k. _ ==> mem_bytes_at _ _ u.vs_memory = _` irule >>
  fs[intcall_expr_cont_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

(* L-agg (C1.3.14.2.3), a step of the induction on expr_size: tuple
   literals (MakeArray NONE), array literals (MakeArray (SOME _)), struct
   literals, attributes and subscripts (every place_type case: tuple and
   struct literal-index, ValPT array, MapPT), given the producers of every
   smaller expression. *)
Theorem intcall_aggregate_producer_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  ((?a t n args. e = Builtin a (MakeArray t n) args) \/
   (?a nm fields. e = StructLit a nm fields) \/
   (?a base fld. e = Attribute a base fld) \/
   (?a base idx. e = Subscript a base idx)) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
