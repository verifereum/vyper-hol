(* Helpers for the seam 2 joint induction agg step and its family leaves. *)
Theory bodyIntCallJointAggCore
Ancestors
  bodyIntCallJointContract loweringPosts exprSimWordArgs
  compileEnv loweringStateRelDefs stmtSimProps bodyMemoryDefs freshWrites
  placeMemoryCopyEffect exprSimCopy bodyIntCallCopySharpDynamic
  venomState intCallFrame context emitHelper emitHelperProps
  exprLoweringProps venomExecSemantics venomInst venomMemProps
  bodyIntCallStorePost bodyIntCallProtectedAlloc exprSimAlloc
  placeMemoryPrimitiveForward instIdxIndep exprSimProps exprSimUnwrap
  exprSimAggregateChildren bodyIntCallAggregateStoreFrame
  bodyIntCallCompletedModes intCallStep exprSimSend
  bodyIntCallWidenedChildStore typedMemoryCopy exprSimSubscriptMap
  memoryLocalRhsProps

(* The continuation uses the standard write-back frame, so its composition
   and old-allocation interface are shared with other expression proofs. *)
Theorem intcall_expr_cont_frame:
  intcall_expr_cont fp ce env es sa s ee sb u <=>
  intcall_expr_res fp ce env ee sb u /\ ~u.vs_halted /\
  u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  wb_frame ce es ee sa s u
Proof
  simp[intcall_expr_cont_def, wb_frame_def] >> metis_tac[]
QED

Theorem intcall_expr_cont_trans:
  intcall_expr_res fp ce env es sa s /\
  intcall_expr_cont fp ce env es sa s em sm t /\
  intcall_expr_cont fp ce env em sm t ee sb u /\
  MAP FDOM es.scopes = MAP FDOM em.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id ==>
  intcall_expr_cont fp ce env es sa s ee sb u
Proof
  simp[intcall_expr_cont_frame] >> rpt strip_tac >>
  `wb_frame ce es ee sa s u` by
    (irule wb_frame_trans >>
     gvs[intcall_joint_res_def, intcall_expr_res_def] >> metis_tac[]) >>
  simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* Transport the fixed-source resources across an operational suffix.  The
   state relation is supplied at that suffix's actual counted endpoint. *)
Theorem intcall_joint_res_frame:
  intcall_frame_ok fp /\
  intcall_expr_res fp ce env es sa s /\
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
  intcall_expr_res fp ce env es sb u
Proof
  rpt strip_tac >>
  `local_ptrs_reserved ce sb` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     gvs[intcall_joint_res_def, intcall_expr_res_def] >> metis_tac[]) >>
  `ret_pc_ok ce sb u` by
    (irule ret_pc_ok_frame >>
     gvs[intcall_joint_res_def, intcall_expr_res_def] >> metis_tac[]) >>
  `return_buf_frame fp.jc_rb ce sb u` by
    (irule return_buf_frame_frame >>
     gvs[intcall_joint_res_def, intcall_expr_res_def] >> metis_tac[]) >>
  `fp.jc_reserved fp.jc_rpc` by
    fs[intcall_frame_ok_def] >>
  gvs[intcall_joint_res_def, intcall_expr_res_def] >>
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
  intcall_expr_res fp ce env es sa s /\
  typed_copy_effect fp.jc_ctx fp.jc_func sa sb s u dst len /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  sa.cs_next_var <= sb.cs_next_var /\
  (!a k. fp.jc_prot a k ==> regions_disjoint a k dst len) ==>
  intcall_expr_res fp ce env es sb u
Proof
  rpt strip_tac >>
  `local_ptrs_reserved ce sa` by fs[intcall_joint_res_def, intcall_expr_res_def] >>
  `!n b k. local_region ce es.scopes u n b k <=>
           local_region ce es.scopes s n b k` by
    (irule copy_buffer_local_region_frame >>
     qexists_tac `sa` >> fs[typed_copy_effect_def]) >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    (drule typed_copy_effect_record >>
     simp[venom_state_component_equality]) >>
  `allocas_above fp.jc_lo u` by
    (fs[intcall_joint_res_def, intcall_expr_res_def, allocas_above_def, typed_copy_effect_def] >>
     metis_tac[]) >>
  irule intcall_joint_res_frame >> simp[] >>
  qexistsl_tac [`s`, `sa`] >> simp[] >>
  conj_tac
  >- (fs[typed_copy_effect_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule typed_copy_effect_bytes >>
      goal_assum (drule_at Any) >> fs[regions_disjoint_def]) >>
  rpt strip_tac >> irule typed_copy_effect_operand_preserved >>
  goal_assum (drule_at Any) >> fs[intcall_joint_res_def, intcall_expr_res_def] >> metis_tac[]
QED

(* Compatible copies share the same counted effect interface as widened copies. *)
Theorem intcall_compatible_store_effect:
  compile_store_memory ce src dst dty sty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv dty = SOME dtv /\ evaluate_type tenv sty = SOME stv /\
  (dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) /\
  value_has_type dtv v /\ value_has_type stv v /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  (if is_word_type sty then sw = typed_val_to_w256 stv v
   else val_in_memory stv v (w2n sw) s.vs_memory) /\
  type_memory_size dtv + 64 < dimword (:256) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    regions_disjoint b sz (w2n dw) (type_memory_size dtv)) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) (w2n dw) (type_memory_size dtv)) ==>
  ?u. typed_copy_effect ctx func sa sb s u (w2n dw) (type_memory_size dtv) /\
    val_in_memory dtv v (w2n dw) u.vs_memory /\
    stmt_state_rel ctx func ce cx es u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST
    [`P` |-> `\b n. regions_disjoint b n (w2n dw) (type_memory_size dtv)`,
     `reserved` |-> `\op. F`]
    (SPEC_ALL protected_compatible_store_state_landing)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qexists_tac `u` >> simp[typed_copy_effect_def] >>
  fs[regions_disjoint_def]
QED

(* A subregion of an owned allocation is clear of constructor immutables. *)
Theorem intcall_owned_destination_immutable_clear:
  stmt_state_rel ctx func ce cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) /\
  b <= d /\ d + n <= b + k ==>
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) d n)
Proof
  rpt strip_tac >>
  `immutable_alloca_sep func ce cx es s` by fs[stmt_state_rel_def] >>
  drule_all owned_alloca_immutable_separation >>
  simp[regions_disjoint_def] >> decide_tac
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
  intcall_expr_res fp ce env es sb u /\
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
  `wb_frame ce es0 es sa s0 u` by
    (irule wb_frame_owned_memory_tail >> goal_assum (drule_at Any) >>
     qexistsl_tac [`aid`, `s`, `si`] >>
     fs[intcall_expr_cont_frame, typed_copy_effect_def] >> metis_tac[]) >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    (drule typed_copy_effect_record >>
     simp[venom_state_component_equality]) >>
  fs[intcall_expr_cont_frame, typed_copy_effect_def]
QED

(* Stores contained in a fresh root preserve the outer continuation. *)
Theorem intcall_owned_store_cont:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es0 sa s0 es si s /\
  typed_copy_effect fp.jc_ctx fp.jc_func si sb s u dst len /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  alloca_inv s /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid /\
  sa.cs_next_var <= si.cs_next_var /\ si.cs_next_var <= sb.cs_next_var /\
  fp.jc_lo <= b /\ b <= dst /\ dst + len <= b + sz /\
  (!n lb lsz. local_region ce es0.scopes s0 n lb lsz ==>
             lb + lsz <= b \/ b + sz <= lb) ==>
  intcall_expr_cont fp ce env es0 sa s0 es sb u
Proof
  rpt strip_tac >>
  `intcall_expr_res fp ce env es si s` by fs[intcall_expr_cont_def] >>
  `!a k. fp.jc_prot a k ==> regions_disjoint a k dst len` by
    (fs[intcall_frame_ok_def, regions_disjoint_def] >> rpt strip_tac >>
     disj1_tac >> qpat_x_assum `!a k. fp.jc_prot a k ==> _ <= fp.jc_lo` drule >>
     decide_tac) >>
  `intcall_expr_res fp ce env es sb u` by
    (drule_all intcall_joint_res_copy >> simp[]) >>
  drule_all intcall_expr_cont_copy >> simp[]
QED

(* Project the resource invariant onto the supplied allocation run. *)
Theorem intcall_joint_res_alloc:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  compile_alloc_buffer sz sa = (buf,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  sz < dimword (:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  intcall_expr_res fp ce env es sb u
Proof
  rpt strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa /\ allocas_above fp.jc_lo s` by
    fs[intcall_joint_res_def, intcall_expr_res_def] >>
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
  gvs[eval_operand_def, lookup_var_def, intcall_joint_res_def, intcall_expr_res_def] >> metis_tac[]
QED

Theorem intcall_joint_res_inst_idx[simp]:
  intcall_expr_res fp ce env es sa (s with vs_inst_idx := n) <=>
  intcall_expr_res fp ce env es sa s
Proof
  Cases_on `fp.jc_rb` >>
  simp[intcall_joint_res_def, intcall_expr_res_def, exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       allocas_above_def, eval_operand_def, lookup_var_def,
       local_region_def, ret_pc_ok_def, return_buf_frame_def] >>
  rename1 `fp.jc_rb = SOME rb` >> Cases_on `rb` >>
  simp[return_buf_frame_def, lookup_var_def]
QED

(* Allocate at the actual counted endpoint, keeping the joint resources. *)
Theorem intcall_alloc_landing:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
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
   local_ptrs_reserved ce sa` by fs[intcall_joint_res_def, intcall_expr_res_def] >>
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
       lookup_var_def, wb_frame_def, locals_kept_mem] >>
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
  `intcall_expr_res fp ce env es si s /\ wb_frame ce es0 es sa s0 s` by
    fs[intcall_expr_cont_frame] >>
  `local_ptrs_reserved ce si` by fs[intcall_joint_res_def, intcall_expr_res_def] >>
  `!n b k. local_region ce es.scopes u n b k <=>
           local_region ce es.scopes s n b k` by
    (irule copy_buffer_local_region_frame >> qexists_tac `si` >> simp[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\ u.vs_labels = s.vs_labels` by
    fs[venom_state_component_equality] >>
  `allocas_above fp.jc_lo u` by
    (fs[intcall_joint_res_def, intcall_expr_res_def, allocas_above_def] >> metis_tac[]) >>
  `intcall_expr_res fp ce env es sb u` by
    (irule intcall_joint_res_frame >> simp[] >>
     qexistsl_tac [`s`, `si`] >> simp[] >>
     rpt strip_tac >> Cases_on `op` >>
     gvs[intcall_joint_res_def, intcall_expr_res_def, eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  `wb_frame ce es0 es sa s0 u` by
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
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
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
    fs[intcall_joint_res_def, intcall_expr_res_def] >>
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
     >- fs[intcall_frame_ok_def, intcall_joint_res_def, intcall_expr_res_def] >>
     conj_tac >- (fs[intcall_frame_ok_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
     rpt strip_tac >> qexistsl_tac [`aid`, `p`, `k`] >> simp[arithmeticTheory.ADD_COMM])) >>
  strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qspec_then `ce` (qspec_then `vv` (qspec_then `sa` mp_tac)) ci_mono_unwrap_value >>
     simp[ci_mono_def]) >>
  `intcall_expr_res fp ce env es sb u` by
    (irule intcall_joint_res_frame >> simp[] >> qexistsl_tac [`s`, `sa`] >> simp[]) >>
  qexists_tac `u` >> simp[intcall_expr_cont_def] >> metis_tac[]
QED

(* Counted ADD followed by materialization, at the literal child's original
   allocation frontier.  This is uniform in word, memory and other locations. *)
Theorem intcall_add_unwrap_landing:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env ee sm s /\
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
  `intcall_expr_res fp ce env ee sn t /\ ~t.vs_halted /\
   t.vs_current_bb = sn.cs_current_bb /\
   t.vs_inst_idx = LENGTH sn.cs_current_insts /\
   vv_holds ce fp.jc_cx (post_value_type ce e) raw vv ee t` by
    fs[intcall_expr_cont_def, vv_post_def] >>
  drule_at (Pat `vv_holds _ _ _ _ _ _ _`) intcall_unwrap_landing >>
  disch_then (drule_at (Pat `intcall_expr_res _ _ _ _ _ _`)) >>
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

(* Identity materialization needs no allocation-size bound. *)
Theorem intcall_identity_unwrap_post:
  unwrap_value ce vv sa = (op,sb) /\
  ((?t q. vv = StackValue t q) \/
   (?t p. vv = LocatedValue t p /\ ~is_word_type t /\
          p.ptr_location = LocMemory)) /\
  vv_post ctx func ce cx e es si sa s0 ee raw vv s /\
  read_result cx raw ee = (INL v,ee) ==>
  sb = sa /\ expr_post ctx func ce cx e es si sa s0 ee v op s
Proof
  strip_tac >>
  `vv_post ctx func ce cx e es si sa s0 ee (Value v) vv s` by
    metis_tac[exprSimUnwrapPropsTheory.vv_post_read_result] >>
  gvs[exprLoweringTheory.unwrap_value_def, comp_return_def]
  >- (drule exprSimUnwrapTheory.expr_post_of_vv_post_stack >> simp[]) >>
  drule_all exprSimUnwrapPropsTheory.expr_post_of_vv_post_memory >> simp[]
QED

Theorem intcall_add_unwrap_landing_conditional:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env ee sm s /\
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
  (type_memory_size tv < 2**64 \/ (?t q. vv = StackValue t q) \/
   (?t p. vv = LocatedValue t p /\ ~is_word_type t /\
          p.ptr_location = LocMemory)) /\
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
  rpt gen_tac >> strip_tac >>
  Cases_on `type_memory_size tv < 2**64`
  >- (drule_all intcall_add_unwrap_landing >> simp[]) >>
  `intcall_expr_cont fp ce env ee sm s ee sm s` by
    simp[intcall_expr_cont_def] >>
  `sm.cs_next_var <= sm.cs_next_var` by simp[] >>
  drule_all intcall_add_landing >> strip_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) intcall_identity_unwrap_post >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> fs[expr_post_def]
QED

Theorem intcall_child_unwrap_condition:
  expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv ==>
  type_memory_size tv < 2**64 \/ (?t q. vv = StackValue t q) \/
  (?t p. vv = LocatedValue t p /\ ~is_word_type t /\
         p.ptr_location = LocMemory)
Proof
  rpt strip_tac >>
  Cases_on `is_word_type (post_value_type ce e)`
  >- (drule_all exprSimPropsTheory.word_tv_memory_size >> simp[]) >>
  Cases_on `post_value_type ce e = expr_type e`
  >- metis_tac[exprSimHypsTheory.expr_body_pre_copy_ok] >>
  `?ann fid args drv. e = Call ann (IntCall fid) args drv` by
    (Cases_on `e` >> gvs[post_value_type_def] >>
     rename1 `Call ann tgt args drv` >> Cases_on `tgt` >>
     gvs[post_value_type_def] >> metis_tac[]) >>
  gvs[post_value_type_def, exprLoweringTheory.lowered_value_type_def,
      exprSimSendTheory.compile_expr_call, vyperASTTheory.expr_type_def] >>
  Cases_on `is_word_type ann \/ is_bytestring_type ann` >> gvs[] >>
  Cases_on `ce.ce_func_info (nsid_to_string fid)` >>
  rename1 `ce.ce_func_info (nsid_to_string fid) = (nret,meta)` >> Cases_on `meta` >>
  drule_all intCallStepTheory.compile_call_intcall_shape >> strip_tac >>
  Cases_on `0 < nret` >> gvs[contextTheory.base_ptr_def] >>
  Cases_on `ce.ce_func_return_type (nsid_to_string fid) = NoneT` >> gvs[]
QED

(* An old root survives a child and remains clear of its live locals. *)
Theorem intcall_expr_cont_root:
  intcall_expr_res fp ce env es sa s /\
  intcall_expr_cont fp ce env es sa s ee sb u /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  FLOOKUP s.vs_allocas rid = SOME (b,k) /\ rid < sa.cs_next_id /\
  eval_operand buf s = SOME w /\ (!lbl. buf <> Label lbl) /\
  (!x. buf = Var x ==> not_fresh_at sa x) /\
  (!n a z. local_region ce es.scopes s n a z ==>
           regions_disjoint b k a z) ==>
  FLOOKUP u.vs_allocas rid = SOME (b,k) /\
  eval_operand buf u = SOME w /\
  mem_bytes_at b k u.vs_memory = mem_bytes_at b k s.vs_memory /\
  (!n a z. local_region ce ee.scopes u n a z ==>
           regions_disjoint b k a z)
Proof
  rpt strip_tac
  >- (fs[intcall_expr_cont_def] >> metis_tac[])
  >- (Cases_on `buf` >> fs[intcall_expr_cont_def, eval_operand_def] >> metis_tac[])
  >- (fs[intcall_expr_cont_def, regions_disjoint_def] >> metis_tac[]) >>
  `local_region ce es.scopes s n a z` by
    (irule exprSimPropsTheory.local_region_frame >> conj_tac
     >- (qexists_tac `fp.jc_func` >>
         fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sa`, `ee.scopes`, `u`] >>
     fs[intcall_joint_res_def, intcall_expr_res_def, intcall_expr_cont_def]) >>
  metis_tac[]
QED

(* Dispatch a materialized child store at its actual endpoint.  Root
   provenance supplies physical source separation and immutable clearance;
   neither is inferred from write-region authorization. *)
Theorem intcall_child_store_effect:
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_expr_res fp ce env es sa s /\
  compile_store_memory ce src dst dty sty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  expr_val_rel fp.jc_cx sty v src s /\
  expr_val_at ce fp.jc_cx sty si sa es v src s /\
  type_widens_to (get_tenv fp.jc_cx) sty dty /\
  evaluate_type (get_tenv fp.jc_cx) dty = SOME dtv /\
  evaluate_type (get_tenv fp.jc_cx) sty = SOME stv /\
  value_has_type dtv v /\ value_has_type stv v /\
  type_memory_size dtv + 64 < dimword (:256) /\
  eval_operand dst s = SOME dw /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) /\
  inst.inst_id < si.cs_next_id /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  b <= w2n dw /\ w2n dw + type_memory_size dtv <= b+k /\
  b+k < dimword (:256) /\
  (!name a n. local_region ce es.scopes s name a n ==>
     a+n <= w2n dw \/ w2n dw + type_memory_size dtv <= a) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. typed_copy_effect fp.jc_ctx fp.jc_func sa sb s u
        (w2n dw) (type_memory_size dtv) /\
      val_in_memory dtv v (w2n dw) u.vs_memory /\
      stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u
Proof
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa /\ expr_sim_inv ce fp.jc_cx env es` by
    fs[intcall_joint_res_def, intcall_expr_res_def] >>
  `!ty tv. evaluate_type (get_tenv fp.jc_cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_bytes ce dty = type_memory_size dtv /\
   type_memory_bytes ce sty = type_memory_size stv` by metis_tac[] >>
  `ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables fp.jc_cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) (w2n dw) (type_memory_size dtv)` by
    metis_tac[intcall_owned_destination_immutable_clear] >>
  fs[expr_val_rel_def] >>
  Cases_on `dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty`
  >- (`!name a n. local_region ce es.scopes s name a n ==>
         regions_disjoint a n (w2n dw) (type_memory_size dtv)` by
        (fs[regions_disjoint_def] >> metis_tac[]) >>
      drule_all intcall_compatible_store_effect >> simp[]) >>
  `~is_word_type dty /\ ~is_word_type sty /\
   ~is_bytestring_type dty /\ ~is_bytestring_type sty` by
    metis_tac[type_widens_to_word, return_source_word_widens_eq,
              typed_copy_bytestring_source, type_widens_from_bytestring] >>
  `w2n w + type_memory_size stv < dimword (:256) /\
   (w2n w + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n w)` by
    (irule aggregate_physical_source_slot_bounds >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `val_wf dtv v /\ val_wf stv v` by
    metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `compile_store_memory_typed ce dst dty src sty sa = ((),sb)` by
    fs[compile_store_memory_def] >>
  `acyclic_struct_metadata ce.ce_struct_fields /\
   sfields_tenv_consistent ce.ce_struct_fields (get_tenv fp.jc_cx) /\
   (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv fp.jc_cx) fty = SOME tv ==>
        sz = type_memory_size tv) fields)` by
    (fs[bodySimTheory.body_inv_def, exprSimHypsDefsTheory.expr_sim_inv_def] >>
     metis_tac[]) >>
  `val_in_memory stv v (w2n w) s.vs_memory /\
   w2n dw + type_memory_size dtv < dimword (:256)` by
    (fs[] >> decide_tac) >>
  drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)
    intcall_widened_child_store_frame >>
  disch_then (drule_at (Pat `eval_operand dst s = _`)) >>
  disch_then (drule_at (Pat `eval_operand src s = _`)) >>
  disch_then (drule_at (Pat `type_widens_to _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ sty = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

(* A materialized child writes only its slice of the literal root.  Its
   continuation is anchored before root allocation, not at child entry. *)
Theorem intcall_child_store_landing:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_expr_cont fp ce env es0 sa s0 es su s /\
  compile_store_memory ce src dst dty sty su = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at su x) /\
  (!x. dst = Var x ==> not_fresh_at su x) /\
  expr_val_rel fp.jc_cx sty v src s /\
  expr_val_at ce fp.jc_cx sty si su es v src s /\
  type_widens_to (get_tenv fp.jc_cx) sty dty /\
  evaluate_type (get_tenv fp.jc_cx) dty = SOME dtv /\
  evaluate_type (get_tenv fp.jc_cx) sty = SOME stv /\
  value_has_type dtv v /\ value_has_type stv v /\
  type_memory_size dtv + 64 < dimword (:256) /\
  eval_operand dst s = SOME dw /\ eval_operand buf s = SOME bw /\
  (!x. buf = Var x ==> not_fresh_at su x) /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) /\
  sa.cs_next_id <= inst.inst_id /\ inst.inst_id < si.cs_next_id /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  sa.cs_next_var <= su.cs_next_var /\ su.cs_next_var <= sb.cs_next_var /\
  fp.jc_lo <= b /\ b <= w2n dw /\
  w2n dw + type_memory_size dtv <= b+k /\ b+k < dimword (:256) /\
  (!name a n. local_region ce es.scopes s name a n ==>
     a+n <= w2n dw \/ w2n dw + type_memory_size dtv <= a) /\
  (!name a n. local_region ce es0.scopes s0 name a n ==>
     a+n <= b \/ b+k <= a) /\
  fn_has_code su sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    val_in_memory dtv v (w2n dw) u.vs_memory /\
    intcall_expr_cont fp ce env es0 sa s0 es sb u /\
    FLOOKUP u.vs_allocas inst.inst_id = SOME (b,k) /\
    eval_operand buf u = SOME bw /\
    (!a n. a+n <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
      mem_bytes_at a n u.vs_memory = mem_bytes_at a n s.vs_memory)
Proof
  rpt strip_tac >>
  `intcall_expr_res fp ce env es su s /\ ~s.vs_halted /\
   s.vs_current_bb = su.cs_current_bb /\
   s.vs_inst_idx = LENGTH su.cs_current_insts` by fs[intcall_expr_cont_def] >>
  drule_all intcall_child_store_effect >> strip_tac >>
  `alloca_inv s` by fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_def] >>
  `intcall_expr_cont fp ce env es0 sa s0 es sb u` by
    (irule intcall_owned_store_cont >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexists_tac `u` >> simp[] >>
  conj_tac >- metis_tac[typed_copy_effect_path] >>
  conj_tac >- fs[typed_copy_effect_def] >>
  conj_tac >- metis_tac[typed_copy_effect_operand_preserved] >>
  fs[typed_copy_effect_def] >> metis_tac[]
QED

(* A counted child supplies the semantic read and both runtime layouts.
   This boundary is independent of literal allocation and destination code. *)
Theorem intcall_child_read_layout:
  vv_post ctx func ce cx e es si sm t
    (mid with gas_obs := []) raw vv q /\
  gas_marked_exec F (ctx,func) (eval_expr cx e) (es,t) marks (INL raw) mid (OK q) /\
  expr_body_pre ce cx env e es /\ expr_sim_inv ce cx env es /\
  type_widens_to env.type_defs (expr_type e) dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME stv ==>
  ?v. (!tail. read_result cx raw (mid with gas_obs := tail) =
          (INL v,mid with gas_obs := tail)) /\
    value_has_type dtv v /\ value_has_type stv v /\
    MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  rpt strip_tac >>
  `?v. read_result cx raw (mid with gas_obs := []) =
       (INL v,mid with gas_obs := [])` by
    metis_tac[exprSimAggregateSourceTheory.vv_post_materialises] >>
  `!tail. read_result cx raw (mid with gas_obs := tail) =
       (INL v,mid with gas_obs := tail)` by
    (drule exprSimMemorySourceTheory.read_result_gas_obs >> simp[]) >>
  `vyperState$bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks t.vs_gas_readings) =
     (INL v,mid with gas_obs := [])` by
    (fs[gasSummaryTheory.gas_marked_exec_def] >>
     qpat_x_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[vyperStateTheory.bind_def]) >>
  `value_runtime_typed env (post_value_type ce e) v /\
   value_runtime_typed env dty v` by
    (fs[GSYM vyperStateTheory.bind_def] >>
     `expr_body_pre ce cx env e
       (es with gas_obs := gas_explicit marks t.vs_gas_readings)` by simp[] >>
     conj_tac
     >- metis_tac[exprSimHypsTheory.memory_rhs_read_post_typed] >>
     metis_tac[memoryLocalRhsPropsTheory.memory_rhs_read_destination_typed]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qspecl_then [`cx`, `e`,
       `es with gas_obs := gas_explicit marks t.vs_gas_readings`,
       `INL v`, `mid with gas_obs := []`] mp_tac
       exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom >>
     impl_tac
     >- (fs[gasSummaryTheory.gas_marked_exec_def] >>
         qpat_x_assum `!tail. eval_expr _ _ _ = _`
           (qspec_then `[]` mp_tac) >>
         simp[vyperStateTheory.bind_def]) >> simp[]) >>
  qexists_tac `v` >> simp[] >> conj_tac
  >- (qpat_assum `value_runtime_typed env dty v`
        (mp_then Any mp_tac memoryLocalRhsPropsTheory.memory_rhs_runtime_layout) >>
      disch_then drule_all >> strip_tac >> gvs[]) >>
  qpat_assum `value_runtime_typed env (post_value_type ce e) v`
    (mp_then Any mp_tac memoryLocalRhsPropsTheory.memory_rhs_runtime_layout) >>
  disch_then drule_all >> strip_tac >> gvs[]
QED

(* Materialization transports an old literal root and composes the outer
   continuation, without depending on the subsequent destination store. *)
Theorem intcall_child_materialize_root:
  intcall_frame_ok fp /\ expr_body_pre ce fp.jc_cx env e es /\
  intcall_expr_res fp ce env es0 s0c s0 /\
  intcall_expr_res fp ce env es si t /\
  intcall_expr_cont fp ce env es0 s0c s0 es si t /\
  intcall_expr_cont fp ce env es si t ee sm q /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  s0c.cs_next_var <= si.cs_next_var /\ s0c.cs_next_id <= si.cs_next_id /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  fn_has_code sm sn fp.jc_func /\ fn_has_code sn su fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es si sm t ee raw vv q /\
  read_result fp.jc_cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME stv /\
  FLOOKUP t.vs_allocas rid = SOME (b,k) /\ rid < si.cs_next_id /\
  eval_operand buf t = SOME bw /\ (!lbl. buf <> Label lbl) /\
  (!x. buf = Var x ==> not_fresh_at si x) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (post_value_type ce e <> NoneT /\ ~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e) /\
   (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
   !tv. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv ==>
   ?w a k. eval_operand (vv_operand vv) q = SOME w /\
     a <= w2n w /\ w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
     (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z)) /\
  (!name a n. local_region ce es.scopes t name a n ==> regions_disjoint b k a n) ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func q 0 (OK u) /\
    intcall_expr_cont fp ce env es0 s0c s0 ee su u /\
    expr_val_rel fp.jc_cx (post_value_type ce e) v op u /\
    expr_val_at ce fp.jc_cx (post_value_type ce e) si su ee v op u /\
    eval_operand dst u = SOME (bw + n2w off) /\
    (!x. dst = Var x ==> not_fresh_at su x) /\
    FLOOKUP u.vs_allocas rid = SOME (b,k) /\ eval_operand buf u = SOME bw /\
    mem_bytes_at b k u.vs_memory = mem_bytes_at b k t.vs_memory /\
    (!name a n. local_region ce ee.scopes u name a n ==> regions_disjoint b k a n)
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `intcall_expr_cont _ _ _ es si t ee sm q`)
    intcall_expr_cont_root >> disch_then drule_all >> strip_tac >>
  `si.cs_next_var <= sm.cs_next_var /\ si.cs_next_id <= sm.cs_next_id` by
    metis_tac[exprSimUnwrapTheory.compile_expr_extends] >>
  `local_ptrs_reserved ce si /\ intcall_expr_res fp ce env ee sm q /\
   ~q.vs_halted /\ q.vs_current_bb = sm.cs_current_bb /\
   q.vs_inst_idx = LENGTH sm.cs_current_insts` by
    (conj_tac >- fs[intcall_joint_res_def, intcall_expr_res_def] >> fs[intcall_expr_cont_def]) >>
  drule_all intcall_child_unwrap_condition >> disch_tac >>
  `type_memory_bytes ce (post_value_type ce e) = type_memory_size stv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size, intcall_joint_res_def, intcall_expr_res_def] >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    intcall_add_unwrap_landing_conditional >>
  disch_then (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  simp[] >> disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  `intcall_expr_cont fp ce env es si t ee su u` by
    (irule intcall_expr_cont_trans >> conj_tac >- simp[] >>
     qexistsl_tac [`ee`, `sm`, `q`] >> simp[]) >>
  drule_at (Pat `intcall_expr_cont _ _ _ es si t ee su u`)
    intcall_expr_cont_root >> disch_then drule_all >> strip_tac >>
  `intcall_expr_cont fp ce env es0 s0c s0 ee su u` by
    (irule intcall_expr_cont_trans >> conj_tac >- simp[] >>
     qexistsl_tac [`es`, `si`, `t`] >> simp[]) >>
  qexists_tac `u` >> simp[] >> gvs[]
QED

(* Static operand liveness for the literal child's interleaved suffix. *)
Theorem intcall_child_store_operands:
  compile_expr ce ty e si = (vv,sm) /\
  emit_op ADD args sm = (dst,sn) /\ unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst dty sty su = ((),sb) /\
  sa.cs_next_var <= si.cs_next_var /\
  (!x. buf = Var x ==> not_fresh_at si x) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) ==>
  sa.cs_next_var <= su.cs_next_var /\ su.cs_next_var <= sb.cs_next_var /\
  (!x. buf = Var x ==> not_fresh_at su x) /\
  (!x. op = Var x ==> not_fresh_at su x)
Proof
  rpt gen_tac >> strip_tac >>
  `si.cs_next_var <= sm.cs_next_var /\ si.cs_next_id <= sm.cs_next_id` by
    metis_tac[exprSimUnwrapTheory.compile_expr_extends] >>
  `sm.cs_next_var <= sn.cs_next_var` by
    (drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[]) >>
  `sn.cs_next_var <= su.cs_next_var /\ sn.cs_next_id <= su.cs_next_id` by
    (mp_tac (Q.SPECL [`ce`, `vv`, `sn`] ci_mono_unwrap_value) >> simp[ci_mono_def]) >>
  `su.cs_next_var <= sb.cs_next_var` by
    (mp_tac (Q.SPECL [`ce`, `op`, `dst`, `dty`, `sty`, `su`]
       ci_mono_compile_store_memory) >> simp[ci_mono_def]) >>
  `si.cs_next_var <= su.cs_next_var /\ sa.cs_next_var <= su.cs_next_var` by decide_tac >>
  `!x. buf = Var x ==> not_fresh_at su x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sn x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  simp[] >> drule exprOperandVarTheory.compiler_unwrap_value_var >>
  Cases_on `vv` >> fs[vv_operand_def]
QED

(* The owned root's untouched slices and separation survive a typed store. *)
Theorem intcall_root_store_landing:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  intcall_expr_res fp ce env es0 sa s0 /\
  intcall_expr_cont fp ce env es0 sa s0 es su s /\
  compile_store_memory ce src dst dty sty su = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at su x) /\
  (!x. dst = Var x ==> not_fresh_at su x) /\
  expr_val_rel fp.jc_cx sty v src s /\
  expr_val_at ce fp.jc_cx sty si su es v src s /\
  type_widens_to (get_tenv fp.jc_cx) sty dty /\
  evaluate_type (get_tenv fp.jc_cx) dty = SOME dtv /\
  evaluate_type (get_tenv fp.jc_cx) sty = SOME stv /\
  value_has_type dtv v /\ value_has_type stv v /\
  type_memory_size dtv + 64 < dimword (:256) /\
  eval_operand dst s = SOME dw /\ eval_operand buf s = SOME bw /\
  (!x. buf = Var x ==> not_fresh_at su x) /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) /\
  sa.cs_next_id <= inst.inst_id /\ inst.inst_id < si.cs_next_id /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  sa.cs_next_var <= su.cs_next_var /\ su.cs_next_var <= sb.cs_next_var /\
  fp.jc_lo <= b /\ b <= w2n dw /\
  w2n dw + type_memory_size dtv <= b+k /\ b+k < dimword (:256) /\
  (!name a n. local_region ce es.scopes s name a n ==> regions_disjoint b k a n) /\
  (!name a n. local_region ce es0.scopes s0 name a n ==> regions_disjoint b k a n) /\
  mem_bytes_at b k s.vs_memory = mem_bytes_at b k t.vs_memory /\
  fn_has_code su sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    val_in_memory dtv v (w2n dw) u.vs_memory /\
    intcall_expr_cont fp ce env es0 sa s0 es sb u /\
    FLOOKUP u.vs_allocas inst.inst_id = SOME (b,k) /\ eval_operand buf u = SOME bw /\
    (!name a n. local_region ce es.scopes u name a n ==> regions_disjoint b k a n) /\
    (!a n. b <= a /\ a+n <= b+k /\
       (a+n <= w2n dw \/ w2n dw + type_memory_size dtv <= a) ==>
       mem_bytes_at a n u.vs_memory = mem_bytes_at a n t.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  `!name a n. local_region ce es.scopes s name a n ==>
     a+n <= w2n dw \/ w2n dw + type_memory_size dtv <= a` by
    (rpt strip_tac >>
     qpat_x_assum `!n a z. local_region ce _ s n a z ==> _` drule >>
     fs[regions_disjoint_def] >> decide_tac) >>
  `!name a n. local_region ce es0.scopes s0 name a n ==> a+n <= b \/ b+k <= a` by
    (rpt strip_tac >>
     qpat_x_assum `!name a n. local_region ce es0.scopes s0 name a n ==> _` drule >>
     simp[regions_disjoint_def, DISJ_COMM]) >>
  drule_all intcall_child_store_landing >> strip_tac >>
  `!name a n. local_region ce es.scopes u name a n ==> regions_disjoint b k a n` by
    (rpt strip_tac >>
     `local_region ce es0.scopes s0 name a n` by
       (irule local_region_frame >> conj_tac
        >- (qexists_tac `fp.jc_func` >>
            fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`sa`, `es.scopes`, `u`] >>
        fs[intcall_expr_cont_def, intcall_joint_res_def, intcall_expr_res_def]) >> metis_tac[]) >>
  qexists_tac `u` >> simp[] >> conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `mem_bytes_at a n u.vs_memory = mem_bytes_at a n s.vs_memory` by simp[] >>
  `a = b + (a-b) /\ a-b+n <= k` by decide_tac >>
  qpat_x_assum `mem_bytes_at b k s.vs_memory = _` mp_tac >>
  disch_then (mp_then Any mp_tac valueEncodingPropsTheory.mem_bytes_at_translated_window) >>
  disch_then (qspecl_then [`a-b`, `n`] mp_tac) >> simp[]
QED

(* A gas-transparent source action may be implemented by a zero-mark path. *)
Theorem intcall_gas_transparent_path_outcome:
  (!tail. source (es with gas_obs := tail) = (res, ee with gas_obs := tail)) /\
  gas_marked_path memory ctx func s 0 r /\
  ((?t. r = OK t /\ Q res (ee with gas_obs := []) t) \/
   (exit_result r /\ R res (ee with gas_obs := []) r)) ==>
  gas_outcome memory tops (ctx,func) source (es,s) Q R
Proof
  rpt gen_tac >> strip_tac >>
  simp[gasOutcomeTheory.gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`res`, `ee`, `r`] >>
  gvs[gasSummaryTheory.gas_marked_exec_def]
QED

Theorem intcall_counted_child_store:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_expr_producer fp e /\
  expr_body_pre ce fp.jc_cx env e es /\
  supportedExprs$supported_expr fp.jc_tops e /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  intcall_expr_res fp ce env es0 s0c s0 /\
  intcall_expr_cont fp ce env es0 s0c s0 es si t /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  s0c.cs_next_var <= si.cs_next_var /\ s0c.cs_next_id <= si.cs_next_id /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst dty (post_value_type ce e) su = ((),sb) /\
  fn_has_code si sm fp.jc_func /\ fn_has_code sm sn fp.jc_func /\
  fn_has_code sn su fp.jc_func /\ fn_has_code su sb fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\
  type_widens_to env.type_defs (expr_type e) dty /\
  type_widens_to (get_tenv fp.jc_cx) (post_value_type ce e) dty /\
  evaluate_type (get_tenv fp.jc_cx) dty = SOME dtv /\
  evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME stv /\
  type_memory_size dtv + 64 < dimword (:256) /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (b,k) /\
  s0c.cs_next_id <= inst.inst_id /\ inst.inst_id < si.cs_next_id /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  eval_operand buf t = SOME bw /\ (!lbl. buf <> Label lbl) /\
  (!x. buf = Var x ==> not_fresh_at si x) /\
  fp.jc_lo <= b /\ b <= w2n bw /\
  w2n bw + off + type_memory_size dtv <= b+k /\ b+k < dimword (:256) /\
  (!name a n. local_region ce es.scopes t name a n ==>
     regions_disjoint b k a n) /\
  (!name a n. local_region ce es0.scopes s0 name a n ==>
     regions_disjoint b k a n) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (vyperState$bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) (es,t)
    (\res ee u. ?v. res = INL v /\
       val_in_memory dtv v (w2n bw + off) u.vs_memory /\
       intcall_expr_cont fp ce env es0 s0c s0 ee sb u /\
       FLOOKUP u.vs_allocas inst.inst_id = SOME (b,k) /\
       eval_operand buf u = SOME bw /\
       MAP FDOM es.scopes = MAP FDOM ee.scopes /\
       (!name a n. local_region ce ee.scopes u name a n ==>
          regions_disjoint b k a n) /\
       (!a n. b <= a /\ a+n <= b+k /\
          (a+n <= w2n bw+off \/ w2n bw+off+type_memory_size dtv <= a) ==>
          mem_bytes_at a n u.vs_memory = mem_bytes_at a n t.vs_memory))
    (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  `intcall_expr_res fp ce env es si t /\ ~t.vs_halted /\
   t.vs_current_bb = si.cs_current_bb /\
   t.vs_inst_idx = LENGTH si.cs_current_insts` by fs[intcall_expr_cont_def] >>
  `gas_admissible (eval_expr fp.jc_cx e) expr_vv_res_ok es` by
    metis_tac[exprSimHypsTheory.expr_body_pre_vv_gas_admissible] >>
  dxrule (iffLR intcall_expr_producer_def) >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then drule_all >> disch_tac >>
  irule gas_outcome_bind_result_exec >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (Cases >> simp[exprSimDefsTheory.expr_exit_INL,
                           stmtSimPropsTheory.expr_exit_INR_type]) >>
  reverse conj_tac >- metis_tac[] >>
  suspend "read_store"
QED

Resume intcall_counted_child_store[read_store]:
  rpt gen_tac >> strip_tac >>
  rename1 `gas_marked_exec _ _ _ _ marks (INL raw) mid (OK q)` >>
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es si sm t
     (mid with gas_obs := []) raw vv q` by
    (fs[vv_post_def, intcall_expr_cont_def, intcall_joint_res_def, intcall_expr_res_def] >>
     metis_tac[]) >>
  `expr_sim_inv ce fp.jc_cx env es` by fs[intcall_joint_res_def, intcall_expr_res_def] >>
  drule_all intcall_child_read_layout >> strip_tac >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    intcall_child_materialize_root >>
  disch_then (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP t.vs_allocas _ = _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand buf t = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (qspec_then `v` mp_tac) >>
  disch_then (rev_drule_at (Pat `intcall_expr_cont _ _ _ es0 s0c s0 es si t`)) >>
  (impl_tac >- (fs[] >> metis_tac[])) >> strip_tac >>
  rename1 `gas_marked_path F _ _ q 0 (OK uu)` >>
  drule_all intcall_child_store_operands >> strip_tac >>
  `w2n bw + off < dimword (:256) /\ off < dimword (:256)` by decide_tac >>
  `w2n (bw + n2w off) = w2n bw + off` by
    (mp_tac (wordsTheory.w2n_add_2 |> INST_TYPE [alpha |-> ``:256``] |>
       Q.INST [`a` |-> `bw`, `b` |-> `n2w off`]) >>
     simp[]) >>
  `b <= w2n (bw + n2w off) /\
   w2n (bw + n2w off) + type_memory_size dtv <= b+k` by fs[] >>
  drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)
    intcall_root_store_landing >>
  disch_then (drule_at (Pat `expr_val_rel _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP uu.vs_allocas _ = _`)) >>
  disch_then (drule_at (Pat `intcall_expr_cont _ _ _ es0 s0c s0 _ su uu`)) >>
  disch_then (drule_at (Pat `mem_bytes_at b k uu.vs_memory = _`)) >>
  disch_then (drule_at (Pat `eval_operand buf uu = _`)) >>
  disch_then (drule_at (Pat `eval_operand dst uu = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  disch_then (qspec_then `dtv` mp_tac) >>
  (impl_tac >- (fs[] >> metis_tac[])) >> strip_tac >>
  `gas_marked_path F fp.jc_ctx fp.jc_func q 0 (OK u)` by
    (drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
  irule intcall_gas_transparent_path_outcome >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`mid`, `INL v`] >> simp[] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  conj_tac >- fs[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!a n. _ ==> mem_bytes_at a n u.vs_memory = _` irule >>
  fs[] >> decide_tac
QED

Finalise intcall_counted_child_store
