(* The RHS snapshot of an Assign whose target can modify memory or storage
   (compile_stmt's Assign, expr_can_mutate), memory-counted: a word value is
   read at once, a composite one is copied into a fresh temporary
   (compile_snapshot_vv cenv T).  The copy's buffer is one of the snapshot's
   own allocations, so the saved value is clear of every live local
   (vv_own), and the snapshot writes nothing outside its own allocations
   (pure_frame).  bodyPtrAssignSnapshot is the pointer-safety sibling. *)
Theory bodyMemAssignSnapshot
Ancestors
  exprSimMemUnwrap exprSimMemDefs loweringPosts allocaHistory fragGasMode
  exprLowering context compileEnv vyperInterpreter vyperState venomState
  exprSimUnwrap exprSimUnwrapProps exprSimDefs venomInst venomExecSemantics
  instMemFrontier fragGasPathMem emitHelper valueCopyBytes memSafeRun
  bodyImmutableUnwrapMemory

Theorem snapshot_storage_word_readonly[local]:
  !ctx func cenv cx e es sa sm sb s0 ee v t p op s.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    is_word_type t /\ local_ptrs_reserved cenv sm /\
    sa.cs_next_var <= sm.cs_next_var /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\
    vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue t p) s /\
    alloca_history func s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path_mem ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
        u.vs_memory = s.vs_memory /\
        u.vs_alloca_next = s.vs_alloca_next /\ alloca_history func u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >> (
  `t = post_value_type cenv e /\
   ?w. eval_operand p.ptr_operand s = SOME w /\
       storage_holds cx (p.ptr_location = LocTransient) (post_value_type cenv e)
         (Value v) w ee s /\
       stmt_state_rel ctx func cenv cx ee s` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  qabbrev_tac `ld = if p.ptr_location = LocTransient then tload w s
                    else sload w s` >>
  `!tvt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tvt ==>
         ld = typed_val_to_w256 tvt v` by
    (rpt strip_tac >> qunabbrev_tac `ld` >>
     drule_all storage_holds_load >> simp[]) >>
  `emit_op (if p.ptr_location = LocTransient then TLOAD else SLOAD)
     [p.ptr_operand] sm = (op, sb)` by
    gvs[unwrap_value_def, contextTheory.compile_ptr_load_def] >>
  drule emit_op_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ee`, `s`, `ld`] mp_tac) >>
  impl_tac
  >- (rw[is_terminator_def, Abbr `ld`] >>
      simp[below_frontier_no_ranges, inst_dload_in_section_def,
           step_inst_base_opcode_eqs, exec_read1_def, mk_inst_def]) >>
  strip_tac >> goal_assum drule >> simp[] >>
  irule exprSimUnwrapPropsTheory.expr_post_of_vv_post_load_physical >> simp[] >>
  qexistsl_tac [`p`, `s`, `sm`, `post_value_type cenv e`] >> simp[])
QED

Theorem snapshot_runtime_word_readonly[local]:
  !ctx func cenv cx e es sa sm sb s0 ee v t p op s.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\
    sa.cs_next_var <= sm.cs_next_var /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\
    vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue t p) s /\
    alloca_history func s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path_mem ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
        u.vs_memory = s.vs_memory /\
        u.vs_alloca_next = s.vs_alloca_next /\ alloca_history func u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  `t = post_value_type cenv e /\
   ?w. eval_operand p.ptr_operand s = SOME w /\
       immutable_holds cenv cx (post_value_type cenv e) (Value v) w ee s /\
       stmt_state_rel ctx func cenv cx ee s` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  `?tv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tv` by
    (gvs[immutable_holds_def] >> metis_tac[]) >>
  `w2n w + type_memory_size tv <= LENGTH s.vs_data_section` by
    (irule runtime_immutable_data_section >> metis_tac[]) >>
  drule_all immutable_holds_dload >> strip_tac >>
  `emit_op DLOAD [p.ptr_operand] sm = (op, sb)` by
    gvs[unwrap_value_def, contextTheory.compile_ptr_load_def,
        contextTheory.compile_imm_load_word_def] >>
  drule emit_op_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ee`, `s`,
    `typed_val_to_w256 tvt v`] mp_tac) >>
  impl_tac
  >- (simp[is_terminator_def] >> rpt strip_tac
      >- (irule below_frontier_no_ranges >> simp[mk_inst_def])
      >- (rw[inst_dload_in_section_def, mk_inst_def] >> gvs[])
      >- (qpat_x_assum `word_of_bytes _ _ _ = _` (SUBST1_TAC o SYM) >>
          irule step_DLOAD >> first_assum ACCEPT_TAC)) >>
  strip_tac >> goal_assum drule >> simp[] >>
  irule expr_post_of_vv_post_load_physical >> simp[] >>
  qexistsl_tac [`p`, `s`, `sm`, `post_value_type cenv e`] >> simp[]
QED

Theorem snapshot_vv_counted_mem:
  !ctx func cenv cx e es sa sm sb s0 ee tv v vv saved s.
    post_value_type cenv e = expr_type e /\
    (* The RHS annotations are compatible, as body_assign_place_mem_case
       carries: the Assign caller has the disjunction from its split
       (bodyMemAssign's Cases_on, as for body_assign_local_memory_mem); the
       widened-aggregate IntCall rest goes to
       body_assign_place_widened_aggregate_call_mem.  A located value not
       in memory comes from a place read, where lowered_value_type_def's
       catch-all clause gives expr_type e: an IntCall result is in memory
       (incompatibleReturnLayout.nonzero_internal_call_located), and
       literals, Concat and AbiEncode compile into memory buffers. *)
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
    (!t p. vv = LocatedValue t p /\ p.ptr_location <> LocMemory ==>
           lowered_value_type cenv e = expr_type e) /\
    compile_snapshot_vv cenv T (vv_with_type (lowered_value_type cenv e) vv) sm =
      (saved, sb) /\
    read_result cx tv ee = (INL v, ee) /\
    (!tvt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tvt ==>
           value_has_type tvt v) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (* Both annotations evaluate: exprSimHyps.expr_body_pre_type_evaluates
       for expr_type e, memoryLocalRhsProps.memory_rhs_lowered_runtime_layout
       (from the compatibility above) for the lowered one. *)
    (?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt) /\
    (?ltv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv) /\
    (!t tvt. (t = expr_type e \/ t = lowered_value_type cenv e) /\
             evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
             type_memory_bytes cenv t = type_memory_size tvt /\
             type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_marked_path T ctx func s 0 (OK u) /\
        vv_post ctx func cenv cx e es sa sb s0 ee tv saved u /\
        vv_own cenv cx (expr_type e) sm sb ee tv saved u /\
        pure_frame cenv func ee sm s u /\
        vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv
          saved u /\
        alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED
