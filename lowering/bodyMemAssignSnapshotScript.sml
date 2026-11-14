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
  bodyImmutableUnwrapMemory bodyMemSnapshotStoreRoom bodyMemSnapshotStages
  bodyMemSnapshotAlloc exprSimAlloc vyperTypeArgFits abiStepAllocRecords

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

Theorem snapshot_ctor_word_readonly[local]:
  !ctx func cenv cx e es sa sm sb s0 ee v t p op s.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ is_word_type t /\
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
  `w2n w + 32 <= s.vs_alloca_next` by
    metis_tac[ctor_immutable_word_frontier] >>
  drule_all immutable_holds_iload >> strip_tac >>
  `compile_imm_load_word T cenv.ce_imm_alloca p.ptr_operand sm = (op, sb)` by
    gvs[unwrap_value_def, contextTheory.compile_ptr_load_def] >>
  drule compile_imm_load_word_ctor_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `ee`, `s`, `w`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >> goal_assum drule >> simp[] >>
  irule expr_post_of_vv_post_load_physical >> simp[] >>
  qexistsl_tac [`p`, `s`, `sm`, `post_value_type cenv e`] >> simp[]
QED

Theorem snapshot_memory_word_readonly[local]:
  !ctx func cenv cx e es sa sm sb s0 ee v t p op s.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocMemory /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\
    sa.cs_next_var <= sm.cs_next_var /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\
    vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue t p) s /\
    (?w. eval_operand p.ptr_operand s = SOME w /\
         w2n w + 32 <= s.vs_alloca_next) /\
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
   (!tvt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tvt ==>
      mem_word_at (w2n w) s.vs_memory = typed_val_to_w256 tvt v) /\
   stmt_state_rel ctx func cenv cx ee s` by
    (gvs[vv_post_def, vv_holds_def, read_result_def, return_def,
         is_bytestring_word_type] >> metis_tac[]) >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  `emit_op MLOAD [p.ptr_operand] sm = (op, sb)` by
    gvs[unwrap_value_def, contextTheory.compile_ptr_load_def] >>
  drule emit_op_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ee`, `s`,
    `mload (w2n w) s`] mp_tac) >>
  impl_tac
  >- (simp[is_terminator_def, below_frontier_MLOAD,
           inst_dload_in_section_def] >>
      simp[step_inst_base_opcode_eqs, exec_read1_def, mk_inst_def]) >>
  strip_tac >> goal_assum drule >> simp[] >>
  irule expr_post_of_vv_post_load_physical >> simp[] >>
  conj_tac
  >- simp[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  qexistsl_tac [`p`, `s`, `sm`, `post_value_type cenv e`] >> simp[]
QED

Theorem snapshot_word_unwrap_readonly[local]:
  !ctx func cenv cx e es sa sm sb s0 ee tv v vv op s.
    post_value_type cenv e = expr_type e /\
    is_word_type (expr_type e) /\
    unwrap_value cenv vv sm = (op, sb) /\
    read_result cx tv ee = (INL v, ee) /\
    local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt) /\
    vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
    vv_store_bound cx (expr_type e) (expr_type e) ee tv vv s /\
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
  drule_all vv_post_read_result >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> simp[]) >>
  Cases_on `vv`
  >- (gvs[unwrap_value_def, comp_return_def] >> qexists_tac `s` >>
      simp[Once gas_path_mem_cases] >>
      gvs[vv_post_def, vv_holds_def, vv_at_def, vv_own_def,
          expr_post_def, expr_val_rel_def, expr_val_at_def, expr_val_own_def,
          read_result_def, return_def] >> metis_tac[]) >>
  rename1 `LocatedValue t p` >>
  `is_word_type t` by
    (gvs[vv_post_def, vv_holds_def, is_bytestring_word_type] >> metis_tac[]) >>
  Cases_on `p.ptr_location`
  >- (irule snapshot_memory_word_readonly >> simp[] >>
      qexistsl_tac [`p`, `sm`, `t`] >> simp[] >>
      `?w. eval_operand p.ptr_operand s = SOME w` by
        (gvs[vv_post_def, vv_holds_def] >> metis_tac[]) >>
      qexists_tac `w` >> simp[] >>
      `type_memory_size tvt = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
      gvs[vv_store_bound_def] >> first_x_assum drule_all >> simp[]) 
  >- (irule snapshot_storage_word_readonly >> simp[] >> metis_tac[])
  >- (irule snapshot_storage_word_readonly >> simp[] >> metis_tac[])
  >- (Cases_on `cenv.ce_is_ctor`
      >- (irule snapshot_ctor_word_readonly >> simp[] >>
          qexistsl_tac [`p`, `sm`, `t`] >> simp[]) >>
      irule snapshot_runtime_word_readonly >> simp[] >>
      qexistsl_tac [`p`, `sm`, `t`] >> simp[]) >>
  gvs[vv_post_def, vv_holds_def]
QED

Theorem snapshot_stack_word_post[local]:
  !ctx func cenv cx e es sa sm sb s0 ee tv v op s u.
    post_value_type cenv e = expr_type e /\
    is_word_type (expr_type e) /\
    read_result cx tv ee = (INL v, ee) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    u.vs_memory = s.vs_memory ==>
    vv_post ctx func cenv cx e es sa sb s0 ee tv
      (StackValue (expr_type e) op) u /\
    vv_own cenv cx (expr_type e) sm sb ee tv
      (StackValue (expr_type e) op) u /\
    pure_frame cenv func ee sm s u /\
    vv_store_bound cx (expr_type e) (expr_type e) ee tv
      (StackValue (expr_type e) op) u
Proof
  rpt strip_tac >>
  gvs[vv_post_def, vv_holds_def, vv_at_def, vv_own_def,
      expr_post_def, expr_val_rel_def, expr_val_own_def,
      pure_frame_def, vv_store_bound_stack_word] >> metis_tac[]
QED

Theorem snapshot_word_counted_mem[local]:
  !ctx func cenv cx e es sa sm sb s0 ee tv v vv saved s.
    is_word_type (expr_type e) /\
    post_value_type cenv e = expr_type e /\
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
  rpt gen_tac >> strip_tac >> (
  `lowered_value_type cenv e = expr_type e` by
    metis_tac[is_bytestring_word_type] >>
  `vv_type (vv_with_type (lowered_value_type cenv e) vv) = expr_type e /\
   unwrap_value cenv (vv_with_type (lowered_value_type cenv e) vv) sm =
     unwrap_value cenv vv sm` by
    (Cases_on `vv`
     >- simp[vv_with_type_def, vv_type_def, unwrap_value_def] >>
     gvs[vv_post_def, vv_holds_def, vv_with_type_def, vv_type_def,
         is_bytestring_word_type]) >>
  qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
  simp[compile_snapshot_vv_def, comp_bind_def, comp_return_def] >>
  gvs[] >>
  Cases_on `unwrap_value cenv vv sm` >>
  rename1 `unwrap_value cenv vv sm = (op, sc)` >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `unwrap_value cenv vv sm = (op, sc)` >>
  `?u. gas_path_mem ctx func s 0 (OK u) /\
       expr_post ctx func cenv cx e es sa sc s0 ee v op u /\
       u.vs_memory = s.vs_memory /\
       u.vs_alloca_next = s.vs_alloca_next /\ alloca_history func u /\
       u.vs_current_bb = sc.cs_current_bb /\
       u.vs_inst_idx = LENGTH sc.cs_current_insts` by
    (irule snapshot_word_unwrap_readonly >> simp[] >>
     metis_tac[]) >>
  simp[gas_marked_path_def] >> goal_assum drule >> simp[] >>
  metis_tac[snapshot_stack_word_post, post_value_type_word])
QED

Theorem snapshot_pointer_contract_cong[local]:
  p.ptr_operand = q.ptr_operand /\ p.ptr_location = q.ptr_location ==>
  (vv_post ctx func ce cx e es sa sb s0 ee raw (LocatedValue ty p) z =
   vv_post ctx func ce cx e es sa sb s0 ee raw (LocatedValue ty q) z) /\
  (vv_own ce cx t sm sb ee raw (LocatedValue ty p) z =
   vv_own ce cx t sm sb ee raw (LocatedValue ty q) z) /\
  (vv_store_bound cx t lt ee raw (LocatedValue ty p) z =
   vv_store_bound cx t lt ee raw (LocatedValue ty q) z)
Proof
  strip_tac >> simp[vv_post_def, vv_holds_def, vv_at_def,
    vv_own_def, vv_store_bound_def, vv_operand_def]
QED

Theorem snapshot_memory_pointer_contract[local]:
  (vv_post ctx fn ce cx e es sa sb s0 ee raw
    (LocatedValue ty <|ptr_location := LocMemory; ptr_operand := op|>) z =
   vv_post ctx fn ce cx e es sa sb s0 ee raw
    (LocatedValue ty (mk_ptr op LocMemory)) z) /\
  (vv_own ce cx t sm sb ee raw
    (LocatedValue ty <|ptr_location := LocMemory; ptr_operand := op|>) z =
   vv_own ce cx t sm sb ee raw (LocatedValue ty (mk_ptr op LocMemory)) z) /\
  (vv_store_bound cx t lt ee raw
    (LocatedValue ty <|ptr_location := LocMemory; ptr_operand := op|>) z =
   vv_store_bound cx t lt ee raw (LocatedValue ty (mk_ptr op LocMemory)) z)
Proof
  irule snapshot_pointer_contract_cong >> simp[mk_ptr_def]
QED

Theorem snapshot_store_suffix_mem[local]:
  post_value_type ce e = expr_type e /\ ~is_word_type (expr_type e) /\
  ~is_word_type (lowered_value_type ce e) /\
  (lowered_value_type ce e = expr_type e \/ is_bytestring_type (expr_type e) /\
   is_bytestring_type (lowered_value_type ce e) /\
   arg_type_fits (lowered_value_type ce e) (expr_type e)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME et /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME lt /\
  value_has_type lt v /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size lt /\
  type_memory_size lt < dimword (:256) /\
  compile_alloc_buffer (type_memory_size lt) sm = (buf,mid) /\
  fn_has_code sm mid func /\ mid.cs_next_id <= sb.cs_next_id /\
  sm.cs_next_id < mid.cs_next_id /\
  compile_store_memory ce src buf.buf_operand (lowered_value_type ce e)
    (lowered_value_type ce e) sc = ((),sb) /\
  fn_has_code sc sb func /\ fn_inst_ids_distinct func /\
  read_result cx raw ee = (INL v,ee) /\
  expr_post ctx func ce cx e es sa sc s0 ee v src z /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x. src = Var x \/ buf.buf_operand = Var x ==> not_fresh_at sc x) /\
  (!w ltv. eval_operand src z = SOME w /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv ==>
    type_memory_size ltv = 0 \/ w2n w + type_memory_size ltv <= z.vs_alloca_next) /\
  eval_operand buf.buf_operand z = SOME d /\
  FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n d,type_memory_size lt) /\
  w2n d + type_memory_size lt <= z.vs_alloca_next /\
  (!n b len. local_region ce ee.scopes z n b len ==>
    regions_disjoint (w2n d) (type_memory_size lt) b len) /\
  (!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
    aid < sa.cs_next_id ==>
    loweringStateRelDefs$regions_disjoint (w2n d) (type_memory_size lt) off len) /\
  alloca_history func z /\ ~z.vs_halted /\
  z.vs_current_bb = sc.cs_current_bb /\
  z.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  ?u. gas_path_mem ctx func z 0 (OK u) /\
    vv_post ctx func ce cx e es sa sb s0 ee raw
      (LocatedValue (lowered_value_type ce e)
        <|ptr_location := LocMemory; ptr_operand := buf.buf_operand|>) u /\
    vv_own ce cx (expr_type e) sm sb ee raw
      (LocatedValue (lowered_value_type ce e)
        <|ptr_location := LocMemory; ptr_operand := buf.buf_operand|>) u /\
    pure_frame ce func ee sm z u /\
    vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw
      (LocatedValue (lowered_value_type ce e)
        <|ptr_location := LocMemory; ptr_operand := buf.buf_operand|>) u /\
    alloca_history func u /\ z.vs_alloca_next <= u.vs_alloca_next /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `value_has_type et v` by metis_tac[arg_type_fits_value_has_type, optionTheory.SOME_11] >>
  drule_all snapshot_lowered_encoding >> strip_tac >>
  `alloca_inv z` by fs[expr_post_def, exprLoweringPropsTheory.stmt_state_rel_def] >>
  drule_all buffer_alloc_code >> strip_tac >>
  irule snapshot_store_result_room_mem >>
  simp[] >>
  qexists_tac `mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size lt))]
    [STRING #"%" (toString sm.cs_next_var)]` >>
  qexistsl_tac [`sc`, `src`, `w`] >>
  simp[mk_inst_def] >> asm_rewrite_tac[] >>
  conj_tac
  >- (qpat_x_assum `type_memory_size lt < _` mp_tac >>
      CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >> simp[]) >>
  qpat_x_assum `!w ltv. _` (qspecl_then [`w`, `lt`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem snapshot_gas_edge_allocas[local]:
  !ctx fn s n r. gas_path_edge ctx fn s n r ==>
    !t aid b len. r = OK t /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      FLOOKUP t.vs_allocas aid = SOME (b,len)
Proof
  rpt gen_tac >> rw[fragGasPathTheory.gas_path_edge_def] >>
  gvs[fragExecTheory.exit_result_def, jump_to_def] >>
  imp_res_tac step_inst_lookup_old >>
  imp_res_tac venomExecProofsTheory.eval_phis_preserves_alloca_fields >> gvs[] >>
  metis_tac[]
QED

Theorem snapshot_gas_allocas:
  !ctx fn s n r. gas_path ctx fn s n r ==>
    !t aid b len. r = OK t /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      FLOOKUP t.vs_allocas aid = SOME (b,len)
Proof
  ho_match_mp_tac fragGasPathTheory.gas_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  metis_tac[snapshot_gas_edge_allocas, fragExecTheory.exit_result_def]
QED

Theorem snapshot_three_stage_frame[local]:
  gas_path_mem ctx func s 0 (OK u) /\
  gas_path_mem ctx func u 0 (OK z) /\
  gas_path_mem ctx func z 0 (OK t) /\
  pure_frame ce func ee sm s u /\ pure_frame ce func ee mid u z /\
  pure_frame ce func ee sm z t /\ ci_mono sm mid /\
  local_ptrs_reserved ce sm /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
  (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) ==>
  gas_path_mem ctx func s 0 (OK t) /\ pure_frame ce func ee sm s t
Proof
  strip_tac >>
  `!a b. FLOOKUP u.vs_allocas a = SOME b ==> FLOOKUP z.vs_allocas a = SOME b` by
    (Cases_on `b` >> metis_tac[snapshot_gas_allocas, gas_path_mem_exec]) >>
  `!a b. FLOOKUP z.vs_allocas a = SOME b ==> FLOOKUP t.vs_allocas a = SOME b` by
    (Cases_on `b` >> metis_tac[snapshot_gas_allocas, gas_path_mem_exec]) >>
  `pure_frame ce func ee sm s z` by
    (irule exprSimPropsTheory.pure_frame_trans >> simp[] >> qexistsl_tac [`ee`, `mid`, `u`] >>
     fs[exprLoweringPropsTheory.ci_mono_def]) >>
  conj_tac >- metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  irule exprSimPropsTheory.pure_frame_trans >> simp[] >> qexistsl_tac [`ee`, `sm`, `z`] >>
  simp[] >> metis_tac[freshWritesTheory.not_fresh_at_mono,
    exprLoweringPropsTheory.ci_mono_def]
QED

Theorem snapshot_old_allocation_separation[local]:
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  sa.cs_next_id <= sm.cs_next_id /\
  (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint dst cap b len) ==>
  !aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
    aid < sa.cs_next_id ==> regions_disjoint dst cap off len
Proof
  simp[vv_post_def] >> rpt strip_tac >>
  qpat_x_assum `!aid b len. aid < sm.cs_next_id /\ _ ==> _` irule >>
  simp[] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem snapshot_unwrap_resources[local]:
  ci_mono sm mid /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ s.vs_alloca_next <= u.vs_alloca_next /\
  ~is_word_type (expr_type e) /\
  (!t tvt. (t = expr_type e \/ t = lowered_value_type cenv e) /\
    evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
    type_memory_bytes cenv t = type_memory_size tvt /\ type_memory_size tvt < 2**64) ==>
  sa.cs_next_var <= mid.cs_next_var /\ sa.cs_next_id <= mid.cs_next_id /\
  local_ptrs_reserved cenv mid /\
  (!x. vv_operand vv = Var x ==> not_fresh_at mid x) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
    type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
    type_memory_size tvt < 2**64)
Proof
  fs[exprLoweringPropsTheory.ci_mono_def] >>
  metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
    freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem snapshot_nonword_counted_mem:
  !ctx func cenv cx e es sa sm sb s0 ee tv v vv saved s.
    ~is_word_type (expr_type e) /\
    post_value_type cenv e = expr_type e /\
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
        vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv saved u /\
        alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_word_type (lowered_value_type cenv e)` by
    metis_tac[is_bytestring_word_type] >>
  drule_all snapshot_nonword_slices >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `?ltv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
     type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv /\
     type_memory_size ltv < 2**64` by metis_tac[] >>
  `type_memory_bytes cenv (lowered_value_type cenv e) < dimword (:256)` by
    (qpat_x_assum `type_memory_size ltv < _` mp_tac >>
     qpat_x_assum `type_memory_bytes _ _ = _` (fn th => rewrite_tac[th]) >>
     CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >> decide_tac) >>
  drule_all snapshot_alloc_source_mem >> strip_tac >>
  drule_all snapshot_unwrap_resources >> strip_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) snapshot_unwrap_source_mem >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`v`, `buf.buf_operand`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `!x. src = Var x ==> not_fresh_at sc x` by
    (drule exprOperandVarTheory.compiler_unwrap_value_var >>
     Cases_on `vv` >> gvs[vv_with_type_def, vv_operand_def]) >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `mid` >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
    aid < sa.cs_next_id ==>
    regions_disjoint (w2n w) (type_memory_bytes cenv (lowered_value_type cenv e)) off len` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ sm _ _ _ _ s`
       (mp_then Any mp_tac snapshot_old_allocation_separation) >>
     disch_then (qspecl_then
       [`w2n w`, `type_memory_bytes cenv (lowered_value_type cenv e)`] assume_tac) >>
     rpt strip_tac >> first_x_assum irule >> fs[] >> metis_tac[]) >>
  drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`) snapshot_store_suffix_mem >>
  disch_then (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (lowered_value_type _ _) = SOME _`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (qspecl_then [`sm`, `mid`, `ltv`] mp_tac) >>
  qpat_x_assum `?tvt. evaluate_type _ (expr_type e) = SOME tvt` strip_assume_tac >>
  disch_then (qspec_then `tvt` mp_tac) >>
  (impl_tac >- (simp[] >> fs[exprLoweringPropsTheory.ci_mono_def] >>
    metis_tac[arithmeticTheory.LESS_EQ_TRANS])) >> strip_tac >>
  drule_all snapshot_three_stage_frame >> strip_tac >>
  qexists_tac `u'` >> simp[gas_marked_path_def] >>
  qpat_x_assum `saved = _` (fn th => rewrite_tac[th]) >>
  fs[snapshot_memory_pointer_contract] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
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
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type (expr_type e)`
  >- (drule_all snapshot_word_counted_mem >> simp[]) >>
  drule_all snapshot_nonword_counted_mem >> simp[]
QED
