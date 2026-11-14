Theory assignEffectfulIndexCodeWordFrame
Ancestors
  fragExec exprSimAccounts stmtSimDefs exprSimUnwrap exprSimUnwrapProps exprSimCopy exprSimProps
  placeStoreStorage typedMemoryCopy exprLoweringProps loweringPosts
  compileEnv context exprLowering loweringStateRelDefs freshWrites
  venomState venomInst venomExecSemantics emitHelper emitHelperProps
  fragGasMode fragGasPath immutableEncoding valueEncodingProps

(* A finite read instruction keeps the entire entry frame, not merely
   variables whose lookups happened to be defined at entry. *)
Theorem snapshot_read_op_frame[local]:
  emit_op opc args sm = (op,sb) /\ fn_has_code sm sb func /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  (!out. step_inst_base (mk_inst sm.cs_next_id opc args [out]) s =
     OK (update_var out w s)) /\
  local_ptrs_reserved ce sm /\ stmt_state_rel ctx func ce cx ee s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    eval_operand op u = SOME w /\ stmt_state_rel ctx func ce cx ee u /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `same_blocks sm sb` by metis_tac[emit_op_same_blocks] >>
  drule_all emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by fs[same_blocks_def] >>
  qabbrev_tac `u = (update_var (STRING #"%" (toString sm.cs_next_var)) w s)
    with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `gas_marked_path F ctx func s 0 (OK u)` by
    (qunabbrev_tac `u` >> irule place_store_emitted_seq_path >> simp[] >>
     qexists_tac `sm` >> gvs[run_inst_seq_def, mk_inst_def]) >>
  `stmt_state_rel ctx func ce cx ee u` by
    (simp[Abbr `u`, stmt_state_rel_inst_idx] >> irule stmt_state_rel_update_var >>
     simp[] >> irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
  qexists_tac `u` >> simp[Abbr `u`, update_var_def, eval_operand_def,
    lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> rpt strip_tac >>
  gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem snapshot_runtime_code_word_frame[local]:
  unwrap_value ce (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocCode /\ ~ce.ce_is_ctor /\ is_word_type t /\
  fn_has_code sm sb func /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\
  vv_post ctx func ce cx e es sa sm s0 ee (Value v) (LocatedValue t p) s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op u /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory /\
    alloca_frame ce ee sm s ce ee u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `t = post_value_type ce e /\
   ?w. eval_operand p.ptr_operand s = SOME w /\
       immutable_holds ce cx (post_value_type ce e) (Value v) w ee s /\
       stmt_state_rel ctx func ce cx ee s` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  drule_all immutable_holds_dload >> strip_tac >>
  `emit_op DLOAD [p.ptr_operand] sm = (op,sb)` by
    gvs[unwrap_value_def, compile_ptr_load_def, compile_imm_load_word_def] >>
  `!out. step_inst_base (mk_inst sm.cs_next_id DLOAD [p.ptr_operand] [out]) s =
    OK (update_var out (typed_val_to_w256 tvt v) s)` by
    (gen_tac >> qpat_x_assum `word_of_bytes _ _ _ = _` (SUBST1_TAC o SYM) >>
     irule step_DLOAD >> simp[]) >>
  `DLOAD <> INVOKE /\ DLOAD <> GAS /\ ~is_terminator DLOAD` by
    simp[is_terminator_def] >>
  drule_all snapshot_read_op_frame >> strip_tac >>
  `alloca_frame ce ee sm s ce ee u` by
    (simp[alloca_frame_def] >> rpt strip_tac >>
     drule_all copy_buffer_local_region_frame >> metis_tac[]) >>
  qexists_tac `u` >> simp[] >>
  irule expr_post_of_vv_post_load_physical >> simp[] >>
  qexistsl_tac [`p`,`s`,`sm`,`post_value_type ce e`] >> simp[]
QED

Theorem snapshot_ctor_read_frame[local]:
  compile_imm_load_word T ce.ce_imm_alloca pop sm = (op,sb) /\
  local_ptrs_reserved ce sm /\ fn_has_code sm sb func /\
  stmt_state_rel ctx func ce cx ee s /\ eval_operand pop s = SOME w /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    eval_operand op u = SOME (mload (w2n w) s) /\
    stmt_state_rel ctx func ce cx ee u /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `ILOAD <> INVOKE /\ ILOAD <> GAS /\ ~is_terminator ILOAD /\
   ADD <> INVOKE /\ ADD <> GAS /\ ~is_terminator ADD` by
    simp[is_terminator_def] >>
  Cases_on `ce.ce_imm_alloca` >> gvs[compile_imm_load_word_def]
  >- (`!out. step_inst_base (mk_inst sm.cs_next_id ILOAD [pop] [out]) s =
        OK (update_var out (mload (w2n w) s) s)` by
        (simp[step_inst_base_def, exec_read1_def, mk_inst_def]) >>
      drule_all (SRULE [is_terminator_def]
        (Q.INST [`opc` |-> `ILOAD`] snapshot_read_op_frame)) >>
      strip_tac >> goal_assum drule >> simp[]) >>
  rename1 `ce.ce_imm_alloca = SOME ib` >>
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
  simp[comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op ADD [pop; ib] sm = (addr,sm1)` >>
  `cs_extends sm sm1 /\ cs_extends sm1 sb` by metis_tac[emit_op_extends_next_var] >>
  `fn_has_code sm sm1 func /\ fn_has_code sm1 sb func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved ce sm1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >>
     gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
         comp_ignore_bind_def, comp_return_def, emit_def]) >>
  `eval_operand ib s = SOME 0w` by
    gvs[stmt_state_rel_def, immutable_base_zero_def] >>
  `!out. step_inst_base (mk_inst sm.cs_next_id ADD [pop;ib] [out]) s =
    OK (update_var out w s)` by
    simp[step_inst_base_def, exec_pure2_def, mk_inst_def, wordsTheory.WORD_ADD_0] >>
  drule_all (SRULE [is_terminator_def]
    (Q.INST [`opc` |-> `ADD`] snapshot_read_op_frame)) >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK s1)` >>
  `!out. step_inst_base (mk_inst sm1.cs_next_id ILOAD [addr] [out]) s1 =
    OK (update_var out (mload (w2n w) s1) s1)` by
    (simp[step_inst_base_def, exec_read1_def, mk_inst_def]) >>
  drule_all (SRULE [is_terminator_def]
    (Q.INST [`opc` |-> `ILOAD`] snapshot_read_op_frame)) >> strip_tac >>
  rename1 `gas_marked_path F ctx func s1 0 (OK s2)` >>
  qexists_tac `s2` >> gvs[mload_def] >> conj_tac
  >- (`0 = 0 + 0` by simp[] >> pop_assum SUBST1_TAC >>
      irule gas_marked_path_then >> metis_tac[]) >>
  rpt strip_tac >>
  `not_fresh_at sm1 x` by
    (gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
         comp_ignore_bind_def, comp_return_def, emit_def, not_fresh_at_def]) >>
  metis_tac[]
QED

Theorem snapshot_ctor_code_word_frame[local]:
  unwrap_value ce (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocCode /\ ce.ce_is_ctor /\ is_word_type t /\
  fn_has_code sm sb func /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\
  vv_post ctx func ce cx e es sa sm s0 ee (Value v) (LocatedValue t p) s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op u /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory /\
    alloca_frame ce ee sm s ce ee u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `t = post_value_type ce e /\
   ?w. eval_operand p.ptr_operand s = SOME w /\
       immutable_holds ce cx (post_value_type ce e) (Value v) w ee s /\
       stmt_state_rel ctx func ce cx ee s` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  drule_all immutable_holds_iload >> strip_tac >>
  `compile_imm_load_word T ce.ce_imm_alloca p.ptr_operand sm = (op,sb)` by
    gvs[unwrap_value_def, compile_ptr_load_def] >>
  drule_all snapshot_ctor_read_frame >> strip_tac >>
  `alloca_frame ce ee sm s ce ee u` by
    (simp[alloca_frame_def] >> rpt strip_tac >>
     drule_all copy_buffer_local_region_frame >> metis_tac[]) >>
  qexists_tac `u` >> simp[] >>
  irule expr_post_of_vv_post_load_physical >> simp[] >>
  qexistsl_tac [`p`,`s`,`sm`,`post_value_type ce e`] >> simp[]
QED

Theorem snapshot_code_word_frame:
  unwrap_value ce (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocCode /\ is_word_type t /\
  fn_has_code sm sb func /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\
  vv_post ctx func ce cx e es sa sm s0 ee (Value v) (LocatedValue t p) s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op u /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory /\
    alloca_frame ce ee sm s ce ee u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> Cases_on `ce.ce_is_ctor`
  >- (irule snapshot_ctor_code_word_frame >> simp[] >> metis_tac[]) >>
  irule snapshot_runtime_code_word_frame >> simp[] >> metis_tac[]
QED
