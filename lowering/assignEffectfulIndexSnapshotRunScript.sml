Theory assignEffectfulIndexSnapshotRun
Ancestors
  assignEffectfulIndexPhysical assignEffectfulIndexAllocUnwrap
  assignEffectfulIndexWord assignEffectfulIndexBytesCopy assignEffectfulIndexMemoryCopy
  exprSimMemoryRead exprSimMemoryPath exprSimUnwrapProps exprSimCopy
  stmtSimDefs exprSimProps freshWrites venomState loweringPosts
  valueCopyBytes exprLowering context compileEnv fragGasMode fragGasPath
  loweringStateRelDefs valueEncodingProps exprLoweringProps
  placeStoreStorage exprSimUnwrap emitHelperProps emitHelper venomInst
  venomExecSemantics vyperStorage
  assignEffectfulIndexCodeWordFrame assignEffectfulIndexStorageCompositeFrame
  assignEffectfulIndexCodeCompositeFrame assignEffectfulIndexSnapshotSeparation
  immutableDeployPhysicalSource exprSimIfExpWidenedPhysicalType
  aggregateEvaluatedLayout exprSimIfExpWidenedCounted

(* Memory unwrap does not write memory.  Unlike the ordinary read boundary,
   this retains entry-relative frames even for allocations made after the
   original expression's ownership origin. *)
Theorem snapshot_memory_unwrap_frame[local]:
  unwrap_value ce (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocMemory /\ fn_has_code sm sb func /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  vv_post ctx func ce cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  read_result cx tv ee = (INL v,ee) /\
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
  `(is_word_type t ==> t = post_value_type ce e) /\
   ?w. eval_operand p.ptr_operand s = SOME w /\
     (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt ==>
       val_in_memory tvt v (w2n w) s.vs_memory /\
       (is_word_type (post_value_type ce e) ==>
         mem_word_at (w2n w) s.vs_memory = typed_val_to_w256 tvt v))` by
    (gvs[vv_post_def, vv_holds_def, is_bytestring_word_type] >> metis_tac[]) >>
  `vv_post ctx func ce cx e es sa sm s0 ee (Value v) (LocatedValue t p) s` by
    metis_tac[vv_post_read_result] >>
  Cases_on `is_word_type t`
  >- (gvs[unwrap_memory_compile] >>
      qabbrev_tac `u = (update_var (STRING #"%" (toString sm.cs_next_var))
        (mload (w2n w) s) s) with vs_inst_idx := SUC s.vs_inst_idx` >>
      `eval_operand op u = SOME (mload (w2n w) s) /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts /\
       u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory` by
        (drule_all emit_mload_endpoint >> simp[Abbr `u`]) >>
      `!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s` by
        (simp[Abbr `u`, lookup_var_def, update_var_def, not_fresh_at_def] >>
         rpt strip_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
      `alloca_frame ce ee sm s ce ee u` by
        (simp[alloca_frame_def] >> rpt strip_tac >>
         drule_all copy_buffer_local_region_frame >> metis_tac[]) >>
      qexists_tac `u` >> simp[] >> conj_tac
      >- (drule_all emit_mload_marked_path >> simp[Abbr `u`]) >>
      conj_tac
      >- (irule expr_post_of_vv_post_load_physical >> simp[] >>
          conj_tac >- (rpt strip_tac >> fs[GSYM mem_word_at_eq_mload]) >>
          conj_tac
          >- (simp[Abbr `u`, stmt_state_rel_inst_idx] >>
              irule stmt_state_rel_update_var >>
              `stmt_state_rel ctx func ce cx ee s` by fs[vv_post_def] >>
              simp[] >> irule local_ptrs_reserved_fresh >>
              qexists_tac `sm` >> simp[]) >>
          qexistsl_tac [`p`,`s`,`sm`,`post_value_type ce e`] >> simp[]) >>
      simp[Abbr `u`, update_var_def]) >>
  gvs[unwrap_memory_compile, comp_return_def] >>
  qexists_tac `s` >> simp[alloca_frame_def, gas_marked_path_def, cj 1 gas_path_rules] >>
  metis_tac[expr_post_of_vv_post_memory]
QED

Theorem snapshot_storage_word_frame[local]:
  unwrap_value ce (LocatedValue t p) sm = (op,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  is_word_type t /\ fn_has_code sm sb func /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `t = post_value_type ce e /\
   ?w. eval_operand p.ptr_operand s = SOME w /\
     storage_holds cx (p.ptr_location = LocTransient) (post_value_type ce e)
       (Value v) w ee s /\ stmt_state_rel ctx func ce cx ee s` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  qabbrev_tac `ld = if p.ptr_location = LocTransient then tload w s else sload w s` >>
  `!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt ==>
    ld = typed_val_to_w256 tvt v` by
    (rpt strip_tac >> qunabbrev_tac `ld` >> drule_all storage_holds_load >> simp[]) >>
  `emit_op (if p.ptr_location = LocTransient then TLOAD else SLOAD)
     [p.ptr_operand] sm = (op,sb)` by
    gvs[unwrap_value_def, compile_ptr_load_def] >>
  `same_blocks sm sb` by metis_tac[emit_op_same_blocks] >>
  drule_all emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    metis_tac[emit_op_same_blocks, same_blocks_def] >>
  qabbrev_tac `u = (update_var (STRING #"%" (toString sm.cs_next_var)) ld s)
    with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `gas_marked_path F ctx func s 0 (OK u)` by
    (qunabbrev_tac `u` >> irule place_store_emitted_seq_path >> simp[] >> qexists_tac `sm` >>
     simp[mk_inst_def, run_inst_seq_def, is_terminator_def] >>
     Cases_on `p.ptr_location = LocTransient` >>
     gvs[step_inst_base_opcode_eqs, exec_read1_def, mk_inst_def,
         is_terminator_def, Abbr `ld`]) >>
  `eval_operand op u = SOME ld` by
    gvs[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def,
        finite_mapTheory.FLOOKUP_UPDATE] >>
  `!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s` by
    (simp[Abbr `u`, lookup_var_def, update_var_def, not_fresh_at_def] >>
     rpt strip_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `stmt_state_rel ctx func ce cx ee u` by
    (simp[Abbr `u`, stmt_state_rel_inst_idx] >> irule stmt_state_rel_update_var >>
     simp[] >> irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas` by
    simp[Abbr `u`, update_var_def] >>
  `alloca_frame ce ee sm s ce ee u` by
    (simp[alloca_frame_def] >> rpt strip_tac >>
     drule_all copy_buffer_local_region_frame >> metis_tac[]) >>
  qexists_tac `u` >> simp[] >> conj_tac
  >- (irule expr_post_of_vv_post_load_physical >> simp[] >>
      conj_tac >- (qexists_tac `ld` >> gvs[]) >>
      qexistsl_tac [`p`,`s`,`sm`,`post_value_type ce e`] >>
      simp[Abbr `u`, update_var_def]) >>
  simp[Abbr `u`, update_var_def, alloca_frame_def] >> rpt strip_tac >>
  drule_all copy_buffer_local_region_frame >> simp[update_var_def] >> strip_tac >> metis_tac[]
QED

(* All representation cases retain the frame at the very endpoint carrying
   expr_post; ownership remains relative to the original expression origin. *)
Theorem snapshot_unwrap_frame[local]:
  (post_value_type ce e <> expr_type e ==>
    ((?t a. vv = StackValue t a) \/
     (?t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory /\
       ~is_word_type t))) /\
  unwrap_value ce vv sm = (op,sb) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
    ~is_word_type (post_value_type ce e) ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
    type_memory_size tvt < 2**64) /\
  vv_post ctx func ce cx e es sa sm s0 ee (Value v) vv s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op u /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    alloca_frame ce ee sm s ce ee u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> Cases_on `vv`
  >- (gvs[unwrap_value_def, comp_return_def] >>
      qexists_tac `s` >> simp[gas_marked_path_def, cj 1 gas_path_rules] >>
      conj_tac >- metis_tac[expr_post_of_vv_post_stack] >>
      simp[alloca_frame_def] >> rpt strip_tac >>
      drule_all copy_buffer_local_region_frame >> metis_tac[]) >>
  rename1 `LocatedValue t p` >>
  `p.ptr_location <> LocCalldata` by
    (strip_tac >> gvs[vv_post_def, vv_holds_def]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (`read_result cx (Value v) ee = (INL v,ee)` by simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
      drule_all snapshot_memory_unwrap_frame >> metis_tac[]) >>
  `post_value_type ce e = expr_type e` by gvs[] >>
  `t = post_value_type ce e` by fs[vv_post_def, vv_holds_def] >>
  Cases_on `is_word_type t`
  >- (Cases_on `p.ptr_location = LocCode`
      >- (drule_all snapshot_code_word_frame >> metis_tac[]) >>
      `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by
        (Cases_on `p.ptr_location` >> gvs[]) >>
      metis_tac[snapshot_storage_word_frame]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    fs[vv_operand_def] >>
  `!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
      type_memory_bytes ce t = type_memory_size tvt /\
      type_memory_size tvt < 2**64` by metis_tac[] >>
  Cases_on `p.ptr_location = LocCode`
  >- (irule snapshot_code_composite_frame >> simp[] >> metis_tac[]) >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by
    (Cases_on `p.ptr_location` >> gvs[]) >>
  irule snapshot_storage_composite_frame >> simp[] >>
  qexistsl_tac [`p`,`t`] >> gvs[]
QED

Theorem snapshot_physical_unwrap_frame[local]:
  expr_body_pre ce cx env e es /\
  (do pv <- eval_expr cx e; read_result cx pv od) es = (INL v,ee) /\
  compile_expr ce ty e sc = (vv,se) /\
  unwrap_value ce (vv_with_type (lowered_value_type ce e) vv) sm = (op,sb) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  read_result cx tv ee = (INL v,ee) /\
  vv_post ctx func ce cx e es sa sm s0 ee tv vv s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u stv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    value_has_type stv v /\ val_wf stv v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
    gas_marked_path F ctx func s 0 (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op u /\
    (is_word_type (lowered_value_type ce e) ==>
      eval_operand op u = SOME (typed_val_to_w256 stv v)) /\
    (~is_word_type (lowered_value_type ce e) ==>
      ?w. eval_operand op u = SOME w /\ val_in_memory stv v (w2n w) u.vs_memory) /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    alloca_frame ce ee sm s ce ee u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_all snapshot_physical_unwrap_path >> strip_tac >>
  `vv_holds ce cx (post_value_type ce e) tv vv ee s` by fs[vv_post_def] >>
  `(vv_location vv <> NONE /\ vv_location vv <> SOME LocMemory ==>
    lowered_value_type ce e = post_value_type ce e)` by
    metis_tac[snapshot_changed_type_location] >>
  `unwrap_value ce (vv_with_type (lowered_value_type ce e) vv) =
    unwrap_value ce vv` by
    (irule snapshot_retag_unwrap >>
     goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
     metis_tac[immutable_rhs_post_physical_classify]) >>
  `unwrap_value ce vv sm = (op,sb)` by metis_tac[] >>
  `(post_value_type ce e <> expr_type e ==>
    ((?t a. vv = StackValue t a) \/
     (?t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory /\
       ~is_word_type t)))` by
    (strip_tac >> irule compile_changed_physical_unwrap_shape >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[] >>
     metis_tac[post_value_type_word, post_value_type_nonword]) >>
  `vv_post ctx func ce cx e es sa sm s0 ee (Value v) vv s` by
    metis_tac[vv_post_read_result] >>
  drule_all snapshot_unwrap_frame >> strip_tac >>
  rename1 `expr_post ctx func ce cx e es sa sb s0 ee v op z` >>
  qexistsl_tac [`z`,`stv`] >> simp[] >> conj_tac
  >- (strip_tac >>
      `post_value_type ce e = lowered_value_type ce e` by
        metis_tac[immutable_rhs_post_physical_classify, is_bytestring_word_type] >>
      gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  strip_tac >> drule_all immutable_rhs_physical_memory >> metis_tac[]
QED
