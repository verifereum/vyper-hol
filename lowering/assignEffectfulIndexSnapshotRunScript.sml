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
  aggregateEvaluatedLayout exprSimIfExpWidenedCounted exprReasonOperand exprOperandVar exprSafeOperand exprSimHypsDefs
  annassignRelayoutSource exprSimHyps

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

(* Whether unwrap returns a label is independent of its compiler cursor. *)
Theorem snapshot_unwrap_not_label_entry[local]:
  unwrap_value ce vv se = (a,sf) /\ (!l. a <> Label l) /\
  unwrap_value ce vv sm = (op,sb) ==>
  !l. op <> Label l
Proof
  Cases_on `vv` >> simp[unwrap_value_def, comp_return_def]
  >- metis_tac[] >>
  Cases_on `is_word_type t` >> simp[]
  >- metis_tac[compile_ptr_load_safe_operand, safe_operand_def] >>
  Cases_on `p.ptr_location = LocMemory` >> simp[comp_return_def]
  >- metis_tac[] >>
  Cases_on `p.ptr_location` >> gvs[compile_ensure_in_memory_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[alloc_buffer_not_label]
QED

Theorem snapshot_compile_unwrap_safe[local]:
  expr_body_pre ce cx env e es /\
  compile_expr ce ty e sc = (vv,se) /\
  unwrap_value ce vv sm = (op,sb) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) ==>
  safe_operand sb op
Proof
  strip_tac >>
  Cases_on `unwrap_value ce vv se` >> rename1 `unwrap_value ce vv se = (a,sf)` >>
  `lower_value compile_expr ce ty e sc = (a,sf)` by
    simp[lower_value_def, comp_bind_def] >>
  `!l. a <> Label l` by
    (irule lower_compile_expr_not_label >>
     goal_assum (drule_at Any) >> qexists_tac `env` >>
     fs[expr_body_pre_def, expr_sim_inv_def]) >>
  `!l. op <> Label l` by metis_tac[snapshot_unwrap_not_label_entry] >>
  simp[safe_operand_def] >> rpt strip_tac >>
  irule compiler_unwrap_value_var >> qexistsl_tac [`ce`,`op`,`sm`,`vv`] >> simp[] >>
  Cases_on `vv` >> fs[vv_operand_def]
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
    safe_operand sb op /\
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
  `safe_operand sb op` by metis_tac[snapshot_compile_unwrap_safe] >>
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

Theorem assign_effectful_snapshot_path:
  expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL pv,ee) /\ read_result cx pv ee = (INL v,ee) /\
  compile_expr ce (expr_type e) e sa = (vv0,sm) /\
  compile_snapshot_vv ce T (vv_with_type (lowered_value_type ce e) vv0) sm = (snap,sb) /\
  vv_post ctx func ce cx e es sa sm s0 ee pv vv0 s /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv0 = Var x ==> not_fresh_at sm x) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u tv w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
    value_has_type tv v /\ val_wf tv v /\
    gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx ee u /\
    eval_operand (vv_operand snap) u = SOME w /\
    (!x. vv_operand snap = Var x ==> not_fresh_at sb x) /\
    (!lbl. vv_operand snap <> Label lbl) /\
    (if is_word_type (lowered_value_type ce e) then
       vv_location snap = NONE /\ w = typed_val_to_w256 tv v
     else vv_location snap = SOME LocMemory /\
       val_in_memory tv v (w2n w) u.vs_memory /\
       ?aid. sm.cs_next_id <= aid /\ aid < sb.cs_next_id /\
         FLOOKUP u.vs_allocas aid =
           SOME (w2n w,type_memory_bytes ce (lowered_value_type ce e)) /\
         (!n b sz. local_region ce ee.scopes u n b sz ==>
           w2n w + type_memory_bytes ce (lowered_value_type ce e) <= b \/
           b+sz <= w2n w)) /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    alloca_frame ce ee sm s ce ee u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `(do pv <- eval_expr cx e; read_result cx pv od) es = (INL v,ee)` by
    simp[vyperStateTheory.bind_def] >>
  Cases_on `is_word_type (lowered_value_type ce e)`
  >- (drule_at (Pat `compile_snapshot_vv _ _ _ _ = _`) assign_effectful_word_snapshot_path >>
      simp[] >> disch_then irule >>
      rpt strip_tac >>
      `vv_type (vv_with_type (lowered_value_type ce e) vv0) = lowered_value_type ce e` by
        (Cases_on `vv0` >> simp[vv_with_type_def, vv_type_def]) >>
      `sb = sk` by fs[compile_snapshot_vv_def, comp_bind_def, comp_return_def] >>
      gvs[] >> drule_all snapshot_physical_unwrap_frame >> strip_tac >>
      qexistsl_tac [`u`,`stv`] >> fs[expr_post_def]) >>
  `vv_type (vv_with_type (lowered_value_type ce e) vv0) = lowered_value_type ce e` by
    (Cases_on `vv0` >> simp[vv_with_type_def, vv_type_def]) >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) sm` >>
  rename1 `compile_alloc_buffer _ sm = (buf,sn)` >>
  Cases_on `unwrap_value ce (vv_with_type (lowered_value_type ce e) vv0) sn` >>
  rename1 `unwrap_value ce _ sn = (op,sk)` >>
  Cases_on `compile_store_memory ce op buf.buf_operand
              (lowered_value_type ce e) (lowered_value_type ce e) sk` >>
  qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
  simp[compile_snapshot_vv_def, compile_materialize_vv_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[] >>
  drule_all immutable_rhs_physical_typed >> strip_tac >>
  `type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e)` by
    (irule immutable_rhs_physical_widens >> qexistsl_tac [`env`,`es`] >>
     simp[vyperTypeSystemTheory.type_widens_to_def]) >>
  `~is_word_type (expr_type e)` by metis_tac[type_widens_to_word] >>
  `type_memory_bytes ce (expr_type e) < 2 ** 64` by
    metis_tac[expr_body_pre_def, alloc_limits_expr_type_alloc_ok, allocLimitsTheory.type_alloc_ok_def] >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >> strip_tac >>
  `type_memory_bytes ce (lowered_value_type ce e) < dimword (:256)` by
    metis_tac[widening_memory_layout_bound] >>
  `ci_mono sm sn` by
    (qspec_then `type_memory_bytes ce (lowered_value_type ce e)`
      (qspec_then `sm` mp_tac) ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono sn sk` by
    (qspecl_then [`ce`,`vv_with_type (lowered_value_type ce e) vv0`,`sn`]
      mp_tac ci_mono_unwrap_value >> simp[]) >>
  `ci_mono sk r` by
    (qspecl_then [`ce`,`op`,`buf.buf_operand`,`lowered_value_type ce e`,
                 `lowered_value_type ce e`,`sk`]
      mp_tac ci_mono_compile_store_memory >> simp[]) >>
  `fn_has_code sm sn func /\ fn_has_code sn sk func /\ fn_has_code sk r func` by
    metis_tac[fragExecTheory.fn_has_code_split, ci_mono_def,
              cs_extends_trans] >>
  `local_ptrs_reserved ce sn /\ local_ptrs_reserved ce sk` by
    metis_tac[local_ptrs_reserved_next_var, ci_mono_def, arithmeticTheory.LESS_EQ_TRANS] >>
  `!u. vv_post ctx func ce cx e es sa sn s0 ee pv vv0 u /\
       ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
       u.vs_inst_idx = LENGTH sn.cs_current_insts ==>
    ?t vty a. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME vty /\
      value_has_type vty v /\ val_wf vty v /\
      gas_marked_path F ctx func u 0 (OK t) /\
      stmt_state_rel ctx func ce cx ee t /\ eval_operand op t = SOME a /\
      safe_operand sk op /\ val_in_memory vty v (w2n a) t.vs_memory /\
      (!z. not_fresh_at sn z ==> lookup_var z t = lookup_var z u) /\
      (!aid entry. FLOOKUP u.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      alloca_frame ce ee sn u ce ee t /\
      ~t.vs_halted /\ t.vs_current_bb = sk.cs_current_bb /\
      t.vs_inst_idx = LENGTH sk.cs_current_insts` by
    (rpt strip_tac >>
     `sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id` by
       (fs[ci_mono_def] >> decide_tac) >>
     `!x. vv_operand vv0 = Var x ==> not_fresh_at sn x` by
       metis_tac[not_fresh_at_mono, ci_mono_def] >>
     drule_all snapshot_physical_unwrap_frame >> strip_tac >>
     gvs[] >> metis_tac[expr_post_def]) >>
  drule_all assign_effectful_alloc_unwrap_path >> strip_tac >>
  `vty = stv` by gvs[] >> gvs[] >>
  `eval_operand (Var x) t = SOME (n2w b)` by simp[eval_operand_def] >>
  `w2n (n2w b : bytes32) = b` by
    (simp[wordsTheory.w2n_n2w] >> fs[wordsTheory.dimword_def] >> decide_tac) >>
  `sm.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < sk.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `!id off n. id < sm.cs_next_id /\ FLOOKUP t.vs_allocas id = SOME (off,n) ==>
    regions_disjoint off n b (type_memory_bytes ce (lowered_value_type ce e))` by
    metis_tac[snapshot_origin_allocations_disjoint] >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  `ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) b
      (type_memory_bytes ce (lowered_value_type ce e))` by
    (drule_at (Pat `MEM _ (fn_insts _)`) snapshot_constructor_allocations_disjoint >>
     simp[mk_inst_def] >> metis_tac[]) >>
  `!z. op = Var z \/ Var x = Var z ==> not_fresh_at sk z` by
    (fs[safe_operand_def] >> metis_tac[not_fresh_at_mono, ci_mono_def]) >>
  `type_memory_size stv < dimword (:256)` by decide_tac >>
  `!name p n. local_region ce ee.scopes t name p n ==>
    p+n <= w2n (n2w b : bytes32) \/ w2n (n2w b : bytes32)+type_memory_size stv <= p` by
    metis_tac[regions_disjoint_def] >>
  Cases_on `is_bytestring_type (lowered_value_type ce e)`
  >- (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)
        assign_effectful_bytes_copy_path >>
      disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `eval_operand op _ = _`)) >>
      simp[] >>
      disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
      disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
      disch_then (qspecl_then [`sm`,`sm.cs_next_id`] mp_tac) >>
      impl_tac >- (gvs[] >> conj_tac
        >- (qpat_x_assum `!z. op = Var z \/ _ ==> _` ACCEPT_TAC) >>
        conj_tac
        >- (rpt strip_tac >>
            qpat_x_assum `!name p n. local_region _ _ _ _ _ _ ==> _ \/ _`
              drule >> simp[arithmeticTheory.ADD_COMM]) >>
        qpat_x_assum `!id off n. _ /\ FLOOKUP _ _ = _ ==> _` ACCEPT_TAC) >>
      strip_tac >>
      suspend "copy_endpoint") >>
  drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)
    assign_effectful_memory_copy_path >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >> simp[] >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (qspecl_then [`sm`,`sm.cs_next_id`] mp_tac) >>
  impl_tac >- (gvs[] >> conj_tac
    >- (rpt strip_tac >>
        qpat_x_assum `!name p n. local_region _ _ _ _ _ _ ==> _ \/ _` drule >>
        simp[arithmeticTheory.ADD_COMM]) >>
    qpat_x_assum `!id off n. _ /\ FLOOKUP _ _ = _ ==> _` ACCEPT_TAC) >>
  strip_tac >> suspend "copy_endpoint"
QED

Resume assign_effectful_snapshot_path[copy_endpoint]:
  markerLib.RESUME_TAC >> (
  `gas_marked_path F ctx func s 0 (OK t')` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `alloca_frame ce ee sm s ce ee t'` by
    (irule alloca_frame_trans >> qexistsl_tac [`ce`,`ee`,`t`,`sm`] >> simp[]) >>
  `!z. not_fresh_at sm z ==> lookup_var z t' = lookup_var z s` by
    (rpt strip_tac >>
     `not_fresh_at sk z` by metis_tac[not_fresh_at_mono,ci_mono_def] >>
     metis_tac[]) >>
  `not_fresh_at r x` by metis_tac[not_fresh_at_mono,ci_mono_def] >>
  qexistsl_tac [`t'`,`n2w b`] >>
  simp[vv_operand_def,vv_location_def,mk_ptr_def] >>
  qexists_tac `sm.cs_next_id` >> simp[] >>
  conj_tac >- (fs[ci_mono_def] >> decide_tac) >>
  rpt strip_tac >>
  qpat_x_assum `!name b' sz. local_region _ _ _ _ _ _ ==> _ \/ _` drule >>
  simp[arithmeticTheory.ADD_COMM])
QED

Finalise assign_effectful_snapshot_path
