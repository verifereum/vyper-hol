(* Expression-resource allocation and forcing boundaries for argument staging. *)
Theory bodyIntCallStageEndpointLanding
Ancestors
  bodyIntCallJointAggCore bodyIntCallJointForce bodyIntCallWindowLanding
  bodyIntCallJointContract bodyIntCallHeldFrame exprSimVVFrame
  bodyIntCallFamCallIntAllocationGeometry
  bodyIntCallStageEndpointForceFrame bodyIntCallStageEndpointForceGeometry
  bodyIntCallFamStmtLogArgsFrame
  exprSimProps exprSimCopy exprLoweringProps freshWrites

Theorem intcall_stage_allocation_cont:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  sa.cs_next_var <= sb.cs_next_var /\
  s.vs_alloca_next <= u.vs_alloca_next /\ allocas_above fp.jc_lo u /\
  u.vs_memory = s.vs_memory /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!name b sz. local_region ce es.scopes u name b sz <=>
    local_region ce es.scopes s name b sz) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  intcall_expr_cont fp ce env es sa s es sb u
Proof
  strip_tac >>
  `!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op s` by
    (rpt strip_tac >>
     `?x w. op = Var x /\ lookup_var x fp.jc_oorig = SOME w` by
       metis_tac[intcall_frame_ok_def] >>
     gvs[venomStateTheory.eval_operand_def] >>
     `not_fresh_at sa x` by metis_tac[intcall_expr_res_def] >> simp[]) >>
  `intcall_expr_res fp ce env es sb u` by
    (irule bodyIntCallJointAggCoreTheory.intcall_joint_res_frame >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  simp[intcall_expr_cont_def] >>
  irule exprSimPropsTheory.locals_kept_mem >> simp[]
QED

Theorem intcall_stage_expr_alloc_landing:
  compile_alloc_buffer sz sa = (buf,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  sz < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es sa s es sb u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    fp.jc_lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    u.vs_memory = s.vs_memory /\
    contract_storage u = contract_storage s /\
    contract_transient u = contract_transient s /\
    sa.cs_next_id < sb.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op u = eval_operand op s) /\
    (!name b len. local_region ce es.scopes u name b len <=>
      local_region ce es.scopes s name b len) /\
    (!name b len. local_region ce es.scopes u name b len ==>
      regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sb p)
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa /\ allocas_above fp.jc_lo s /\
   (!q x. fp.jc_reserved q /\ q = Var x ==> not_fresh_at sa x)` by
    fs[intcall_expr_res_def] >>
  drule_all (SRULE [] (Q.INST
    [`reserved` |-> `\q. !x. q = Var x ==> not_fresh_at sa x`]
    bodyIntCallWindowLandingTheory.materialization_alloc_landing)) >> strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id < sb.cs_next_id` by
    (drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[]) >>
  `!name b len. local_region ce es.scopes u name b len <=>
    local_region ce es.scopes s name b len` by
    metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame] >>
  `intcall_expr_cont fp ce env es sa s es sb u` by
    (irule intcall_stage_allocation_cont >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`u`, `w`] >>
  simp[venomStateTheory.contract_storage_def,
       venomStateTheory.contract_transient_def] >> metis_tac[]
QED

(* Allocation preserves the producer's original ownership interval. *)
Theorem intcall_stage_alloc_value_landing:
  compile_alloc_buffer sz sa = (buf,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  sz < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  vv_holds ce fp.jc_cx ty r vv es s /\
  vv_at ce fp.jc_cx ty origin sa es r vv s /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) ==>
  ?u w. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es sa s es sb u /\
    vv_holds ce fp.jc_cx ty r vv es u /\
    vv_at ce fp.jc_cx ty origin sb es r vv u /\
    eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    fp.jc_lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    u.vs_memory = s.vs_memory /\
    sa.cs_next_id < sb.cs_next_id /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op u = eval_operand op s) /\
    (!name b len. local_region ce es.scopes u name b len <=>
      local_region ce es.scopes s name b len) /\
    (!name b len. local_region ce es.scopes u name b len ==>
      regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sb p) /\
    (!v tv src. read_result fp.jc_cx r es = (INL v,es) /\
      evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
      eval_operand (vv_operand vv) u = SOME src /\
      (case vv of StackValue _ _ => ~is_word_type ty
        | LocatedValue _ p => p.ptr_location = LocMemory) /\
      val_footprint tv v <> 0 ==>
      regions_disjoint (w2n src) (val_footprint tv v) (w2n w) sz)
Proof
  strip_tac >> drule_all intcall_stage_expr_alloc_landing >> strip_tac >>
  `eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s` by
    metis_tac[] >>
  `vv_holds ce fp.jc_cx ty r vv es u` by
    (irule vv_holds_vars_frame >> goal_assum (drule_at Any) >> simp[]) >>
  `vv_at ce fp.jc_cx ty origin sb es r vv u` by
    (irule held_vv_at_alloc_frame >> goal_assum (drule_at Any) >>
     fs[intcall_expr_cont_def] >> qexists `sa` >> simp[]) >>
  qexistsl_tac [`u`, `w`] >> simp[] >> conj_tac
  >- metis_tac[] >> rpt strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
   (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry)` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  `!name b len. local_region ce es.scopes s name b len ==>
     regions_disjoint (w2n w) sz b len` by metis_tac[] >>
  drule_all intcall_vv_at_allocation_disjoint >> simp[]
QED

Theorem intcall_stage_alloc_force_landing:
  compile_alloc_buffer sz sa = (buf,sm) /\
  unwrap_value ce vv sm = (op,sb) /\
  fn_has_code sa sm fp.jc_func /\ fn_has_code sm sb fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  sz < dimword (:256) /\ origin.cs_next_id <= sa.cs_next_id /\
  vv_holds ce fp.jc_cx ty (Value v) vv es s /\
  vv_at ce fp.jc_cx ty origin sa es (Value v) vv s /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (ty <> NoneT /\ ~is_word_type ty /\ ~is_bytestring_type ty /\
    (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
    ?w a k. eval_operand (vv_operand vv) s = SOME w /\
      a <= w2n w /\ w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
      (fp.jc_lo <= a \/ ?d z. fp.jc_staged d z /\ d <= a /\ a+k <= d+z)) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es sa s es sb u /\
    expr_val_rel fp.jc_cx ty v op u /\
    expr_val_at ce fp.jc_cx ty origin sb es v op u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    fp.jc_lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    sa.cs_next_id < sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sb x) /\
    (!x. op = Var x ==> not_fresh_at sb x) /\
    (!name a k. local_region ce es.scopes u name a k ==>
      regions_disjoint (w2n w) sz a k) /\
    (!src. ~is_word_type ty /\ val_footprint tv v <> 0 /\ eval_operand op u = SOME src ==>
      regions_disjoint (w2n src) (val_footprint tv v) (w2n w) sz) /\
    (ty <> NoneT /\ ~is_word_type ty /\ ~is_bytestring_type ty ==>
      ?src a k. eval_operand op u = SOME src /\ a <= w2n src /\
        w2n src + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
        (fp.jc_lo <= a \/ ?d z. fp.jc_staged d z /\ d <= a /\ a+k <= d+z))
Proof
  strip_tac >> drule_all intcall_stage_alloc_value_landing >>
  disch_then (qx_choosel_then [`t`, `dw`] strip_assume_tac) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sb.cs_next_var /\
   sm.cs_next_id <= sb.cs_next_id` by
    (mp_tac (Q.SPECL [`ce`, `vv`, `sm`] ci_mono_unwrap_value) >>
     drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[ci_mono_def]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es t /\
   local_ptrs_reserved ce sm /\ allocas_above fp.jc_lo t /\
   ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
   t.vs_inst_idx = LENGTH sm.cs_current_insts /\
   (!q x. fp.jc_reserved q /\ q = Var x ==> not_fresh_at sm x)` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  qabbrev_tac `Win = \p k. ?id. id < sm.cs_next_id /\ FLOOKUP t.vs_allocas id = SOME (p,k)` >>
  mp_tac (Q.INST [`sa` |-> `sm`, `s` |-> `t`,
    `ctx` |-> `fp.jc_ctx`, `cx` |-> `fp.jc_cx`, `func` |-> `fp.jc_func`,
    `lo` |-> `fp.jc_lo`, `staged` |-> `fp.jc_staged`, `P` |-> `fp.jc_prot`,
    `reserved` |-> `\q. fp.jc_reserved q \/ q = buf.buf_operand`,
    `Win` |-> `Win`, `scopes` |-> `es.scopes`,
    `aid` |-> `sa.cs_next_id`, `b` |-> `w2n (dw:256 word)`, `cap` |-> `sz`]
      (SPEC_ALL intcall_stage_protected_forcing)) >>
  (impl_tac >- (simp[Abbr `Win`] >>
    fs[intcall_frame_ok_def, vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
    map_every qx_gen_tac [`off`, `len`] >> strip_tac >>
    qexistsl_tac [`id`, `off`, `len`] >> simp[])) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `intcall_expr_res fp ce env es sm t` by fs[intcall_expr_cont_def] >>
  `intcall_expr_cont fp ce env es sm t es sb u` by
    (irule intcall_stage_forcing_cont >> simp[] >>
     fs[Abbr `Win`] >> metis_tac[]) >>
  `intcall_expr_cont fp ce env es sa s es sb u` by
    (irule intcall_expr_cont_trans >> simp[] >>
     qexistsl_tac [`es`, `sm`, `t`] >> simp[]) >>
  `eval_operand buf.buf_operand u = SOME dw` by metis_tac[] >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sb x` by
    (simp[] >> irule not_fresh_at_mono >> qexists `sm` >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    metis_tac[unwrap_value_operand_reserved] >>
  qexistsl_tac [`u`, `dw`] >> simp[] >>
  conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
        (SPEC_ALL fragGasModeTheory.gas_marked_path_then))) >>
      qexists `t` >> simp[]) >>
  gvs[]
QED
