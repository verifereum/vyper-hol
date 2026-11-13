(* Argument preparation at an expression boundary, without declared locals. *)
Theory bodyIntCallNRStageFragments
Ancestors
  bodyIntCallFamCallIntStageAllocation bodyIntCallFamCallIntWordStage
  bodyIntCallJointAggCore bodyIntCallJointContract bodyIntCallWindowForcing exprLoweringProps

Theorem intcall_stage_expr_alloc:
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
    fp.jc_lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    u.vs_memory = s.vs_memory /\
    sa.cs_next_id < sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var /\
    (!q. (!x. q = Var x ==> not_fresh_at sa x) ==>
      eval_operand q u = eval_operand q s) /\
    (!name b k. local_region ce es.scopes u name b k <=>
                 local_region ce es.scopes s name b k) /\
    (!name b k. local_region ce es.scopes s name b k ==>
      regions_disjoint (w2n w) sz b k) /\
    (!aid b k p n. FLOOKUP s.vs_allocas aid = SOME (b,k) /\
      aid < sa.cs_next_id /\ b <= p /\ p+n <= b+k ==>
      regions_disjoint p n (w2n w) sz) /\
    (ce.ce_is_ctor ==>
      !name off tv v.
        FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
        FLOOKUP (case ALOOKUP es.immutables fp.jc_cx.txn.target of NONE => FEMPTY
          | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
        regions_disjoint off (type_memory_size tv) (w2n w) sz) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sb p)
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa /\ allocas_above fp.jc_lo s` by
    fs[intcall_expr_res_def] >>
  drule_all intcall_stage_allocation_landing >> strip_tac >>
  `intcall_expr_res fp ce env es sb u` by
    (irule bodyIntCallJointAggCoreTheory.intcall_joint_res_frame >>
     simp[] >> qexistsl_tac [`s`, `sa`] >> simp[] >>
     fs[intcall_expr_res_def] >> metis_tac[]) >>
  `intcall_expr_cont fp ce env es sa s es sb u` by
    (simp[intcall_expr_cont_def, exprSimPropsTheory.locals_kept_mem] >>
     metis_tac[]) >>
  qexistsl_tac [`u`, `w`] >> simp[] >> conj_tac
  >- metis_tac[] >> conj_tac
  >- (map_every qx_gen_tac [`aid0`, `base0`, `len0`, `ptr0`, `size0`] >> strip_tac >>
      `ptr0 + size0 <= base0 + len0` by decide_tac >>
      drule_all intcall_stage_allocation_old_window >> simp[]) >>
  rpt strip_tac >> irule intcall_stage_allocation_immutable_window >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem intcall_stage_expr_word_force:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  unwrap_value ce vv sa = (op,sb) /\
  vv_holds ce fp.jc_cx ty (Value v) vv es s /\ is_word_type ty /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  fn_has_code sa sb fp.jc_func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    expr_val_rel fp.jc_cx ty v op u /\
    intcall_expr_cont fp ce env es sa s es sb u /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\
    (!q. (!x. q = Var x ==> not_fresh_at sa x) ==>
      eval_operand q u = eval_operand q s) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!name b k. local_region ce es.scopes u name b k <=>
                 local_region ce es.scopes s name b k) /\
    (!x. op = Var x ==> not_fresh_at sb x)
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa` by fs[intcall_expr_res_def] >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (mp_tac (Q.SPECL [`ce`, `vv`, `sa`] ci_mono_unwrap_value) >>
     simp[ci_mono_def]) >>
  drule_all intcall_word_forcing_readonly >>
  disch_then (qspec_then `es.scopes` strip_assume_tac) >>
  `allocas_above fp.jc_lo u` by
    (gvs[intcall_expr_res_def, intCallFrameTheory.allocas_above_def] >> metis_tac[]) >>
  `intcall_expr_res fp ce env es sb u` by
    (irule bodyIntCallJointAggCoreTheory.intcall_joint_res_frame >>
     simp[] >> qexistsl_tac [`s`, `sa`] >> simp[] >>
     fs[intcall_expr_res_def] >> metis_tac[]) >>
  qexists_tac `u` >> simp[intcall_expr_cont_def]
QED

(* Win may contain any previous snapshot subwindows.  Full old allocations
   are retained as well, to discharge the guarded continuation frame. *)
Theorem intcall_stage_expr_window_force:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  unwrap_value ce vv sa = (op,sb) /\ vv_holds ce fp.jc_cx ty r vv es s /\
  read_result fp.jc_cx r es = (INL v,es) /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  (!p k. Win p k ==> ?aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len) /\
  (ty <> NoneT /\ ~is_word_type ty /\ ~is_bytestring_type ty /\
    (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
    ?w a k. eval_operand (vv_operand vv) s = SOME w /\
      a <= w2n w /\ w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
      (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z)) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    expr_val_rel fp.jc_cx ty v op u /\
    intcall_expr_cont fp ce env es sa s es sb u /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!p k. Win p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!name b k. local_region ce es.scopes u name b k <=>
                 local_region ce es.scopes s name b k) /\
    (!sv. sv.cs_next_id <= sa.cs_next_id /\ vv_at ce fp.jc_cx ty sv sa es r vv s ==>
      expr_val_at ce fp.jc_cx ty sv sb es v op u) /\
    (!sv. sv.cs_next_id <= sa.cs_next_id /\ vv_own ce fp.jc_cx ty sv sa es r vv s ==>
      expr_val_own ce fp.jc_cx ty sv sb es v op u) /\
    (!x. op = Var x ==> not_fresh_at sb x) /\
    (ty <> NoneT /\ ~is_word_type ty /\ ~is_bytestring_type ty ==>
      ?w a k. eval_operand op u = SOME w /\ a <= w2n w /\
        w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
        (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z))
Proof
  strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (mp_tac (Q.SPECL [`ce`, `vv`, `sa`] ci_mono_unwrap_value) >> simp[ci_mono_def]) >>
  qpat_assum `intcall_expr_res _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [intcall_expr_res_def]) >>
  `!p k. fp.jc_prot p k ==> p+k <= fp.jc_lo` by fs[intcall_frame_ok_def] >>
  qabbrev_tac `Old = \p k. ?aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len` >>
  mp_tac (Q.INST [`Win` |-> `Old`, `reserved` |-> `\q. fp.jc_reserved q \/ reserved q`,
    `P` |-> `fp.jc_prot`, `lo` |-> `fp.jc_lo`, `staged` |-> `fp.jc_staged`,
    `scopes` |-> `es.scopes`, `ctx` |-> `fp.jc_ctx`, `func` |-> `fp.jc_func`,
    `cx` |-> `fp.jc_cx`] protected_value_window_forcing) >>
  (impl_tac >- (simp[Abbr `Old`] >> metis_tac[])) >> strip_tac >>
  `intcall_expr_res fp ce env es sb u` by
    (irule bodyIntCallJointAggCoreTheory.intcall_joint_res_frame >>
     simp[] >> qexistsl_tac [`s`, `sa`] >> simp[] >> metis_tac[]) >>
  `intcall_expr_cont fp ce env es sa s es sb u` by
    (simp[intcall_expr_cont_def] >> rpt strip_tac >>
     qpat_x_assum `!p k. Old p k ==> _` irule >>
     simp[Abbr `Old`] >> goal_assum (drule_at Any) >> simp[]) >>
  `!p k. Win p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory` by
    (rpt strip_tac >> qpat_x_assum `!p k. Old p k ==> _` irule >>
     simp[Abbr `Old`] >> gvs[]) >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    metis_tac[bodyIntCallJointForceTheory.unwrap_value_operand_reserved] >>
  qexists_tac `u` >> simp[] >> metis_tac[]
QED
