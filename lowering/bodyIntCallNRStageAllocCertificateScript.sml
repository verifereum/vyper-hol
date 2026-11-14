(* Read-only allocation and single-value certificate transport. *)
Theory bodyIntCallNRStageAllocCertificate
Ancestors
  bodyIntCallNRStageFragments bodyIntCallJointCallCore abiEncodeMaterialize
  exprSimVVFrame exprSimCopy exprLoweringProps bodyIntCallJointContract
  bodyIntCallFamCallIntStageAllocation

Theorem intcall_stage_alloc_readonly_landing:
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
    contract_storage u = contract_storage s /\
    contract_transient u = contract_transient s /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    s.vs_alloca_next <= u.vs_alloca_next /\
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
  mp_tac (Q.INST [`reserved` |-> `\q. !x. q = Var x ==> not_fresh_at sa x`,
    `sm` |-> `sb`, `ctx` |-> `fp.jc_ctx`, `func` |-> `fp.jc_func`,
    `cx` |-> `fp.jc_cx`, `lo` |-> `fp.jc_lo`]
    (SPEC_ALL bodyIntCallWindowLandingTheory.materialization_alloc_landing)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!name b k. local_region ce es.scopes u name b k <=>
                local_region ce es.scopes s name b k` by
    (rpt strip_tac >> irule copy_buffer_local_region_frame >> metis_tac[]) >>
  `sa.cs_next_id < sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.fresh_id_def,
       compileEnvTheory.fresh_var_def, compileEnvTheory.emit_def] >>
     strip_tac >> gvs[]) >>
  `intcall_expr_res fp ce env es sb u` by
    (irule bodyIntCallJointAggCoreTheory.intcall_joint_res_frame >>
     simp[] >> qexistsl_tac [`s`, `sa`] >> simp[] >>
     fs[intcall_expr_res_def] >> metis_tac[]) >>
  `intcall_expr_cont fp ce env es sa s es sb u` by
    (simp[intcall_expr_cont_def, exprSimPropsTheory.locals_kept_mem] >> metis_tac[]) >>
  qexistsl_tac [`u`, `w`] >>
  simp[venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (map_every qx_gen_tac [`aid0`, `base0`, `len0`, `ptr0`, `size0`] >>
      strip_tac >> `ptr0 + size0 <= base0 + len0` by decide_tac >>
      drule_all intcall_stage_allocation_old_window >> simp[]) >>
  rpt strip_tac >> irule intcall_stage_allocation_immutable_window >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem intcall_stage_alloc_value_certificate:
  vv_holds ce cx ty r vv es s /\ vv_at ce cx ty a b es r vv s /\
  (Own ==> vv_own ce cx ty a b es r vv s) /\
  u.vs_memory = s.vs_memory /\
  contract_storage u = contract_storage s /\
  contract_transient u = contract_transient s /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!name off len. local_region ce es.scopes u name off len <=>
                  local_region ce es.scopes s name off len) /\
  b.cs_next_id <= d.cs_next_id /\
  (ty <> NoneT /\ ~is_word_type ty /\ ~is_bytestring_type ty /\
    (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
    ?w off len. eval_operand (vv_operand vv) s = SOME w /\
      off <= w2n w /\ w2n w + type_memory_size tv <= off+len /\
      off+len < dimword (:256) /\
      (lo <= off \/ ?base size. staged base size /\ base <= off /\ off+len <= base+size)) ==>
  vv_holds ce cx ty r vv es u /\ vv_at ce cx ty a d es r vv u /\
  (Own ==> vv_own ce cx ty a d es r vv u) /\
  (ty <> NoneT /\ ~is_word_type ty /\ ~is_bytestring_type ty /\
    (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
    ?w off len. eval_operand (vv_operand vv) u = SOME w /\
      off <= w2n w /\ w2n w + type_memory_size tv <= off+len /\
      off+len < dimword (:256) /\
      (lo <= off \/ ?base size. staged base size /\ base <= off /\ off+len <= base+size))
Proof
  strip_tac >> conj_tac
  >- (irule vv_holds_vars_frame >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (irule materialize_vv_at_alloc_frame >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[]) >>
  conj_tac
  >- (strip_tac >> irule intcall_vv_own_frame >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED
