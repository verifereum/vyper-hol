(* Allocation/copy finalization retaining a payload on the actual endpoint. *)
Theory extcallProtFrameUnwrapCopy
Ancestors
  exprExtRequestJointUnwrap exprExtRequestAllocationEndpoint
  exprExtRequestHistory exprSimCopy exprSimAlloc exprSimStorageCopy
  loweringPosts exprLoweringProps compileEnv freshWrites
  gasSummary fragGasMode fragGasPath
  venomState venomExecSemantics emitHelperProps emitHelper
  venomInst context valueEncodingProps loweringStateRelDefs valueEncodingDefs

Theorem extcall_allocated_copy_joint_payload:
  compile_alloc_buffer sz sn = (buf,mid) /\
  fn_has_code sn mid func /\ fn_inst_ids_distinct func /\
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e ee sa sn t ee (Value v) vv t /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ sz < dimword (:256) /\
  ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts /\ ci_mono mid sb /\
  (!u w. gas_marked_path F ctx func t 0 (OK u) /\
    stmt_state_rel ctx func cenv cx ee u /\
    extrequest_history_frame cenv cx ee sn t ee mid u /\
    ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
    u.vs_inst_idx = LENGTH mid.cs_current_insts /\
    eval_operand buf.buf_operand u = SOME w /\ w2n w + sz < dimword (:256) /\
    u.vs_memory = t.vs_memory /\ u.vs_labels = t.vs_labels /\
    contract_storage u = contract_storage t /\
    contract_transient u = contract_transient t /\ ci_mono sn mid /\
    (!aid entry. FLOOKUP t.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region cenv ee.scopes t name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region cenv ee.scopes u name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    FLOOKUP u.vs_allocas sn.cs_next_id = SOME (w2n w,sz) /\
    (!x. not_fresh_at sn x ==> lookup_var x u = lookup_var x t) /\
    local_ptrs_reserved cenv mid /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at mid p) /\
    (cenv.ce_is_ctor ==> !name tv' v' off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv',v') ==>
      regions_disjoint (w2n w) sz off (type_memory_size tv')) ==>
    ?z. gas_marked_path F ctx func u 0 (OK z) /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      copy_static z = copy_static u /\
      (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
      LENGTH u.vs_memory <= LENGTH z.vs_memory /\
      (!off len. regions_disjoint (w2n w) sz off len ==>
        mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
      val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
      val_footprint tv v <= sz /\ eval_operand buf.buf_operand z = SOME w /\ Q z) ==>
  ?z. gas_marked_path F ctx func t 0 (OK z) /\
    expr_post ctx func cenv cx e ee sa sb t ee v buf.buf_operand z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    extrequest_history_frame cenv cx ee sn t ee sb z /\
    (!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k z.vs_memory = mem_bytes_at p k t.vs_memory) /\ Q z
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx ee t` by fs[vv_post_def] >>
  drule_all extrequest_allocation_endpoint >> strip_tac >>
  qpat_x_assum `!u w. _` (qspecl_then [`u`, `w`] mp_tac) >>
  (impl_tac >- (simp[] >>
    metis_tac[])) >> strip_tac >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `mid` >> fs[ci_mono_def]) >>
  `sn.cs_next_id < sb.cs_next_id` by
    (`mid.cs_next_id = sn.cs_next_id + 1` by
       (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
        simp[contextTheory.compile_alloc_buffer_def, emit_op_def, fresh_id_def, fresh_var_def,
          emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
        strip_tac >> gvs[]) >>
     fs[ci_mono_def] >> decide_tac) >>
  `expr_post ctx func cenv cx e ee sa sb t ee v buf.buf_operand z` by
    (irule copy_buffer_post_transport >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`mk_inst sn.cs_next_id ALLOCA [Lit (n2w sz)]
        [STRING #"%" (toString sn.cs_next_var)]`, `mid`, `t`, `sn`, `sz`, `u`, `vv`] >>
     simp[ci_mono_def, venomInstTheory.mk_inst_def] >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!name b len. local_region cenv ee.scopes u name b len ==> _` irule >>
       qexists_tac `name` >> simp[]) >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!aid b len. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==> _` irule >>
       qexists_tac `aid` >> simp[]) >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!off len. regions_disjoint _ _ off len ==> _` mp_tac >>
       disch_then (qspecl_then [`off`, `len`] mp_tac) >>
       simp[regions_disjoint_def]) >>
     conj_tac >- fs[ci_mono_def] >>
     drule_all exprSimAllocTheory.buffer_alloc_code >> simp[venomInstTheory.mk_inst_def]) >>
  `extrequest_history_frame cenv cx ee sn t ee sb z` by
    (irule extrequest_copy_history >> goal_assum (drule_at Any) >>
     qexistsl_tac [`sz`, `w2n w`, `mid`, `u`] >> fs[ci_mono_def] >>
     conj_tac >- fs[copy_static_def] >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!aid b len. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==> _` irule >>
       qexists_tac `aid` >> simp[]) >>
     `z.vs_allocas = u.vs_allocas` by metis_tac[copy_static_fields] >>
     simp[] >> qpat_x_assum `cenv.ce_is_ctor ==> _` ACCEPT_TAC) >>
  `!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
     mem_bytes_at p k z.vs_memory = mem_bytes_at p k t.vs_memory` by
    (map_every qx_gen_tac [`aid`, `old_base`, `old_size`] >> strip_tac >>
     `loweringStateRelDefs$regions_disjoint (w2n w) sz old_base old_size` by metis_tac[] >>
     metis_tac[]) >>
  qexists_tac `z` >> simp[] >>
  `gas_marked_path F ctx func t (0 + 0) (OK z)` by
    (irule gas_marked_path_then >> qexists_tac `u` >> simp[]) >>
  pop_assum mp_tac >> simp[] >> metis_tac[]
QED
