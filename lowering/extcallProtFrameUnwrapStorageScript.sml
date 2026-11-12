Theory extcallProtFrameUnwrapStorage
Ancestors
  extcallProtFrameUnwrapCopy extcallProtFrameKwargUnwrap
  exprExtRequestJointUnwrap exprExtRequestStoragePath
  exprExtRequestAllocationEndpoint exprExtRequestHistory
  exprSimStorageCopy exprSimAlloc exprSimCopy exprSimUnwrapProps
  loweringPosts exprLoweringProps compileEnv freshWrites
  gasSummary fragGasMode fragGasPath venomState venomExecSemantics
  valueEncodingProps emitHelperProps emitHelper venomInst context
  exprSimUnwrap vyperInterpreter vyperState exprSimProps
  exprLowering exprSimMemorySource loweringStateRelDefs valueEncodingDefs

Theorem extcall_protframe_storage_joint_copy:
  unwrap_value cenv (LocatedValue ty p) sn = (op,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ~is_word_type ty /\ fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     type_memory_bytes cenv ty = type_memory_size tv /\ type_memory_size tv < 2**64) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sn x) /\
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e ee sa sn t ee r (LocatedValue ty p) t /\
  ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!pa pk. prot pa pk ==> pa + pk <= t.vs_alloca_next /\
    mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk M /\
    !pid pb pz. FLOOKUP t.vs_allocas pid = SOME (pb,pz) ==>
      loweringStateRelDefs$regions_disjoint pa pk pb pz) ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
          [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e ee sa sb t ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k u.vs_memory = mem_bytes_at p k t.vs_memory) /\
    extrequest_history_frame cenv cx ee sn t ee sb u /\
    (!pa pk. prot pa pk ==> pa + pk <= u.vs_alloca_next /\
      mem_bytes_at pa pk u.vs_memory = mem_bytes_at pa pk M /\
      !pid pb pz. FLOOKUP u.vs_allocas pid = SOME (pb,pz) ==>
        loweringStateRelDefs$regions_disjoint pa pk pb pz)
Proof
  strip_tac >>
  `ty = expr_type e /\ ?a tv v. eval_operand p.ptr_operand t = SOME a /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    read_result cx r ee = (INL v,ee) /\
    storage_holds cx (p.ptr_location = LocTransient) ty (Value v) a ee t` by
    (Cases_on `p.ptr_location = LocStorage` >>
     gvs[vv_post_def, vv_holds_def, storage_holds_def, read_result_def, return_def] >>
     metis_tac[]) >>
  `vv_post ctx func cenv cx e ee sa sn t ee (Value v) (LocatedValue ty p) t` by
    metis_tac[vv_post_read_result] >>
  `type_memory_bytes cenv ty = type_memory_size tv /\ type_memory_size tv < 2**64` by
    metis_tac[] >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  Cases_on `p.ptr_location = LocStorage` >>
  simp[unwrap_value_def, contextTheory.compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  fs[] >>
  qpat_x_assum `cs'' = sb` (assume_tac o SYM) >> gvs[] >>
  rename1 `compile_alloc_buffer _ sn = (buf,mid)` >>
  `((type_memory_size tv + 31) DIV 32) = type_slot_size tv` by
    simp[type_memory_size_slots] >>
  fs[contextTheory.compile_storage_to_memory_def,
     contextTheory.compile_transient_to_memory_def] >>
  rename1 `fn_has_code sn se func` >>
  `(if type_slot_size tv = 1 then
      comp_bind (emit_op (if p.ptr_location = LocStorage then SLOAD else TLOAD) [p.ptr_operand])
        (\v. emit_void MSTORE [buf.buf_operand; v])
    else comp_ignore_bind
      (compile_word_copy_loop p.ptr_operand buf.buf_operand (type_slot_size tv)
         p.ptr_location LocMemory F) (comp_return ())) mid = ((),se)` by
      gvs[comp_ignore_bind_def, comp_bind_def] >>
  `cs_extends mid se` by
    (irule storage_copy_suffix_extends >> goal_assum (drule_at Any) >> simp[]) >>
  `cs_extends sn mid` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `fn_has_code sn mid func /\ fn_has_code mid se func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `ci_mono mid se` by
    (irule storage_copy_suffix_ci_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `type_memory_size tv < dimword (:256)` by (simp[wordsTheory.dimword_def] >> decide_tac) >>
  `?z. gas_marked_path F ctx func t 0 (OK z) /\
    expr_post ctx func cenv cx e ee sa se t ee v buf.buf_operand z /\
    z.vs_current_bb = se.cs_current_bb /\ z.vs_inst_idx = LENGTH se.cs_current_insts /\
    extrequest_history_frame cenv cx ee sn t ee se z /\
    (!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k z.vs_memory = mem_bytes_at p k t.vs_memory) /\
    (!pa pk. prot pa pk ==> pa + pk <= z.vs_alloca_next /\
      mem_bytes_at pa pk z.vs_memory = mem_bytes_at pa pk M /\
      !pid pb pz. FLOOKUP z.vs_allocas pid = SOME (pb,pz) ==>
        loweringStateRelDefs$regions_disjoint pa pk pb pz)` by
    (irule (BETA_RULE (Q.INST [`Q` |-> `\z. !pa pk. prot pa pk ==>
       pa + pk <= z.vs_alloca_next /\
       mem_bytes_at pa pk z.vs_memory = mem_bytes_at pa pk M /\
       !pid pb pz. FLOOKUP z.vs_allocas pid = SOME (pb,pz) ==>
         loweringStateRelDefs$regions_disjoint pa pk pb pz`]
       (SPEC_ALL extcall_allocated_copy_joint_payload))) >>
     goal_assum (drule_at Any) >> simp[] >>
     reverse conj_tac >- metis_tac[] >>
     qexistsl_tac [`mid`, `type_memory_size tv`] >> simp[] >>
     rpt gen_tac >> strip_tac >>
     `storage_holds cx (p.ptr_location = LocTransient) (expr_type e)
        (Value v) a ee u` by
       gvs[storage_holds_def] >>
     `eval_operand p.ptr_operand u = SOME a` by
       (Cases_on `p.ptr_operand` >> gvs[eval_operand_def] >> metis_tac[]) >>
     `local_ptrs_reserved cenv se` by
       (irule local_ptrs_reserved_next_var >> qexists_tac `mid` >> fs[ci_mono_def]) >>
     `!x. p.ptr_operand = Var x \/ buf.buf_operand = Var x ==> not_fresh_at mid x` by
       (rpt strip_tac >> gvs[] >> irule not_fresh_at_mono >>
        qexists_tac `sn` >> fs[ci_mono_def]) >>
     `type_slot_size tv < 2**256` by (fs[type_memory_size_slots] >> decide_tac) >>
     `?z. gas_marked_path F ctx func u 0 (OK z) /\
       val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
       val_footprint tv v <= type_memory_size tv /\
       LENGTH u.vs_memory <= LENGTH z.vs_memory /\ copy_static z = copy_static u /\
       (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
       (!off len. regions_disjoint (w2n w) (type_memory_size tv) off len ==>
         mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
       z.vs_current_bb = se.cs_current_bb /\ z.vs_inst_idx = LENGTH se.cs_current_insts /\
       extrequest_history_frame cenv cx ee sn t ee se z` by
       (irule extrequest_storage_suffix_joint >> goal_assum (drule_at Any) >>
        fs[ci_mono_def, wordsTheory.dimword_def] >>
        conj_tac >- metis_tac[] >>
        conj_tac >- metis_tac[] >>
        conj_tac >- metis_tac[] >>
        qexistsl_tac [`a`, `buf.buf_operand`, `p.ptr_location`, `p.ptr_operand`, `expr_type e`] >>
        gvs[comp_ignore_bind_def] >> metis_tac[]) >>
     `eval_operand buf.buf_operand z = SOME w` by
       (gvs[eval_operand_def, lookup_var_def] >> metis_tac[]) >>
     `!pa pk. prot pa pk ==> pa + pk <= u.vs_alloca_next /\
       mem_bytes_at pa pk u.vs_memory = mem_bytes_at pa pk M /\
       !pid pb pz. FLOOKUP u.vs_allocas pid = SOME (pb,pz) ==>
         loweringStateRelDefs$regions_disjoint pa pk pb pz` by
       (rpt gen_tac >> disch_tac >> irule extcall_protframe_readonly_path >>
        goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >>
        qexists_tac `prot` >> simp[] >> metis_tac[]) >>
     qexists_tac `z` >> simp[] >>
     conj_tac >- metis_tac[] >>
     rpt gen_tac >> disch_tac >>
     irule extcall_protframe_allocated_write_path >>
     goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >>
     qexistsl_tac [`w2n w`, `type_memory_size tv`] >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
     qexistsl_tac [`w2n w`, `type_memory_size tv`, `sn.cs_next_id`] >> simp[]) >>
  qexistsl_tac [`v`, `z`] >> simp[] >>
  simp[gas_marked_exec_def] >>
  `!tail. read_result cx r (ee with gas_obs := tail) =
      (INL v,ee with gas_obs := tail)` by
    (irule read_result_gas_obs >> simp[]) >>
  metis_tac[]
QED
