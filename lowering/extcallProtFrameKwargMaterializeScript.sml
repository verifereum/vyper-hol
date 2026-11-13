Theory extcallProtFrameKwargMaterialize
Ancestors
  extcallProtFrameTupleHead extcallProtFrameKwargUnwrap
  exprExtRequestMaterializeRead venomState gasSummary fragGasPath fragGasMode
  extcallProtFrameJointUnwrap exprExtRequestAllocationEndpoint
  exprExtRequestHistoryCompose exprExtRequestHistory exprExtRequestMaterialize
  exprOperandVar exprSafeOperand exprLoweringProps exprSimProps exprSimDefs loweringPosts
  freshWrites compileEnv exprLowering emitHelper valueCopy valueEncodingProps
  exprSimBufferStore placeMemoryPrimitiveForward loweringStateRelDefs valueEncodingDefs

Theorem extcall_materialize_store_finalize[local]:
  gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
    [] (INL v) ee (OK u) /\
  gas_marked_path F ctx func u 0 (OK q) /\
  extrequest_history_frame cenv cx ee sn t ee sm u /\
  stmt_state_rel ctx func cenv cx ee t /\
  allocas_non_overlapping u /\
  FLOOKUP u.vs_allocas sn.cs_next_id = SOME (w2n (w:256 word),type_memory_bytes cenv dty) /\
  ci_mono sm sb /\ local_ptrs_reserved cenv sb /\
  (q with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
            vs_inst_idx := u.vs_inst_idx|>) = u /\
  (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x u) /\
  (!a k. loweringStateRelDefs$regions_disjoint a k (w2n w) (type_memory_bytes cenv dty) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k u.vs_memory) /\
  (!name b len. local_region cenv ee.scopes u name b len ==>
    loweringStateRelDefs$regions_disjoint b len (w2n w) (type_memory_bytes cenv dty)) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    loweringStateRelDefs$regions_disjoint off (type_memory_size tv)
      (w2n w) (type_memory_bytes cenv dty)) /\
  (!pa pk. prot pa pk ==> pa + pk <= u.vs_alloca_next /\
    mem_bytes_at pa pk u.vs_memory = mem_bytes_at pa pk M /\
    !i b n. FLOOKUP u.vs_allocas i = SOME (b,n) ==>
      loweringStateRelDefs$regions_disjoint pa pk b n) ==>
  gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
    [] (INL v) ee (OK q) /\
  extrequest_history_frame cenv cx ee sn t ee sb q /\
  (!pa pk. prot pa pk ==> pa + pk <= q.vs_alloca_next /\
    mem_bytes_at pa pk q.vs_memory = mem_bytes_at pa pk M /\
    !i b n. FLOOKUP q.vs_allocas i = SOME (b,n) ==>
      loweringStateRelDefs$regions_disjoint pa pk b n)
Proof
  strip_tac >>
  `q.vs_allocas = u.vs_allocas /\ q.vs_alloca_next = u.vs_alloca_next` by
    (qpat_x_assum `q with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = u`
      mp_tac >> simp[venom_state_component_equality]) >>
  conj_tac
  >- (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_def] >> strip_tac >>
      drule_all gas_marked_path_then >> simp[]) >>
  conj_tac
  >- (irule extcall_tuple_store_history >>
      first_assum (irule_at (Pat `extrequest_history_frame _ _ ee sn t _ _ _`)) >>
      first_assum (irule_at (Pat `stmt_state_rel _ _ _ _ ee t`)) >>
      simp[] >>
      qexistsl_tac [`w2n w`, `type_memory_bytes cenv dty`,
        `type_memory_bytes cenv dty`, `sn.cs_next_id`, `w2n w`] >>
      simp[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem extcall_materialize_read_protected:
  compile_materialize_vv cenv dty vv sn = (dst,sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e es sa sc s0 ec r vv tc /\
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  stmt_state_rel ctx func cenv cx ee t /\
  (case vv of StackValue ty a => safe_operand sc a
   | LocatedValue ty p => safe_operand sc p.ptr_operand) /\
  (!ty p tr w tv.
     vv = LocatedValue ty p /\ p.ptr_location = slot_loc tr /\
     eval_operand p.ptr_operand tc = SOME w /\
     evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
     storage_read_live cx tr (get_storage cx ec tr) w tv) /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
         ~is_word_type (expr_type e) ==>
         type_memory_bytes cenv (expr_type e) = type_memory_size tv /\
         type_memory_size tv < 2**64) /\
  ~is_word_type dty /\ evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_size dtv + 64 < dimword (:256) /\
  (!v src z. read_result cx r ee = (INL v,ee) /\
     expr_val_rel cx (expr_type e) v src z ==>
     value_has_type dtv v /\ val_wf dtv v /\ expr_val_rel cx dty v src z) /\
  ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!pa pk. prot pa pk ==> pa + pk <= t.vs_alloca_next /\
    mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk M /\
    !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
      loweringStateRelDefs$regions_disjoint pa pk b n) ==>
  ?v z w. gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
      [] (INL v) ee (OK z) /\
    stmt_state_rel ctx func cenv cx ee z /\
    extrequest_history_frame cenv cx ee sn t ee sb z /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand dst z = SOME w /\ expr_val_rel cx dty v dst z /\
    value_has_type dtv v /\ val_wf dtv v /\
    w2n w + val_footprint dtv v <= z.vs_alloca_next /\
    FLOOKUP z.vs_allocas sn.cs_next_id = SOME (w2n w,type_memory_bytes cenv dty) /\
    w2n w + type_memory_bytes cenv dty < dimword (:256) /\
    safe_operand sb dst /\
    (!aid b len. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) (type_memory_bytes cenv dty) b len) /\
    (!name b len. local_region cenv ee.scopes t name b len ==>
       regions_disjoint (w2n w) (type_memory_bytes cenv dty) b len) /\
    (!name b len. local_region cenv ee.scopes z name b len ==>
       regions_disjoint (w2n w) (type_memory_bytes cenv dty) b len) /\
    (cenv.ce_is_ctor ==> !name tv v off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
       regions_disjoint (w2n w) (type_memory_bytes cenv dty) off (type_memory_size tv)) /\
    (!pa pk. prot pa pk ==> pa + pk <= z.vs_alloca_next /\
      mem_bytes_at pa pk z.vs_memory = mem_bytes_at pa pk M /\
      !i b n. FLOOKUP z.vs_allocas i = SOME (b,n) ==>
        loweringStateRelDefs$regions_disjoint pa pk b n)
Proof
  strip_tac >>
  qpat_x_assum `compile_materialize_vv _ _ _ _ = _` mp_tac >>
  simp[compile_materialize_vv_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ sn = (buf,mid)` >>
  rename1 `unwrap_value cenv vv mid = (src,sm)` >>
  rename1 `compile_store_memory cenv src buf.buf_operand dty dty sm = ((),sb)` >>
  `ci_mono sm sb` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `ci_mono mid sm` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `cs_extends sn mid` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends mid sm /\ cs_extends sm sb` by fs[ci_mono_def] >>
  `fn_has_code sn mid func /\ fn_has_code mid sm func /\ fn_has_code sm sb func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `stmt_state_rel ctx func cenv cx ec tc` by fs[vv_post_def] >>
  `local_ptrs_reserved cenv sn` by fs[extrequest_history_frame_def] >>
  `type_memory_size dtv < dimword (:256)` by decide_tac >>
  drule_all extrequest_allocation_endpoint >> strip_tac >>
  `!pa pk. prot pa pk ==> pa + pk <= u.vs_alloca_next /\
    mem_bytes_at pa pk u.vs_memory = mem_bytes_at pa pk M /\
    !i b n. FLOOKUP u.vs_allocas i = SOME (b,n) ==>
      loweringStateRelDefs$regions_disjoint pa pk b n` by
    (rpt gen_tac >> disch_tac >> irule extcall_protframe_readonly_path >>
     goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >>
     qexists_tac `prot` >> simp[] >> metis_tac[]) >>
  suspend "unwrap"
QED

Resume extcall_materialize_read_protected[unwrap]:
  `extrequest_history_frame cenv cx ec sc tc ee mid u` by
    (irule extrequest_history_frame_trans >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`ee`, `sn`, `t`] >> simp[]) >>
  drule_all (SRULE [] extcall_joint_unwrap_read_protected) >> strip_tac >>
  `read_result cx r ee = (INL v,ee)` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o SRULE [gas_marked_exec_def, gas_explicit_def]) >>
     disch_then (qspec_then `ee.gas_obs` mp_tac o CONJUNCT1) >> simp[]) >>
  `value_has_type dtv v /\ val_wf dtv v /\ expr_val_rel cx dty v src u'` by
    (fs[expr_post_def] >> metis_tac[]) >>
  `eval_operand buf.buf_operand u' = SOME w /\
   FLOOKUP u'.vs_allocas sn.cs_next_id = SOME (w2n w,type_memory_size dtv)` by
    (fs[extrequest_history_frame_def, eval_operand_def] >> metis_tac[]) >>
  `!x. src = Var x ==> not_fresh_at sm x` by
    (`sc.cs_next_var <= mid.cs_next_var` by
       (fs[extrequest_history_frame_def] >> decide_tac) >>
     rpt strip_tac >> drule compiler_unwrap_value_var >>
     disch_then (qspec_then `x` mp_tac) >>
     impl_tac >- (Cases_on `vv` >> fs[exprSafeOperandTheory.safe_operand_def] >>
       metis_tac[not_fresh_at_mono]) >> simp[]) >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sm x` by
    (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  `?sw. eval_operand src u' = SOME sw /\
        val_in_memory dtv v (w2n sw) u'.vs_memory` by
    (qpat_assum `expr_val_rel cx dty v src u'`
       (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
     goal_assum (drule_at Any) >>
     first_x_assum (qspec_then `dtv` mp_tac) >> simp[]) >>
  `if is_word_type dty then sw = typed_val_to_w256 dtv v
   else val_in_memory dtv v (w2n sw) u'.vs_memory` by simp[] >>
  suspend "store"
QED

Resume extcall_materialize_read_protected[store]:
  drule_all compile_store_memory_run_size_bound_with_capacity >> strip_tac >>
  `stmt_state_rel ctx func cenv cx ee u'` by fs[expr_post_def] >>
  `local_ptrs_reserved cenv sm` by fs[extrequest_history_frame_def] >>
  `!name b len. local_region cenv ee.scopes u' name b len ==>
       regions_disjoint (w2n w) (type_memory_size dtv) b len` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes u name b len` by
       metis_tac[extrequest_history_local_regions] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx ee t'` by
    (irule buffer_store_state_frame >>
     qexistsl_tac [`w2n w`, `type_memory_size dtv`, `u'`, `sm`] >>
     simp[] >> conj_tac
     >- (rpt strip_tac >> fs[regions_disjoint_def] >> metis_tac[]) >>
     fs[regions_disjoint_def] >> metis_tac[]) >>
  qabbrev_tac `z = t' with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `stmt_state_rel ctx func cenv cx ee z` by
    simp[Abbr `z`, stmt_state_rel_inst_idx] >>
  `~u'.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o SRULE [gas_marked_exec_def]) >>
     metis_tac[gas_marked_path_def, fragGasPathTheory.gas_path_normal]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
       ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (drule compile_store_memory_same_type_no_gas >> fs[listTheory.EVERY_MEM]) >>
  `gas_marked_path F ctx func u' 0 (OK z)` by
    (qunabbrev_tac `z` >> irule extrequest_straight_run_path >>
     simp[] >> qexists_tac `sm` >> simp[]) >>
  suspend "frame"
QED

Resume extcall_materialize_read_protected[frame]:
  `extrequest_history_frame cenv cx ee sn t ee sm u'` by
    (irule extrequest_history_frame_trans >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`ee`, `mid`, `u`] >> simp[]) >>
  `(z with <|vs_vars := u'.vs_vars; vs_memory := u'.vs_memory;
              vs_inst_idx := u'.vs_inst_idx|>) = u'` by
    (simp[Abbr `z`] >>
     qpat_x_assum `t' with <|vs_vars := _; vs_memory := _|> = u'` mp_tac >>
     simp[venom_state_component_equality]) >>
  `allocas_non_overlapping u'` by
    fs[stmt_state_rel_def, state_rel_def, venomMemDefsTheory.alloca_inv_def] >>
  `!a k. regions_disjoint a k (w2n w) (type_memory_bytes cenv dty) ==>
    mem_bytes_at a k z.vs_memory = mem_bytes_at a k u'.vs_memory` by
    (simp[Abbr `z`] >> fs[regions_disjoint_def] >> metis_tac[]) >>
  `!name b len. local_region cenv ee.scopes u' name b len ==>
    regions_disjoint b len (w2n w) (type_memory_bytes cenv dty)` by
    (fs[regions_disjoint_def] >> metis_tac[]) >>
  `(cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint off (type_memory_size tv) (w2n w) (type_memory_bytes cenv dty))` by
    (fs[regions_disjoint_def] >> metis_tac[]) >>
  `!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u'` by
    (rpt strip_tac >> simp[Abbr `z`] >>
     qpat_x_assum `!x. not_fresh_at sm x ==> lookup_var x t' = _` drule >>
     simp[lookup_var_def]) >>
  `gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
      [] (INL v) ee (OK u')` by
    (`gas_marked_path F ctx func u 0 (OK u')` by fs[gas_marked_exec_def] >>
     `gas_marked_path F ctx func t 0 (OK u')` by
       metis_tac[gas_marked_path_then, arithmeticTheory.ADD] >>
     simp[gas_marked_exec_def] >>
     qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >> simp[]) >>
  `gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
      [] (INL v) ee (OK z) /\
   extrequest_history_frame cenv cx ee sn t ee sb z /\
   (!pa pk. prot pa pk ==> pa + pk <= z.vs_alloca_next /\
     mem_bytes_at pa pk z.vs_memory = mem_bytes_at pa pk M /\
     !i b n. FLOOKUP z.vs_allocas i = SOME (b,n) ==>
       regions_disjoint pa pk b n)` by
    (irule extcall_materialize_store_finalize >>
     conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`dty`, `sm`, `u'`, `w`] >>
     asm_rewrite_tac []) >>
  suspend "package"
QED

Resume extcall_materialize_read_protected[package]:
  `z.vs_allocas = u'.vs_allocas /\ z.vs_alloca_next = u'.vs_alloca_next /\
   z.vs_halted = u'.vs_halted /\ z.vs_current_bb = u'.vs_current_bb` by
    (qpat_assum `z with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = u'`
      mp_tac >> simp[venom_state_component_equality]) >>
  `eval_operand buf.buf_operand z = SOME w` by
    (`not_fresh_at sm p` by metis_tac[] >>
     qpat_x_assum `!x. not_fresh_at sm x ==> lookup_var x z = _`
       (qspec_then `p` mp_tac) >>
     simp[Abbr `z`, eval_operand_def, lookup_var_def] >>
     gvs[eval_operand_def, lookup_var_def]) >>
  `expr_val_rel cx dty v buf.buf_operand z` by
    (simp[expr_val_rel_def, Abbr `z`] >> rpt strip_tac >> gvs[]) >>
  qexistsl_tac [`v`, `z`, `w`] >> simp[] >>
  conj_tac >- fs[same_blocks_def] >>
  conj_tac >- simp[Abbr `z`] >>
  conj_tac
  >- (`val_footprint dtv v <= type_memory_size dtv` by
        metis_tac[val_footprint_le] >>
      `w2n w + type_memory_size dtv <= u'.vs_alloca_next` by
        (qpat_assum `stmt_state_rel ctx func cenv cx ee u'`
           (mp_tac o REWRITE_RULE [stmt_state_rel_def,
             venomMemDefsTheory.alloca_inv_def,
             venomMemDefsTheory.alloca_next_valid_def]) >>
         strip_tac >>
         qpat_x_assum `!aid base sz. FLOOKUP u'.vs_allocas aid = _ ==> _`
           (qspec_then `sn.cs_next_id` mp_tac) >> simp[]) >> decide_tac) >>
  conj_tac >- (simp[exprSafeOperandTheory.safe_operand_def] >>
               metis_tac[not_fresh_at_mono]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `local_region cenv ee.scopes t name b len` by
        metis_tac[extrequest_history_local_regions] >> metis_tac[]) >>
  metis_tac[]
QED

Finalise extcall_materialize_read_protected
