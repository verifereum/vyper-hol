(* A single operational endpoint for allocation, delayed read and store. *)
Theory exprExtRequestMaterializeRead
Ancestors
  exprExtRequestAllocationEndpoint exprExtRequestJointUnwrap
  exprExtRequestHistoryCompose exprExtRequestHistory exprExtRequestMaterialize
  exprOperandVar exprSafeOperand exprLoweringProps exprSimProps exprSimDefs loweringPosts
  gasSummary fragGasMode fragGasPath freshWrites compileEnv venomState
  exprLowering emitHelper valueCopy valueEncodingProps exprSimBufferStore

Theorem extrequest_store_same_no_gas[local]:
  compile_store_memory ce src dst ty ty sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Cases_on `is_word_type ty` >> Cases_on `is_bytestring_type ty` >>
  simp[contextTheory.compile_store_memory_def,
       contextTheory.compile_store_bytestring_def,
       contextTheory.compile_bytestring_copy_len_def,
       contextTheory.compile_copy_memory_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, listTheory.DROP_APPEND,
    venomInstTheory.mk_inst_def] >>
  `!n k:num. n - (n+k) = 0` by decide_tac >>
  simp[] >>
  Cases_on `type_memory_bytes ce ty` >>
  gvs[contextTheory.compile_copy_memory_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, emit_def, emitted_insts_def, listTheory.DROP_APPEND,
      venomInstTheory.mk_inst_def]
QED

Theorem extrequest_materialize_read:
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
  t.vs_inst_idx = LENGTH sn.cs_current_insts ==>
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
       regions_disjoint (w2n w) (type_memory_bytes cenv dty) off (type_memory_size tv))
Proof
  strip_tac >>
  qpat_x_assum `compile_materialize_vv _ _ _ _ = _` mp_tac >>
  simp[compile_materialize_vv_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  gvs[] >>
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
  `extrequest_history_frame cenv cx ec sc tc ee mid u` by
    (irule extrequest_history_frame_trans >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`ee`, `sn`, `t`] >> simp[]) >>
  drule_all (SRULE [] extrequest_joint_unwrap_read) >> strip_tac >>
  `read_result cx r ee = (INL v,ee)` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o SRULE [gas_marked_exec_def, gas_explicit_def]) >>
     disch_then (qspec_then `ee.gas_obs` mp_tac o CONJUNCT1) >> simp[]) >>
  `value_has_type dtv v /\ val_wf dtv v /\ expr_val_rel cx dty v src u'` by
    (fs[expr_post_def] >> metis_tac[]) >>
  `eval_operand buf.buf_operand u' = SOME w /\
   FLOOKUP u'.vs_allocas sn.cs_next_id = SOME (w2n w,type_memory_size dtv)` by
    (fs[extrequest_history_frame_def, eval_operand_def] >> metis_tac[]) >>
  `(!x. src = Var x ==> not_fresh_at sm x)` by
    (`sc.cs_next_var <= mid.cs_next_var` by
       (fs[extrequest_history_frame_def] >> decide_tac) >>
     rpt strip_tac >> drule compiler_unwrap_value_var >>
     disch_then (qspec_then `x` mp_tac) >>
     impl_tac >- (Cases_on `vv` >> fs[exprSafeOperandTheory.safe_operand_def] >>
       metis_tac[freshWritesTheory.not_fresh_at_mono]) >> simp[]) >>
  `(!x. buf.buf_operand = Var x ==> not_fresh_at sm x)` by
    (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  `?sw. eval_operand src u' = SOME sw /\
        val_in_memory dtv v (w2n sw) u'.vs_memory` by
    (qpat_assum `expr_val_rel cx dty v src u'`
       (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
     goal_assum (drule_at Any) >>
     first_x_assum (qspec_then `dtv` mp_tac) >> simp[]) >>
  `if is_word_type dty then sw = typed_val_to_w256 dtv v
   else val_in_memory dtv v (w2n sw) u'.vs_memory` by simp[] >>
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
    (drule extrequest_store_same_no_gas >> fs[listTheory.EVERY_MEM]) >>
  `gas_marked_path F ctx func u' 0 (OK z)` by
    (qunabbrev_tac `z` >> irule extrequest_straight_run_path >>
     simp[] >> qexists_tac `sm` >> simp[]) >>
  `extrequest_history_frame cenv cx ee sn t ee sm u'` by
    (irule extrequest_history_frame_trans >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`ee`, `mid`, `u`] >> simp[]) >>
  `z.vs_allocas = u'.vs_allocas /\ z.vs_alloca_next = u'.vs_alloca_next /\
   z.vs_halted = u'.vs_halted /\ z.vs_current_bb = u'.vs_current_bb` by
    (qpat_assum `t' with <|vs_vars := _; vs_memory := _|> = u'` mp_tac >>
     simp[venom_state_component_equality, Abbr `z`]) >>
  `extrequest_history_frame cenv cx ee sn t ee sb z` by
    (rewrite_tac[extrequest_history_frame_def] >> rpt conj_tac
     >- simp[exprExtRequestReadProbeTheory.extrequest_read_frame_def]
     >- (fs[extrequest_history_frame_def] >> decide_tac)
     >- (fs[extrequest_history_frame_def] >> decide_tac)
     >- simp[]
     >- (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[])
     >- (rpt strip_tac >>
         `not_fresh_at sm x` by
           (fs[extrequest_history_frame_def] >> metis_tac[not_fresh_at_mono]) >>
         `lookup_var x u' = SOME w'` by
           (qpat_assum `extrequest_history_frame _ _ ee sn t ee sm u'`
              (mp_tac o REWRITE_RULE [extrequest_history_frame_def]) >>
            simp[] >> metis_tac[]) >>
         simp[Abbr `z`, lookup_var_def] >>
         qpat_x_assum `!x. not_fresh_at sm x ==> _` (qspec_then `x` mp_tac) >>
         gvs[lookup_var_def])
     >- (qpat_assum `extrequest_history_frame _ _ ee sn t ee sm u'`
            (mp_tac o REWRITE_RULE [extrequest_history_frame_def]) >>
          simp[] >> metis_tac[])
     >- suspend "store_locals"
     >- suspend "store_allocas"
     >> suspend "store_immutables") >>
  suspend "finish"
QED

Resume extrequest_materialize_read[store_locals]:
  rpt strip_tac >>
  `mem_bytes_at b sz u'.vs_memory = mem_bytes_at b sz t.vs_memory` by
    (qpat_assum `extrequest_history_frame _ _ ee sn t ee sm u'`
       (mp_tac o REWRITE_RULE [extrequest_history_frame_def]) >>
     simp[] >> metis_tac[]) >>
  `regions_disjoint (w2n w) (type_memory_size dtv) b sz` by metis_tac[] >>
  simp[Abbr `z`] >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at a len t'.vs_memory = _`
    (qspecl_then [`b`, `sz`] mp_tac) >>
  fs[regions_disjoint_def]
QED

Resume extrequest_materialize_read[store_allocas]:
  rpt strip_tac >>
  `mem_bytes_at b sz u'.vs_memory = mem_bytes_at b sz t.vs_memory` by
    (qpat_assum `extrequest_history_frame _ _ ee sn t ee sm u'`
       (mp_tac o REWRITE_RULE [extrequest_history_frame_def]) >>
     simp[] >> metis_tac[]) >>
  `regions_disjoint (w2n w) (type_memory_size dtv) b sz` by metis_tac[] >>
  simp[Abbr `z`] >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at a len t'.vs_memory = _`
    (qspecl_then [`b`, `sz`] mp_tac) >>
  fs[regions_disjoint_def]
QED

Resume extrequest_materialize_read[store_immutables]:
  rpt strip_tac >>
  `mem_bytes_at off (type_memory_size tv) u'.vs_memory =
   mem_bytes_at off (type_memory_size tv) t.vs_memory` by
    (qpat_assum `extrequest_history_frame _ _ ee sn t ee sm u'`
       (mp_tac o REWRITE_RULE [extrequest_history_frame_def]) >>
     simp[] >> metis_tac[]) >>
  `regions_disjoint (w2n w) (type_memory_size dtv) off (type_memory_size tv)` by
    metis_tac[] >>
  simp[Abbr `z`] >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at a len t'.vs_memory = _`
    (qspecl_then [`off`, `type_memory_size tv`] mp_tac) >>
  fs[regions_disjoint_def]
QED

Resume extrequest_materialize_read[finish]:
  `eval_operand buf.buf_operand z = SOME w` by
    (`not_fresh_at sm p` by metis_tac[] >>
     qpat_x_assum `!x. not_fresh_at sm x ==> _` (qspec_then `p` mp_tac) >>
     simp[Abbr `z`, eval_operand_def, lookup_var_def] >>
     gvs[eval_operand_def, lookup_var_def]) >>
  `expr_val_rel cx dty v buf.buf_operand z` by
    (simp[expr_val_rel_def, Abbr `z`] >> rpt strip_tac >> gvs[]) >>
  qexistsl_tac [`v`, `z`, `w`] >> simp[] >>
  conj_tac >- suspend "gas" >>
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

Resume extrequest_materialize_read[gas]:
  `gas_marked_path F ctx func u 0 (OK u')` by
    fs[gas_marked_exec_def] >>
  `gas_marked_path F ctx func t 0 (OK u')` by
    metis_tac[gas_marked_path_then, arithmeticTheory.ADD] >>
  `gas_marked_path F ctx func t 0 (OK z)` by
    metis_tac[gas_marked_path_then, arithmeticTheory.ADD] >>
  simp[gas_marked_exec_def] >>
  qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >> simp[]
QED

Finalise extrequest_materialize_read
