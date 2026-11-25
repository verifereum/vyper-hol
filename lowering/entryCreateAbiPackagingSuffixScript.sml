(* The common normal ABI packaging suffix on its actual installed cuts. *)
Theory entryCreateAbiPackagingSuffix
Ancestors
  bodyFullAbiEncodeArgs entryCreateAbiSetupSegment entryCreateAbiFinishSegment
  entryCreateAbiPackagingBind entryCreateIntervalLayout entryCreateRegionLift
  bodyFullAbiEncodeAllocOrigin bodyFullAbiEncodeSetupTail bodyFullAbiEncodeFinish
  abiBuiltinEncodeCode abiBuiltinAllocation abiEncoderProps exprSimAbiDecodeSiteCoverage
  venomExecSemantics venomInst words
  entryCreateFocusSpec entryCreateCompletedCut entryCreatePathScope createSizePrefixReplay
  createSizeCutCode createSizeCutRegion compileEnv gasSummary list arithmetic

Definition abi_packaging_segment_def:
  abi_packaging_segment E ctx f a b s t <=>
    create_operand_at a s /\ create_operand_full_scope a b E ctx f s [] (OK t)
End

Triviality packaging_segment_join:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_layout a b /\ create_cut_code {} a m /\ create_cut_code {} m b /\
  fn_has_code a m f /\ create_operand_at a s /\
  abi_packaging_segment E ctx f a m s u /\
  abi_packaging_segment E ctx f m b u t ==>
  abi_packaging_segment E ctx f a b s t
Proof
  strip_tac >>
  `create_cut_region a m s` by
    (irule (cj 1 create_cut_region_rules) >> fs[create_operand_at_def] >>
     qexists_tac `f` >> simp[]) >>
  `cs_extends a m /\ cs_extends m b /\ a.cs_next_id <= m.cs_next_id /\
   m.cs_next_id <= b.cs_next_id` by fs[create_cut_code_def] >>
  fs[abi_packaging_segment_def,create_operand_full_scope_def] >>
  `create_expr_prefix a b E ctx f s [] u` by
    (irule create_left_prefix_lift_at >> first_assum (irule_at Any) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     metis_tac[create_layout_left_stop]) >>
  `create_expr_prefix a b E ctx f u [] t` by
    (irule create_expr_prefix_mono >> first_assum (irule_at Any) >>
     simp[create_prefix_step_def,frag_ids_def] >> metis_tac[LESS_EQ_TRANS]) >>
  metis_tac[SIMP_RULE (srw_ss()) [] (Q.INST [`left` |-> `[]`,`right` |-> `[]`]
    create_expr_prefix_append)]
QED

Triviality packaging_alloc_phase:
  compile_alloc_buffer n a = (buf,b) ==>
  abi_packaging_alloc_law (abi_packaging_segment E ctx f) ctx f E PG lo a b n buf H
Proof
  strip_tac >> pure_rewrite_tac[abi_packaging_alloc_law_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all (INST_TYPE [Type.beta |-> ``:256``] abi_encode_alloc_origin_run) >>
  disch_then (qspecl_then [`tn`,`E`,`PG`,`G`] strip_assume_tac) >>
  qexistsl_tac [`q`,`w`,`t`,`G'`,`tn'`] >>
  reverse conj_tac >- asm_rewrite_tac[] >>
  simp[abi_packaging_segment_def,create_operand_at_def] >>
  qpat_assum `t = raw with vs_inst_idx := _` (fn th => once_rewrite_tac[th]) >>
  drule (cj 1 abi_encode_setup_scoped_phases) >>
  disch_then (irule o cj 1) >> simp[create_operand_at_def]
QED

Triviality packaging_setup_phase:
  abi_builtin_encode_method_id mid buf a = ((),method_st) /\
  emit_op ADD [buf;Lit (n2w (32+k))] method_st = (data,b) ==>
  abi_packaging_setup_law (abi_packaging_segment E ctx f) ctx f E PG lo
    a method_st b mid data k N maxlen
Proof
  strip_tac >> pure_rewrite_tac[abi_packaging_setup_law_def] >>
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.INST [`explicit` |-> `E`,`func` |-> `f`,`ready` |-> `b`] abi_encode_setup_tail_origin_run) >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  qexistsl_tac [`dp`,`t`,`G'`,`tn'`] >>
  reverse conj_tac >- rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  simp[abi_packaging_segment_def,create_operand_at_def] >>
  qpat_assum `t = raw with vs_inst_idx := _` (fn th => once_rewrite_tac[th]) >>
  `emit_op ADD [buf;Lit (n2w (32+(case mid of NONE => 0 | SOME _ => 4)))]
    method_st = (data,b)` by metis_tac[] >>
  drule_all (cj 2 abi_encode_setup_scoped_phases) >>
  disch_then (irule o cj 1) >> simp[create_operand_at_def]
QED

Triviality packaging_finish_phase:
  abi_builtin_encode_finish buf lenop k a = ((),b) ==>
  abi_packaging_finish_law (abi_packaging_segment E ctx f) ctx f E PG lo a b lenop k
Proof
  strip_tac >> pure_rewrite_tac[abi_packaging_finish_law_def] >>
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.INST [`explicit` |-> `E`,`func` |-> `f`] abi_encode_finish_origin_run) >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  qexistsl_tac [`t`,`G'`,`tn'`] >>
  reverse conj_tac >- rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  simp[abi_packaging_segment_def,create_operand_at_def] >>
  `create_operand_at a s` by simp[create_operand_at_def] >>
  drule_all abi_encode_finish_scoped_phase >> disch_then (irule o cj 2) >> simp[]
QED

Triviality packaging_alloc_code:
  compile_alloc_buffer n a = (buf,b) ==>
  create_cut_code {} a b /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code a b)
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  conj_tac >- metis_tac[SIMP_RULE (srw_ss()) [create_cut_targets_def]
    (Q.INST [`opc` |-> `ALLOCA`] create_cut_code_emit_op),pairTheory.SND] >>
  drule exprLoweringPropsTheory.emit_op_extends >> strip_tac >>
  drule abi_encode_setup_alloc_layout >> strip_tac >>
  fs[exprLoweringPropsTheory.same_blocks_def,exprSimAbiGasBridgeTheory.frag_code_def,
     fragExecTheory.emitted_blocks_def,EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[]
QED

Triviality packaging_method_blocks:
  abi_builtin_encode_method_id mid buf a = ((),b) ==> b.cs_blocks = a.cs_blocks
Proof
  Cases_on `mid` >>
  simp[abi_builtin_encode_method_id_def,comp_bind_def,comp_ignore_bind_def,
       comp_return_def,emitHelperTheory.emit_op_def,emitHelperTheory.emit_void_def,
       fresh_var_def,fresh_id_def,emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Triviality packaging_setup_code:
  abi_builtin_encode_method_id mid buf a = ((),m) /\
  emit_op ADD [buf;Lit (n2w (32+(case mid of NONE => 0 | SOME _ => 4)))] m = (data,b) ==>
  create_cut_code {} a b /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code a b)
Proof
  strip_tac >> drule_all abi_encode_setup_tail_layout >> strip_tac >>
  drule packaging_method_blocks >> strip_tac >>
  drule exprLoweringPropsTheory.emit_op_extends >> strip_tac >>
  `ci_mono a m` by metis_tac[ci_mono_abi_builtin_encode_method_id,pairTheory.SND] >>
  `ci_mono m b` by metis_tac[exprLoweringPropsTheory.ci_mono_emit_op,pairTheory.SND] >>
  `ci_mono a b` by metis_tac[exprLoweringPropsTheory.ci_mono_trans] >>
  fs[exprLoweringPropsTheory.ci_mono_def,exprLoweringPropsTheory.same_blocks_def] >>
  simp[create_cut_code_def,exprSimAbiGasBridgeTheory.frag_code_def,fragExecTheory.emitted_blocks_def] >>
  fs[EVERY_MEM] >> rpt conj_tac >> rpt gen_tac >> disch_tac >>
  qpat_assum `!i. MEM i (emitted_insts a b) ==> _` (drule_then strip_assume_tac) >>
  simp[create_cut_targets_def]
QED

Triviality packaging_finish_code:
  abi_builtin_encode_finish buf len k a = ((),b) ==>
  create_cut_code {} a b /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code a b)
Proof
  strip_tac >> drule abi_encode_finish_fetch_inventory >> strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  `cs_extends a b /\ a.cs_next_id <= b.cs_next_id` by
    (simp[cs_extends_same_block] >> decide_tac) >>
  simp[create_cut_code_def,exprSimAbiGasBridgeTheory.frag_code_def,fragExecTheory.emitted_blocks_def] >>
  fs[EVERY_MEM] >> rpt conj_tac >> rpt gen_tac >> disch_tac >>
  ntac 2 (qpat_x_assum `!i. MEM i (emitted_insts a b) ==> _` (drule_then strip_assume_tac)) >>
  simp[create_cut_targets_def] >>
  rpt (COND_CASES_TAC >> fs[is_terminator_def])
QED

Triviality packaging_inventory_join:
  create_cut_code {} a m /\ create_cut_code {} m b /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code a m) /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code m b) ==>
  create_cut_code {} a b /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code a b)
Proof
  strip_tac >> conj_tac >- metis_tac[create_cut_code_join] >>
  fs[create_cut_code_def,EVERY_MEM] >>
  drule_all abi_decode_frag_code_compose >> metis_tac[]
QED

(* This is the compiler itinerary, independent of the runtime witnesses. *)
Definition abi_packaging_site_def:
  abi_packaging_site ce single svs tys meth k N out st sb
    buf allocated method_st data_ptr ready len body_end <=>
  compile_alloc_buffer N st = (buf,allocated) /\
  buf.buf_operand = out /\
  abi_builtin_encode_method_id meth out allocated = ((),method_st) /\
  emit_op ADD [out; Lit (n2w (32+k))] method_st = (data_ptr,ready) /\
  compile_abi_encode_payload ce single svs tys data_ptr ready = (len,body_end) /\
  abi_builtin_encode_finish out len k body_end = ((),sb)
End

Triviality packaging_site_exists:
  lower_abi_encode meth maxlen (compile_abi_encode_payload ce single svs tys) st = (out,sb) /\
  k = (case meth of NONE => 0 | SOME _ => 4) /\ N = 32 + 32 * word_size (maxlen+k) ==>
  ?buf allocated method_st data_ptr ready len body_end.
    abi_packaging_site ce single svs tys meth k N out st sb
      buf allocated method_st data_ptr ready len body_end
Proof
  strip_tac >> drule lower_abi_encode_trace >> strip_tac >>
  drule abi_builtin_encode_setup_trace >> strip_tac >>
  gvs[abi_packaging_site_def] >> metis_tac[]
QED

Triviality packaging_static_parts:
  abi_packaging_site ce single svs tys meth k N out st sb
    buf allocated method_st data_ptr ready len body_end /\
  k = (case meth of NONE => 0 | SOME _ => 4) ==>
  (create_cut_code {} st allocated /\
   EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code st allocated)) /\
  (create_cut_code {} allocated ready /\
   EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code allocated ready)) /\
  (create_cut_code {} body_end sb /\
   EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code body_end sb))
Proof
  simp[abi_packaging_site_def] >> strip_tac >>
  drule packaging_alloc_code >> strip_tac >>
  drule packaging_finish_code >> strip_tac >>
  `create_cut_code {} allocated ready /\
   EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code allocated ready)` by
    (irule packaging_setup_code >> qexistsl_tac [`out`,`data_ptr`,`method_st`,`meth`] >>
     qpat_assum `k = _` (fn th => rewrite_tac[GSYM th]) >>
     once_rewrite_tac[ADD_COMM] >> asm_rewrite_tac[]) >> fs[]
QED

(* The caller supplies just the active encoder phase. The separate static
   input rules out native hits whether or not the list has a normal exit. *)
Definition abi_packaging_payload_phases_def:
  abi_packaging_payload_phases Seg RowSide ctx func explicit PG lo ce cx st0 DF d
    single tys args svs k N st ready data_ptr len body_end <=>
    (single ==> !src unwrap_end.
      unwrap_value ce (HD svs) ready = (src,unwrap_end) ==>
      create_cut_code {} ready unwrap_end /\ create_cut_code {} unwrap_end body_end /\
      abi_packaging_restore_law Seg ctx func explicit PG lo ce cx st0 DF d st
        ready unwrap_end (HD args) (HD svs) src /\
      abi_packaging_window_law Seg ctx func explicit PG lo unwrap_end body_end data_ptr src
        (type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce (HD args))) len) /\
    (~single ==> !dp. data_ptr = Var dp ==>
      abi_packaging_row_law RowSide ctx func explicit PG lo ce cx st0 DF d st
        ready.cs_next_id st.cs_next_id N (32+k) dp /\
      abi_packaging_fold_law Seg RowSide ctx func explicit PG lo ce cx st0 DF d st
        ready body_end st.cs_next_id N (32+k) len (ZIP (svs,tys)) dp)
End

Triviality packaging_compose_four:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_layout st sb /\ fn_has_code st sb f /\
  create_cut_code {} st a /\ create_cut_code {} a r /\
  create_cut_code {} r b /\ create_cut_code {} b sb /\
  create_operand_at st t /\
  abi_packaging_segment E ctx f st a t u /\ abi_packaging_segment E ctx f a r u pre /\
  abi_packaging_segment E ctx f r b pre q /\ abi_packaging_segment E ctx f b sb q actual ==>
  abi_packaging_segment E ctx f st sb t actual
Proof
  strip_tac >>
  `create_cut_code {} a sb /\ create_cut_code {} r sb` by metis_tac[create_cut_code_join] >>
  `cs_extends st a /\ cs_extends a r /\ cs_extends r b /\ cs_extends b sb /\
   cs_extends a sb /\ cs_extends r sb` by fs[create_cut_code_def] >>
  `fn_has_code st a f /\ fn_has_code a r f /\ fn_has_code r b f` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `create_layout a sb /\ create_layout r sb` by
    metis_tac[create_layout_subinterval,cs_extends_refl,cs_extends_trans] >>
  `create_operand_at a u /\ create_operand_at r pre` by
    fs[abi_packaging_segment_def,create_operand_full_scope_def,create_operand_at_def] >>
  `abi_packaging_segment E ctx f r sb pre actual` by metis_tac[packaging_segment_join] >>
  `abi_packaging_segment E ctx f a sb u actual` by metis_tac[packaging_segment_join] >>
  metis_tac[packaging_segment_join]
QED

Triviality packaging_single_compose:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_layout st sb /\ fn_has_code st sb f /\
  create_cut_code {} st a /\ create_cut_code {} a r /\
  create_cut_code {} r m /\ create_cut_code {} m b /\ create_cut_code {} b sb /\
  create_operand_at r pre /\ abi_packaging_segment E ctx f r m pre z /\
  abi_packaging_segment E ctx f m b z q ==>
  abi_packaging_segment E ctx f r b pre q
Proof
  strip_tac >>
  `cs_extends st a /\ cs_extends a r /\ cs_extends r m /\ cs_extends m b /\ cs_extends b sb`
    by fs[create_cut_code_def] >>
  `cs_extends st r /\ cs_extends r b /\ cs_extends r sb /\ cs_extends m sb` by
    metis_tac[cs_extends_trans] >>
  `create_layout r b` by metis_tac[create_layout_subinterval] >>
  `fn_has_code r m f` by metis_tac[fragExecTheory.fn_has_code_split] >>
  metis_tac[packaging_segment_join]
QED

Theorem abi_encode_packaging_suffix_inventory:
  lower_abi_encode meth maxlen (compile_abi_encode_payload ce single svs tys) st = (out,sb) /\
  k = (case meth of NONE => 0 | SOME _ => 4) /\ N = 32 + 32 * word_size (maxlen+k) /\
  (!buf a m data r len b.
    abi_packaging_site ce single svs tys meth k N out st sb buf a m data r len b ==>
    create_cut_code {} r b /\
    EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code r b)) ==>
  create_cut_code {} st sb /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code st sb)
Proof
  strip_tac >> drule_all packaging_site_exists >> strip_tac >>
  first_assum (drule_then strip_assume_tac) >>
  drule_all packaging_static_parts >> strip_tac >>
  `create_cut_code {} ready sb /\
   EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code ready sb)` by
    metis_tac[packaging_inventory_join] >>
  `create_cut_code {} allocated sb /\
   EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code allocated sb)` by
    metis_tac[packaging_inventory_join] >>
  metis_tac[packaging_inventory_join]
QED

Triviality packaging_installed_phases:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_layout st sb /\ fn_has_code st sb f /\
  k = (case meth of NONE => 0 | SOME _ => 4) /\
  (!buf a m data r len b.
    abi_packaging_site ce single svs tys meth k N out st sb buf a m data r len b ==>
    create_cut_code {} r b) /\
  (!buf a m data r len b.
    abi_packaging_site ce single svs tys meth k N out st sb buf a m data r len b ==>
    abi_packaging_payload_phases (abi_packaging_segment E ctx f) RowSide
      ctx f E PG lo ce cx st0 DF d single tys args svs k N st r data len b) ==>
  abi_packaging_phases (abi_packaging_segment E ctx f) RowSide
    ctx f E PG lo ce cx st0 DF d hz single tys args svs meth maxlen k N out st sb
Proof
  strip_tac >> simp_tac bool_ss [abi_packaging_phases_def] >>
  map_every qx_gen_tac [`buf`,`a`,`m`,`data`,`r`,`len`,`b`] >> strip_tac >>
  `abi_packaging_site ce single svs tys meth k N out st sb buf a m data r len b` by
    asm_rewrite_tac[abi_packaging_site_def] >>
  first_assum (drule_then strip_assume_tac) >>
  `create_cut_code {} r b` by metis_tac[] >>
  drule_all packaging_static_parts >> strip_tac >>
  rpt conj_tac
  >- (irule packaging_alloc_phase >> simp[])
  >- (irule packaging_setup_phase >> first_assum (irule_at Any) >> simp[])
  >- (irule packaging_finish_phase >> goal_assum drule) >>
  qhdtm_x_assum `abi_packaging_payload_phases`
    (strip_assume_tac o REWRITE_RULE [abi_packaging_payload_phases_def]) >>
  rpt conj_tac
  >- (disch_tac >> rpt gen_tac >> disch_tac >>
      qpat_assum `single ==> _` (drule_then (drule_then strip_assume_tac)) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> rpt strip_tac >>
      irule packaging_single_compose >>
      `create_operand_at r pre` by fs[abi_packaging_segment_def] >>
      simp[] >> rpt conj_tac
      >- (qexistsl_tac [`a`,`sb`,`st`] >> simp[])
      >- (qexistsl_tac [`ce`,`cx`,`tops`] >> simp[]) >>
      qexistsl_tac [`unwrap_end`,`z`] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `create_operand_at st t` by fs[abi_packaging_segment_def] >>
  mp_tac packaging_compose_four >> asm_rewrite_tac[]
QED

Theorem abi_encode_scoped_suffix_from_payload_phases:
  body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  (LENGTH args = 1 /\ ~ensure ==> ~is_word_type (lowered_value_type ce (HD args))) /\
  1 <= LENGTH args /\
  compile_abi_encode_args compile_expr ce args sa = (svs,st) /\
  lower_abi_encode (OPTION_MAP bytes_method_id_word mid)
    (abi_size_bound ce.ce_struct_fields
      (if LENGTH args = 1 /\ ~ensure then lowered_value_type ce (HD args)
       else TupleT (MAP (lowered_value_type ce) args)))
    (compile_abi_encode_payload ce (LENGTH args = 1 /\ ~ensure) svs
      (MAP (lowered_value_type ce) args)) st = (out,sb) /\
  LocatedValue ann (mk_ptr out LocMemory) = vv /\
  LENGTH svs = LENGTH args /\ ci_mono sa st /\ ci_mono st sb /\ create_layout st sb /\
  fn_has_code sa st func /\ fn_has_code st sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func ce cx es s0) /\
  (let single = (LENGTH args = 1 /\ ~ensure);
       tys = MAP (lowered_value_type ce) args;
       meth = OPTION_MAP bytes_method_id_word mid;
       k = (case meth of NONE => 0 | SOME _ => 4);
       maxlen = abi_size_bound ce.ce_struct_fields
         (if single then lowered_value_type ce (HD args) else TupleT tys);
       N = 32 + 32 * word_size (maxlen+k);
       E = gas_explicit_sites ctx shadow_ctx
   in (!buf a m data r len b.
         abi_packaging_site ce single svs tys meth k N out st sb buf a m data r len b ==>
         create_cut_code {} r b /\
         EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code r b)) /\
      (!buf a m data r len b.
         abi_packaging_site ce single svs tys meth k N out st sb buf a m data r len b ==>
         abi_packaging_payload_phases (abi_packaging_segment E ctx func) RowSide
           ctx func E PG lo ce cx st0 DF d single tys args svs k N st r data len b)) ==>
  create_cut_code {} st sb /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code st sb) /\
  (!marks vs mid' G1 tn1 t.
    (!tail. eval_exprs cx args (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL vs,mid' with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid'.storage_trace /\ mid'.gas_obs = [] /\
    create_operand_at st t /\
    (!H. valid_horizon cx st0 H mid'.storage_trace ==>
       extcall_positional_post T DF lo d ctx func ce cx env [] args svs sa st es s0 G0 tn0
         H (INL vs : value list + exception) mid' G1 tn1 t /\
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) marks (OK t,G1,tn1)) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      tops cx st0 st sb (abi_encode_packaging_action cx ensure mid target args vs) (mid',t,G1,tn1)
      (expr_vv_sim_full_post (DF,lo,d,ctx,func) ce cx
        (TypeBuiltin ann (AbiEncode ensure mid) target args) (es,sa,sb,s0,vv,G0,tn0))
      (create_operand_exit_post ctx cx))
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `single = (LENGTH args = 1 /\ ~ensure)` >>
  qabbrev_tac `tys = MAP (lowered_value_type ce) args` >>
  qabbrev_tac `meth = OPTION_MAP bytes_method_id_word mid` >>
  qabbrev_tac `k = case meth of NONE => 0 | SOME _ => 4` >>
  qabbrev_tac `maxlen = abi_size_bound ce.ce_struct_fields
    (if single then lowered_value_type ce (HD args) else TupleT tys)` >>
  qabbrev_tac `N = 32 + 32 * word_size (maxlen+k)` >>
  `create_cut_code {} st sb /\
   EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code st sb)` by
    (irule abi_encode_packaging_suffix_inventory >>
     qpat_assum `lower_abi_encode _ _ _ _ = _` (irule_at Any) >>
     qexistsl_tac [`k`,`N`] >> asm_rewrite_tac[] >> simp[Abbr `N`,Abbr `k`]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `E = gas_explicit_sites ctx shadow_ctx` >>
  `abi_packaging_phases (abi_packaging_segment E ctx func) RowSide
    ctx func E PG lo ce cx st0 DF d (storage_trace_horizon mid'.storage_trace)
    single tys args svs meth maxlen k N out st sb` by
    (irule packaging_installed_phases >>
     rpt (first_assum (irule_at Any)) >>
     simp[Abbr `k`] >> conj_tac >> rpt gen_tac >> disch_tac
     >- (qpat_assum `!buf a m data r len b. _ ==> create_cut_code _ _ _ /\ _`
           (drule_then (ACCEPT_TAC o cj 1))) >>
     first_assum (drule_then ACCEPT_TAC)) >>
  mp_tac (Q.INST [`Seg` |-> `abi_packaging_segment E ctx func`,
                  `res` |-> `INL (vs:value list)`] abi_encode_normal_packaging_side) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  impl_tac >- (unabbrev_all_tac >> rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
    rpt gen_tac >> disch_tac >> first_assum (drule_then (CONJUNCTS_THEN ASSUME_TAC)) >>
    first_assum ACCEPT_TAC) >>
  strip_tac >> simp[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`INL (Value (BytesV payload))`,`mid'`,`OK actual`,`Gf`,`tf`] >>
  fs[abi_packaging_segment_def,abi_encode_packaging_action_def] >> simp[Abbr `E`]
QED
