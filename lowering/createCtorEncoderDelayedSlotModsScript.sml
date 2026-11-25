(* The delayed storage/transient read begins at the encoder cut, not at
   the cut at which the source expression was evaluated. *)
Theory createCtorEncoderDelayedSlotMods
Ancestors
  bodyFullPostsMods bodyFullUnwrapSlotOrigin exprPtrUnwrapAllocSemantic
  exprPtrUnwrapRetained exprPtrUnwrapAllocSeparation exprSimAlloc abiBufferAllocationCode
  fragGasOriginPtrExec fragGasOriginPtrDead gasOriginPtrLabels exprPtrUnwrapStorage
  localPtrsProps exprSimProps exprSimUnwrapProps vyperStorageFootprint vyperStorageTrace
  valueEncodingTyping valueEncodingProps loweringPosts loweringStateRelDefs bodyPtrDefs
  bodyFullShadowBodyInv bodyFullHashKeccakFixed exprSimFieldLayout exprLowering
  exprLoweringProps compileEnv context venomState venomInst venomExecSemantics
  fragGasOriginPtr bufferAllocationExecution slotCopyExecution exprSimPtrTopLevelStorageCopy
  exprSimStorageCopy copyExecution words finite_map pred_set arithmetic
  allocaHistory fragExec bodyBinopFragMemory freshWrites exprOperandVar

Theorem ctor_encoder_slot_rebase[local]:
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  post_value_type ce e = expr_type e /\
  read_result cx raw ee = (INL v,ee) /\
  vv_holds_mods ce cx (expr_type e) raw (LocatedValue (expr_type e) p) ee t /\
  vv_storage_live H cx (LocatedValue (expr_type e) p) ee t /\
  stmt_state_rel H ctx fn ce cx ee t /\ immutable_frame_mods fn ce cx ee t /\
  storage_well_formed_on cx ee (FST H) ==>
  vv_post_mods H ctx fn ce cx e ee si sm t ee (Value v)
    (LocatedValue (expr_type e) p) t
Proof
  strip_tac >> simp[vv_post_mods_def, vv_at_def, vv_place_ptr_mods_def,
    vv_place_ptr_def, locals_kept_def, pure_frame_def] >>
  gvs[vv_holds_mods_def, vv_holds_def, storage_holds_def,
      vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  metis_tac[]
QED

(* The semantic endpoint rule is a callback, so the machine execution is
   independent of the proof relating the copied words to source storage. *)
Theorem ctor_encoder_delayed_slot_mods:
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  lowered_value_type ce e = expr_type e /\ ~is_word_type (expr_type e) /\
  compile_expr ce (expr_type e) e si = (LocatedValue (expr_type e) p,sm) /\
  sm.cs_next_var <= su.cs_next_var /\ sm.cs_next_id <= su.cs_next_id /\
  unwrap_value ce (LocatedValue (expr_type e) p) su = (src,sb) /\
  local_ptrs_reserved ce si /\ local_ptrs_reserved ce sm /\
  si.cs_next_var <= sm.cs_next_var /\ si.cs_next_id <= sm.cs_next_id /\
  fn_has_code su sb fn /\ fn_inst_ids_distinct fn /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  type_memory_bytes ce (expr_type e) = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ value_has_type rt v /\
  storage_trace_domain cx st0 ee.storage_trace /\
  read_result cx raw ee = (INL v,ee) /\
  vv_holds_mods ce cx (expr_type e) raw (LocatedValue (expr_type e) p) ee t /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue (expr_type e) p) ee G tn t /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx fn ce cx ee t /\ immutable_frame_mods fn ce cx ee t /\
     storage_well_formed_on cx ee (FST H) /\
     vv_storage_live H cx (LocatedValue (expr_type e) p) ee t /\
     ghost_inv_at_mods (DF H) lo d ce cx ee G tn t) /\
  alloca_history fn t /\ ~t.vs_halted /\ t.vs_current_bb = su.cs_current_bb /\
  t.vs_inst_idx = LENGTH su.cs_current_insts /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!nb n a mid u root dst allocated G0 tn0 buf z Gf tnf.
    compile_ensure_in_memory p.ptr_operand p.ptr_location nb n
      ce.ce_is_ctor ce.ce_imm_alloca su = (src,sb) /\
    nb = type_memory_bytes ce (expr_type e) /\ nb = type_memory_size rt /\
    n = type_slot_size rt /\ nb < dimword (:256) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post_mods H ctx fn ce cx e ee si sm t ee (Value v)
         (LocatedValue (expr_type e) p) t /\
       ghost_inv_at_mods (DF H) lo d ce cx ee G tn t) /\
    ptr_vv_ok cx (expr_type e) (Value v) (LocatedValue (expr_type e) p) ee G tn t /\
    eval_operand p.ptr_operand t = SOME a /\
    fn_has_code su mid fn /\ fn_has_code mid sb fn /\
    u = update_var root dst (buffer_allocation_fields t su.cs_next_id nb) /\
    step_inst_base (mk_inst su.cs_next_id ALLOCA [Lit (n2w nb)] [root]) t = OK u /\
    allocated = u with vs_inst_idx := SUC t.vs_inst_idx /\
    G0 = step_prov PG G (mk_inst su.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
    tn0 = step_taint (mk_inst su.cs_next_id ALLOCA [Lit (n2w nb)] [root]) t u tn /\
    src = Var root /\ dst = n2w (buffer_allocation_base t su.cs_next_id) /\
    compile_alloc_buffer nb su = (buf,mid) /\ buf.buf_operand = Var root /\
    gas_origin_ptr_path (<| d_stor := K (K {}); d_trans := K (K {});
        d_imm := K {}; d_ret := K {} |>,lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,Gf,tnf) /\
    (n <> 1 ==> ?cv ds.
      toplevel_copy_inv cv ds root p.ptr_operand p.ptr_location a (w2n dst) n
        allocated G0 tn0 n Gf tnf z /\
      (!x. not_fresh_at mid x ==> ~MEM x ds) /\ ~z.vs_halted) /\
    (n = 1 ==>
      z = (mstore (w2n dst) (slot_copy_word (if p.ptr_location = LocStorage then SLOAD else TLOAD) allocated a)
        (update_var (STRING #"%" (toString mid.cs_next_var))
          (slot_copy_word (if p.ptr_location = LocStorage then SLOAD else TLOAD) allocated a) allocated)
              with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      tnf.t_mem = (tn0.t_mem DIFF {j | w2n dst <= j /\ j < w2n dst+32}) UNION
        {w2n dst+b | b IN key_taint (if p.ptr_location = LocStorage then tn0.t_stor else tn0.t_trans) a} /\
      tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm /\
      (!x. x <> STRING #"%" (toString mid.cs_next_var) ==>
         FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tnf (Var x) = op_taint tn0 (Var x))) ==>
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post_mods H ctx fn ce cx e ee si sb t ee v src z /\
       ghost_inv_at_mods (DF H) lo d ce cx ee Gf tnf z) /\
    vv_own ce cx (expr_type e) su sb ee (Value v)
      (LocatedValue (expr_type e) (mk_ptr src LocMemory)) z /\
    expr_store_bound cx (expr_type e) v src z /\
    ptr_val_ok cx (expr_type e) v src Gf tnf z /\ ptr_buf_ok ce e src Gf z /\
    (!rt' w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt' /\
       eval_operand src z = SOME w ==> w2n w + type_memory_size rt' <= z.vs_alloca_next) /\
    (!x. not_fresh_at su x ==> lookup_var x z = lookup_var x t /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    wb_frame ce ee ee su t z /\ ghost_kept_at lo ce ee su G tn t Gf tnf) ==>
  ?z Gf tnf.
    pure_frame ce fn ee su t z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx fn ce cx ee z /\ immutable_frame_mods fn ce cx ee z /\
       storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at_mods (DF H) lo d ce cx ee Gf tnf z) /\
    expr_val_rel cx (expr_type e) v src z /\ ptr_val_ok cx (expr_type e) v src Gf tnf z /\
    expr_store_bound cx (expr_type e) v src z /\ ptr_buf_ok ce e src Gf z /\
    (!w. eval_operand src z = SOME w ==> w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    alloca_history fn z /\ t.vs_alloca_next <= z.vs_alloca_next /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\ z.vs_labels = t.vs_labels /\
    (!x. not_fresh_at su x ==> lookup_var x z = lookup_var x t /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    wb_frame ce ee ee su t z /\ ghost_kept_at lo ce ee su G tn t Gf tnf /\
    (!x. src = Var x ==> not_fresh_at sb x) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,Gf,tnf)) /\
    expr_val_at ce cx (expr_type e) su sb ee v src z
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `post_value_type ce e = expr_type e` by metis_tac[post_value_type_lowered] >>
  `ptr_vv_ok cx (expr_type e) (Value v) (LocatedValue (expr_type e) p) ee G tn t` by
    (qpat_assum `ptr_vv_ok _ _ raw _ _ _ _ _` mp_tac >>
     qpat_assum `p.ptr_location = LocStorage \/ _` strip_assume_tac >>
     qpat_assum `p.ptr_location = _` (fn th => simp[NoAsms, th, ptr_vv_ok_def])) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post_mods H ctx fn ce cx e ee si sm t ee (Value v)
         (LocatedValue (expr_type e) p) t /\
       ghost_inv_at_mods (DF H) lo d ce cx ee G tn t` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     simp[] >> irule ctor_encoder_slot_rebase >> simp[] >> qexists_tac `raw` >> simp[]) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by
    (qpat_assum `storage_trace_domain _ _ _` mp_tac >>
     simp[NoAsms, storage_trace_domain_def, Abbr `H0`]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods (DF H0) _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms, ghost_inv_at_mods_def]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `op_taint tn p.ptr_operand = {}` by
    (qpat_assum `ptr_vv_ok _ _ raw _ _ _ _ _` mp_tac >> simp[NoAsms, ptr_vv_ok_def]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at su x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `?a. eval_operand p.ptr_operand t = SOME a` by
    (qpat_assum `vv_holds_mods _ _ _ raw _ _ _` mp_tac >>
     qpat_assum `p.ptr_location = LocStorage \/ _` strip_assume_tac >>
     qpat_assum `p.ptr_location = _`
       (fn th => simp[NoAsms, th, vv_holds_mods_def, vv_holds_def]) >>
     disch_then (qx_choose_then `a` (assume_tac o CONJUNCT1)) >>
     qexists_tac `a` >> first_assum ACCEPT_TAC) >>
  rename1 `eval_operand p.ptr_operand t = SOME a` >>
  qabbrev_tac `nb = type_memory_size rt` >>
  qabbrev_tac `n = type_slot_size rt` >>
  `nb = 32*n /\ (nb+31) DIV 32 = n` by
    (qpat_assum `Abbrev (nb = _)` mp_tac >> qpat_assum `Abbrev (n = _)` mp_tac >>
     simp[NoAsms, markerTheory.Abbrev_def] >>
     metis_tac[type_memory_size_slots, slot_count_of_memory_size]) >>
  `nb < dimword (:256) /\ n < 2**256` by
    (qpat_assum `nb < 2**64` mp_tac >> qpat_assum `nb = 32*n` mp_tac >>
     simp[NoAsms, dimword_def] >> decide_tac) >>
  `compile_ensure_in_memory p.ptr_operand p.ptr_location nb n
      ce.ce_is_ctor ce.ce_imm_alloca su = (src,sb)` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     qpat_x_assum `p.ptr_location = LocStorage \/ _` strip_assume_tac >>
     simp[unwrap_value_def]) >>
  `32*n <= nb` by simp[] >>
  drule_all unwrap_ensure_slot_origin_execution >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choosel_then [`root`,`dst`,`allocated`,`G0`,`tn0`,`Gf`,`tnf`,`z`,`mid`,`buf`,`u`]
      (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  (* Use exactly the execution witnesses, including the final endpoint
     rather than the intermediate endpoint of the allocation. *)
  qpat_x_assum `!nb n a mid u root dst allocated G0 tn0 buf z Gf tnf. _`
    (qspecl_then [`nb`,`n`,`a`,`mid`,`u`,`root`,`dst`,`allocated`,`G0`,`tn0`,`buf`,`z`,`Gf`,`tnf`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC,
     sym_tac >> first_assum ACCEPT_TAC])) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `pure_frame ce fn ee su t z` by suspend "physical_frame" >>
  suspend "result"
QED

Resume ctor_encoder_delayed_slot_mods[physical_frame]:
  `local_ptrs_reserved ce su` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
  `w2n dst = buffer_allocation_base t su.cs_next_id` by
    (drule_all unwrap_alloc_site_bound >> strip_tac >>
     `buffer_allocation_base t su.cs_next_id < dimword (:256)` by
       (qpat_assum `_ + nb < dimword (:256)` mp_tac >> decide_tac) >>
     simp[w2n_n2w]) >>
  `(!name b len. local_region ce ee.scopes t name b len ==>
      w2n dst + nb <= b \/ b+len <= w2n dst)` by
    (rpt strip_tac >> drule_all unwrap_alloc_local_separation >>
     asm_rewrite_tac[]) >>
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  `allocated.vs_memory = t.vs_memory /\ allocated.vs_allocas = u.vs_allocas` by simp[] >>
  `z.vs_allocas = allocated.vs_allocas /\
    (!off len. off+len <= w2n dst \/ w2n dst+nb <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len allocated.vs_memory)` by
    (Cases_on `n = 1` >- suspend "word_frame" >> suspend "loop_frame") >>
  `MEM (mk_inst su.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts fn)` by
    (`root = STRING #"%" (toString su.cs_next_var)` by
      (drule compile_alloc_buffer_code >> simp[]) >>
     drule_all buffer_alloc_code >> simp[]) >>
  irule pure_frame_fresh_alloca >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!name b len. local_region _ _ t name b len ==> _`
        (drule_then strip_assume_tac) >>
      qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _`
        (qspecl_then [`lb`,`lsz`] mp_tac) >> simp[]) >>
  qexistsl_tac [`w2n dst`,`su.cs_next_id`,`[Lit (n2w nb)]`,`[root]`,`nb`] >>
  conj_tac
  >- (pure_rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
      qpat_assum `allocated.vs_memory = t.vs_memory` (fn th => once_rewrite_tac[GSYM th]) >>
      rpt gen_tac >> disch_tac >>
      qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _`
        (drule_then ACCEPT_TAC)) >>
  conj_tac >- simp[] >>
  conj_tac
  >- (qpat_assum `z.vs_allocas = allocated.vs_allocas` (fn th => pure_rewrite_tac[th]) >>
      qpat_assum `allocated.vs_allocas = u.vs_allocas` (fn th => pure_rewrite_tac[th]) >>
      first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Resume ctor_encoder_delayed_slot_mods[word_frame]:
  `nb = 32` by simp[] >>
  qpat_x_assum `(n = 1 ==> _)` (drule_then strip_assume_tac) >>
  conj_tac
  >- (qpat_assum `z = _` SUBST1_TAC >>
      simp[NoAsms, mstore_def, write_memory_with_expansion_def, update_var_def]) >>
  rpt strip_tac >>
  qpat_assum `z = _` SUBST1_TAC >>
  simp_tac (srw_ss()) [] >>
  dep_rewrite.DEP_REWRITE_TAC[mstore_mem_bytes_at_disjoint] >>
  simp[update_var_def]
QED

Resume ctor_encoder_delayed_slot_mods[loop_frame]:
  qpat_x_assum `(n <> 1 ==> _)` (drule_then strip_assume_tac) >>
  qpat_assum `toplevel_copy_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[toplevel_copy_inv_def,storage_copy_inv_def,copy_prefix_def]) >>
  drule_then strip_assume_tac copy_static_fields >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `nb = 32*n` (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC
QED

Resume ctor_encoder_delayed_slot_mods[result]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,Gf,tnf)` by
    (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
  `~z.vs_halted /\ z.vs_labels = t.vs_labels` by
    (qpat_assum `gas_origin_ptr_path _ (t,G,tn) [] (OK z,Gf,tnf)`
       (fn th => mp_tac (MATCH_MP gas_origin_ptr_path_exec th) >>
                 mp_tac (MATCH_MP gas_origin_ptr_path_preserves_labels th)) >>
     simp[exit_result_def]) >>
  `expr_val_rel cx (expr_type e) v src z` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then (mp_tac o CONJUNCT1)) >>
     qpat_assum `post_value_type ce e = _`
       (fn th => simp[NoAsms, th, expr_post_mods_def, expr_post_def])) >>
  qexistsl_tac [`z`,`Gf`,`tnf`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (qspec_then `H` (drule_then mp_tac)) >> simp[NoAsms, expr_post_mods_def, expr_post_def])
  >- (gen_tac >> disch_tac >>
      qpat_assum `!rt' w. evaluate_type _ (lowered_value_type ce e) = _ /\ _ ==> _`
        (qspecl_then [`rt`,`w`] mp_tac) >>
      (impl_tac >- (conj_tac >- simp[] >> first_assum ACCEPT_TAC)) >>
      simp[NoAsms, Abbr `nb`])
  >- (drule compiler_unwrap_value_var >> simp[]) >>
  qpat_assum `vv_own _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `evaluate_type _ _ = SOME rt` (fn th =>
    simp[NoAsms, th, expr_val_at_def, vv_own_def, mk_ptr_def,
         vyperStateTheory.read_result_def, vyperStateTheory.return_def]) >>
  disch_then (qx_choose_then `pw` (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_tac >> disch_tac >>
  conj_tac >- (irule (cj 1 value_has_type_val_wf) >> first_assum ACCEPT_TAC) >>
  qexists_tac `pw` >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `(?aid b sz. _) \/ val_footprint _ _ = 0` mp_tac >>
  tautLib.TAUT_TAC
QED

Finalise ctor_encoder_delayed_slot_mods
