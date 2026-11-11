(* Joint ADD/read landing; the conditional read rule is discharged at publication. *)
Theory extcallProtFrameTupleHead
Ancestors
  exprExtRequestMaterialize stmtSimDeclGas exprExtRequestTupleStore
  exprExtRequestHistory venomMemDefs exprExtRequestReconstruct gasSummary
  extcallProtFrameKwargUnwrap exprExtRequestTupleCapturedHead
  exprExtRequestTupleHead exprExtRequestHistoryCompose exprExtRequestJointUnwrap
  exprSafeOperand exprLoweringProps emitHelperProps exprLowering compileEnv
  context emitHelper venomState venomInst loweringPosts venomInstProofs
  venomExecSemantics freshWrites gasSummaryCompose fragGasMode

Theorem extcall_tuple_head_read_protected:
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value cenv vv sn = (op,sb) /\
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e es sa sc s0 ec r vv tc /\
  extrequest_history_frame cenv cx ec sc tc ee sm s /\
  stmt_state_rel ctx func cenv cx ec tc /\
  stmt_state_rel ctx func cenv cx ee s /\
  (case vv of StackValue ty a => safe_operand sc a
   | LocatedValue ty p => safe_operand sc p.ptr_operand) /\
  (!ty p tr w tv.
     vv = LocatedValue ty p /\ p.ptr_location = slot_loc tr /\
     eval_operand p.ptr_operand tc = SOME w /\
     evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
     storage_read_live cx tr (get_storage cx ec tr) w tv) /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
         ~is_word_type (expr_type e) ==>
         type_memory_bytes cenv (expr_type e) = type_memory_size tv /\
         type_memory_size tv < 2**64) /\
  eval_operand buf s = SOME w /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!pa pk. prot pa pk ==>
    pa + pk <= s.vs_alloca_next /\
    mem_bytes_at pa pk s.vs_memory = mem_bytes_at pa pk original /\
    !i b n. FLOOKUP s.vs_allocas i = SOME (b,n) ==>
      compileEnv$regions_disjoint pa pk b n) /\
  (!t. extrequest_history_frame cenv cx ec sc tc ee sn t /\
    stmt_state_rel ctx func cenv cx ee t /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    (!pa pk. prot pa pk ==>
      pa + pk <= t.vs_alloca_next /\
      mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk original /\
      !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
        compileEnv$regions_disjoint pa pk b n) ==>
    ?v u. gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
      [] (INL v) ee (OK u) /\
      expr_post ctx func cenv cx e ee sa sb t ee v op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
        mem_bytes_at p k u.vs_memory = mem_bytes_at p k t.vs_memory) /\
      extrequest_history_frame cenv cx ee sn t ee sb u /\
      (!pa pk. prot pa pk ==>
        pa + pk <= u.vs_alloca_next /\
        mem_bytes_at pa pk u.vs_memory = mem_bytes_at pa pk original /\
        !i b n. FLOOKUP u.vs_allocas i = SOME (b,n) ==>
          compileEnv$regions_disjoint pa pk b n)) ==>
  ?v t u. gas_marked_exec F (ctx,func) (read_result cx r) (ee,s)
      [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e ee sa sb t ee v op u /\
    eval_operand dst u = SOME (w + n2w off) /\ safe_operand sb dst /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    extrequest_history_frame cenv cx ec sc tc ee sb u /\
    extrequest_history_frame cenv cx ee sm s ee sb u /\
    (!aid p k. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!pa pk. prot pa pk ==>
      pa + pk <= u.vs_alloca_next /\
      mem_bytes_at pa pk u.vs_memory = mem_bytes_at pa pk original /\
      !i b n. FLOOKUP u.vs_allocas i = SOME (b,n) ==>
        compileEnv$regions_disjoint pa pk b n)
Proof
  strip_tac >>
  `ci_mono sm sn /\ ci_mono sn sb` by
    (conj_tac
     >- (qspecl_then [`ADD`, `[buf; Lit (n2w off)]`, `sm`] mp_tac ci_mono_emit_op >> simp[]) >>
     qspecl_then [`cenv`, `vv`, `sn`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  `fn_has_code sm sn func /\ fn_has_code sn sb func` by
    (irule fragExecTheory.fn_has_code_split >> gvs[ci_mono_def]) >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn` by
    (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >>
     irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> gvs[ci_mono_def]) >>
  qabbrev_tac `t = (update_var (STRING #"%" (toString sm.cs_next_var))
    (w + n2w off) s) with vs_inst_idx := LENGTH sn.cs_current_insts` >>
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s` by
    (simp[Abbr `t`, lookup_var_def, update_var_def] >>
     rpt strip_tac >> fs[not_fresh_at_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `stmt_state_rel ctx func cenv cx ee t` by
    (simp[Abbr `t`, stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> simp[] >>
     irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
  `extrequest_history_frame cenv cx ee sm s ee sn t` by
    (irule extrequest_unchanged_memory_history >>
     gvs[ci_mono_def, Abbr `t`, update_var_def]) >>
  `extrequest_history_frame cenv cx ec sc tc ee sn t` by
    metis_tac[extrequest_history_frame_trans] >>
  `eval_operand dst t = SOME (w + n2w off) /\ safe_operand sn dst` by
    (drule emitted_insts_emit_op >> strip_tac >>
     simp[Abbr `t`, eval_operand_def, lookup_var_update_var, lookup_var_def] >>
     metis_tac[emit_op_safe_operand]) >>
  `~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
   t.vs_inst_idx = LENGTH sn.cs_current_insts` by
    (drule emit_op_same_blocks >> gvs[Abbr `t`, update_var_def, same_blocks_def]) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (`run_inst_seq (emitted_insts sm sn) s =
        OK (update_var (STRING #"%" (toString sm.cs_next_var)) (w + n2w off) s)` by
       (irule buffer_emit_add_run >> metis_tac[]) >>
     simp[Abbr `t`] >> irule extrequest_straight_run_path >>
     simp[] >> qexists_tac `sm` >> simp[] >>
     drule emitted_insts_emit_op >> strip_tac >>
     drule emit_op_same_blocks >> strip_tac >>
     gvs[mk_inst_def, is_terminator_def]) >>
  qpat_x_assum `!t. extrequest_history_frame _ _ _ _ _ _ _ _ /\ _ ==> _`
    (qspec_then `t` mp_tac) >>
  (impl_tac >- (simp[Abbr `t`, update_var_def] >> metis_tac[])) >> strip_tac >>
  `eval_operand dst u = SOME (w + n2w off)` by
    (Cases_on `dst` >> gvs[safe_operand_def, eval_operand_def] >>
     fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
  `extrequest_history_frame cenv cx ee sm s ee sb u` by
    metis_tac[extrequest_history_frame_trans] >>
  `extrequest_history_frame cenv cx ec sc tc ee sb u` by
    metis_tac[extrequest_history_frame_trans] >>
  `!aid p k. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory` by
    (`t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas` by
       simp[Abbr `t`, update_var_def] >>
     fs[ci_mono_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  qexistsl_tac [`v`, `t`, `u`] >> simp[] >> conj_tac
  >- (irule gas_marked_exec_zero_prefix >> goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[safe_operand_mono, ci_mono_def]
QED

(* Root-parametric history transport for a store with an adjusted cursor. *)
Theorem extcall_tuple_store_history:
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  stmt_state_rel ctx func cenv cx ec tc /\
  allocas_non_overlapping t /\
  FLOOKUP t.vs_allocas live = SOME (tuple_base,sz) /\ sc.cs_next_id <= live /\
  tuple_base <= dst /\ dst + n <= tuple_base + sz /\ ci_mono sn sm /\
  local_ptrs_reserved cenv sm /\
  (q with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
            vs_inst_idx := t.vs_inst_idx|>) = t /\
  (!x. not_fresh_at sn x ==> lookup_var x q = lookup_var x t) /\
  (!a k. compileEnv$regions_disjoint a k dst n ==>
     mem_bytes_at a k q.vs_memory = mem_bytes_at a k t.vs_memory) /\
  (!name b len. local_region cenv ee.scopes t name b len ==>
     compileEnv$regions_disjoint b len dst n) /\
  (cenv.ce_is_ctor ==> !name tv v off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
     compileEnv$regions_disjoint off (type_memory_size tv) dst n) ==>
  extrequest_history_frame cenv cx ec sc tc ee sm q
Proof
  strip_tac >>
  `extrequest_history_frame cenv cx ec sc tc ee sm
      (q with vs_inst_idx := t.vs_inst_idx)` by
    (irule extrequest_history_store_alloca >>
     conj_tac >- simp[] >>
     conj_tac >- (qexistsl_tac [`ctx`, `func`] >> simp[]) >>
     qexistsl_tac [`dst`, `live`, `n`, `sn`, `sz`, `t`, `tuple_base`] >>
     fs[ci_mono_def, lookup_var_def] >> metis_tac[]) >>
  pop_assum mp_tac >> simp[extrequest_history_frame_def, lookup_var_def] >>
  metis_tac[]
QED

(* Pointwise ordinary finalization: no endpoint is chosen after Q is supplied. *)
Theorem extcall_tuple_store_finalize:
  gas_marked_exec F (ctx,func) (read_result cx r) (ee,s)
    [] (INL v) ee (OK u) /\
  extrequest_history_frame cenv cx ec sc tc ee su u /\
  extrequest_history_frame cenv cx ee sm s ee su u /\
  stmt_state_rel ctx func cenv cx ec tc /\
  stmt_state_rel ctx func cenv cx ee u /\
  FLOOKUP s.vs_allocas live = SOME (tuple_base,sz) /\
  sc.cs_next_id <= live /\ live < sm.cs_next_id /\
  (!name b len. local_region cenv ee.scopes s name b len ==>
    compileEnv$regions_disjoint tuple_base sz b len) /\
  tuple_base <= d /\ d + type_memory_size tv <= tuple_base + sz /\
  ci_mono su sb /\ local_ptrs_reserved cenv sb /\
  (!aid p k. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
    mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
  (!name b len. local_region cenv ee.scopes u name b len ==>
    compileEnv$regions_disjoint b len d (type_memory_size tv)) /\
  (cenv.ce_is_ctor ==> !name itv iv io.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (itv,iv) ==>
    compileEnv$regions_disjoint io (type_memory_size itv) d (type_memory_size tv)) /\
  gas_marked_path F ctx func u 0 (OK q) /\
  stmt_state_rel ctx func cenv cx ee q /\
  val_in_memory tv v d q.vs_memory /\
  (q with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
            vs_inst_idx := u.vs_inst_idx|>) = u /\
  (!x. not_fresh_at su x ==> lookup_var x q = lookup_var x u) /\
  (!a k. a + k <= d \/ d + type_memory_size tv <= a ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k u.vs_memory) /\
  ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
  q.vs_inst_idx = LENGTH sb.cs_current_insts /\ Q q ==>
  gas_marked_exec F (ctx,func) (read_result cx r) (ee,s)
    [] (INL v) ee (OK q) /\
  stmt_state_rel ctx func cenv cx ee q /\
  val_in_memory tv v d q.vs_memory /\
  extrequest_history_frame cenv cx ec sc tc ee sb q /\
  FLOOKUP q.vs_allocas live = SOME (tuple_base,sz) /\
  (!a k. tuple_base <= a /\ a + k <= tuple_base + sz /\
    compileEnv$regions_disjoint a k d (type_memory_size tv) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!x z. not_fresh_at sm x /\ lookup_var x s = SOME z ==>
    lookup_var x q = SOME z) /\
  ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
  q.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
    FLOOKUP q.vs_allocas aid = SOME row) /\
  (!aid p k. aid < sm.cs_next_id /\ aid <> live /\
    FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
    mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory) /\
  (!eb cb tb. stmt_state_rel ctx func cenv cx eb tb /\
    extrequest_history_frame cenv cx eb cb tb ee sm s /\ cb.cs_next_id <= live ==>
    extrequest_history_frame cenv cx eb cb tb ee sb q) /\ Q q
Proof
  strip_tac >>
  `FLOOKUP u.vs_allocas live = SOME (tuple_base,sz)` by
    (fs[extrequest_history_frame_def] >> metis_tac[]) >>
  `allocas_non_overlapping u` by
    fs[stmt_state_rel_def, state_rel_def, alloca_inv_def] >>
  `q.vs_allocas = u.vs_allocas` by
    (qpat_x_assum `q with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = u`
       mp_tac >> simp[venom_state_component_equality]) >>
  `extrequest_history_frame cenv cx ec sc tc ee sb q` by
    (irule extcall_tuple_store_history >>
     first_assum (irule_at (Pat `extrequest_history_frame _ _ _ _ _ _ _ _`)) >>
     first_assum (irule_at (Pat `stmt_state_rel _ _ _ _ ec tc`)) >>
     simp[] >> goal_assum (drule_at (Pat `FLOOKUP _ live = _`)) >>
     qexistsl_tac [`type_memory_size tv`, `d`] >>
     fs[compileEnvTheory.regions_disjoint_def] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_def] >> strip_tac >>
      drule_all gas_marked_path_then >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory` by
        (irule extrequest_history_alloc_window >>
         first_assum (irule_at (Pat `extrequest_history_frame _ _ _ _ _ _ _ _`)) >>
         first_assum (irule_at (Pat `FLOOKUP _ live = _`)) >>
         fs[compileEnvTheory.regions_disjoint_def] >> metis_tac[]) >>
      fs[compileEnvTheory.regions_disjoint_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at su x` by
        (irule not_fresh_at_mono >> qexists_tac `sm` >>
         fs[extrequest_history_frame_def]) >>
      fs[extrequest_history_frame_def] >> metis_tac[]) >>
  conj_tac
  >- (fs[extrequest_history_frame_def] >> metis_tac[]) >>
  conj_tac
  >- (map_every qx_gen_tac [`aid`, `old_base`, `old_size`] >> strip_tac >>
      `FLOOKUP u.vs_allocas aid = SOME (old_base,old_size)` by
        (fs[extrequest_history_frame_def] >> metis_tac[]) >>
      `old_base + old_size <= tuple_base \/ tuple_base + sz <= old_base` by
        (qpat_x_assum `allocas_non_overlapping u` mp_tac >>
         rewrite_tac[allocas_non_overlapping_def] >>
         disch_then (qspecl_then [`aid`, `live`, `old_base`, `old_size`, `tuple_base`, `sz`] mp_tac) >>
         simp[]) >>
      `compileEnv$regions_disjoint old_base old_size d (type_memory_size tv)` by
        (simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
      fs[compileEnvTheory.regions_disjoint_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `extrequest_history_frame cenv cx eb cb tb ee su u` by
    (irule extrequest_history_frame_trans >>
     first_assum (irule_at (Pat `extrequest_history_frame _ _ eb cb tb _ _ _`)) >>
     metis_tac[]) >>
  irule extcall_tuple_store_history >>
  first_assum (irule_at (Pat `extrequest_history_frame _ _ eb cb tb _ _ _`)) >>
  first_assum (irule_at (Pat `stmt_state_rel _ _ _ _ eb tb`)) >>
  simp[] >> goal_assum (drule_at (Pat `FLOOKUP _ live = _`)) >>
  qexistsl_tac [`type_memory_size tv`, `d`] >>
  fs[compileEnvTheory.regions_disjoint_def] >> metis_tac[]
QED
