(* The deterministic transition from the keyword midpoint to the raw call. *)
Theory bodyFullRawCallPreparedEntry
Ancestors
  bodyFullRawCallGas bodyFullRawCallOutbuf bodyFullRawCallKwargsBytes
  bodyFullRawCallKwargsSource bodyFullWordArgs bodyFullIfExpReach stateRelProj
  bodyFullIntCallReturnFrame gasOutcomeFullCompose exprSimRawCall
  exprSimSource wordArgsPtr gasShadowState representationCleanPtr
  vyperEvalExprPreservesScopesDom exprLoweringProps exprSimWordArgs
  fragExec list gasShadow vyperStorageTrace
  exprSimHypsDefs[qualified]

Theorem raw_call_kwargs_prepared_entry:
  expr_body_pre_mods mods cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) NONE) es /\
  expr_type a = BaseT AddressT /\ expr_type d = BaseT (BytesT (Dynamic cap)) /\
  post_value_type cenv d = expr_type d /\
  evaluate_type (get_tenv cx) (post_value_type cenv d) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_word_args cenv (K (BaseT (UintT 256))) kws s4 = (xs,s5) /\
  (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas,s6) /\
  (case go of SOME g => (g,h5) | NONE => emit_op GAS [] h5) = (gas,h6) /\
  compile_raw_call_outbuf flags.rcf_max_outsize s6 = ((ov,op),s7) /\
  vo = ext_call_kwarg EKValue flags.rcf_kws xs /\
  go = ext_call_kwarg EKGas flags.rcf_kws xs /\
  gas_shadow_state s5 h5 /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code s5 s6 func /\ fn_has_code h5 h6 shadow_func /\
  fn_has_code s6 s7 func /\ fn_inst_ids_distinct func /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  sa.cs_next_var <= s2.cs_next_var /\
  ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
  ci_mono s4 s5 /\ ci_mono s5 s6 /\ ci_mono s6 s7 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s1 /\
  local_ptrs_reserved cenv s2 /\ local_ptrs_reserved cenv s4 /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z) /\
  return_buf_frame dframe cenv sa s0 /\
  (!e ee. MEM e kws /\ expr_sim_inv_mods mods cenv cx env ee ==>
    expr_body_pre_mods mods cenv cx env e ee /\ is_word_type (expr_type e)) /\
  bind (eval_expr cx a) (read_result cx) (es with gas_obs := gsA) = (INL av,esA) /\
  bind (eval_expr cx d) (read_result cx) (esA with gas_obs := gsD) = (INL (BytesV bs),esD) /\
  eval_exprs cx kws (esD with gas_obs := gsK) = (INL kvs,esK) /\
  expr_sim_inv_mods mods cenv cx env esD /\
  storage_trace_domain cx st0 es.storage_trace /\
  storage_trace_domain cx st0 esD.storage_trace /\
  storage_trace_domain cx st0 esK.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H esD.storage_trace ==>
    expr_post H ctx func cenv cx a es sa s1 s0 esA av addr tA /\
    expr_post H ctx func cenv cx d esA s1 s2 tA esD (BytesV bs) data tD) /\
  expr_store_bound cx (post_value_type cenv d) (BytesV bs) data tD /\
  ptr_val_ok cx (post_value_type cenv a) av addr GA tnA tA /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 GA tnA /\
  ghost_kept_at lo cenv esA s1 GA tnA tA GD tnD /\
  s0.vs_alloca_next <= tA.vs_alloca_next /\ tA.vs_alloca_next <= tD.vs_alloca_next /\
  data = Var x /\ len = Var l /\ dp = Var p /\
  (!z. data = Var z ==> not_fresh_at s2 z) /\
  (!z. len = Var z \/ dp = Var z ==> not_fresh_at s4 z) /\
  eval_operand data tD = SOME (n2w b) /\ b < dimword (:256) /\
  b+32+LENGTH bs < dimword (:256) /\
  eval_operand len t4 = SOME (n2w (LENGTH bs)) /\ eval_operand dp t4 = SOME (n2w (b+32)) /\
  op_taint tn4 len = {} /\ op_taint tn4 dp = {} /\ op_prov G4 len = NONE /\
  FLOOKUP G4 p = SOME (base',cap') /\ base' <= b /\ b+32+LENGTH bs <= base'+cap' /\
  (!mem. mem_agree_outside tn4.t_mem t4.vs_memory mem ==>
    mem_bytes_at (b+32) (LENGTH bs) mem = bs) /\
  (!z. not_fresh_at s2 z ==> lookup_var z t4 = lookup_var z tD /\
    FLOOKUP G4 z = FLOOKUP GD z /\ op_taint tn4 (Var z) = op_taint tnD (Var z)) /\
  t4.vs_allocas = tD.vs_allocas /\ t4.vs_alloca_next = tD.vs_alloca_next /\
  (!sa es0 s0 G0 tn0. sa.cs_next_var <= s2.cs_next_var /\
    ghost_kept_at lo cenv es0 sa G0 tn0 s0 GD tnD ==>
    ghost_kept_at lo cenv es0 sa G0 tn0 s0 G4 tn4) /\
  (!sa es0 s0. sa.cs_next_var <= s2.cs_next_var /\
    wb_frame cenv es0 esD sa s0 tD ==> wb_frame cenv es0 esD sa s0 t4) /\
  (!H. valid_horizon cx st0 H esK.storage_trace ==>
    typed_args_post H ctx func cenv cx esD s4 t4 esK kws xs kvs tk /\
    stmt_state_rel H ctx func cenv cx esK tk /\
    storage_well_formed_on cx esK (FST H) /\ ghost_inv_at (DF H) lo dframe cenv cx esK GK tnK tk) /\
  ~tk.vs_halted /\ tk.vs_current_bb = s5.cs_current_bb /\
  tk.vs_inst_idx = LENGTH s5.cs_current_insts /\ alloca_history func tk /\
  t4.vs_alloca_next <= tk.vs_alloca_next /\
  ghost_kept_at lo cenv esD s4 G4 tn4 t4 GK tnK /\
  EVERY (\x. op_taint tnK x = {}) xs ==>
  ?t7 G7 tn7 n ob gw.
    expr_sim_inv_mods mods cenv cx env esK /\
    (!H. valid_horizon cx st0 H esK.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (tk,GK,tnK) (REPLICATE n F) (OK t7,G7,tn7) /\
      expr_post H ctx func cenv cx a es sa s1 s0 esA av addr tA /\
      expr_post H ctx func cenv cx d esA s1 s2 tA esD (BytesV bs) data tD /\
      expr_store_bound cx (expr_type d) (BytesV bs) data tD /\
      typed_args_post H ctx func cenv cx esD s4 t4 esK kws xs kvs tk /\
      stmt_state_rel H ctx func cenv cx esK t7 /\
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx esK (FST H) /\
      expr_val_rel cx (BaseT AddressT) av addr t7 /\
      (!x w. MEM x xs /\ eval_operand x tk = SOME w ==> eval_operand x t7 = SOME w) /\
      eval_operand len t7 = SOME (n2w (LENGTH bs)) /\
      eval_operand dp t7 = SOME (n2w (b+32)) /\ eval_operand gas t7 = SOME gw /\
      b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
      b+32+LENGTH bs <= t7.vs_alloca_next /\
      mem_bytes_at (b+32) (LENGTH bs) t7.vs_memory = bs /\
      (!mem. mem_agree_outside tn7.t_mem t7.vs_memory mem ==>
        mem_bytes_at (b+32) (LENGTH bs) mem = bs) /\
      EVERY (\x. op_taint tn7 x = {})
        [addr;len;dp;gas;(case vo of NONE => Lit 0w | SOME v => v)] /\
      EVERY (\x. op_prov G7 x = NONE) [addr;len] /\
      (LENGTH bs <> 0 ==> ?base sz. op_prov G7 dp = SOME (base,sz) /\
        base <= b+32 /\ b+32+LENGTH bs <= base+sz) /\
      eval_operand ov t7 = SOME (n2w ob) /\
      eval_operand op t7 = SOME (n2w (if flags.rcf_max_outsize = 0 then ob else ob+32)) /\
      (flags.rcf_max_outsize = 0 ==> ov = op) /\
      ob+(if flags.rcf_max_outsize = 0 then 0
          else ((flags.rcf_max_outsize+31) DIV 32)*32+32) < dimword (:256) /\
      FLOOKUP t7.vs_allocas s6.cs_next_id =
        SOME (ob,if flags.rcf_max_outsize = 0 then 0
                 else ((flags.rcf_max_outsize+31) DIV 32)*32+32) /\
      op_prov G7 ov = SOME (ob,if flags.rcf_max_outsize = 0 then 0
                                else ((flags.rcf_max_outsize+31) DIV 32)*32+32) /\
      op_prov G7 op = SOME (ob,if flags.rcf_max_outsize = 0 then 0
                                else ((flags.rcf_max_outsize+31) DIV 32)*32+32) /\
      op_taint tn7 ov = {} /\ op_taint tn7 op = {} /\
      (!name lb sz. local_region cenv esK.scopes t7 name lb sz ==>
        regions_disjoint ob (if flags.rcf_max_outsize = 0 then 0
                             else ((flags.rcf_max_outsize+31) DIV 32)*32+32) lb sz) /\
      (cenv.ce_is_ctor ==> !name tv v off.
        FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
        FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
          | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
        regions_disjoint off (type_memory_size tv) ob
          (if flags.rcf_max_outsize = 0 then 0
           else ((flags.rcf_max_outsize+31) DIV 32)*32+32)) /\
      wb_frame cenv es esK sa s0 t7 /\ return_buf_frame dframe cenv sa t7 /\
      ~t7.vs_halted /\ t7.vs_current_bb = s7.cs_current_bb /\
      t7.vs_inst_idx = LENGTH s7.cs_current_insts /\ alloca_history func t7 /\
      s0.vs_alloca_next <= t7.vs_alloca_next /\ lo <= t7.vs_alloca_next /\ allocas_from lo t7 /\
      ghost_inv_at (DF H) lo dframe cenv cx esK G7 tn7 t7 /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G7 tn7 /\
      EVERY (safe_operand s7)
        [addr;len;dp;gas;(case vo of NONE => Lit 0w | SOME v => v);ov;op] /\
      (!x. MEM (Var x) [addr;len;dp;gas;(case vo of NONE => Lit 0w | SOME v => v);ov;op] ==>
        not_fresh_at s7 x))
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon esK.storage_trace) esK.storage_trace` by
    (fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon esD.storage_trace) esD.storage_trace` by
    (fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> _`
    (qspec_then `storage_trace_horizon esK.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==> _`
    (qspec_then `storage_trace_horizon esD.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `expr_sim_inv cenv cx env esK /\ MAP FDOM esK.scopes = MAP FDOM esD.scopes` by
    (qpat_assum `eval_exprs cx kws _ = _` mp_tac >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` mp_tac >>
     qpat_assum `expr_sim_inv cenv cx env esD` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_at (Pat `eval_exprs _ _ _ = _`) raw_call_kwargs_source_inv >>
     disch_then (qspecl_then [`cenv`,`env`,`ann`,`flags`,`a::d::kws`,`NONE`,`es`] mp_tac) >>
     simp[EVERY_MEM]) >>
  suspend "keyword_frames"
QED

Resume raw_call_kwargs_prepared_entry[keyword_frames]:
  `wb_frame cenv esD esK s4 t4 tk` by
    (qpat_assum `typed_args_post _ _ _ _ _ _ _ _ esK _ _ kvs tk`
       (mp_tac o REWRITE_RULE [exprSimPrecompilesTheory.typed_args_post_def]) >> simp[]) >>
  `s2.cs_next_id <= s4.cs_next_id /\ sa.cs_next_var <= s4.cs_next_var /\
   sa.cs_next_id <= s4.cs_next_id /\ s1.cs_next_var <= s4.cs_next_var /\
   s1.cs_next_id <= s4.cs_next_id` by
    (rpt (qhdtm_x_assum `ci_mono` (mp_tac o REWRITE_RULE [ci_mono_def])) >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `!name lb sz. local_region cenv esD.scopes t4 name lb sz <=>
                 local_region cenv esD.scopes tD name lb sz` by
    (rpt gen_tac >> irule loweringStateRelDefsTheory.local_region_lookup_cong >>
     qpat_assum `local_ptrs_reserved cenv s2`
       (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
     qpat_assum `!z. not_fresh_at s2 z ==> lookup_var z t4 = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `eval_operand data t4 = SOME(n2w b)` by
    (qpat_assum `eval_operand data tD = _` mp_tac >>
     qpat_assum `data = Var _` mp_tac >>
     qpat_assum `!z. data = Var z ==> not_fresh_at s2 z` mp_tac >>
     qpat_assum `!z. not_fresh_at s2 z ==> lookup_var z t4 = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `expr_val_at cenv cx (BaseT(BytesT(Dynamic cap))) s1 s2 esD (BytesV bs) data t4` by
    (qpat_assum `expr_post _ _ _ _ _ d _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     qpat_assum `post_value_type cenv d = _` mp_tac >>
     qpat_assum `expr_type d = _` mp_tac >>
     qpat_assum `eval_operand data t4 = _` mp_tac >>
     qpat_assum `eval_operand data tD = _` mp_tac >>
     qpat_assum `t4.vs_allocas = tD.vs_allocas` mp_tac >>
     qpat_assum `!name lb sz. local_region _ _ t4 _ _ _ <=> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringPostsTheory.expr_val_at_def] >> metis_tac[]) >>
  `evaluate_type (get_tenv cx) (BaseT(BytesT(Dynamic cap))) =
     SOME(BaseTV(BytesT(Dynamic cap)))` by
    (qpat_assum `evaluate_type _ _ = SOME (BaseTV (BytesT (Dynamic cap)))` mp_tac >>
     qpat_assum `post_value_type cenv d = _` mp_tac >>
     qpat_assum `expr_type d = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `!mem. mem_agree_outside tnK.t_mem tk.vs_memory mem ==>
       mem_bytes_at (b+32) (LENGTH bs) mem = bs` by
    (gen_tac >> strip_tac >> drule_all raw_call_kwargs_bytes_frame >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM esA.scopes /\
   MAP FDOM esA.scopes = MAP FDOM esD.scopes` by
    (qpat_assum `bind (eval_expr cx a) (read_result cx) _ = _`
       (mp_tac o MATCH_MP (REWRITE_RULE [ETA_THM] forced_eval_expr_preserves_scopes_dom)) >>
     qpat_assum `bind (eval_expr cx d) (read_result cx) _ = _`
       (mp_tac o MATCH_MP (REWRITE_RULE [ETA_THM] forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     qpat_assum `storage_trace_domain cx st0 es.storage_trace`
       (mp_tac o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def]) >> simp[]) >>
  `wb_frame cenv es esA sa s0 tA /\ wb_frame cenv esA esD s1 tA tD` by
    metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `sa.cs_next_id <= s1.cs_next_id` by
    (qpat_assum `ci_mono sa s1` (mp_tac o REWRITE_RULE [ci_mono_def]) >> simp[]) >>
  `wb_frame cenv es esD sa s0 tD /\ ghost_kept_at lo cenv es sa G0 tn0 s0 GD tnD` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`wb_frame cenv es esA sa s0 tA`, `wb_frame cenv esA esD s1 tA tD`,
        `ghost_kept_at lo cenv es sa G0 tn0 s0 GA tnA`,
        `ghost_kept_at lo cenv esA s1 GA tnA tA GD tnD`,
        `stmt_state_rel _ _ _ _ _ es s0`, `local_ptrs_reserved cenv sa`,
        `MAP FDOM es.scopes = MAP FDOM esA.scopes`,
        `sa.cs_next_var <= s1.cs_next_var`, `sa.cs_next_id <= s1.cs_next_id`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[wb_frame_trans,ghost_kept_at_wb_trans]) >>
  `wb_frame cenv es esD sa s0 t4 /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G4 tn4` by
    (conj_tac
     >- (qpat_assum `!sa es0 s0. _ ==> wb_frame _ _ _ _ _ t4` irule >> simp[]) >>
     qpat_assum `!sa es0 s0 G0 tn0. _ ==> ghost_kept_at _ _ _ _ _ _ _ G4 tn4` irule >> simp[]) >>
  `wb_frame cenv es esK sa s0 tk /\ ghost_kept_at lo cenv es sa G0 tn0 s0 GK tnK` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`wb_frame cenv es esD sa s0 t4`, `wb_frame cenv esD esK s4 t4 tk`,
        `ghost_kept_at lo cenv es sa G0 tn0 s0 G4 tn4`,
        `ghost_kept_at lo cenv esD s4 G4 tn4 t4 GK tnK`,
        `stmt_state_rel _ _ _ _ _ es s0`, `local_ptrs_reserved cenv sa`,
        `MAP FDOM es.scopes = MAP FDOM esA.scopes`, `MAP FDOM esA.scopes = MAP FDOM esD.scopes`,
        `sa.cs_next_var <= s4.cs_next_var`, `sa.cs_next_id <= s4.cs_next_id`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[wb_frame_trans,ghost_kept_at_wb_trans]) >>
  `return_buf_frame dframe cenv sa tk` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame dframe cenv sa s0` (irule_at Any) >>
     qpat_assum `wb_frame cenv es esK sa s0 tk`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     map_every (fn q => qpat_assum q mp_tac)
       [`s0.vs_alloca_next <= tA.vs_alloca_next`, `tA.vs_alloca_next <= tD.vs_alloca_next`,
        `t4.vs_alloca_next <= tk.vs_alloca_next`, `t4.vs_alloca_next = tD.vs_alloca_next`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  suspend "keyword_operands"
QED

Resume raw_call_kwargs_prepared_entry[keyword_operands]:
  `!x. not_fresh_at s4 x ==>
     FLOOKUP GK x = FLOOKUP G4 x /\ op_taint tnK (Var x) = op_taint tn4 (Var x)` by
    (qpat_assum `ghost_kept_at lo cenv esD s4 G4 tn4 t4 GK tnK`
       (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >> simp[]) >>
  `!x w. not_fresh_at s4 x /\ lookup_var x t4 = SOME w ==>
     lookup_var x tk = SOME w` by
    (qpat_assum `wb_frame cenv esD esK s4 t4 tk`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >> simp[]) >>
  `eval_operand len tk = SOME(n2w(LENGTH bs)) /\ eval_operand dp tk = SOME(n2w(b+32)) /\
   op_taint tnK len = {} /\ op_taint tnK dp = {} /\
   op_prov GK len = NONE /\ op_prov GK dp = SOME(base',cap')` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`!x w. not_fresh_at s4 x /\ _ ==> _`, `!x. not_fresh_at s4 x ==> _ /\ _`,
        `!z. len = Var z \/ dp = Var z ==> _`, `len = Var l`, `dp = Var p`,
        `eval_operand len t4 = _`, `eval_operand dp t4 = _`,
        `op_taint tn4 len = {}`, `op_taint tn4 dp = {}`, `op_prov G4 len = NONE`, `FLOOKUP G4 p = _`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_prov_def] >> metis_tac[]) >>
  `wb_frame cenv esA esD s1 tA t4 /\ ghost_kept_at lo cenv esA s1 GA tnA tA G4 tn4` by
    (conj_tac
     >- (qpat_assum `!sa es0 s0. _ ==> wb_frame _ _ _ _ _ t4` irule >> simp[]) >>
     qpat_assum `!sa es0 s0 G0 tn0. _ ==> ghost_kept_at _ _ _ _ _ _ _ G4 tn4` irule >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon esD.storage_trace) ctx func cenv cx esA tA` by
    (qpat_assum `expr_post _ ctx func cenv cx a es sa s1 s0 esA av addr tA`
       (mp_tac o MATCH_MP exprSimWordArgsTheory.expr_post_state) >> simp[]) >>
  `wb_frame cenv esA esK s1 tA tk /\ ghost_kept_at lo cenv esA s1 GA tnA tA GK tnK` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`wb_frame cenv esA esD s1 tA t4`, `wb_frame cenv esD esK s4 t4 tk`,
        `ghost_kept_at lo cenv esA s1 GA tnA tA G4 tn4`,
        `ghost_kept_at lo cenv esD s4 G4 tn4 t4 GK tnK`,
        `stmt_state_rel _ _ _ _ _ esA tA`, `local_ptrs_reserved cenv s1`,
        `MAP FDOM esA.scopes = MAP FDOM esD.scopes`,
        `s1.cs_next_var <= s4.cs_next_var`, `s1.cs_next_id <= s4.cs_next_id`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[wb_frame_trans,ghost_kept_at_wb_trans]) >>
  `!z. addr = Var z ==> not_fresh_at s1 z` by
    (qpat_assum `lower_value compile_expr cenv (BaseT AddressT) a sa = _` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[exprOperandVarTheory.compile_lower_value_var]) >>
  `post_value_type cenv a = BaseT AddressT` by
    simp[loweringPostsTheory.post_value_type_word,compileEnvTheory.is_word_type_def] >>
  `expr_val_rel cx (BaseT AddressT) av addr tA /\
   op_taint tnA addr = {} /\ op_prov GA addr = NONE` by
    (qpat_assum `expr_post _ _ _ _ _ a _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     qpat_assum `ptr_val_ok cx (post_value_type cenv a) av addr GA tnA tA` mp_tac >>
     qpat_assum `post_value_type cenv a = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodyPtrDefsTheory.ptr_val_ok_def,compileEnvTheory.is_word_type_def]) >>
  `expr_body_pre cenv cx env a es` by
    (irule exprSimRawCallTheory.expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
     fs[exprSimHypsDefsTheory.expr_body_pre_def]) >>
  `!l. addr <> Label l` by
    (qpat_assum `lower_value compile_expr cenv (BaseT AddressT) a sa = _` mp_tac >>
     qpat_assum `expr_body_pre cenv cx env a es` mp_tac >>
     qpat_assum `expr_type a = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `is_word_type (expr_type a)` by simp[compileEnvTheory.is_word_type_def] >>
     drule_all expr_body_pre_lower_value_word_shape >> simp[]) >>
  `!w. eval_operand addr tA = SOME w ==> eval_operand addr tk = SOME w` by
    (qpat_assum `wb_frame cenv esA esK s1 tA tk`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     qpat_assum `!z. addr = Var z ==> not_fresh_at s1 z` mp_tac >>
     qpat_assum `!l. addr <> Label l` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `addr` >>
     simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `expr_val_rel cx (BaseT AddressT) av addr tk` by
    (qpat_assum `expr_val_rel cx (BaseT AddressT) av addr tA` mp_tac >>
     qpat_assum `!w. eval_operand addr tA = SOME w ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringPostsTheory.expr_val_rel_def,compileEnvTheory.is_word_type_def] >> metis_tac[]) >>
  `op_taint tnK addr = {} /\ op_prov GK addr = NONE` by
    (qpat_assum `ghost_kept_at lo cenv esA s1 GA tnA tA GK tnK`
       (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >>
     qpat_assum `!z. addr = Var z ==> not_fresh_at s1 z` mp_tac >>
     qpat_assum `op_taint tnA addr = {}` mp_tac >> qpat_assum `op_prov GA addr = NONE` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `addr` >>
     simp[ptrDisciplineTheory.op_prov_def,ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `!x. MEM x xs ==> ?w. eval_operand x tk = SOME w` by
    (qpat_assum `typed_args_post _ _ _ _ _ _ _ _ esK _ _ kvs tk`
       (mp_tac o REWRITE_RULE [exprSimPrecompilesTheory.typed_args_post_def]) >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_all LIST_REL_MEM_IMP >> metis_tac[]) >>
  `!kw x. ext_call_kwarg kw flags.rcf_kws xs = SOME x ==>
       ?w. eval_operand x tk = SOME w /\ op_taint tnK x = {}` by
    (qpat_assum `!x. MEM x xs ==> ?w. eval_operand x tk = SOME w` mp_tac >>
     qpat_assum `EVERY (\x. op_taint tnK x = {}) xs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> qid_spec_tac `xs` >> qspec_tac (`flags.rcf_kws`,`ks`) >>
     Induct_on `ks` >> Cases_on `xs` >> simp[vyperInterpreterTheory.ext_call_kwarg_def] >>
     rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]) >>
  `(!g. go = SOME g ==> ?w. eval_operand g tk = SOME w /\ op_taint tnK g = {}) /\
   (!v. vo = SOME v ==> ?w. eval_operand v tk = SOME w /\ op_taint tnK v = {})` by
    (qpat_assum `!kw x. ext_call_kwarg _ _ _ = _ ==> _` mp_tac >>
     qpat_assum `go = ext_call_kwarg _ _ _` mp_tac >>
     qpat_assum `vo = ext_call_kwarg _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  suspend "gas_stage"
QED

Resume raw_call_kwargs_prepared_entry[gas_stage]:
  `s4.cs_next_var <= s5.cs_next_var` by
    (qpat_assum `ci_mono s4 s5` (mp_tac o REWRITE_RULE [ci_mono_def]) >> simp[]) >>
  `local_ptrs_reserved cenv s5` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s5 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s5 z)` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `?t6 G6 tn6 gw n.
     eval_operand gas t6 = SOME gw /\ op_taint tn6 gas = {} /\
     ~t6.vs_halted /\ t6.vs_current_bb = s6.cs_current_bb /\
     t6.vs_inst_idx = LENGTH s6.cs_current_insts /\ alloca_history func t6 /\
     t6.vs_memory = tk.vs_memory /\ t6.vs_allocas = tk.vs_allocas /\
     t6.vs_alloca_next = tk.vs_alloca_next /\ t6.vs_fmp = tk.vs_fmp /\
     tn6.t_mem = tnK.t_mem /\ tn6.t_stor = tnK.t_stor /\
     tn6.t_trans = tnK.t_trans /\ tn6.t_imm = tnK.t_imm /\
     (!x. not_fresh_at s5 x ==> lookup_var x t6 = lookup_var x tk /\
       FLOOKUP G6 x = FLOOKUP GK x /\ op_taint tn6 (Var x) = op_taint tnK (Var x)) /\
     (!H. valid_horizon cx st0 H esK.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (tk,GK,tnK) (REPLICATE n F) (OK t6,G6,tn6) /\
       ghost_inv_at (DF H) lo dframe cenv cx esK G6 tn6 t6 /\
       stmt_state_rel H ctx func cenv cx esK t6 /\
       storage_well_formed_on cx esK (FST H) /\
       ghost_kept_at lo cenv esK s5 GK tnK tk G6 tn6)` by
    (Cases_on `go`
     >- (mp_tac (Q.INST [`go` |-> `NONE`, `shadow_go` |-> `NONE`,
           `sa` |-> `s5`, `sb` |-> `s6`, `shadow_sa` |-> `h5`, `shadow_sb` |-> `h6`,
           `shadow_gas` |-> `gas`, `s` |-> `tk`, `G` |-> `GK`, `tn` |-> `tnK`,
           `es` |-> `esK`, `d` |-> `dframe`] raw_call_optional_gas_joint) >>
         (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
         qexistsl_tac [`t`,`G6`,`tn6`,`gw`,`1`] >> simp[] >>
         qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         `REPLICATE 1 F = [F]` by EVAL_TAC >> simp[] >> metis_tac[]) >>
     qpat_assum `(case SOME _ of NONE => _ | SOME _ => _) = (gas,s6)` mp_tac >>
     simp_tac std_ss [] >> disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) >>
     qpat_assum `!g. SOME _ = SOME g ==> _` (qspec_then `gas` mp_tac) >>
     simp_tac std_ss [] >> strip_tac >>
     qexistsl_tac [`tk`,`GK`,`tnK`,`w`,`0`] >>
     simp[bodyPtrDefsTheory.ghost_kept_at_def,fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
     metis_tac[]) >>
  `stmt_state_rel (storage_trace_horizon esK.storage_trace) ctx func cenv cx esK t6 /\
   ghost_inv_at (DF (storage_trace_horizon esK.storage_trace)) lo dframe cenv cx esK G6 tn6 t6` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon esK.storage_trace` mp_tac) >> simp[]) >>
  suspend "outbuf_stage"
QED

Resume raw_call_kwargs_prepared_entry[outbuf_stage]:
  `local_ptrs_reserved cenv s6 /\ sa.cs_next_var <= s6.cs_next_var /\
   sa.cs_next_var <= s5.cs_next_var /\ sa.cs_next_id <= s5.cs_next_id` by
    (qpat_assum `ci_mono s5 s6` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono s4 s5` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `sa.cs_next_var <= s4.cs_next_var` mp_tac >>
     qpat_assum `sa.cs_next_id <= s4.cs_next_id` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv s5` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[local_ptrs_reserved_next_var,arithmeticTheory.LESS_EQ_TRANS]) >>
  `s5.cs_next_var <= s6.cs_next_var` by
    (qpat_assum `ci_mono s5 s6` (mp_tac o REWRITE_RULE [ci_mono_def]) >> simp[]) >>
  `!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s6 z` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists `s5` >> simp[]) >>
  `!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s6 z` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists `s5` >> simp[]) >>
  `(if flags.rcf_max_outsize = 0 then 0 else
       ((flags.rcf_max_outsize+31) DIV 32)*32+32) < dimword (:256)` by
    (Cases_on `flags.rcf_max_outsize = 0` >- simp[] >>
     qpat_assum `flags.rcf_max_outsize <> 0` mp_tac >>
     qpat_assum `expr_body_pre cenv cx env (Call ann (RawCallTarget flags) _ _) es` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule exprSimRawCallTheory.raw_call_pre_flags >> strip_tac >>
     `type_alloc_ok cenv ann` by
       fs[exprSimHypsDefsTheory.expr_body_pre_def,allocLimitsTheory.alloc_limits_expr_def] >>
     Cases_on `flags.rcf_revert_on_failure` >>
     gvs[vyperTypeSystemTheory.raw_call_return_type_def,allocLimitsTheory.type_alloc_ok_def,
         compileEnvTheory.is_word_type_def,compileEnvTheory.type_memory_bytes_def] >>
     `2 ** 64 < dimword (:256)` by simp[wordsTheory.dimword_def] >> fs[] >> decide_tac) >>
  `?u. run_inst_seq (emitted_insts s6 s7) t6 = OK u` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`compile_raw_call_outbuf flags.rcf_max_outsize s6 = _`, `stmt_state_rel _ _ _ _ _ esK t6`,
        `fn_inst_ids_distinct func`, `local_ptrs_reserved cenv s6`, `fn_has_code s6 s7 func`,
        `(if flags.rcf_max_outsize = 0 then 0 else _) < _`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     Cases_on `flags.rcf_max_outsize = 0` >> fs[]
     >- (drule_all raw_call_outbuf_zero_run >> metis_tac[]) >>
     `0 < flags.rcf_max_outsize` by decide_tac >>
     metis_tac[raw_call_outbuf_positive_run,arithmeticTheory.MULT_COMM]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s5 x` by
    (qpat_assum `sa.cs_next_var <= s5.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `wb_frame cenv es esK sa s0 t6` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`s5`, `tk`] >> simp[] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at s5 x ==> _ /\ _` drule >> simp[]) >>
  `return_buf_frame dframe cenv sa t6` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`, `tk`, `sa`] >> simp[] >> rpt strip_tac >>
     `not_fresh_at s5 x` by metis_tac[] >>
     qpat_assum `!x. not_fresh_at s5 x ==> _ /\ _` drule >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G6 tn6` by
    (irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
     qexistsl_tac [`GK`, `tnK`] >> simp[] >> rpt strip_tac >>
     `not_fresh_at s5 x` by metis_tac[] >>
     qpat_assum `!x. not_fresh_at s5 x ==> _ /\ _` drule >> simp[]) >>
  `allocas_from lo t6 /\ lo <= t6.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ lo dframe cenv cx esK G6 tn6 t6`
       (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >> simp[]) >>
  `s0.vs_alloca_next <= t6.vs_alloca_next` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`s0.vs_alloca_next <= tA.vs_alloca_next`, `tA.vs_alloca_next <= tD.vs_alloca_next`,
        `t4.vs_alloca_next = tD.vs_alloca_next`, `t4.vs_alloca_next <= tk.vs_alloca_next`,
        `t6.vs_alloca_next = tk.vs_alloca_next`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME(off,sz) /\
     aid < sa.cs_next_id ==> off+sz <= t6.vs_alloca_next` by
    (qpat_assum `wb_frame cenv es esK sa s0 t6`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     qpat_assum `stmt_state_rel _ _ _ _ _ esK t6`
       (mp_tac o MATCH_MP (cj 2 stmt_state_rel_local_ptrs_alloca)) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[venomMemDefsTheory.alloca_inv_def,venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
  `!name lb sz. local_region cenv es.scopes s0 name lb sz ==> lb+sz <= t6.vs_alloca_next` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ es s0` mp_tac >>
     qpat_assum `s0.vs_alloca_next <= t6.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[bodyMemoryDefsTheory.body_local_region_frontier,arithmeticTheory.LESS_EQ_TRANS]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t6 /\
    t6.vs_alloca_next + pending_alloca_size func t6 <= w2n t6.vs_initial_fmp` by
    (strip_tac >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx esK t6`
       (fn rel => conj_tac
          >- (match_mp_tac (MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp rel) >>
              first_assum ACCEPT_TAC)
          >> mp_tac (MATCH_MP stmt_state_rel_fmp_room rel)) >>
     qpat_assum `ctx_has_dalloca ctx` (fn has => simp[NoAsms,fmp_room_def,has]) >> decide_tac) >>
  qabbrev_tac `t7 = u with vs_inst_idx := LENGTH s7.cs_current_insts` >>
  mp_tac (Q.INST [`sa` |-> `s6`, `sb` |-> `s7`, `sk` |-> `sa`,
    `es0` |-> `es`, `es` |-> `esK`, `s` |-> `t6`, `d` |-> `dframe`,
    `G` |-> `G6`, `tn` |-> `tn6`, `M` |-> `flags.rcf_max_outsize`,
    `n` |-> `if flags.rcf_max_outsize = 0 then 0 else
       ((flags.rcf_max_outsize+31) DIV 32)*32+32`] raw_call_outbuf_joint) >>
  (impl_tac >- (simp[Abbr `t7`] >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _` mp_tac >>
    qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _` mp_tac >>
    qpat_assum `!name lb sz. local_region cenv es.scopes s0 name lb sz ==> _` mp_tac >>
    qpat_assum `t6.vs_alloca_next = tk.vs_alloca_next` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> metis_tac[])) >>
  strip_tac >> suspend "ready_operands"
QED

Resume raw_call_kwargs_prepared_entry[ready_operands]:
  `s5.cs_next_var <= s6.cs_next_var` by
    (qpat_assum `ci_mono s5 s6` (mp_tac o REWRITE_RULE [ci_mono_def]) >> simp[]) >>
  `!x. not_fresh_at s5 x ==>
     lookup_var x t7 = lookup_var x tk /\ FLOOKUP G7 x = FLOOKUP GK x /\
     op_taint tn7 (Var x) = op_taint tnK (Var x)` by
    (qpat_assum `!x. not_fresh_at s5 x ==> _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at s6 x ==> _ /\ _` mp_tac >>
     qpat_assum `s5.cs_next_var <= s6.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `!x. safe_operand s5 x ==> eval_operand x t7 = eval_operand x tk /\
      op_prov G7 x = op_prov GK x /\ op_taint tn7 x = op_taint tnK x` by
    (qpat_assum `!x. not_fresh_at s5 x ==> _ /\ _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >> Cases >>
     simp[exprSafeOperandTheory.safe_operand_def,venomStateTheory.eval_operand_def,
          ptrDisciplineTheory.op_prov_def,ptrDisciplineTheory.op_taint_def]) >>
  `safe_operand s5 addr /\ safe_operand s5 len /\ safe_operand s5 dp` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`!z. addr = Var z ==> not_fresh_at s1 z`, `!l. addr <> Label l`,
        `!z. len = Var z \/ dp = Var z ==> not_fresh_at s4 z`, `len = Var l`, `dp = Var p`,
        `s1.cs_next_var <= s4.cs_next_var`, `s4.cs_next_var <= s5.cs_next_var`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[exprSafeOperandTheory.safe_operand_def] >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `EVERY (safe_operand s5) xs` by
    (`wb_args_shape cenv (K (BaseT (UintT 256))) kws` by
      (qpat_assum `!e ee. MEM e kws /\ _ ==> _` mp_tac >>
       qpat_assum `expr_sim_inv cenv cx env esK` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >> simp[wb_args_shape_def] >> rpt strip_tac >>
       drule expr_body_pre_lower_value_word_shape >> metis_tac[]) >>
     qpat_assum `wb_args_shape cenv _ kws` mp_tac >>
     qpat_assum `lower_word_args cenv _ kws s4 = (xs,s5)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> drule_all lower_word_args_shape_ready >>
     simp[EVERY_MEM,exprSafeOperandTheory.safe_operand_def] >> metis_tac[]) >>
  `!kw x. ext_call_kwarg kw flags.rcf_kws xs = SOME x ==> safe_operand s5 x` by
    (qpat_assum `EVERY (safe_operand s5) xs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> qid_spec_tac `xs` >>
     qspec_tac (`flags.rcf_kws`,`ks`) >> Induct_on `ks` >> Cases_on `xs` >>
     simp[vyperInterpreterTheory.ext_call_kwarg_def] >> rpt strip_tac >>
     gvs[AllCaseEqs()] >> metis_tac[]) >>
  `safe_operand s5 (case vo of NONE => Lit 0w | SOME v => v)` by
    (Cases_on `vo` >> simp[] >> metis_tac[]) >>
  `expr_val_rel cx (BaseT AddressT) av addr t7 /\
   eval_operand len t7 = SOME(n2w(LENGTH bs)) /\ eval_operand dp t7 = SOME(n2w(b+32)) /\
   op_taint tn7 addr = {} /\ op_taint tn7 len = {} /\ op_taint tn7 dp = {} /\
   op_prov G7 addr = NONE /\ op_prov G7 len = NONE /\ op_prov G7 dp = SOME(base',cap')` by
    (qpat_assum `!x. safe_operand s5 x ==> _ /\ _ /\ _` mp_tac >>
     map_every (fn q => qpat_assum q mp_tac)
       [`safe_operand s5 addr`, `safe_operand s5 len`, `safe_operand s5 dp`,
        `expr_val_rel cx (BaseT AddressT) av addr tk`,
        `eval_operand len tk = _`, `eval_operand dp tk = _`,
        `op_taint tnK addr = {}`, `op_taint tnK len = {}`, `op_taint tnK dp = {}`,
        `op_prov GK addr = NONE`, `op_prov GK len = NONE`, `op_prov GK dp = _`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringPostsTheory.expr_val_rel_def,compileEnvTheory.is_word_type_def]) >>
  `safe_operand s6 gas` by
    (qpat_assum `(case go of NONE => _ | SOME _ => _) = (gas,s6)` mp_tac >>
     qpat_assum `go = ext_call_kwarg _ _ _` mp_tac >>
     qpat_assum `!kw x. ext_call_kwarg _ _ _ = _ ==> safe_operand s5 x` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `go` >> simp[] >>
     metis_tac[exprSafeOperandTheory.emit_op_safe_operand]) >>
  `eval_operand gas t7 = SOME gw /\ op_taint tn7 gas = {}` by
    (qpat_assum `!x. not_fresh_at s6 x ==> _ /\ _` mp_tac >>
     qpat_assum `safe_operand s6 gas` mp_tac >>
     qpat_assum `eval_operand gas t6 = SOME gw` mp_tac >>
     qpat_assum `op_taint tn6 gas = {}` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `gas` >>
     simp[exprSafeOperandTheory.safe_operand_def,venomStateTheory.eval_operand_def,
          ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `op_taint tn7 (case vo of NONE => Lit 0w | SOME v => v) = {}` by
    (qpat_assum `!x. safe_operand s5 x ==> _ /\ _ /\ _` mp_tac >>
     qpat_assum `safe_operand s5 (case vo of NONE => _ | SOME _ => _)` mp_tac >>
     qpat_assum `!v. vo = SOME v ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `vo` >>
     simp[ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  suspend "ready_memory"
QED

Resume raw_call_kwargs_prepared_entry[ready_memory]:
  `b+32+LENGTH bs <= tD.vs_alloca_next` by
    (qpat_assum `expr_store_bound cx _ (BytesV bs) data tD`
       (mp_tac o REWRITE_RULE [exprSimMemDefsTheory.expr_store_bound_def]) >>
     map_every (fn q => qpat_assum q mp_tac)
       [`evaluate_type _ _ = SOME (BaseTV (BytesT (Dynamic cap)))`,
        `eval_operand data tD = SOME(n2w b)`, `b < dimword (:256)`,
        `post_value_type cenv d = _`, `expr_type d = _`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[compileEnvTheory.is_word_type_def,exprSimPropsTheory.val_store_size_def] >>
     qspec_then `LENGTH bs` mp_tac exprSimPropsTheory.le_word_size_mul >> rpt strip_tac >> decide_tac) >>
  `b+32+LENGTH bs <= t6.vs_alloca_next` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`b+32+LENGTH bs <= tD.vs_alloca_next`, `t4.vs_alloca_next = tD.vs_alloca_next`,
        `t4.vs_alloca_next <= tk.vs_alloca_next`, `t6.vs_alloca_next = tk.vs_alloca_next`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `mem_bytes_at (b+32) (LENGTH bs) t7.vs_memory = bs /\
   (!mem. mem_agree_outside tn7.t_mem t7.vs_memory mem ==>
       mem_bytes_at (b+32) (LENGTH bs) mem = bs)` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`!mem. mem_agree_outside tnK.t_mem _ _ ==> _`, `t7.vs_memory = t6.vs_memory`,
        `t6.vs_memory = tk.vs_memory`, `tn6.t_mem = tnK.t_mem`, `!i. i IN tn7.t_mem <=> _`,
        `b+32+LENGTH bs <= t6.vs_alloca_next`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `mem_bytes_at (b+32) (LENGTH bs) t7.vs_memory = bs` by
       metis_tac[bodyPtrDefsTheory.mem_agree_outside_def] >> simp[] >>
     `!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tnK.t_mem` by
       (drule representationCleanPtrTheory.robust_mem_bytes_at_clean >> simp[]) >>
     `mem_bytes_at (b+32) (LENGTH bs) t7.vs_memory =
      mem_bytes_at (b+32) (LENGTH bs) mem` by
       (irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
        fs[bodyPtrDefsTheory.mem_agree_outside_def] >> rpt strip_tac >>
        first_x_assum irule >> simp[] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
     metis_tac[]) >>
  `stmt_state_rel (storage_trace_horizon esK.storage_trace) ctx func cenv cx esK t7` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ t7 /\ _`
       (qspec_then `storage_trace_horizon esK.storage_trace` mp_tac) >> simp[]) >>
  drule_all raw_call_outbuf_separated >> strip_tac >>
  `s6.cs_next_var <= s7.cs_next_var /\ s5.cs_next_var <= s7.cs_next_var` by
    (qpat_assum `ci_mono s6 s7` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `s5.cs_next_var <= s6.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `safe_operand s7 ov /\ safe_operand s7 op` by
    (qpat_assum `!x. ov = Var x \/ op = Var x ==> not_fresh_at s7 x` mp_tac >>
     qpat_assum `op_prov G7 ov = SOME _` mp_tac >> qpat_assum `op_prov G7 op = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `ov` >> Cases_on `op` >>
     simp[exprSafeOperandTheory.safe_operand_def,ptrDisciplineTheory.op_prov_def]) >>
  `EVERY (safe_operand s7)
     [addr;len;dp;gas;(case vo of NONE => Lit 0w | SOME v => v);ov;op]` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`safe_operand s5 addr`, `safe_operand s5 len`, `safe_operand s5 dp`,
        `safe_operand s5 (case vo of NONE => _ | SOME _ => _)`,
        `safe_operand s6 gas`, `safe_operand s7 ov`, `safe_operand s7 op`,
        `s6.cs_next_var <= s7.cs_next_var`, `s5.cs_next_var <= s7.cs_next_var`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[exprSafeOperandTheory.safe_operand_mono]) >>
  `!x. MEM (Var x) [addr;len;dp;gas;(case vo of NONE => Lit 0w | SOME v => v);ov;op] ==>
      not_fresh_at s7 x` by
    (qpat_assum `EVERY (safe_operand s7) _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[EVERY_MEM,exprSafeOperandTheory.safe_operand_def] >> metis_tac[]) >>
  `(flags.rcf_max_outsize = 0 ==> ov = op)` by
    (qpat_assum `compile_raw_call_outbuf flags.rcf_max_outsize s6 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >> strip_tac >>
     gvs[builtinSystemTheory.compile_raw_call_outbuf_def,compileEnvTheory.comp_bind_def,
         compileEnvTheory.comp_return_def] >> pairarg_tac >> gvs[]) >>
  suspend "assemble"
QED

Resume raw_call_kwargs_prepared_entry[assemble]:
  qexistsl_tac [`t7`,`G7`,`tn7`,`n`,`b'`,`gw`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `H` >> strip_tac >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (tk,GK,tnK) (REPLICATE n F) (OK t7,G7,tn7)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (t6,G6,tn6) [] _`
        (qspecl_then [`DF H`,`gas_explicit_sites ctx shadow_ctx`] mp_tac) >>
     qpat_assum `gas_origin_ptr_path _ (tk,GK,tnK) _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,APPEND_NIL]) >>
  `valid_horizon cx st0 H esD.storage_trace` by
    (qpat_assum `eval_exprs cx kws _ = _` mp_tac >>
     qpat_assum `valid_horizon cx st0 H esK.storage_trace` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `storage_trace_frame (eval_exprs cx kws)` by simp[cj 6 evaluate_storage_trace_frame] >>
     drule_all storage_trace_frame_prefix >> simp[] >> strip_tac >>
     gvs[] >> metis_tac[gasOutcomeFullTheory.valid_horizon_append]) >>
  `valid_horizon cx st0 H esA.storage_trace` by
    (qpat_assum `bind (eval_expr cx d) (read_result cx) _ = _` mp_tac >>
     qpat_assum `valid_horizon cx st0 H esD.storage_trace` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `storage_trace_frame (bind (eval_expr cx d) (read_result cx))` by
       simp[cj 5 evaluate_storage_trace_frame,storage_trace_frame_bind,storage_trace_frame_read_result] >>
     drule_all storage_trace_frame_prefix >> simp[] >> strip_tac >>
     gvs[] >> metis_tac[gasOutcomeFullTheory.valid_horizon_append]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `bind (eval_expr cx a) (read_result cx) _ = _` mp_tac >>
     qpat_assum `valid_horizon cx st0 H esA.storage_trace` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `storage_trace_frame (bind (eval_expr cx a) (read_result cx))` by
       simp[cj 5 evaluate_storage_trace_frame,storage_trace_frame_bind,storage_trace_frame_read_result] >>
     drule_all storage_trace_frame_prefix >> simp[] >> strip_tac >>
     gvs[] >> metis_tac[gasOutcomeFullTheory.valid_horizon_append]) >>
  qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
     (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> stmt_state_rel _ _ _ _ _ _ t7 /\ _`
     (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `data = Var x` SUBST_ALL_TAC >>
  simp[] >>
  conj_tac >-
    (qpat_assum `expr_store_bound cx (post_value_type cenv d) (BytesV bs) _ tD` mp_tac >>
     qpat_assum `post_value_type cenv d = expr_type d` mp_tac >>
     qpat_assum `expr_type d = BaseT (BytesT (Dynamic cap))` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  conj_tac >-
    (qpat_assum `EVERY (safe_operand s5) xs` mp_tac >>
     qpat_assum `!x. safe_operand s5 x ==> eval_operand x t7 = eval_operand x tk /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
  conj_tac >-
    (qpat_assum `!name lb sz. local_region cenv esK.scopes t7 name lb sz ==> _` mp_tac >>
     simp[arithmeticTheory.MULT_COMM]) >>
  qpat_assum `cenv.ce_is_ctor ==> !name tv v off. _` mp_tac >>
  simp[arithmeticTheory.MULT_COMM]
QED

Finalise raw_call_kwargs_prepared_entry
