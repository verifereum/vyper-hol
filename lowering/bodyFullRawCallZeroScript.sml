(* Concrete raw_call suffix at one endpoint for every valid storage horizon. *)
Theory bodyFullRawCallZero
Ancestors
  bodyFullPreds bodySimFull bodyFullShared bodyFullAllocaFresh
  gasOutcomeFullCompose gasShadowCompile gasShadow
  rawCallSourceDomainPtr rawCallShapePtr rawCallBufferPtr rawCallMemoryFramePtr
  rawCallOutcomeLengthPtr exprSimHypsDefs exprLowering builtinSystem
  loweringPosts vyperStorageFootprint vyperAST vyperInterpreter vyperState
  venomState list bodyMemoryDefs freshWrites vyperEvalExprPreservesScopesDom
  vyperTypeEnvPreservation bodyFullExtCallGhost oracleCallOriginPtr
  bodyFullUnwrapSlotPost bodyPtrMakeArrayEmission exprSimHash decoderArraySetupPtr
  vyperFiniteStoragePreservation rawCallFinishCodePtr fragGasEmitCtrl callStepPtr
  bodyFullRawCallForward

Theorem raw_call_zero_full_finish:
 (!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env cx ty ann flags
  args dflt es st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0
  sc shadow_sc s7 shadow_s7 addr dp dl gas_op value_op ov op result
  mid t G tn marks target bs kvs amount source_gas aw vw gw
  b region_base region_size.
  flags.rcf_max_outsize = 0 /\
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env (Call ann (RawCallTarget flags) args dflt) es /\
  compile_expr cenv ty (Call ann (RawCallTarget flags) args dflt) sa = (vv,sb) /\
  compile_expr cenv ty (gas_shadow_expr (Call ann (RawCallTarget flags) args dflt)) shadow_sa = (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_state sc shadow_sc /\ gas_shadow_state s7 shadow_s7 /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_has_code sc sb func /\ fn_has_code shadow_sc shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sc /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
           not_fresh_at sa x /\ not_fresh_at sc x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
           not_fresh_at sa x /\ not_fresh_at sc x) /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
  ~flags.rcf_is_delegate /\ (~flags.rcf_is_static \/ amount = 0) /\
  flags.rcf_max_outsize < dimword(:256) /\
  ann = raw_call_return_type flags /\ dflt = NONE /\
  compile_raw_call_outbuf flags.rcf_max_outsize sc = ((ov,op),s7) /\
  compile_raw_call_outbuf flags.rcf_max_outsize shadow_sc = ((ov,op),shadow_s7) /\
  compile_raw_call_finish addr dp dl gas_op value_op
   (if flags.rcf_is_static then StaticCall else RegularCall)
   flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s7 = (result,sb) /\
  compile_raw_call_finish addr dp dl gas_op value_op
   (if flags.rcf_is_static then StaticCall else RegularCall)
   flags.rcf_max_outsize flags.rcf_revert_on_failure ov op shadow_s7 = (result,shadow_sb) /\
  vv = (if flags.rcf_max_outsize = 0 then StackValue ann result
        else LocatedValue ann (mk_ptr result LocMemory)) /\
  (!tail. eval_exprs cx args
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (INL (AddressV target::BytesV bs::kvs),mid with gas_obs := tail)) /\
  LENGTH kvs = LENGTH flags.rcf_kws /\
  raw_call_value flags.rcf_kws kvs = SOME amount /\
  source_gas = forwarded_gas default_evm_gas_limit
                 (ext_call_kwarg EKGas flags.rcf_kws kvs) /\
  gas_admissible (eval_expr cx (Call ann (RawCallTarget flags) args dflt)) expr_vv_res_ok es /\
  gas_admissible (eval_raw_call cx flags target bs amount source_gas)
                expr_vv_res_ok mid /\
  expr_sim_inv cenv cx env mid /\ mid.gas_obs = [] /\
  storage_trace_domain cx st0 mid.storage_trace /\
  return_buf_frame d cenv sa s0 /\ return_buf_frame d cenv sc t /\
  alloca_history func s0 /\ alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ allocas_from lo t /\
  lo <= t.vs_alloca_next /\ ~t.vs_halted /\
  t.vs_current_bb = sc.cs_current_bb /\
  t.vs_inst_idx = LENGTH sc.cs_current_insts /\
  eval_operand addr t = SOME aw /\ w2w aw = target /\
  eval_operand gas_op t = SOME gw /\
  (~flags.rcf_is_static ==> eval_operand value_op t = SOME vw /\ w2n vw = amount) /\
  eval_operand dp t = SOME (n2w (b+32)) /\
  eval_operand dl t = SOME (n2w (LENGTH bs)) /\
  b+32 < dimword(:256) /\ LENGTH bs < dimword(:256) /\
  (LENGTH bs = 0 \/ b+32+LENGTH bs <= t.vs_alloca_next) /\
  op_prov G dp = SOME (region_base,region_size) /\
  region_base <= b /\ b+32+LENGTH bs <= region_base+region_size /\
  mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
  (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
  EVERY (\arg. (!x. arg = Var x ==> not_fresh_at sc x) /\
                (!l. arg <> Label l) /\ op_taint tn arg = {})
   (if flags.rcf_is_static then [gas_op;addr;dp;dl]
    else [gas_op;addr;value_op;dp;dl]) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
          lookup_var x t = SOME w) /\
  (!aid site. FLOOKUP s0.vs_allocas aid = SOME site ==>
               FLOOKUP t.vs_allocas aid = SOME site) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
     (!n a z. local_region cenv es.scopes s0 n a z ==>
                 off+sz <= a \/ a+z <= off) ==>
     mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
  locals_kept cenv es mid s0 t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G tn t)
  ==>
  gas_outcome_full
   (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (cx_tops cx) cx st0 (eval_raw_call cx flags target bs amount source_gas)
   (mid,t,G,tn)
   (\H res ee J un u. ?tv. res = INL tv /\
    vv_post H ctx func cenv cx (Call ann (RawCallTarget flags) args dflt) es sa sb s0 ee tv vv u /\
    vv_store_bound cx (expr_type (Call ann (RawCallTarget flags) args dflt)) (lowered_value_type cenv (Call ann (RawCallTarget flags) args dflt)) ee tv vv u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx ee J un u /\
    ptr_vv_ok cx (post_value_type cenv (Call ann (RawCallTarget flags) args dflt)) tv vv ee J un u /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Call ann (RawCallTarget flags) args dflt)) = SOME rt /\
       eval_operand (vv_operand vv) u = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside un.t_mem u.vs_memory mem ==>
              val_in_memory rt val (w2n w) mem)) /\
    (!ty' op'. vv = StackValue ty' op' /\ ~is_word_type (post_value_type cenv (Call ann (RawCallTarget flags) args dflt)) ==>
              ptr_buf_ok cenv (Call ann (RawCallTarget flags) args dflt) op' J u) /\
    (!ty' p. vv = LocatedValue ty' p /\ p.ptr_location = LocMemory ==>
             ptr_buf_ok cenv (Call ann (RawCallTarget flags) args dflt) p.ptr_operand J u) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 J un)
   (\H res ee gt r. expr_exit res r))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace`
      (fn th => qpat_assum
        `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
           mid.storage_trace`
        (strip_assume_tac o MATCH_MP th))) >>
  drule_all (Q.INST [`flags` |-> `flags`, `target` |-> `target`,
    `data` |-> `bs`, `amount` |-> `amount`, `gas` |-> `source_gas`]
    raw_call_prepared_source_total) >> strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0
    (SND (adopt_call_outcome rq outcome es1)).storage_trace`)
  >- (irule gas_outcome_full_bad_nil >> simp[]) >>
  `cs_extends sc s7 /\ cs_extends s7 sb` by
    (qspecl_then [`flags.rcf_max_outsize`,`sc`] mp_tac
       exprLoweringPropsTheory.ci_mono_compile_raw_call_outbuf >>
     qspecl_then [`addr`,`dp`,`dl`,`gas_op`,`value_op`,
       `if flags.rcf_is_static then StaticCall else RegularCall`,
       `flags.rcf_max_outsize`,`flags.rcf_revert_on_failure`,`ov`,`op`,`s7`]
       mp_tac exprLoweringPropsTheory.ci_mono_compile_raw_call_finish >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  qspecl_then [`sc`,`s7`,`sb`,`func`] mp_tac fragExecTheory.fn_has_code_split >>
  simp[] >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `!tail. eval_exprs cx args _ = _`
      (qspec_then `[]` (mp_then Any mp_tac eval_exprs_preserves_scopes_dom)) >>
     simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) ==>
    off + sz <= t.vs_alloca_next` by
    (rpt strip_tac >>
     `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by res_tac >>
     `alloca_inv t` by fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
     fs[venomMemDefsTheory.alloca_inv_def,venomMemDefsTheory.alloca_next_valid_def] >>
     res_tac) >>
  `!name b sz. local_region cenv es.scopes s0 name b sz ==>
    b + sz <= t.vs_alloca_next` by
    (qx_genl_tac [`local_name`,`local_base`,`local_size`] >>
     disch_then (qx_choosel_then [`entry_local`,`local_ptr`,`local_word`]
       strip_assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.local_region_def]) >>
     qpat_x_assum `local_base = _` SUBST_ALL_TAC >>
     `not_fresh_at sa local_ptr` by
       (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
     `lookup_var local_ptr t = SOME local_word` by res_tac >>
     drule_all lookup_scopes_same_fdoms_some >>
     simp[optionTheory.IS_SOME_EXISTS] >>
     disch_then (qx_choose_then `entry_mid` assume_tac) >>
     `local_region cenv mid.scopes t local_name (w2n local_word) local_size` by
       (simp[loweringStateRelDefsTheory.local_region_def] >>
        qexistsl_tac [`entry_mid`,`local_ptr`,`local_word`] >> simp[]) >>
     drule_all body_local_region_frontier >> simp[]) >>
  `wb_frame cenv es mid sa s0 t` by
    (rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "zero"
QED

Resume raw_call_zero_full_finish[zero]:
  qpat_x_assum `compile_raw_call_outbuf _ sc = _`
    (mp_tac o REWRITE_RULE [builtinSystemTheory.compile_raw_call_outbuf_def,
      compileEnvTheory.comp_bind_def,compileEnvTheory.comp_return_def]) >>
  simp[compileEnvTheory.comp_bind_def,compileEnvTheory.comp_return_def] >>
  pairarg_tac >> strip_tac >>
  rename1 `compile_alloc_buffer 0 sc = (buf_alloc,out_cs)` >>
  qpat_assum `compile_alloc_buffer 0 sc = (buf_alloc,out_cs)`
    (fn alloc_th => qpat_x_assum `_ = ((ov,op),s7)`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [alloc_th])) >>
  qpat_x_assum `_ = ov` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `_ = op` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `out_cs = s7` (SUBST_ALL_TAC o SYM) >>
  `0 < dimword (:256)` by simp[] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace`
      (fn th => qpat_assum
        `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
           mid.storage_trace`
        (strip_assume_tac o MATCH_MP th))) >>
  drule_all (Q.INST [`PG` |-> `PG`, `G` |-> `G`, `tn` |-> `tn`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``, gamma |-> ``:256``]
      alloc_buffer_origin_ptr_path)) >>
  disch_then (qspecl_then [`tn`,`shadow_ctx`,`PG`,`G`]
    (qx_choosel_then [`q_alloc`,`w_alloc`,`t_alloc`,`G_alloc`,`tn_alloc`]
      strip_assume_tac)) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t_alloc /\
    ghost_inv_at (DF H) lo d cenv cx mid G_alloc tn_alloc t_alloc` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` (fn th => qpat_assum
         `valid_horizon cx st0 H mid.storage_trace`
         (strip_assume_tac o MATCH_MP th))) >>
     conj_tac
     >- (qpat_assum `!H'. stmt_state_rel H' _ _ _ _ _ t ==> _`
           (qspec_then `H` irule) >> first_assum ACCEPT_TAC) >>
     mp_tac (Q.INST [`D` |-> `DF H`, `sa` |-> `sc`, `es` |-> `mid`,
       `s` |-> `t`, `t` |-> `t_alloc`, `G'` |-> `G_alloc`,
       `tn'` |-> `tn_alloc`, `e` |-> `w2n (w_alloc:256 word)`]
       (INST_TYPE [alpha |-> ``:256``] alloc_buffer_ghost_inv_at)) >>
     impl_tac >- simp[] >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G_alloc tn_alloc` by
    (mp_tac (Q.INST [`es0` |-> `es`, `sk` |-> `sa`, `s` |-> `t`,
       `G'` |-> `G_alloc`, `tn'` |-> `tn_alloc`,
       `e` |-> `w2n (w_alloc:256 word)`]
       (INST_TYPE [alpha |-> ``:num # num``] alloc_buffer_ghost_kept_at)) >>
     impl_tac
     >- (simp[] >> conj_tac
         >- (rpt strip_tac >>
             qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) ==> _`
               (drule_then ACCEPT_TAC)) >>
         first_assum ACCEPT_TAC) >> simp[]) >>
  `t_alloc.vs_memory = t.vs_memory` by
    (qpat_assum `t_alloc with <| vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _ |> = t`
       (mp_tac o Q.AP_TERM `\z. z.vs_memory`) >> simp[]) >>
  `t_alloc.vs_labels = t.vs_labels` by
    (qpat_assum `t_alloc with <| vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _ |> = t`
       (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >> simp[]) >>
  `wb_frame cenv es mid sa s0 t_alloc` by
    (mp_tac (Q.INST [`sm` |-> `sc`, `s` |-> `t`, `t` |-> `t_alloc`,
       `es'` |-> `mid`, `scopes` |-> `mid.scopes`]
       exprSimHashTheory.wb_frame_allocating_tail) >>
     impl_tac >- (simp[] >> rpt strip_tac >> res_tac) >> simp[]) >>
  `!arg. (!x. arg = Var x ==> not_fresh_at sc x) ==>
    eval_operand arg t_alloc = eval_operand arg t /\
    op_taint tn_alloc arg = op_taint tn arg /\
    op_prov G_alloc arg = op_prov G arg` by
    (gen_tac >> strip_tac >>
     irule (Q.INST [`st` |-> `sc`]
       decoderArraySetupPtrTheory.old_operand_ghost_frame) >>
     simp[] >> qexists_tac `sc` >> simp[]) >>
  suspend "zeroCall"
QED

Resume raw_call_zero_full_finish[zeroCall]:
  markerLib.RESUME_TAC >>
  mp_tac (Q.INST [`addr` |-> `addr`,`dp` |-> `dp`,`dl` |-> `dl`,
    `gas` |-> `gas_op`,`value` |-> `value_op`,
    `ct` |-> `if flags.rcf_is_static then StaticCall else RegularCall`,
    `n` |-> `flags.rcf_max_outsize`,`rev` |-> `flags.rcf_revert_on_failure`,
    `ov` |-> `buf_alloc.buf_operand`,`op` |-> `buf_alloc.buf_operand`,
    `sa` |-> `out_cs`,`result` |-> `result`,`sb` |-> `sb`,`func` |-> `func`]
    rawCallFinishCodePtrTheory.raw_call_finish_call_code) >>
  (impl_tac >- (Cases_on `flags.rcf_is_static` >> simp[])) >>
  disch_then (qx_choosel_then [`call_out`,`call_cs`,`call_bb`] strip_assume_tac) >>
  qabbrev_tac `call_result = Var call_out` >>
  `(case if flags.rcf_is_static then StaticCall else RegularCall of
      RegularCall => emit_op CALL
        [gas_op;addr;value_op;dp;dl;Var q_alloc;Lit 0w]
    | DelegateCall => emit_op DELEGATECALL
        [gas_op;addr;dp;dl;Var q_alloc;Lit 0w]
    | StaticCall => emit_op STATICCALL
        [gas_op;addr;dp;dl;Var q_alloc;Lit 0w]) =
    emit_op (if flags.rcf_is_static then STATICCALL else CALL)
      (if flags.rcf_is_static then [gas_op;addr;dp;dl;Var q_alloc;Lit 0w]
       else [gas_op;addr;value_op;dp;dl;Var q_alloc;Lit 0w])` by
    (Cases_on `flags.rcf_is_static` >> simp[]) >>
  `emit_op (if flags.rcf_is_static then STATICCALL else CALL)
    (if flags.rcf_is_static then [gas_op;addr;dp;dl;Var q_alloc;Lit 0w]
     else [gas_op;addr;value_op;dp;dl;Var q_alloc;Lit 0w])
    out_cs = (call_result,call_cs)` by
    (qpat_x_assum `_ = (call_result,call_cs)` mp_tac >>
     Cases_on `flags.rcf_is_static` >> simp[Abbr `call_result`]) >>
  mp_tac (Q.INST [`opc` |-> `if flags.rcf_is_static then STATICCALL else CALL`,
    `args` |-> `if flags.rcf_is_static then [gas_op;addr;dp;dl;Var q_alloc;Lit 0w]
                else [gas_op;addr;value_op;dp;dl;Var q_alloc;Lit 0w]`,
    `sm` |-> `out_cs`,`op` |-> `call_result`,`sb` |-> `call_cs`,
    `fn` |-> `func`,`s` |-> `t_alloc`]
    bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  `EVERY (\arg. (!x. arg = Var x ==> not_fresh_at sc x) /\
      (!l. arg <> Label l) /\ op_taint tn arg = {}) [gas_op;addr;dp;dl]` by
    (qpat_x_assum `EVERY _ (if flags.rcf_is_static then _ else _)` mp_tac >>
     Cases_on `flags.rcf_is_static` >> simp[] >> rpt strip_tac >> simp[]) >>
  qpat_assum `EVERY _ [gas_op;addr;dp;dl]`
    (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  `eval_operand gas_op t_alloc = SOME gw /\
   eval_operand addr t_alloc = SOME aw /\
   eval_operand dp t_alloc = SOME (n2w (b+32)) /\
   eval_operand dl t_alloc = SOME (n2w (LENGTH bs))` by simp[] >>
  `read_memory (b+32) (LENGTH bs) t_alloc = bs` by
    simp[venomStateTheory.read_memory_def, GSYM valueEncodingDefsTheory.mem_bytes_at_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace`
      (fn th => qpat_assum
        `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
           mid.storage_trace`
        (strip_assume_tac o MATCH_MP th))) >>
  qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace)
    ctx func cenv cx mid t_alloc`
    (strip_assume_tac o REWRITE_RULE [exprLoweringPropsTheory.stmt_state_rel_def]) >>
  qmatch_asmsub_abbrev_tac
    `get_instruction bb t_alloc.vs_inst_idx = SOME call_inst` >>
  qspecl_then [`storage_trace_horizon mid.storage_trace`, `func`, `cenv`,
    `cx`, `mid`, `t_alloc`, `call_inst`, `gw`, `aw`,
    `if flags.rcf_is_static then 0w else vw`,
    `n2w (b+32):256 word`, `n2w (LENGTH bs):256 word`, `w_alloc`, `0w:256 word`,
    `flags.rcf_is_static`, `tmp`, `target`,
    `if flags.rcf_is_static then NONE else SOME amount`, `rq`, `outcome`, `es1`] mp_tac
    extCallOracleStepTheory.exec_ext_call_oracle_step >>
  impl_tac
  >- (simp[Abbr `call_inst`, venomInstTheory.mk_inst_def] >>
      Cases_on `flags.rcf_is_static` >> simp[]) >>
  disch_then (qx_choose_then `call_state` strip_assume_tac) >>
  `~flags.rcf_is_static ==> eval_operand value_op t_alloc = SOME vw` by
    (strip_tac >>
     qpat_x_assum `EVERY _ (if flags.rcf_is_static then _ else _)` mp_tac >>
     simp[] >> rpt strip_tac >> simp[]) >>
  qabbrev_tac `u_call = update_var tmp
    (if outcome.co_success then 1w else 0w) call_state` >>
  `~t_alloc.vs_call_ctx.cc_static` by
    fs[loweringStateRelDefsTheory.state_rel_def] >>
  `step_inst_base call_inst t_alloc = OK u_call` by
    (qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `flags.rcf_is_static` >>
     simp[Abbr `call_inst`, Abbr `u_call`, venomInstTheory.mk_inst_def,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomStateTheory.eval_operand_def]) >>
  `call_state.vs_vars = t_alloc.vs_vars /\
   call_state.vs_allocas = t_alloc.vs_allocas /\
   call_state.vs_alloca_next = t_alloc.vs_alloca_next /\
   call_state.vs_fmp = t_alloc.vs_fmp /\
   call_state.vs_labels = t_alloc.vs_labels /\
   call_state.vs_current_bb = t_alloc.vs_current_bb /\
   call_state.vs_inst_idx = t_alloc.vs_inst_idx /\
   call_state.vs_halted = t_alloc.vs_halted` by
    (qpat_assum `call_state = _` (fn th => once_rewrite_tac [th]) >> simp[]) >>
  `?p. dp = Var p /\ FLOOKUP G_alloc p = SOME (region_base,region_size)` by
    (`op_prov G_alloc dp = SOME (region_base,region_size)` by simp[] >>
     Cases_on `dp` >>
     qpat_x_assum `op_prov G_alloc _ = SOME (region_base,region_size)`
       (mp_tac o REWRITE_RULE [ptrDisciplineTheory.op_prov_def]) >> simp[]) >>
  rename1 `dp = Var data_ptr` >>
  `op_taint tn_alloc (Var q_alloc) = {}` by
    fs[bodyPtrDefsTheory.ptr_covers_def] >>
  `op_taint tn (Lit 0w) = {} /\ op_taint tn_alloc (Lit 0w) = {}` by
    simp[ptrDisciplineTheory.op_taint_def] >>
  `EVERY (\arg. op_taint tn_alloc arg = {}) call_inst.inst_operands` by
    (qpat_x_assum `EVERY _ (if flags.rcf_is_static then _ else _)` mp_tac >>
     Cases_on `flags.rcf_is_static` >>
     simp[Abbr `call_inst`, venomInstTheory.mk_inst_def] >>
     rpt strip_tac >> simp[]) >>
  `!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn_alloc.t_mem` by
    (rpt strip_tac >>
     `i NOTIN tn.t_mem` by res_tac >>
     `i < t.vs_alloca_next` by decide_tac >>
     qpat_assum `!i. i IN tn_alloc.t_mem <=> _` (qspec_then `i` mp_tac) >>
     simp[] >> decide_tac) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    access_ok lo G_alloc func call_inst t_alloc /\
    taint_ok func tn_alloc call_inst t_alloc /\
    inst_mem_below_frontier call_inst t_alloc /\ allocas_from lo t_alloc /\
    stor_taint_ok_at (DF H) tn_alloc t_alloc` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid t_alloc /\ _`
       (qspec_then `H` (fn th => qpat_assum
         `valid_horizon cx st0 H mid.storage_trace`
         (strip_assume_tac o MATCH_MP th))) >>
     qspecl_then [`call_inst`,`gas_op`,`addr`,`value_op`,`dp`,`dl`,
       `Var q_alloc`,`Lit 0w`,`t_alloc`,`n2w (b+32):256 word`,
       `n2w (LENGTH bs):256 word`,`w_alloc`,`0w:256 word`,
       `tn_alloc`,`G_alloc`,`lo`,`func`,`DF H`,`d`,`cenv`,`cx`,`mid`] mp_tac
       (Q.GENL [`inst`,`gas`,`addr`,`value`,`ao`,`az`,`ro`,`rz`,`s`,
         `aw`,`an`,`rw`,`rn`,`tn`,`G`,`lo`,`fn`,`D`,`d`,`cenv`,`cx`,`es`]
         bodyFullExtCallGhostTheory.extcall_call_pointer_conditions) >>
     impl_tac
     >- (Cases_on `flags.rcf_is_static` >>
         simp[Abbr `call_inst`, venomInstTheory.mk_inst_def,
           venomStateTheory.eval_operand_def] >>
         rpt conj_tac >> rpt strip_tac >>
         `LENGTH bs <> 0` by simp[] >> decide_tac) >>
     simp[]) >>
  `~t_alloc.vs_halted` by
    (qpat_assum `t_alloc with <| vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _ |> = t`
       (mp_tac o Q.AP_TERM `\z. z.vs_halted`) >> simp[]) >>
  (Q.SUBGOAL_THEN
   `((call_inst.inst_opcode = CALL /\
     call_inst.inst_operands = [gas_op;addr;value_op;dp;dl;Var q_alloc;Lit 0w]) \/
    (call_inst.inst_opcode = STATICCALL /\
     call_inst.inst_operands = [gas_op;addr;dp;dl;Var q_alloc;Lit 0w]))`
    assume_tac
   >- (Cases_on `flags.rcf_is_static` >>
       simp[Abbr `call_inst`,venomInstTheory.mk_inst_def])) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_edge (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t_alloc,G_alloc,tn_alloc) []
      (OK (u_call with vs_inst_idx := SUC t_alloc.vs_inst_idx),
       step_prov PG G_alloc call_inst u_call,
       step_taint call_inst t_alloc u_call tn_alloc)` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       access_ok _ _ _ _ _ /\ _`
       (qspec_then `H` (fn th => qpat_assum
         `valid_horizon cx st0 H mid.storage_trace`
         (strip_assume_tac o MATCH_MP th))) >>
     qspecl_then [`call_inst`,`gas_op`,`addr`,`value_op`,`dp`,`dl`,
       `Var q_alloc`,`Lit 0w`,`lo`,`G_alloc`,`func`,`t_alloc`,`tn_alloc`,
       `ctx`,`DF H`,`bb`,`u_call`,`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac
       (Q.GENL [`inst`,`gas`,`addr`,`value`,`ao`,`az`,`ro`,`rz`,`lo`,`G`,
         `fn`,`s`,`tn`,`ctx`,`D`,`bb`,`u`,`explicit`,`PG`]
         oracleCallOriginPtrTheory.call_origin_ptr_edge) >>
     impl_tac >- simp[] >> simp[]) >>
  `!off len. mem_bytes_at off len call_state.vs_memory =
             mem_bytes_at off len t_alloc.vs_memory` by
    (rpt gen_tac >>
     qpat_assum `call_state.vs_memory = _` (fn th => rewrite_tac [th]) >>
     simp[venomStateTheory.write_memory_with_expansion_def,listTheory.TAKE_DROP] >>
     IF_CASES_TAC >> simp[valueEncodingProofsTheory.mem_bytes_at_append_zero]) >>
  `call_state.vs_data_section = t_alloc.vs_data_section /\
   call_state.vs_call_ctx = t_alloc.vs_call_ctx /\
   call_state.vs_immutables = t_alloc.vs_immutables` by
    (qpat_assum `call_state = _` (fn th => once_rewrite_tac [th]) >> simp[]) >>
  `LENGTH t_alloc.vs_memory <= LENGTH call_state.vs_memory` by
    (qpat_assum `call_state.vs_memory = _` (fn th => rewrite_tac [th]) >>
     simp[venomMemPropsTheory.LENGTH_write_memory_with_expansion]) >>
  `local_ptrs_rel func cenv mid.scopes t_alloc /\
   immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor mid t_alloc` by
    fs[loweringStateRelDefsTheory.state_rel_def] >>
  `local_ptrs_rel func cenv mid.scopes call_state` by
    (irule localPtrsPropsTheory.local_ptrs_rel_mem_agree >>
     qexists_tac `t_alloc` >>
     simp[venomStateTheory.lookup_var_def] >> rpt strip_tac >>
     qpat_x_assum `FLOOKUP t_alloc.vs_allocas _ = NONE` mp_tac >> simp[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor mid call_state` by
    (irule loweringSliceTheory.immutables_rel_mem_agree >>
     qexists_tac `t_alloc` >> simp[]) >>
  `!H. valid_horizon cx st0 H
       (SND (adopt_call_outcome rq outcome es1)).storage_trace ==>
    valid_horizon cx st0 H mid.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `!tail. eval_raw_call _ _ _ _ _ _ _ = _`
       (qspec_then `[]` mp_tac) >>
     disch_then (mp_then Any mp_tac vyperStorageFootprintTheory.valid_horizon_frame) >>
     simp[vyperStorageTraceTheory.storage_trace_frame_raw_call]) >>
  `!H. valid_horizon cx st0 H
       (SND (adopt_call_outcome rq outcome es1)).storage_trace ==>
    state_rel H func cenv cx (SND (adopt_call_outcome rq outcome es1)) call_state` by
    (qx_gen_tac `H` >> strip_tac >>
     `valid_horizon cx st0 H mid.storage_trace` by res_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid t_alloc /\ _`
       (qspec_then `H` (fn th => qpat_assum
         `valid_horizon cx st0 H mid.storage_trace`
         (strip_assume_tac o MATCH_MP th))) >>
     `state_rel H func cenv cx mid t_alloc` by
       (qpat_assum `stmt_state_rel H ctx func cenv cx mid t_alloc`
          (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE
            [exprLoweringPropsTheory.stmt_state_rel_def])) >>
     qspecl_then [`H`, `func`, `cenv`, `cx`, `mid`, `t_alloc`,
       `call_inst`, `gw`, `aw`, `if flags.rcf_is_static then 0w else vw`,
       `n2w (b+32):256 word`, `n2w (LENGTH bs):256 word`, `w_alloc`, `0w:256 word`,
       `flags.rcf_is_static`, `tmp`, `target`,
       `if flags.rcf_is_static then NONE else SOME amount`, `rq`, `outcome`, `es1`]
       mp_tac extCallOracleStepTheory.exec_ext_call_oracle_step >>
     impl_tac
     >- (simp[Abbr `call_inst`, venomInstTheory.mk_inst_def] >>
         Cases_on `flags.rcf_is_static` >> simp[]) >>
     disch_then (qx_choose_then `call_state_H` strip_assume_tac) >>
     `call_state_H = call_state` by
       (qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
        qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
        qpat_x_assum `call_state_H = _` mp_tac >>
        qpat_x_assum `call_state = _` mp_tac >>
        qpat_x_assum `Abbrev (u_call = _)`
          (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        rpt (pop_assum kall_tac) >>
        simp[venomStateTheory.update_var_def,
             venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
     qpat_assum `call_state_H = call_state`
       (fn eq => qpat_assum
          `_ ==> state_rel H func cenv cx
            (SND (adopt_call_outcome rq outcome es1)) call_state_H`
          (mp_tac o SUBS [eq])) >> simp[]) >>
  `ci_mono sc out_cs` by
    (qspecl_then [`0`,`sc`] mp_tac
       exprLoweringPropsTheory.ci_mono_compile_alloc_buffer >> simp[]) >>
  `sc.cs_next_var <= out_cs.cs_next_var` by
    (qpat_assum `ci_mono sc out_cs`
       (strip_assume_tac o REWRITE_RULE [exprLoweringPropsTheory.ci_mono_def]) >>
     first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at sc x ==> x <> tmp` by
    (qx_gen_tac `x` >> disch_tac >>
     qpat_assum `!x. not_fresh_at out_cs x ==> x <> tmp`
       (qspec_then `x` irule) >>
     irule stmtFragPtrTheory.not_fresh_at_mono >>
     qexists_tac `sc` >> simp[]) >>
  `~not_fresh_at sc tmp` by
    (qpat_x_assum `!x. not_fresh_at sc x ==> x <> tmp`
       (qspec_then `tmp` mp_tac) >> simp[]) >>
  `not_local_ptr cenv mid.scopes tmp` by
    (irule exprSimOperandsTheory.fresh_not_local_ptr >>
     qexists_tac `sc` >> simp[]) >>
  `eval_operand (Var q_alloc) t_alloc = SOME w_alloc /\
   eval_operand (Lit 0w) t_alloc = SOME (0w:256 word)` by
    simp[venomStateTheory.eval_operand_def] >>
  qspecl_then [`call_inst`,`gas_op`,`addr`,`value_op`,`dp`,`dl`,
    `Var q_alloc`,`Lit 0w`,`tmp`,`t_alloc`,`gw`,`aw`,`vw`,
    `n2w (b+32):256 word`,`n2w (LENGTH bs):256 word`,`w_alloc`,`0w:256 word`,
    `u_call`,`PG`,`G_alloc`,`tn_alloc`] mp_tac
    (Q.GENL [`inst`,`gas`,`addr`,`value`,`ao`,`az`,`ro`,`rz`,`out`,`s`,
       `gw`,`dw`,`vw`,`aw`,`an`,`rw`,`rn`,`u`,`PG`,`G`,`tn`]
       bodyFullExtCallGhostTheory.extcall_call_ghost_frame) >>
  impl_tac
  >- (Cases_on `flags.rcf_is_static` >>
      simp[Abbr `call_inst`,Abbr `u_call`,venomInstTheory.mk_inst_def,
        venomStateTheory.update_var_def]) >>
  strip_tac >>
  `!x. not_fresh_at sc x ==> lookup_var x u_call = lookup_var x t_alloc` by
    (qx_gen_tac `x` >> disch_tac >>
     `x <> tmp` by
       (qpat_assum `!x. not_fresh_at sc x ==> x <> tmp`
          (qspec_then `x` irule) >> first_assum ACCEPT_TAC) >>
     qpat_assum `call_state.vs_vars = t_alloc.vs_vars`
       (fn vars => qpat_assum `x <> tmp`
         (fn fresh => simp_tac bool_ss
           [Abbr `u_call`,emitHelperPropsTheory.lookup_var_update_var,
            venomStateTheory.lookup_var_def,boolTheory.COND_CLAUSES,vars,fresh]))) >>
  `~(call_inst.inst_opcode = CALL /\ ~t_alloc.vs_call_ctx.cc_static /\
      u_call.vs_requests <> t_alloc.vs_requests /\
      u_call.vs_outcomes <> t_alloc.vs_outcomes /\
      (HD t_alloc.vs_outcomes).co_success) ==>
    u_call.vs_accounts = t_alloc.vs_accounts /\
    u_call.vs_transient = t_alloc.vs_transient` by
    (qpat_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _`
       (mp_then Any mp_tac oracleCallStepPtrTheory.exec_ext_call_storage_cases) >>
     Cases_on `flags.rcf_is_static` >>
     simp[Abbr `call_inst`,Abbr `u_call`,venomInstTheory.mk_inst_def,
       venomStateTheory.update_var_def] >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stor_taint_ok_at (DF H) (step_taint call_inst t_alloc u_call tn_alloc) u_call` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       access_ok _ _ _ _ _ /\ _`
       (qspec_then `H` (fn th => qpat_assum
         `valid_horizon cx st0 H mid.storage_trace`
         (strip_assume_tac o MATCH_MP th))) >>
     irule bodyFullExtCallGhostTheory.extcall_call_storage_ghost >>
     simp[Abbr `u_call`,venomStateTheory.update_var_def] >>
     Cases_on `flags.rcf_is_static` >>
     simp[Abbr `call_inst`,venomInstTheory.mk_inst_def]) >>
  suspend "zeroCallPost"
QED

Resume raw_call_zero_full_finish[zeroCallPost]:
  markerLib.RESUME_TAC >>
  qabbrev_tac `G_call = step_prov PG G_alloc call_inst u_call` >>
  qabbrev_tac `tn_call = step_taint call_inst t_alloc u_call tn_alloc` >>
  `u_call.vs_memory = call_state.vs_memory /\
   u_call.vs_allocas = t_alloc.vs_allocas /\
   u_call.vs_alloca_next = t_alloc.vs_alloca_next /\
   u_call.vs_fmp = t_alloc.vs_fmp /\
   u_call.vs_labels = t_alloc.vs_labels /\
   u_call.vs_current_bb = t_alloc.vs_current_bb /\
   u_call.vs_halted = t_alloc.vs_halted` by
    simp[Abbr `u_call`,venomStateTheory.update_var_def] >>
  qpat_assum `u_call.vs_memory = call_state.vs_memory`
    (fn eq => qpat_assum `!off len. mem_bytes_at off len call_state.vs_memory =
                                      mem_bytes_at off len t_alloc.vs_memory`
       (assume_tac o REWRITE_RULE [SYM eq])) >>
  `allocas_from lo u_call` by
    (qpat_assum `allocas_from lo t_alloc`
       (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
     simp[ptrDisciplineTheory.allocas_from_def]) >>
  `tn_call.t_mem = tn_alloc.t_mem` by simp[Abbr `tn_call`] >>
  `!x. not_fresh_at sc x ==>
    lookup_var x u_call = lookup_var x t_alloc /\
    FLOOKUP G_call x = FLOOKUP G_alloc x /\
    op_taint tn_call (Var x) = op_taint tn_alloc (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     `x <> tmp` by
       (qpat_assum `!x. not_fresh_at sc x ==> x <> tmp`
          (qspec_then `x` irule) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!x. x <> tmp ==> FLOOKUP _ x = FLOOKUP G_alloc x /\ _`
       (qspec_then `x` mp_tac) >>
     simp[Abbr `G_call`,Abbr `tn_call`]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx mid G_call tn_call u_call` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid t_alloc /\ _`
       (qspec_then `H` (fn th => qpat_assum
         `valid_horizon cx st0 H mid.storage_trace`
         (strip_assume_tac o MATCH_MP th))) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       stor_taint_ok_at (DF H) _ _`
       (qspec_then `H` (fn th => qpat_assum
         `valid_horizon cx st0 H mid.storage_trace` (assume_tac o MATCH_MP th))) >>
     qspecl_then [`DF H`,`lo`,`d`,`cenv`,`cx`,`mid`,`G_alloc`,`tn_alloc`,
       `t_alloc`,`sc`,`func`,`t_alloc.vs_alloca_next`,`0`,`u_call`,`G_call`,`tn_call`]
       mp_tac
       (Q.GENL [`D`,`lo`,`d`,`cenv`,`cx`,`es`,`G`,`tn`,`s`,`sa`,`func`,
          `start`,`nb`,`z`,`H`,`tf`]
          bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_inv_at) >>
     impl_tac
     >- (qpat_assum `!off len. mem_bytes_at off len u_call.vs_memory =
                              mem_bytes_at off len t_alloc.vs_memory`
           (fn th => PURE_REWRITE_TAC [th]) >>
         simp[] >>
         map_every qx_gen_tac [`name`,`a`,`n`] >> disch_tac >>
         qspecl_then [`func`,`cenv`,`mid.scopes`,`t_alloc`,`name`,`a`,`n`,
           `t_alloc.vs_alloca_next`,`0`] mp_tac
           localPtrsPropsTheory.local_ptrs_rel_above_frontier >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def,DISJ_COMM]) >>
     simp[]) >>
  `(SND (adopt_call_outcome rq outcome es1)).scopes = mid.scopes /\
   (SND (adopt_call_outcome rq outcome es1)).immutables = mid.immutables` by
    (simp[rawCallMemoryFramePtrTheory.oracle_adoption_locals] >>
     qpat_assum `take_call_outcome _ _ _ mid = _`
       (mp_then Any mp_tac vyperCallOutcomeTheory.take_call_outcome_frame) >>
     disch_then (fn th => once_rewrite_tac [th]) >> simp[]) >>
  suspend "zeroCallRel"
QED

Resume raw_call_zero_full_finish[zeroCallRel]:
  markerLib.RESUME_TAC >>
  qabbrev_tac `ee_call = SND (adopt_call_outcome rq outcome es1) with gas_obs := []` >>
  `ee_call.scopes = mid.scopes /\ ee_call.immutables = mid.immutables` by
    simp[Abbr `ee_call`] >>
  `!id a n. local_region cenv ee_call.scopes call_state id a n <=>
            local_region cenv mid.scopes t_alloc id a n` by
    simp[loweringStateRelDefsTheory.local_region_def,venomStateTheory.lookup_var_def] >>
  `immutable_alloca_sep func cenv cx ee_call call_state` by
    (qspecl_then [`func`,`cenv`,`cx`,`mid`,`ee_call`,`t_alloc`,`call_state`]
       mp_tac exprLoweringPropsTheory.immutable_alloca_sep_fields >>
     impl_tac
     >- (simp[] >> rpt strip_tac >> qexists_tac `id` >> simp[]) >> simp[]) >>
  `immutable_base_zero cenv call_state` by
    (qspecl_then [`cenv`,`t_alloc`,`call_state`] mp_tac
       exprLoweringPropsTheory.immutable_base_zero_frame >>
     simp[venomStateTheory.lookup_var_def]) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee_call u_call` by
    (qx_gen_tac `H` >> disch_tac >>
     `valid_horizon cx st0 H
        (SND (adopt_call_outcome rq outcome es1)).storage_trace` by
       (qpat_x_assum `valid_horizon cx st0 H ee_call.storage_trace` mp_tac >>
        simp[Abbr `ee_call`]) >>
     qpat_assum `!H. valid_horizon _ _ H
          (SND (adopt_call_outcome rq outcome es1)).storage_trace ==>
          valid_horizon cx st0 H mid.storage_trace`
       (qspec_then `H` (fn th => qpat_assum
          `valid_horizon cx st0 H
             (SND (adopt_call_outcome rq outcome es1)).storage_trace`
          (assume_tac o MATCH_MP th))) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid t_alloc /\ _`
       (qspec_then `H` (fn th => qpat_assum
          `valid_horizon cx st0 H mid.storage_trace`
          (strip_assume_tac o MATCH_MP th))) >>
     `state_rel H func cenv cx ee_call call_state` by
       (qpat_assum `!H. valid_horizon _ _ H
           (SND (adopt_call_outcome rq outcome es1)).storage_trace ==>
           state_rel H func cenv cx (SND (adopt_call_outcome rq outcome es1)) call_state`
          (qspec_then `H` mp_tac) >>
        simp[Abbr `ee_call`,loweringStateRelDefsTheory.state_rel_gas_obs]) >>
     qspecl_then [`H`,`func`,`cenv`,`cx`,`mid`,`t_alloc`,`ee_call`,`call_state`,`ctx`]
       mp_tac exprLoweringPropsTheory.stmt_state_rel_allocas_frame >>
     impl_tac >- simp[] >> strip_tac >>
     qspecl_then [`H`,`func`,`cenv`,`cx`,`ee_call`,`call_state`,`tmp`,
       `if outcome.co_success then 1w else 0w`,`ctx`] mp_tac
       exprLoweringPropsTheory.stmt_state_rel_update_var >>
     impl_tac
     >- (conj_tac
         >- (qpat_assum `stmt_state_rel H ctx func cenv cx ee_call call_state`
               ACCEPT_TAC) >>
         qpat_assum `not_local_ptr cenv mid.scopes tmp`
           (fn th => qpat_assum `ee_call.scopes = mid.scopes`
              (fn eq => REWRITE_TAC [eq] >> ACCEPT_TAC th))) >>
     simp[Abbr `u_call`]) >>
  `(mid with gas_obs := []) = mid` by
    (qpat_assum `mid.gas_obs = []`
       (fn th => once_rewrite_tac [GSYM th]) >> simp[]) >>
  `SND (eval_raw_call cx flags target bs amount source_gas mid) = ee_call` by
    (qpat_x_assum `!tail. eval_raw_call _ _ _ _ _ _ _ = _`
       (qspec_then `[]` mp_tac) >> simp[Abbr `ee_call`]) >>
  `eval_raw_call cx flags target bs amount source_gas mid =
    (FST (eval_raw_call cx flags target bs amount source_gas mid),ee_call)` by
    (qpat_assum `SND (eval_raw_call _ _ _ _ _ _ mid) = ee_call`
       (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
     REWRITE_TAC [pairTheory.PAIR]) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    storage_well_formed_on cx ee_call (FST H)` by
    (qx_gen_tac `H` >> disch_tac >>
     `valid_horizon cx st0 H mid.storage_trace` by
       (qpat_assum `eval_raw_call _ _ _ _ _ _ mid = _`
          (mp_then (Pat `_ _ = (_,_)`) mp_tac
             vyperStorageFootprintTheory.valid_horizon_frame) >>
        simp[vyperStorageTraceTheory.storage_trace_frame_raw_call]) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` (fn th => qpat_assum
          `valid_horizon cx st0 H mid.storage_trace`
          (strip_assume_tac o MATCH_MP th))) >>
     qpat_assum `eval_raw_call _ _ _ _ _ _ mid = _`
       (mp_then (Pat `eval_raw_call _ _ _ _ _ _ _ = _`) mp_tac
          vyperFiniteStoragePreservationTheory.eval_raw_call_preserves_storage_well_formed_on) >>
     disch_then irule >>
     qpat_x_assum `valid_horizon cx st0 H ee_call.storage_trace`
       (mp_tac o REWRITE_RULE [vyperStorageFootprintTheory.valid_horizon_def]) >>
     simp[]) >>
  suspend "zeroCallFrame"
QED

Resume raw_call_zero_full_finish[zeroCallFrame]:
  markerLib.RESUME_TAC >>
  `!x. not_fresh_at sa x ==> lookup_var x u_call = lookup_var x t_alloc` by
    (qx_gen_tac `x` >> disch_tac >>
     qpat_assum `!x. not_fresh_at sc x ==>
       lookup_var x u_call = lookup_var x t_alloc /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `locals_kept cenv es mid s0 u_call` by
    (qspecl_then [`cenv`,`es`,`mid`,`s0`,`t_alloc`,`u_call`] mp_tac
       exprSimPropsTheory.locals_kept_regions_tail >>
     qpat_assum `wb_frame cenv es mid sa s0 t_alloc`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     simp[]) >>
  `wb_frame cenv es mid sa s0 u_call` by
    (qpat_assum `wb_frame cenv es mid sa s0 t_alloc`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     rewrite_tac[loweringPostsTheory.wb_frame_def] >> rpt conj_tac
     >- (map_every qx_gen_tac [`x`,`w`] >> disch_tac >>
         qpat_assum `!x. not_fresh_at sa x ==>
           lookup_var x u_call = lookup_var x t_alloc`
           (qspec_then `x` mp_tac) >>
         qpat_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t_alloc = SOME w`
           (qspecl_then [`x`,`w`] mp_tac) >> simp[])
     >- (qpat_assum `u_call.vs_allocas = t_alloc.vs_allocas`
           (fn th => PURE_REWRITE_TAC [th]) >> first_assum ACCEPT_TAC)
     >- (qpat_assum `!off len. mem_bytes_at off len u_call.vs_memory =
                              mem_bytes_at off len t_alloc.vs_memory`
           (fn th => PURE_REWRITE_TAC [th]) >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `wb_frame cenv es ee_call sa s0 u_call` by
    (qpat_assum `wb_frame cenv es mid sa s0 u_call`
       (fn th => REWRITE_TAC [loweringPostsTheory.wb_frame_def,
          loweringPostsTheory.locals_kept_def,loweringPostsTheory.popped_kept_def] >>
        qpat_assum `ee_call.scopes = mid.scopes`
          (fn eq => PURE_REWRITE_TAC [eq]) >>
        ACCEPT_TAC (REWRITE_RULE [loweringPostsTheory.wb_frame_def,
          loweringPostsTheory.locals_kept_def,loweringPostsTheory.popped_kept_def] th))) >>
  qabbrev_tac `z_call = u_call with vs_inst_idx := SUC t_alloc.vs_inst_idx` >>
  `alloca_history func z_call` by
    (qspecl_then [`func`,`t_alloc`,`bb`,`call_inst`,`u_call`] mp_tac
       allocaHistoryTheory.alloca_history_base_step >>
     impl_tac >- simp[] >>
     Cases_on `flags.rcf_is_static` >>
     simp[Abbr `z_call`,Abbr `call_inst`,venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def]) >>
  `wb_frame cenv es ee_call sa s0 z_call` by
    (qpat_assum `wb_frame cenv es ee_call sa s0 u_call`
       (fn th => simp_tac bool_ss [Abbr `z_call`,loweringPostsTheory.wb_frame_def,
          loweringPostsTheory.locals_kept_def,loweringPostsTheory.popped_kept_def,
          venomStateTheory.lookup_var_def,venomStateTheory.venom_state_accfupds] >>
        ACCEPT_TAC (REWRITE_RULE [loweringPostsTheory.wb_frame_def,
          loweringPostsTheory.locals_kept_def,loweringPostsTheory.popped_kept_def,
          venomStateTheory.lookup_var_def] th))) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
       valid_horizon cx st0 H mid.storage_trace` by
    (qpat_x_assum `!H. valid_horizon _ _ H
       (SND (adopt_call_outcome rq outcome es1)).storage_trace ==>
       valid_horizon cx st0 H mid.storage_trace` mp_tac >> simp[Abbr `ee_call`]) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee_call z_call` by
    (qpat_x_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee_call u_call` mp_tac >>
     simp[Abbr `z_call`,exprLoweringPropsTheory.stmt_state_rel_inst_idx]) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee_call G_call tn_call z_call` by
    (qx_gen_tac `H` >> disch_tac >>
     `valid_horizon cx st0 H mid.storage_trace` by res_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       ghost_inv_at (DF H) lo d cenv cx mid G_call tn_call u_call`
       (qspec_then `H` (fn th => qpat_assum
          `valid_horizon cx st0 H mid.storage_trace`
          (fn guard => assume_tac (MATCH_MP th guard)))) >>
     qpat_assum `Abbrev (z_call = _)`
       (fn th => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     PURE_REWRITE_TAC [ghostPcTransportPtrTheory.ghost_inv_at_inst_idx] >>
     qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid G_call tn_call u_call`
       (fn th => REWRITE_TAC [bodyPtrDefsTheory.ghost_inv_at_def] >>
        qpat_assum `ee_call.scopes = mid.scopes`
          (fn eq => PURE_REWRITE_TAC [eq]) >>
        ACCEPT_TAC (REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def] th))) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G_call tn_call` by
    (qpat_assum `!lo cenv es sa G0 tn0 s0. _`
       (qspecl_then [`lo`,`cenv`,`es`,`sa`,`G0`,`tn0`,`s0`] mp_tac) >>
     `~not_fresh_at sa tmp` by
       (qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sc x`
          (qspec_then `tmp` mp_tac) >> simp[]) >>
     simp[Abbr `G_call`,Abbr `tn_call`]) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G,tn) [] (OK z_call,G_call,tn_call)` by
    (qx_gen_tac `H` >> disch_tac >>
     `valid_horizon cx st0 H mid.storage_trace` by res_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       gas_origin_ptr_edge _ _ _ _`
       (qspec_then `H` (fn th => qpat_assum
          `valid_horizon cx st0 H mid.storage_trace`
          (assume_tac o MATCH_MP th))) >>
     `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t_alloc,G_alloc,tn_alloc) [] (OK z_call,G_call,tn_call)` by
       (qpat_assum `gas_origin_ptr_edge _ _ _ _`
          (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
             (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules))) >>
        simp[Abbr `z_call`,Abbr `G_call`,Abbr `tn_call`] >>
        disch_then irule >>
        irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> simp[]) >>
     qpat_assum `!D. gas_origin_ptr_path (D,lo,_,_,_,_) (t,G,tn) [] _`
       (qspec_then `DF H` (mp_then Any mp_tac
          fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >>
     disch_then (qspecl_then [`t_alloc`,`G_alloc`,`tn_alloc`,`[]`,
       `OK z_call`,`G_call`,`tn_call`] mp_tac) >> simp[]) >>
  (Cases_on `flags.rcf_revert_on_failure`
   >- suspend "zeroRevert" >> suspend "zeroBoolValue")
QED

Resume raw_call_zero_full_finish[zeroBoolValue]:
  markerLib.RESUME_TAC >>
  `emit_op (if flags.rcf_is_static then STATICCALL else CALL)
    (if flags.rcf_is_static then [gas_op;addr;dp;dl;Var q_alloc;Lit 0w]
     else [gas_op;addr;value_op;dp;dl;Var q_alloc;Lit 0w])
    out_cs = (result,sb)` by
    (qpat_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ out_cs = _` mp_tac >>
     qpat_assum `emit_op _ _ out_cs = (call_result,call_cs)` mp_tac >>
     qpat_assum `buf_alloc.buf_operand = Var q_alloc` mp_tac >>
     qpat_assum `flags.rcf_max_outsize = 0` mp_tac >>
     qpat_assum `~flags.rcf_revert_on_failure` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `flags.rcf_is_static` >>
     fs[builtinSystemTheory.compile_raw_call_finish_def,
       compileEnvTheory.comp_bind_def,compileEnvTheory.comp_return_def] >>
     pairarg_tac >> gvs[compileEnvTheory.comp_return_def]) >>
  `(call_result,call_cs) = (result,sb)` by
    (qpat_assum `emit_op _ _ out_cs = (call_result,call_cs)`
       (fn a => qpat_assum `emit_op _ _ out_cs = (result,sb)`
          (fn b => ACCEPT_TAC (TRANS (SYM a) b)))) >>
  qpat_x_assum `(call_result,call_cs) = (result,sb)`
    (CONJUNCTS_THEN SUBST_ALL_TAC o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
  `ann = BaseT BoolT` by simp[vyperTypeSystemTheory.raw_call_return_type_def] >>
  `eval_operand result z_call = SOME (if outcome.co_success then 1w else 0w)` by
    simp[Abbr `z_call`,Abbr `u_call`,venomStateTheory.eval_operand_def,
      emitHelperPropsTheory.lookup_var_update_var] >>
  `op_taint tn_call result = {} /\ op_prov G_call result = NONE` by
    simp[Abbr `G_call`,Abbr `tn_call`,ptrDisciplineTheory.op_taint_def,
      ptrDisciplineTheory.op_prov_def,finite_mapTheory.FLOOKUP_DRESTRICT,
      finite_mapTheory.FLOOKUP_UPDATE] >>
  qpat_assum `result = Var tmp` (fn result_eq =>
    qpat_assum `tmp = STRING #"%" (toString out_cs.cs_next_var)` (fn tmp_eq =>
      qpat_assum `eval_operand result z_call = _`
        (assume_tac o PURE_REWRITE_RULE [result_eq,tmp_eq]) >>
      qpat_assum `op_taint tn_call result = {}`
        (assume_tac o PURE_REWRITE_RULE [result_eq,tmp_eq]) >>
      qpat_assum `op_prov G_call result = NONE`
        (assume_tac o PURE_REWRITE_RULE [result_eq,tmp_eq]))) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    vv_post H ctx func cenv cx (Call ann (RawCallTarget flags) args dflt)
      es sa sb s0 ee_call (Value (BoolV outcome.co_success)) vv z_call` by
    (qx_gen_tac `H` >> disch_tac >>
     simp[] >>
     irule exprSimHashTheory.vv_post_word_intro >>
     simp[vyperASTTheory.expr_type_def,
       compileEnvTheory.is_word_type_def,
       vyperValueTheory.evaluate_type_def,valueEncodingTheory.typed_val_to_w256_def,
       valueEncodingTheory.val_to_w256_def,
       supportedExprTraverseTheory.expr_has_effect_def]) >>
  `ptr_vv_ok cx (post_value_type cenv (Call ann (RawCallTarget flags) args dflt))
     (Value (BoolV outcome.co_success)) vv ee_call G_call tn_call z_call` by
    (simp[bodyPtrDefsTheory.ptr_vv_ok_def,vyperStateTheory.read_result_def,
       vyperStateTheory.return_def,vyperASTTheory.expr_type_def] >>
     irule bodyPtrDefsTheory.ptr_val_ok_word >>
     simp[compileEnvTheory.is_word_type_def,ptrDisciplineTheory.op_prov_def,
       finite_mapTheory.FLOOKUP_DRESTRICT]) >>
  `vv_store_bound cx (expr_type (Call ann (RawCallTarget flags) args dflt))
     (lowered_value_type cenv (Call ann (RawCallTarget flags) args dflt))
     ee_call (Value (BoolV outcome.co_success)) vv z_call` by
    simp[exprSimMemDefsTheory.vv_store_bound_def,vyperASTTheory.expr_type_def,
      compileEnvTheory.is_word_type_def] >>
  `z_call.vs_current_bb = sb.cs_current_bb /\
   z_call.vs_inst_idx = LENGTH sb.cs_current_insts /\
   ~z_call.vs_halted /\ s0.vs_alloca_next <= z_call.vs_alloca_next` by
    simp[Abbr `z_call`] >>
  suspend "zeroBoolClose"
QED

Resume raw_call_zero_full_finish[zeroBoolClose]:
  markerLib.RESUME_TAC >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G_call`,`ee_call`,`INL (Value (BoolV outcome.co_success))`,
    `z_call`,`tn_call`] >>
  conj_tac
  >- (qpat_x_assum `!tail. eval_raw_call _ _ _ _ _ _ _ = _` mp_tac >>
      simp[Abbr `ee_call`]) >>
  qx_gen_tac `H` >> disch_tac >>
  `(ee_call with gas_obs := []) = ee_call` by simp[Abbr `ee_call`] >>
  simp[vyperASTTheory.expr_type_def,compileEnvTheory.is_word_type_def,
    contextTheory.vv_location_def] >>
  `raw_call_return_type flags = BaseT BoolT` by
    (qpat_assum `ann = raw_call_return_type flags`
       (fn a => qpat_assum `ann = BaseT BoolT`
          (fn b => ACCEPT_TAC (TRANS (SYM a) b)))) >>
  `G_call = DRESTRICT G_alloc
    (COMPL {STRING #"%" (toString out_cs.cs_next_var)})` by
    simp[Abbr `G_call`] >>
  qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
    vv_post H ctx func cenv cx _ es sa sb s0 ee_call _ vv z_call` mp_tac >>
  qpat_assum `vv_store_bound _ _ _ ee_call _ vv z_call` mp_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee_call G_call tn_call z_call` mp_tac >>
  qpat_assum `ptr_vv_ok _ _ _ vv ee_call G_call tn_call z_call` mp_tac >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G_call tn_call` mp_tac >>
  qpat_assum `valid_horizon cx st0 H ee_call.storage_trace` mp_tac >>
  qpat_assum `raw_call_return_type flags = BaseT BoolT` mp_tac >>
  qpat_assum `G_call = DRESTRICT G_alloc _` mp_tac >>
  qpat_assum `vv = _` mp_tac >>
  qpat_assum `ann = raw_call_return_type flags` mp_tac >>
  qpat_assum `dflt = NONE` mp_tac >>
  qpat_assum `result = Var tmp` mp_tac >>
  qpat_assum `tmp = STRING #"%" (toString out_cs.cs_next_var)` mp_tac >>
  qpat_assum `flags.rcf_max_outsize = 0` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  gvs[vyperASTTheory.expr_type_def,compileEnvTheory.is_word_type_def]
QED

Resume raw_call_zero_full_finish[zeroRevert]:
  markerLib.RESUME_TAC >>
  mp_tac (Q.INST [`addr` |-> `addr`,`dp` |-> `dp`,`dl` |-> `dl`,
    `gas` |-> `gas_op`,`value` |-> `value_op`,
    `ct` |-> `if flags.rcf_is_static then StaticCall else RegularCall`,
    `n` |-> `0`,`ov` |-> `buf_alloc.buf_operand`,`op` |-> `buf_alloc.buf_operand`,
    `sa` |-> `out_cs`,`result` |-> `result`,`sb` |-> `sb`,`func` |-> `func`]
    rawCallFinishCodePtrTheory.raw_call_reverting_code_groups) >>
  (impl_tac >-
    (qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ out_cs = _`
       mp_tac >> simp[])) >>
  disch_then (qx_choosel_then [`branch_ok`,`branch_cs`,`bad`,`label_cs`,`good`,
    `jump_cs`,`jumped_cs`,`fail_block`,`fail_cs`,`failed_cs`,`pass_block`,`pass_cs`]
    strip_assume_tac) >>
  `(branch_ok,branch_cs) = (call_result,call_cs)` by
    (qpat_assum `_ = (branch_ok,branch_cs)` mp_tac >>
     qpat_assum `emit_op _ _ out_cs = (call_result,call_cs)` mp_tac >>
     qpat_assum `buf_alloc.buf_operand = Var q_alloc` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `flags.rcf_is_static` >> gvs[]) >>
  qpat_x_assum `(branch_ok,branch_cs) = (call_result,call_cs)`
    (CONJUNCTS_THEN SUBST_ALL_TAC o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
  `eval_operand call_result z_call = SOME (if outcome.co_success then 1w else 0w)` by
    simp[Abbr `z_call`,Abbr `u_call`,venomStateTheory.eval_operand_def,
      emitHelperPropsTheory.lookup_var_update_var] >>
  `op_taint tn_call call_result = {}` by
    simp[Abbr `tn_call`,ptrDisciplineTheory.op_taint_def,
      finite_mapTheory.FLOOKUP_UPDATE] >>
  `allocas_from lo z_call` by
    (simp[Abbr `z_call`,ptrDisciplineTheory.allocas_from_def] >>
     qpat_assum `allocas_from lo t_alloc`
       (ACCEPT_TAC o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def])) >>
  `!D. gas_origin_ptr_path
    (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (z_call,G_call,tn_call) []
    (OK (jump_to (if outcome.co_success then good else bad) z_call),G_call,tn_call)` by
    (gen_tac >>
     mp_tac (Q.INST [`sa` |-> `jump_cs`,`sb` |-> `jumped_cs`,
       `op` |-> `call_result`,`lt` |-> `good`,`lf` |-> `bad`,
       `b` |-> `outcome.co_success`,`s` |-> `z_call`,`G` |-> `G_call`,
       `tn` |-> `tn_call`,`D` |-> `D`,`lo` |-> `lo`,`ctx` |-> `ctx`,
       `func` |-> `func`,`PG` |-> `PG`,
       `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
       fragGasEmitCtrlTheory.emit_jnz_origin_ptr) >>
     impl_tac >- simp[Abbr `z_call`] >> simp[]) >>
  suspend "zeroRevertBranch"
QED

Resume raw_call_zero_full_finish[zeroRevertBranch]:
  markerLib.RESUME_TAC >>
  qpat_assum `new_block bad jumped_cs = (fail_block,fail_cs)`
    (strip_assume_tac o MATCH_MP emitHelperPropsTheory.new_block_props) >>
  qpat_assum `new_block good failed_cs = (pass_block,pass_cs)`
    (strip_assume_tac o MATCH_MP emitHelperPropsTheory.new_block_props) >>
  `result = Lit 0w /\ sb = pass_cs` by
    (qpat_x_assum `_ pass_cs = (result,sb)` mp_tac >>
     simp[compileEnvTheory.comp_return_def] >> rpt strip_tac >> gvs[]) >>
  qabbrev_tac `z_jump = jump_to (if outcome.co_success then good else bad) z_call` >>
  `alloca_history func z_jump` by
    (qspecl_then [`func`,`z_call`,`z_jump`] mp_tac
       allocaHistoryTheory.alloca_history_jump >>
     impl_tac >- simp[Abbr `z_jump`,venomStateTheory.jump_to_def] >> simp[]) >>
  `allocas_from lo z_jump` by
    (simp_tac (srw_ss()) [Abbr `z_jump`,venomStateTheory.jump_to_def,
       ptrDisciplineTheory.allocas_from_def] >>
     qpat_assum `allocas_from lo z_call`
       (ACCEPT_TAC o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def])) >>
  `lo <= z_jump.vs_alloca_next /\ ~z_jump.vs_halted` by
    simp[Abbr `z_jump`,venomStateTheory.jump_to_def,Abbr `z_call`] >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee_call z_jump` by
    simp[Abbr `z_jump`,exprLoweringPropsTheory.stmt_state_rel_jump_to] >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G,tn) [] (OK z_jump,G_call,tn_call)` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       gas_origin_ptr_path _ (t,G,tn) [] (OK z_call,G_call,tn_call)`
       (qspec_then `H` (fn th => qpat_assum
         `valid_horizon cx st0 H ee_call.storage_trace`
         (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append o
           MATCH_MP th))) >>
     disch_then (qspecl_then [`z_call`,`G_call`,`tn_call`,`[]`,
       `OK z_jump`,`G_call`,`tn_call`] mp_tac) >>
     simp[Abbr `z_jump`]) >>
  Cases_on `outcome.co_success`
  >- suspend "zeroNonePost" >> suspend "zeroFailurePost"
QED

Resume raw_call_zero_full_finish[zeroNonePost]:
  markerLib.RESUME_TAC >>
  `ann = NoneT` by simp[vyperTypeSystemTheory.raw_call_return_type_def] >>
  `wb_frame cenv es ee_call sa s0 z_jump` by
    (qpat_assum `wb_frame cenv es ee_call sa s0 z_call`
       (fn th => simp_tac bool_ss [Abbr `z_jump`,loweringPostsTheory.wb_frame_def,
          loweringPostsTheory.locals_kept_def,loweringPostsTheory.popped_kept_def,
          venomStateTheory.jump_to_def,venomStateTheory.lookup_var_def,
          venomStateTheory.venom_state_accfupds] >>
        ACCEPT_TAC (REWRITE_RULE [loweringPostsTheory.wb_frame_def,
          loweringPostsTheory.locals_kept_def,loweringPostsTheory.popped_kept_def,
          venomStateTheory.lookup_var_def] th))) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee_call G_call tn_call z_jump` by
    (qx_gen_tac `H` >> disch_tac >>
     `(ee_call with gas_obs := []) = ee_call` by simp[Abbr `ee_call`] >>
     qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       ghost_inv_at (DF H) lo d cenv cx ee_call G_call tn_call z_call`
       (qspec_then `H` (fn th => qpat_assum
         `valid_horizon cx st0 H ee_call.storage_trace`
         (fn guard =>
           let val jumped = MATCH_MP
             (snd (EQ_IMP_RULE fragGasEmitCtrlTheory.ghost_inv_at_jump_to))
             (MATCH_MP th guard)
           in qpat_assum `(ee_call with gas_obs := []) = ee_call`
             (fn ee_eq => mp_tac (REWRITE_RULE [ee_eq]
               (Q.INST [`gs` |-> `[]`,`l` |-> `good`] jumped))) end))) >>
     simp[Abbr `z_jump`]) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    vv_post H ctx func cenv cx (Call ann (RawCallTarget flags) args dflt)
      es sa sb s0 ee_call (Value NoneV) vv z_jump` by
    (qx_gen_tac `H` >> disch_tac >> simp[] >>
     irule exprSimHashTheory.vv_post_frame_intro >>
     simp[loweringPostsTheory.vv_holds_def,loweringPostsTheory.vv_at_def,
       vyperASTTheory.expr_type_def,
       vyperStateTheory.read_result_def,vyperStateTheory.return_def,
       loweringPostsTheory.expr_val_rel_def,loweringPostsTheory.expr_val_at_def,
       venomStateTheory.eval_operand_def,vyperValueTheory.evaluate_type_def,
       compileEnvTheory.is_word_type_def,valueEncodingDefsTheory.val_in_memory_def,
       valueEncodingDefsTheory.val_wf_def,loweringPostsTheory.val_footprint_def,
       valueEncodingTheory.type_memory_size_def,supportedExprTraverseTheory.expr_has_effect_def]) >>
  `ptr_vv_ok cx (post_value_type cenv (Call ann (RawCallTarget flags) args dflt))
     (Value NoneV) vv ee_call G_call tn_call z_jump` by
    simp[bodyPtrDefsTheory.ptr_vv_ok_def,vyperStateTheory.read_result_def,
      vyperStateTheory.return_def,vyperASTTheory.expr_type_def,
      callStepPtrTheory.ptr_val_ok_none] >>
  `vv_store_bound cx (expr_type (Call ann (RawCallTarget flags) args dflt))
     (lowered_value_type cenv (Call ann (RawCallTarget flags) args dflt))
     ee_call (Value NoneV) vv z_jump` by
    simp[exprSimMemDefsTheory.vv_store_bound_def,vyperASTTheory.expr_type_def,
      exprLoweringTheory.lowered_value_type_def,vyperValueTheory.evaluate_type_def,
      vyperStateTheory.read_result_def,vyperStateTheory.return_def,
      venomStateTheory.eval_operand_def,exprSimPropsTheory.val_store_size_def,
      valueEncodingTheory.type_memory_size_def] >>
  `z_jump.vs_current_bb = sb.cs_current_bb /\
   z_jump.vs_inst_idx = LENGTH sb.cs_current_insts /\
   s0.vs_alloca_next <= z_jump.vs_alloca_next` by
    simp[Abbr `z_jump`,Abbr `z_call`,venomStateTheory.jump_to_def] >>
  suspend "zeroNoneClose"
QED

Resume raw_call_zero_full_finish[zeroNoneClose]:
  markerLib.RESUME_TAC >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G_call`,`ee_call`,`INL (Value NoneV)`,`z_jump`,`tn_call`] >>
  conj_tac
  >- (qpat_x_assum `!tail. eval_raw_call _ _ _ _ _ _ _ = _` mp_tac >>
      simp[Abbr `ee_call`]) >>
  qx_gen_tac `H` >> disch_tac >>
  `(ee_call with gas_obs := []) = ee_call` by simp[Abbr `ee_call`] >>
  simp[vyperASTTheory.expr_type_def,compileEnvTheory.is_word_type_def,
    contextTheory.vv_location_def] >>
  `raw_call_return_type flags = NoneT` by
    (qpat_assum `ann = raw_call_return_type flags`
       (fn a => qpat_assum `ann = NoneT`
          (fn b => ACCEPT_TAC (TRANS (SYM a) b)))) >>
  `G_call = DRESTRICT G_alloc
    (COMPL {STRING #"%" (toString out_cs.cs_next_var)})` by
    simp[Abbr `G_call`] >>
  qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
    vv_post H ctx func cenv cx _ es sa sb s0 ee_call _ vv z_jump` mp_tac >>
  qpat_assum `vv_store_bound _ _ _ ee_call _ vv z_jump` mp_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee_call G_call tn_call z_jump` mp_tac >>
  qpat_assum `ptr_vv_ok _ _ _ vv ee_call G_call tn_call z_jump` mp_tac >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G_call tn_call` mp_tac >>
  qpat_assum `valid_horizon cx st0 H ee_call.storage_trace` mp_tac >>
  qpat_assum `raw_call_return_type flags = NoneT` mp_tac >>
  qpat_assum `G_call = DRESTRICT G_alloc _` mp_tac >>
  qpat_assum `vv = _` mp_tac >>
  qpat_assum `ann = raw_call_return_type flags` mp_tac >>
  qpat_assum `dflt = NONE` mp_tac >>
  qpat_assum `result = Lit 0w` mp_tac >>
  qpat_assum `sb = pass_cs` mp_tac >>
  qpat_assum `flags.rcf_max_outsize = 0` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  gvs[vyperASTTheory.expr_type_def,compileEnvTheory.is_word_type_def,
    exprLoweringTheory.lowered_value_type_def,compileEnvTheory.type_memory_bytes_def,
    callStepPtrTheory.ptr_buf_ok_zero_type]
QED

Resume raw_call_zero_full_finish[zeroFailurePost]:
  markerLib.RESUME_TAC >>
  `outcomes_accounts_typed mid.outcomes` by
    (qpat_assum `expr_sim_inv cenv cx env mid` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[exprSimHypsDefsTheory.expr_sim_inv_def]) >>
  `LENGTH outcome.co_returnData < dimword (:256)` by
    (drule_all rawCallOutcomeLengthPtrTheory.take_call_outcome_returnData_length >> simp[]) >>
  `z_jump.vs_returndata = outcome.co_returnData` by
    simp[Abbr `z_jump`,venomStateTheory.jump_to_def,Abbr `z_call`,Abbr `u_call`,
      venomStateTheory.update_var_def] >>
  `storage_trace_domain cx st0 ee_call.storage_trace` by simp[Abbr `ee_call`] >>
  `valid_horizon cx st0 (storage_trace_horizon ee_call.storage_trace)
     ee_call.storage_trace` by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon ee_call.storage_trace)
     ctx func cenv cx ee_call z_jump` by
    (qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee_call z_jump`
       (qspec_then `storage_trace_horizon ee_call.storage_trace` (fn th =>
         qpat_assum `valid_horizon cx st0 (storage_trace_horizon ee_call.storage_trace)
           ee_call.storage_trace` (ACCEPT_TAC o MATCH_MP th)))) >>
  `local_ptrs_reserved cenv fail_cs` by
    (qspecl_then [`cenv`,`sc`,`fail_cs`] mp_tac
       exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     impl_tac >- (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >> simp[]) >>
  `z_jump.vs_current_bb = fail_cs.cs_current_bb /\
   z_jump.vs_inst_idx = LENGTH fail_cs.cs_current_insts` by
    simp[Abbr `z_jump`,venomStateTheory.jump_to_def] >>
  qpat_assum `stmt_state_rel (storage_trace_horizon ee_call.storage_trace)
    ctx func cenv cx ee_call z_jump` (fn rel =>
    mp_tac (Q.INST [`sa` |-> `fail_cs`,`sb` |-> `failed_cs`,
      `G` |-> `G_call`,`tn` |-> `tn_call`,`lo` |-> `lo`,
      `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,`PG` |-> `PG`]
      (PART_MATCH (find_term (fn tm =>
         same_const (fst (strip_comb tm)) ``stmt_state_rel``))
       bodyFullRawCallForwardTheory.raw_call_failure_tail_origin_ptr (concl rel)))) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`reverted`,`G_revert`,`tn_revert`] strip_assume_tac) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G,tn) [] (Abort Revert_abort reverted,G_revert,tn_revert)` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       gas_origin_ptr_path _ (t,G,tn) [] (OK z_jump,G_call,tn_call)`
       (qspec_then `H` (fn th => qpat_assum
         `valid_horizon cx st0 H ee_call.storage_trace`
         (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append o
           MATCH_MP th))) >>
     disch_then (qspecl_then [`z_jump`,`G_call`,`tn_call`,`[]`,
       `Abort Revert_abort reverted`,`G_revert`,`tn_revert`] mp_tac) >> simp[]) >>
  suspend "zeroFailureClose"
QED

Resume raw_call_zero_full_finish[zeroFailureClose]:
  markerLib.RESUME_TAC >>
  irule gas_outcome_full_exit >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G_revert`,`ee_call`,`Abort Revert_abort reverted`,
    `INR (Error (RevertData outcome.co_returnData))`,`tn_revert`] >>
  conj_tac
  >- (qpat_x_assum `!tail. eval_raw_call _ _ _ _ _ _ _ = _` mp_tac >>
      simp[Abbr `ee_call`]) >>
  simp[fragExecTheory.exit_result_def,exprSimDefsTheory.expr_exit_def]
QED

Finalise raw_call_zero_full_finish
