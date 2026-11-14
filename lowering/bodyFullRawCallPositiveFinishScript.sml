(* Positive-capacity raw_call suffix, with one endpoint before every horizon. *)
Theory bodyFullRawCallPositiveFinish
Ancestors
  bodyFullPreds bodySimFull bodyFullShared bodyFullAllocaFresh
  bodyFullExtCallGhost oracleCallOriginPtr bodyFullUnwrapSlotPost
  gasOutcomeFullCompose gasShadowCompile gasShadow
  rawCallSourceDomainPtr rawCallShapePtr rawCallBufferPtr rawCallMemoryFramePtr
  rawCallOutcomeLengthPtr rawCallResultLayoutPtr exprSimHypsDefs
  exprLowering builtinSystem loweringPosts vyperStorageFootprint
  vyperAST vyperInterpreter vyperState venomState list bodyMemoryDefs
  freshWrites vyperEvalExprPreservesScopesDom vyperTypeEnvPreservation
  bodyFullAttributeAdd exprSimPtrLiteralOps exprSimHash emitHelperProps
  valueTypingMemoryProps decoderArraySetupPtr bodyPtrMakeArrayEmission
  exprLoweringProps loweringStateRelDefs bodyPtrDefs fragExec compileEnv
  bodyFullUnwrapRun
  blockPrefixEquiv bodyFullRawCallForward bodyFullRawCallLength
  exprSimRawCallCalldata bodyFullRawCallTupleStore
  exprSimAbiEncodeMemoryLength bodyPtrMakeArrayCopyStateFrame
Libs
  pairLib monadsyntax

Theorem raw_call_positive_full_finish:
 (!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env cx ty ann flags
  args dflt es st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0
  sc shadow_sc s7 shadow_s7 addr dp dl gas_op value_op ov op result
  mid t G tn marks target bs kvs amount source_gas aw vw gw
  b region_base region_size.
  0 < flags.rcf_max_outsize /\
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
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace`
      (fn th => qpat_assum `valid_horizon cx st0
          (storage_trace_horizon mid.storage_trace) mid.storage_trace`
        (strip_assume_tac o MATCH_MP th))) >>
  `flags.rcf_max_outsize <> 0` by decide_tac >>
  `((flags.rcf_max_outsize+31) DIV 32)*32+32 < dimword(:256)` by
    (Cases_on `flags.rcf_revert_on_failure`
     >- (`expr_body_pre cenv cx env
          (Call (BaseT (BytesT (Dynamic flags.rcf_max_outsize)))
            (RawCallTarget flags) args dflt) es` by
           fs[vyperTypeSystemTheory.raw_call_return_type_def] >>
         drule raw_call_bytes_pre_capacity >> decide_tac) >>
     `expr_body_pre cenv cx env
        (Call (TupleT [BaseT BoolT;BaseT (BytesT (Dynamic flags.rcf_max_outsize))])
          (RawCallTarget flags) args dflt) es` by
       fs[vyperTypeSystemTheory.raw_call_return_type_def] >>
     drule raw_call_tuple_pre_capacity >> decide_tac) >>
  `cs_extends sc s7 /\ cs_extends s7 sb` by
    (qspecl_then [`flags.rcf_max_outsize`,`sc`] mp_tac
       exprLoweringPropsTheory.ci_mono_compile_raw_call_outbuf >>
     qspecl_then [`addr`,`dp`,`dl`,`gas_op`,`value_op`,
       `if flags.rcf_is_static then StaticCall else RegularCall`,
       `flags.rcf_max_outsize`,`flags.rcf_revert_on_failure`,`ov`,`op`,`s7`]
       mp_tac exprLoweringPropsTheory.ci_mono_compile_raw_call_finish >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `fn_has_code sc s7 func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `!tail. eval_exprs cx args _ = _`
      (qspec_then `[]` (mp_then Any mp_tac eval_exprs_preserves_scopes_dom)) >>
     simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) ==>
    off + sz <= t.vs_alloca_next` by
    (rpt strip_tac >>
     `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by res_tac >>
     `alloca_inv t` by fs[stmt_state_rel_def] >>
     fs[venomMemDefsTheory.alloca_inv_def,venomMemDefsTheory.alloca_next_valid_def] >>
     res_tac) >>
  `!name b sz. local_region cenv es.scopes s0 name b sz ==>
    b + sz <= t.vs_alloca_next` by
    (qx_genl_tac [`local_name`,`local_base`,`local_size`] >>
     disch_then (qx_choosel_then [`entry_local`,`local_ptr`,`local_word`]
       strip_assume_tac o REWRITE_RULE [local_region_def]) >>
     qpat_x_assum `local_base = _` SUBST_ALL_TAC >>
     `not_fresh_at sa local_ptr` by
       (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     `lookup_var local_ptr t = SOME local_word` by res_tac >>
     drule_all lookup_scopes_same_fdoms_some >>
     simp[optionTheory.IS_SOME_EXISTS] >>
     disch_then (qx_choose_then `entry_mid` assume_tac) >>
     `local_region cenv mid.scopes t local_name (w2n local_word) local_size` by
       (simp[local_region_def] >>
        qexistsl_tac [`entry_mid`,`local_ptr`,`local_word`] >> simp[]) >>
     drule_all body_local_region_frontier >> simp[]) >>
  `wb_frame cenv es mid sa s0 t` by
    (rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `compile_raw_call_outbuf _ sc = _`
    (fn compiled => qpat_assum `0 < flags.rcf_max_outsize`
      (fn positive => mp_tac
        (MATCH_MP raw_call_outbuf_steps (CONJ positive compiled)))) >>
  disch_then (qx_choosel_then [`out_buffer`,`out_alloc_cs`] strip_assume_tac) >>
  `cs_extends sc out_alloc_cs /\ cs_extends out_alloc_cs s7` by
    (qspecl_then [`((flags.rcf_max_outsize+31) DIV 32)*32+32`,`sc`]
       mp_tac exprLoweringPropsTheory.ci_mono_compile_alloc_buffer >>
     qspecl_then [`ADD`,`[ov;Lit 32w]`,`out_alloc_cs`]
       mp_tac exprLoweringPropsTheory.ci_mono_emit_op >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `fn_has_code sc out_alloc_cs func /\ fn_has_code out_alloc_cs s7 func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  mp_tac (Q.INST [`n` |-> `((flags.rcf_max_outsize+31) DIV 32)*32+32`,
    `sa` |-> `sc`, `sb` |-> `out_alloc_cs`, `buf` |-> `out_buffer`,
    `H` |-> `storage_trace_horizon mid.storage_trace`,
    `es` |-> `mid`, `s` |-> `t`,
    `PG` |-> `PG`, `G` |-> `G`, `tn` |-> `tn`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``, gamma |-> ``:256``]
      alloc_buffer_origin_ptr_path)) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`out_var`,`w_alloc`,`allocated`,`G_alloc`,`tn_alloc`]
    strip_assume_tac) >>
  `~allocated.vs_halted` by
    (qpat_assum `allocated with <| vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _ |> = t`
       (mp_tac o Q.AP_TERM `\z. z.vs_halted`) >> simp[]) >>
  qabbrev_tac `out_name = STRING #"%" (toString out_alloc_cs.cs_next_var)` >>
  qabbrev_tac `out_inst = mk_inst out_alloc_cs.cs_next_id ADD
    [ov;Lit 32w] [out_name]` >>
  qabbrev_tac `out_update = update_var out_name (w_alloc+32w) allocated` >>
  qabbrev_tac `ready = out_update with vs_inst_idx := SUC allocated.vs_inst_idx` >>
  qabbrev_tac `G_ready = step_prov PG G_alloc out_inst out_update` >>
  qabbrev_tac `tn_ready = step_taint out_inst allocated out_update tn_alloc` >>
  `ov = Var out_var` by metis_tac[] >>
  `eval_operand ov allocated = SOME w_alloc` by
    simp[venomStateTheory.eval_operand_def] >>
  `op_taint tn_alloc ov = {}` by
    (qpat_assum `ptr_covers G_alloc tn_alloc out_var allocated _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [ptr_covers_def]) >> simp[]) >>
  mp_tac (Q.INST [`sm` |-> `out_alloc_cs`, `sn` |-> `s7`,
    `left` |-> `ov`, `off` |-> `32w`, `dst` |-> `op`,
    `w` |-> `w_alloc`, `s` |-> `allocated`, `PG` |-> `PG`,
    `G` |-> `G_alloc`, `tn` |-> `tn_alloc`, `out` |-> `out_name`,
    `i` |-> `out_inst`, `u` |-> `out_update`, `t` |-> `ready`,
    `G'` |-> `G_ready`, `tn'` |-> `tn_ready`] attribute_add_full_frame) >>
  impl_tac >- simp[Abbr `out_name`,Abbr `out_inst`,Abbr `out_update`,
    Abbr `ready`,Abbr `G_ready`,Abbr `tn_ready`] >> strip_tac >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid allocated /\
    ghost_inv_at (DF H) lo d cenv cx mid G_alloc tn_alloc allocated` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
       (qspec_then `H` (fn th => qpat_assum
         `valid_horizon cx st0 H mid.storage_trace`
         (strip_assume_tac o MATCH_MP th))) >>
     conj_tac
     >- (qpat_assum `!H'. stmt_state_rel H' _ _ _ _ _ t ==> _`
           (qspec_then `H` irule) >> first_assum ACCEPT_TAC) >>
     mp_tac (Q.INST [`D` |-> `DF (H:(bool # 256 word # type_value) list # num list)`, `sa` |-> `sc`, `es` |-> `mid`,
       `s` |-> `t`, `t` |-> `allocated`, `G'` |-> `G_alloc`,
       `tn'` |-> `tn_alloc`, `e` |->
         `w2n (w_alloc:256 word) + (((flags.rcf_max_outsize+31) DIV 32)*32+32)`]
       (INST_TYPE [alpha |-> ``:256``] alloc_buffer_ghost_inv_at)) >>
     impl_tac >- simp[] >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G_alloc tn_alloc` by
    (mp_tac (Q.INST [`es0` |-> `es`, `sk` |-> `sa`, `s` |-> `t`,
       `G'` |-> `G_alloc`, `tn'` |-> `tn_alloc`,
       `e` |-> `w2n (w_alloc:256 word) + (((flags.rcf_max_outsize+31) DIV 32)*32+32)`]
       (INST_TYPE [alpha |-> ``:num # num``] alloc_buffer_ghost_kept_at)) >>
     impl_tac
     >- (simp[] >> conj_tac
         >- (rpt strip_tac >>
             qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) ==> _`
               (drule_then ACCEPT_TAC)) >> first_assum ACCEPT_TAC) >> simp[]) >>
  `sc.cs_next_var <= out_alloc_cs.cs_next_var` by
    (qspecl_then [`((flags.rcf_max_outsize+31) DIV 32)*32+32`,`sc`]
       mp_tac ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
  mp_tac (Q.INST [`sa` |-> `sc`, `sm` |-> `out_alloc_cs`,
    `s` |-> `allocated`, `G` |-> `G_alloc`, `tn` |-> `tn_alloc`,
    `G'` |-> `G_ready`, `tn'` |-> `tn_ready`,
    `w` |-> `w_alloc+32w`, `n` |-> `SUC allocated.vs_inst_idx`]
    attribute_fresh_full_ghost_update) >>
  impl_tac >- (simp[Abbr `out_name`] >> metis_tac[]) >> strip_tac >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx mid G_ready tn_ready ready` by
    (rpt strip_tac >> simp[Abbr `ready`,Abbr `out_update`,Abbr `out_name`] >>
     first_assum irule >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G_ready tn_ready` by
    (irule ghost_kept_at_clean_suffix >>
     qexistsl_tac [`G_alloc`,`tn_alloc`] >> simp[] >> rpt strip_tac >>
     `not_fresh_at sc x` by res_tac >>
     `x <> out_name` by
       (qpat_assum `not_fresh_at sc x`
          (mp_tac o REWRITE_RULE [not_fresh_at_def]) >>
        disch_then (qspec_then `out_alloc_cs.cs_next_var` mp_tac) >>
        simp[Abbr `out_name`]) >>
     simp[]) >>
  `flags.rcf_max_outsize <= ((flags.rcf_max_outsize+31) DIV 32)*32` by
    (qspec_then `flags.rcf_max_outsize` mp_tac word_size_capacity >>
     simp[vfmConstantsTheory.word_size_def]) >>
  `w2n (w_alloc:256 word) + 32 < dimword(:256) /\
   w2n (w_alloc:256 word) + 32 + flags.rcf_max_outsize <= allocated.vs_alloca_next` by
    decide_tac >>
  `w_alloc + 32w = n2w (w2n (w_alloc:256 word) + 32)` by
    (mp_tac (Q.SPECL [`w2n (w_alloc:256 word)`,`32`]
       (INST_TYPE [alpha |-> ``:256``] wordsTheory.word_add_n2w)) >> simp[]) >>
  `eval_operand op ready = SOME (n2w (w2n (w_alloc:256 word)+32))` by
    simp[Abbr `ready`,Abbr `out_update`,venomStateTheory.eval_operand_def,
      lookup_var_def,update_var_def,finite_mapTheory.FLOOKUP_UPDATE] >>
  (Q.SUBGOAL_THEN
   `?rb_out rn_out. FLOOKUP G_alloc out_var = SOME (rb_out,rn_out) /\
    rb_out <= w2n (w_alloc:256 word) /\
    w2n (w_alloc:256 word) + (((flags.rcf_max_outsize+31) DIV 32)*32+32) <= rb_out+rn_out`
    (qx_choosel_then [`rb_out`,`rn_out`] strip_assume_tac)
   >- (qpat_assum `ptr_covers G_alloc tn_alloc out_var allocated _`
        (mp_tac o REWRITE_RULE [ptr_covers_def]) >> simp[])) >>
  `ptr_covers G_ready tn_ready out_name ready flags.rcf_max_outsize` by
    (rewrite_tac[ptr_covers_def] >> conj_tac
     >- (once_rewrite_tac[GSYM (ASSUME ``op = Var out_name``)] >>
         first_assum ACCEPT_TAC) >>
     qexistsl_tac [`n2w (w2n (w_alloc:256 word)+32):256 word`,`rb_out`,`rn_out`] >>
     simp[ptrDisciplineTheory.op_prov_def,venomStateTheory.eval_operand_def,
       wordsTheory.w2n_n2w,Abbr `ready`,Abbr `out_update`,
       lookup_var_def,update_var_def,finite_mapTheory.FLOOKUP_UPDATE] >> decide_tac) >>
  drule_all (Q.INST [`sm` |-> `out_alloc_cs`, `s` |-> `allocated`]
    emit_op_fetch_boundary) >>
  disch_then (qx_choosel_then [`add_name`,`add_bb`] strip_assume_tac) >>
  `add_name = out_name` by simp[Abbr `out_name`] >>
  qpat_x_assum `add_name = out_name` SUBST_ALL_TAC >>
  `step_inst_base out_inst allocated = OK out_update` by
    (simp_tac bool_ss [Abbr `out_inst`,Abbr `out_update`] >>
     irule step_ADD >> simp[venomStateTheory.eval_operand_def]) >>
  `alloca_inv allocated` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid allocated /\
       ghost_inv_at (DF H) lo d cenv cx mid G_alloc tn_alloc allocated`
       (fn th => ACCEPT_TAC
         (CONJUNCT1 (CONJUNCT2 (REWRITE_RULE [stmt_state_rel_def]
           (CONJUNCT1 (MATCH_MP
             (Q.SPEC `storage_trace_horizon mid.storage_trace` th)
             (ASSUME ``valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
               mid.storage_trace``)))))))) >>
  `alloca_history func ready` by
    (qspecl_then [`func`,`allocated`,`add_bb`,`out_inst`,`out_update`]
       mp_tac allocaHistoryTheory.alloca_history_base_step >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         simp_tac bool_ss [Abbr `out_inst`] >> first_assum ACCEPT_TAC) >>
     simp_tac (srw_ss()) [Abbr `ready`,Abbr `out_inst`,venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def]) >>
  `not_local_ptr cenv mid.scopes out_name` by
    (qspecl_then [`cenv`,`sc`,`mid.scopes`,`out_alloc_cs.cs_next_var`]
       mp_tac local_ptrs_reserved_fresh >> simp[Abbr `out_name`]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid ready` by
    (rpt strip_tac >>
     simp_tac bool_ss [Abbr `ready`,Abbr `out_update`,stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
          stmt_state_rel H ctx func cenv cx mid allocated /\
          ghost_inv_at (DF H) lo d cenv cx mid G_alloc tn_alloc allocated`
          (fn th => ACCEPT_TAC (CONJUNCT1
            (MATCH_MP (Q.SPEC `H` th)
              (ASSUME ``valid_horizon cx st0 H mid.storage_trace``))))]) >>
  `!x. not_fresh_at sc x ==> x <> out_name` by
    (rpt strip_tac >> qpat_assum `not_fresh_at sc x`
       (mp_tac o REWRITE_RULE [not_fresh_at_def]) >>
     disch_then (qspec_then `out_alloc_cs.cs_next_var` mp_tac) >>
     simp[Abbr `out_name`]) >>
  `!x. not_fresh_at sc x ==>
    lookup_var x ready = lookup_var x t /\
    FLOOKUP G_ready x = FLOOKUP G x /\
    op_taint tn_ready (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     simp_tac (srw_ss()) [Abbr `ready`,Abbr `out_update`,lookup_var_set_inst_idx] >>
     asm_simp_tac bool_ss [lookup_var_update_var]) >>
  `allocated.vs_memory = t.vs_memory /\ allocated.vs_labels = t.vs_labels` by
    (qpat_assum `allocated with <| vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _ |> = t`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `ready.vs_memory = t.vs_memory /\ ready.vs_labels = t.vs_labels /\
   ready.vs_allocas = allocated.vs_allocas /\
   ready.vs_alloca_next = allocated.vs_alloca_next /\ ~ready.vs_halted /\
   ready.vs_current_bb = s7.cs_current_bb /\
   ready.vs_inst_idx = LENGTH s7.cs_current_insts` by
    simp[Abbr `ready`,Abbr `out_update`,update_var_def] >>
  `!arg. (!x. arg = Var x ==> not_fresh_at sc x) ==>
    eval_operand arg ready = eval_operand arg t /\
    op_taint tn_ready arg = op_taint tn arg /\
    op_prov G_ready arg = op_prov G arg` by
    (gen_tac >> strip_tac >>
     mp_tac (Q.INST [`st` |-> `sc`, `s` |-> `t`, `t` |-> `ready`,
       `HG` |-> `G_ready`, `u` |-> `tn_ready`, `op` |-> `arg`]
       old_operand_ghost_frame) >> impl_tac >- simp[] >> simp[]) >>
  `fn_has_code s7 sb func` by metis_tac[fn_has_code_split] >>
  mp_tac (Q.INST [`sa` |-> `s7`, `gas` |-> `gas_op`,
    `value` |-> `value_op`, `ct` |->
      `if flags.rcf_is_static then StaticCall else RegularCall`,
    `n` |-> `flags.rcf_max_outsize`, `rev` |-> `flags.rcf_revert_on_failure`]
    rawCallShapePtrTheory.raw_call_finish_call_code) >>
  impl_tac >- (Cases_on `flags.rcf_is_static` >> simp[]) >>
  disch_then (qx_choosel_then [`q_call`,`call_cs`,`bb_call`] strip_assume_tac) >>
  qabbrev_tac `call_inst = mk_inst s7.cs_next_id
    (if flags.rcf_is_static then STATICCALL else CALL)
    (if flags.rcf_is_static then [gas_op;addr;dp;dl;op;Lit (n2w flags.rcf_max_outsize)]
     else [gas_op;addr;value_op;dp;dl;op;Lit (n2w flags.rcf_max_outsize)]) [q_call]` >>
  `EVERY (\arg. (!x. arg = Var x ==> not_fresh_at sc x) /\
      (!l. arg <> Label l) /\ op_taint tn arg = {}) [gas_op;addr;dp;dl]` by
    (qpat_assum `EVERY _ (if flags.rcf_is_static then _ else _)`
       (fn th => POP_ASSUM_LIST (K ALL_TAC) >> mp_tac th) >>
     Cases_on `flags.rcf_is_static` >>
     asm_simp_tac bool_ss [listTheory.EVERY_DEF] >> metis_tac[]) >>
  qpat_assum `EVERY _ [gas_op;addr;dp;dl]`
    (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  `eval_operand gas_op ready = SOME gw /\ eval_operand addr ready = SOME aw /\
   eval_operand dp ready = SOME (n2w (b+32)) /\
   eval_operand dl ready = SOME (n2w (LENGTH (bs:word8 list)))` by simp[] >>
  `~flags.rcf_is_static ==> eval_operand value_op ready = SOME vw /\
    op_taint tn_ready value_op = {}` by
    (strip_tac >>
     qpat_assum `EVERY _ (if flags.rcf_is_static then _ else _)`
       (strip_assume_tac o SIMP_RULE (srw_ss())
         [ASSUME ``~flags.rcf_is_static``]) >> simp[]) >>
  `read_memory (b+32) (LENGTH (bs:word8 list)) ready = bs` by
    simp[venomStateTheory.read_memory_def, GSYM valueEncodingDefsTheory.mem_bytes_at_def] >>
  `state_rel (storage_trace_horizon mid.storage_trace) func cenv cx mid ready` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       stmt_state_rel H _ _ _ _ _ ready`
       (fn th => ACCEPT_TAC (CONJUNCT1 (REWRITE_RULE [stmt_state_rel_def]
         (MATCH_MP (Q.SPEC `storage_trace_horizon mid.storage_trace` th)
           (ASSUME ``valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
             mid.storage_trace``)))))) >>
  `ready.vs_call_ctx.cc_static = cx.txn.is_static` by
    (qpat_assum `state_rel (storage_trace_horizon mid.storage_trace)
       func cenv cx mid ready`
       (fn th => POP_ASSUM_LIST (K ALL_TAC) >> mp_tac th) >>
     simp[state_rel_def,call_ctx_rel_def]) >>
  (Q.SUBGOAL_THEN
   `?p. dp = Var p /\ FLOOKUP G_ready p = SOME (region_base,region_size)`
    (qx_choose_then `data_ptr` strip_assume_tac)
   >- (`op_prov G_ready dp = SOME (region_base,region_size)` by simp[] >>
     Cases_on `dp` >>
     qpat_assum `op_prov G_ready _ = SOME (region_base,region_size)`
       (mp_tac o REWRITE_RULE [ptrDisciplineTheory.op_prov_def]) >>
     simp_tac (srw_ss()) [])) >>
  `op_taint tn_ready (Lit (n2w flags.rcf_max_outsize)) = {}` by
    simp_tac (srw_ss()) [ptrDisciplineTheory.op_taint_def] >>
  `EVERY (\arg. op_taint tn_ready arg = {}) call_inst.inst_operands` by
    (simp_tac (srw_ss()) [Abbr `call_inst`,venomInstTheory.mk_inst_def] >>
     qpat_assum `op_taint tn_ready (Lit (n2w flags.rcf_max_outsize)) = {}` mp_tac >>
     qpat_assum `op_taint tn_ready op = {}` mp_tac >>
     qpat_assum `~flags.rcf_is_static ==> _ /\ _` mp_tac >>
     qpat_assum `!arg. (!x. arg = Var x ==> not_fresh_at sc x) ==> _ /\ _ /\ _` mp_tac >>
     qpat_assum `EVERY _ [gas_op;addr;dp;dl]` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `flags.rcf_is_static` >> simp[listTheory.EVERY_DEF] >> metis_tac[]) >>
  `!i. b+32 <= i /\ i < b+32+LENGTH (bs:word8 list) ==> i NOTIN tn_ready.t_mem` by
    (qx_gen_tac `i` >> disch_then strip_assume_tac >>
     `i NOTIN tn.t_mem` by res_tac >>
     `i < t.vs_alloca_next` by decide_tac >>
     qpat_assum `tn_ready.t_mem = tn_alloc.t_mem` (fn th => rewrite_tac [th]) >>
     qpat_assum `!i. i IN tn_alloc.t_mem <=> _` (qspec_then `i` mp_tac) >>
     qpat_assum `i NOTIN tn.t_mem` mp_tac >>
     qpat_assum `i < t.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `t.vs_alloca_next <= i` by metis_tac[] >> decide_tac) >>
  (Q.SUBGOAL_THEN
   `((call_inst.inst_opcode = CALL /\ call_inst.inst_operands =
      [gas_op;addr;value_op;dp;dl;op;Lit (n2w flags.rcf_max_outsize)]) \/
     (call_inst.inst_opcode = STATICCALL /\ call_inst.inst_operands =
      [gas_op;addr;dp;dl;op;Lit (n2w flags.rcf_max_outsize)]))`
    assume_tac
   >- (simp_tac (srw_ss()) [Abbr `call_inst`,venomInstTheory.mk_inst_def] >>
       POP_ASSUM_LIST (K ALL_TAC) >>
       Cases_on `flags.rcf_is_static` >> simp[])) >>
  `w2n (n2w (b+32):256 word) = b+32 /\
   w2n (n2w (LENGTH (bs:word8 list)):256 word) = LENGTH (bs:word8 list) /\
   w2n (n2w (w2n (w_alloc:256 word)+32):256 word) = w2n (w_alloc:256 word)+32 /\
   w2n (n2w flags.rcf_max_outsize:256 word) = flags.rcf_max_outsize` by
    simp_tac (srw_ss()) [wordsTheory.w2n_n2w,
      ASSUME ``b+32 < dimword(:256)``,
      ASSUME ``LENGTH (bs:word8 list) < dimword(:256)``,
      ASSUME ``w2n (w_alloc:256 word)+32 < dimword(:256)``,
      ASSUME ``flags.rcf_max_outsize < dimword(:256)``] >>
  `eval_operand (Lit (n2w flags.rcf_max_outsize)) ready =
    SOME (n2w flags.rcf_max_outsize)` by
    simp_tac (srw_ss()) [venomStateTheory.eval_operand_def] >>
  `FLOOKUP G_ready out_name = SOME (rb_out,rn_out)` by
    (qpat_assum `FLOOKUP G_ready out_name = op_prov G_alloc ov`
       (fn th => rewrite_tac [th]) >>
     simp_tac (srw_ss()) [ASSUME ``ov = Var out_var``,ptrDisciplineTheory.op_prov_def] >>
     first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    access_ok lo G_ready func call_inst ready /\
    taint_ok func tn_ready call_inst ready /\
    inst_mem_below_frontier call_inst ready /\ allocas_from lo ready /\
    stor_taint_ok_at (DF H) tn_ready ready` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       ghost_inv_at _ _ _ _ _ _ _ _ ready`
       (qspec_then `H` (fn th => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
         (strip_assume_tac o MATCH_MP th))) >>
     mp_tac (Q.INST [`inst` |-> `call_inst`,`gas` |-> `gas_op`,`addr` |-> `addr`,
       `value` |-> `value_op`,`ao` |-> `dp`,`az` |-> `dl`,
       `ro` |-> `op`,`rz` |-> `Lit (n2w flags.rcf_max_outsize)`,
       `s` |-> `ready`,`aw` |-> `n2w (b+32):256 word`,
       `an` |-> `n2w (LENGTH (bs:word8 list)):256 word`,
       `rw` |-> `n2w (w2n (w_alloc:256 word)+32):256 word`,
       `rn` |-> `n2w flags.rcf_max_outsize:256 word`,
       `tn` |-> `tn_ready`,`G` |-> `G_ready`,`fn` |-> `func`,
       `D` |-> `DF (H:(bool # 256 word # type_value) list # num list)`,`es` |-> `mid`]
       extcall_call_pointer_conditions) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         PURE_REWRITE_TAC
           [ASSUME ``w2n (n2w (b+32):256 word) = b+32``,
            ASSUME ``w2n (n2w (LENGTH (bs:word8 list)):256 word) = LENGTH (bs:word8 list)``,
            ASSUME ``w2n (n2w (w2n (w_alloc:256 word)+32):256 word) = w2n (w_alloc:256 word)+32``,
            ASSUME ``w2n (n2w flags.rcf_max_outsize:256 word) = flags.rcf_max_outsize``] >>
         rpt strip_tac
         >- (qexistsl_tac [`data_ptr`,`region_base`,`region_size`] >>
             rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac)
         >- (qexistsl_tac [`out_name`,`rb_out`,`rn_out`] >>
             rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
             TRY (once_rewrite_tac [ASSUME ``op = Var out_name``] >>
               first_assum ACCEPT_TAC) >> decide_tac)
         >- (qpat_assum `!i. b+32 <= i /\ i < b+32+LENGTH (bs:word8 list) ==> _`
               (qspec_then `i` mp_tac) >>
             impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
             qpat_assum `i IN tn_ready.t_mem` mp_tac >>
             POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
         >- (Cases_on `LENGTH (bs:word8 list) = 0`
             >- (qpat_assum `(n2w (LENGTH (bs:word8 list)):256 word) <> 0w` mp_tac >>
                 simp_tac (srw_ss()) [ASSUME ``LENGTH (bs:word8 list) = 0``]) >>
             decide_tac)
         >> decide_tac) >>
     disch_then ACCEPT_TAC) >>
  Cases_on `cx.txn.is_static /\ amount <> 0`
  >- suspend "positiveStatic" >>
  `cx.txn.is_static ==> amount = 0` by metis_tac[] >>
  drule_all (Q.INST [`flags` |-> `flags`,`target` |-> `target`,
    `data` |-> `bs`,`amount` |-> `amount`,`gas` |-> `source_gas`]
    raw_call_prepared_source_total) >>
  simp_tac (srw_ss()) [ASSUME ``~(cx.txn.is_static /\ amount <> 0)``,
    ASSUME ``flags.rcf_max_outsize <> 0``] >>
  disch_then (qx_choosel_then [`rq`,`outcome`,`es1`] strip_assume_tac) >>
  reverse (Cases_on `storage_trace_domain cx st0
    (SND (adopt_call_outcome rq outcome es1)).storage_trace`)
  >- (irule gas_outcome_full_bad_nil >> simp[]) >>
  qspecl_then [`storage_trace_horizon mid.storage_trace`,`func`,`cenv`,
    `cx`,`mid`,`ready`,`call_inst`,`gw`,`aw`,
    `if flags.rcf_is_static then 0w else vw`,
    `n2w (b+32):256 word`,`n2w (LENGTH (bs:word8 list)):256 word`,
    `n2w (w2n (w_alloc:256 word)+32):256 word`,`n2w flags.rcf_max_outsize:256 word`,
    `flags.rcf_is_static \/ cx.txn.is_static`,`q_call`,`target`,
    `if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount`,`rq`,`outcome`,`es1`]
    mp_tac extCallOracleStepTheory.exec_ext_call_oracle_step >>
  impl_tac
  >- (simp[Abbr `call_inst`,venomInstTheory.mk_inst_def] >>
      Cases_on `flags.rcf_is_static` >> Cases_on `cx.txn.is_static` >> simp[]) >>
  disch_then (qx_choose_then `call_state` strip_assume_tac) >>
  qabbrev_tac `u_call = update_var q_call
    (if outcome.co_success then 1w else 0w) call_state` >>
  `cx.txn.is_static /\ ~flags.rcf_is_static ==> vw = 0w` by
    (qpat_assum `cx.txn.is_static ==> amount = 0` mp_tac >>
     qpat_assum `~flags.rcf_is_static ==>
       eval_operand value_op t = SOME vw /\ w2n vw = amount` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[wordsTheory.w2n_eq_0] >> metis_tac[wordsTheory.w2n_eq_0]) >>
  `step_inst_base call_inst ready = OK u_call` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`eval_operand gas_op ready = SOME gw`,`eval_operand addr ready = SOME aw`,
        `eval_operand dp ready = SOME (n2w (b+32))`,
        `eval_operand dl ready = SOME (n2w (LENGTH (bs:word8 list)))`,
        `eval_operand op ready = SOME (n2w (w2n (w_alloc:256 word)+32))`,
        `~flags.rcf_is_static ==> eval_operand value_op ready = SOME vw /\ _`,
        `cx.txn.is_static /\ ~flags.rcf_is_static ==> vw = 0w`,
        `ready.vs_call_ctx.cc_static = cx.txn.is_static`,
        `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _`] >>
     simp_tac pure_ss [Abbr `call_inst`,Abbr `u_call`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     Cases_on `flags.rcf_is_static` >> Cases_on `cx.txn.is_static` >>
     gvs[venomInstTheory.mk_inst_def,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomStateTheory.eval_operand_def,wordsTheory.w2n_eq_0]) >>
  `call_state.vs_vars = ready.vs_vars /\
   call_state.vs_allocas = ready.vs_allocas /\
   call_state.vs_alloca_next = ready.vs_alloca_next /\
   call_state.vs_fmp = ready.vs_fmp /\
   call_state.vs_labels = ready.vs_labels /\
   call_state.vs_current_bb = ready.vs_current_bb /\
   call_state.vs_inst_idx = ready.vs_inst_idx /\
   call_state.vs_halted = ready.vs_halted /\
   call_state.vs_data_section = ready.vs_data_section /\
   call_state.vs_call_ctx = ready.vs_call_ctx /\
   call_state.vs_immutables = ready.vs_immutables /\
   call_state.vs_gas_readings = ready.vs_gas_readings` by
    (qpat_assum `call_state = _` (fn th => once_rewrite_tac [th]) >>
     simp_tac (srw_ss()) []) >>
  qpat_x_assum `call_state = _` (K ALL_TAC) >>
  qabbrev_tac `s_call = u_call with vs_inst_idx := SUC ready.vs_inst_idx` >>
  qabbrev_tac `G_call = step_prov PG G_ready call_inst u_call` >>
  qabbrev_tac `tn_call = step_taint call_inst ready u_call tn_ready` >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_edge (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (ready,G_ready,tn_ready) [] (OK s_call,G_call,tn_call)` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       access_ok _ _ _ _ _ /\ _`
       (qspec_then `H` (fn th => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
         (strip_assume_tac o MATCH_MP th))) >>
     mp_tac (Q.INST [`inst` |-> `call_inst`,`gas` |-> `gas_op`,`addr` |-> `addr`,
       `value` |-> `value_op`,`ao` |-> `dp`,`az` |-> `dl`,
       `ro` |-> `op`,`rz` |-> `Lit (n2w flags.rcf_max_outsize)`,
       `s` |-> `ready`,`u` |-> `u_call`,`G` |-> `G_ready`,`tn` |-> `tn_ready`,
       `D` |-> `DF (H:(bool # 256 word # type_value) list # num list)`,`fn` |-> `func`,`bb` |-> `bb_call`,
       `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
       call_origin_ptr_edge) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         FIRST
          [qpat_assum `lookup_block s7.cs_current_bb func.fn_blocks = SOME bb_call`
             (fn th => simp_tac bool_ss
                [ASSUME ``ready.vs_current_bb = s7.cs_current_bb``] >> ACCEPT_TAC th),
           qpat_assum `get_instruction bb_call (LENGTH s7.cs_current_insts) = _`
             (fn th =>
                simp_tac bool_ss [Abbr `call_inst`,
                  ASSUME ``ready.vs_inst_idx = LENGTH s7.cs_current_insts``] >>
                POP_ASSUM_LIST (K ALL_TAC) >> mp_tac th >>
                Cases_on `flags.rcf_is_static` >> simp[])]) >>
     disch_then (fn th =>
       simp_tac bool_ss [Abbr `s_call`,Abbr `G_call`,Abbr `tn_call`] >>
       ACCEPT_TAC th)) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid ready`
    (fn th => MAP_EVERY ASSUME_TAC (CONJUNCTS
      (REWRITE_RULE [stmt_state_rel_def]
        (MATCH_MP (Q.SPEC `storage_trace_horizon mid.storage_trace` th)
          (ASSUME ``valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
            mid.storage_trace``))))) >>
  `call_state.vs_memory =
    (write_memory_with_expansion (w2n (w_alloc:256 word)+32)
      (TAKE flags.rcf_max_outsize outcome.co_returnData) ready).vs_memory` by
    (qpat_assum `call_state.vs_memory = _`
       (ACCEPT_TAC o SIMP_RULE (srw_ss())
          [ASSUME ``w2n (n2w (w2n (w_alloc:256 word)+32):256 word) = w2n w_alloc+32``,
           ASSUME ``w2n (n2w flags.rcf_max_outsize:256 word) = flags.rcf_max_outsize``])) >>
  `LENGTH ready.vs_memory <= LENGTH call_state.vs_memory` by
    (qpat_assum `call_state.vs_memory = _` (fn th => rewrite_tac [th]) >>
     simp_tac (srw_ss()) [venomMemPropsTheory.LENGTH_write_memory_with_expansion]) >>
  `!a k. a+k <= w2n (w_alloc:256 word)+32 \/
      w2n (w_alloc:256 word)+32+MIN flags.rcf_max_outsize (LENGTH outcome.co_returnData) <= a ==>
    mem_bytes_at a k call_state.vs_memory = mem_bytes_at a k ready.vs_memory` by
    (qx_genl_tac [`a`,`k`] >> disch_tac >>
     qpat_assum `call_state.vs_memory = _` (fn th => rewrite_tac [th]) >>
     irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >>
     PURE_REWRITE_TAC
       [listTheory.LENGTH_TAKE_EQ,
        ASSUME ``w2n (n2w (w2n (w_alloc:256 word)+32):256 word) = w2n w_alloc+32``,
        ASSUME ``w2n (n2w flags.rcf_max_outsize:256 word) = flags.rcf_max_outsize``] >>
     qpat_assum `a+k <= w2n (w_alloc:256 word)+32 \/ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[arithmeticTheory.MIN_DEF]) >>
  `!name entry p sz. lookup_scopes name mid.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p ready = lookup_var p allocated` by
    (rpt strip_tac >>
     `p <> out_name` by
       (qpat_assum `not_local_ptr cenv mid.scopes out_name`
          (mp_tac o CONJUNCT1 o REWRITE_RULE [not_local_ptr_def]) >>
        qpat_assum `lookup_scopes name mid.scopes = SOME entry` mp_tac >>
        qpat_assum `FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     simp_tac bool_ss [Abbr `ready`,Abbr `out_update`,lookup_var_set_inst_idx,
       lookup_var_update_var,ASSUME ``(p:string) <> out_name``]) >>
  `!name a len. local_region cenv mid.scopes ready name a len ==>
    regions_disjoint (w2n (w_alloc:256 word)+32)
      (MIN flags.rcf_max_outsize (LENGTH outcome.co_returnData)) a len` by
    (rpt strip_tac >>
     `local_region cenv mid.scopes allocated name a len` by
       (qpat_assum `!name entry p sz.
          lookup_scopes name mid.scopes = SOME entry /\
          FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
          lookup_var p ready = lookup_var p allocated`
          (fn th => ACCEPT_TAC (EQ_MP
            (Q.INST [`name` |-> `name`,`lo` |-> `a`,`sz` |-> `len`]
              (MATCH_MP local_region_lookup_cong th))
            (ASSUME ``local_region cenv mid.scopes ready name a len``)))) >>
     qpat_assum `!name b len. local_region cenv mid.scopes allocated name b len ==> _`
       (drule_then mp_tac) >>
     simp[regions_disjoint_def] >> strip_tac >>
     `MIN flags.rcf_max_outsize (LENGTH outcome.co_returnData) <= flags.rcf_max_outsize`
       by simp[] >> decide_tac) >>
  `local_ptrs_rel func cenv mid.scopes ready /\
   immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor mid ready` by
    (qpat_assum `state_rel (storage_trace_horizon mid.storage_trace)
       func cenv cx mid ready`
       (fn th => POP_ASSUM_LIST (K ALL_TAC) >> mp_tac th) >>
     simp[state_rel_def]) >>
  `local_ptrs_rel func cenv mid.scopes call_state` by
    (irule local_ptrs_rel_clean_write_frame >>
     qexistsl_tac [`TAKE flags.rcf_max_outsize outcome.co_returnData`,
       `w2n (w_alloc:256 word)+32`,`ready`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     FIRST
      [simp_tac (srw_ss()) [lookup_var_def,
          ASSUME ``call_state.vs_vars = ready.vs_vars``] >> NO_TAC,
       simp_tac (srw_ss()) [listTheory.LENGTH_TAKE_EQ] >>
       qpat_assum `!name a len. local_region cenv mid.scopes ready name a len ==> _`
         (ACCEPT_TAC o SIMP_RULE (srw_ss()) [arithmeticTheory.MIN_ALT])]) >>
  `MEM (mk_inst sc.cs_next_id ALLOCA
     [Lit (n2w (((flags.rcf_max_outsize+31) DIV 32)*32+32))]
     [STRING #"%" (toString sc.cs_next_var)]) (fn_insts func)` by
    (qspecl_then [`((flags.rcf_max_outsize+31) DIV 32)*32+32`,`sc`,
       `out_alloc_cs`,`out_buffer`,`func`] mp_tac exprSimAllocTheory.buffer_alloc_code >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  `FLOOKUP ready.vs_allocas sc.cs_next_id =
    SOME (w2n (w_alloc:256 word),((flags.rcf_max_outsize+31) DIV 32)*32+32)` by
    (once_rewrite_tac [ASSUME ``ready.vs_allocas = allocated.vs_allocas``] >>
     first_assum ACCEPT_TAC) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor mid call_state` by
    (irule loweringSliceTheory.immutables_rel_mem_agree >> qexists_tac `ready` >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     `regions_disjoint off (type_memory_size tv) (w2n (w_alloc:256 word))
        (((flags.rcf_max_outsize+31) DIV 32)*32+32)` by
       (qpat_assum `immutable_alloca_sep func cenv cx mid ready`
          (fn th => mp_tac (Q.SPECL [`name`,`tv`,`v`,`off`]
            (MP (CONJUNCT2 (REWRITE_RULE [immutable_alloca_sep_def] th))
              (ASSUME ``cenv.ce_is_ctor``)))) >>
        impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
        disch_then (fn th => mp_tac (Q.SPECL
          [`mk_inst sc.cs_next_id ALLOCA
              [Lit (n2w (((flags.rcf_max_outsize+31) DIV 32)*32+32))]
              [STRING #"%" (toString sc.cs_next_var)]`,
           `w2n (w_alloc:256 word)`,
           `((flags.rcf_max_outsize+31) DIV 32)*32+32`]
          (CONJUNCT1 (CONJUNCT2 th)))) >>
        impl_tac
        >- (simp_tac (srw_ss()) [venomInstTheory.mk_inst_def] >>
            conj_tac >> FIRST
             [first_assum ACCEPT_TAC,
              qpat_assum `MEM (mk_inst sc.cs_next_id ALLOCA _ _) (fn_insts func)`
                (ACCEPT_TAC o REWRITE_RULE [venomInstTheory.mk_inst_def])]) >>
        disch_then ACCEPT_TAC) >>
     qpat_assum `!a k. _ ==> mem_bytes_at a k call_state.vs_memory = _` irule >>
     qpat_assum `regions_disjoint off _ _ _`
       (mp_tac o REWRITE_RULE [regions_disjoint_def]) >>
     `MIN flags.rcf_max_outsize (LENGTH outcome.co_returnData) <=
        flags.rcf_max_outsize` by simp_tac (srw_ss()) [] >>
     strip_tac >> decide_tac) >>
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
       stmt_state_rel H ctx func cenv cx mid ready`
       (qspec_then `H` (fn th => qpat_assum
         `valid_horizon cx st0 H mid.storage_trace`
         (strip_assume_tac o MATCH_MP th))) >>
     `state_rel H func cenv cx mid ready` by
       (qpat_assum `stmt_state_rel H ctx func cenv cx mid ready`
          (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE
            [exprLoweringPropsTheory.stmt_state_rel_def])) >>
     qspecl_then [`H`, `func`, `cenv`, `cx`, `mid`, `ready`,
       `call_inst`, `gw`, `aw`, `if flags.rcf_is_static then 0w else vw`,
       `n2w (b+32):256 word`, `n2w (LENGTH (bs:word8 list)):256 word`, `n2w (w2n (w_alloc:256 word)+32):256 word`, `n2w flags.rcf_max_outsize:256 word`,
       `flags.rcf_is_static \/ cx.txn.is_static`, `q_call`, `target`,
       `if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount`, `rq`, `outcome`, `es1`]
       mp_tac extCallOracleStepTheory.exec_ext_call_oracle_step >>
     impl_tac
     >- (simp[Abbr `call_inst`, venomInstTheory.mk_inst_def] >>
         Cases_on `flags.rcf_is_static` >> Cases_on `cx.txn.is_static` >> simp[]) >>
     disch_then (qx_choose_then `call_state_H` strip_assume_tac) >>
     `call_state_H.vs_vars = ready.vs_vars` by
       (qpat_assum `call_state_H = _` (fn th => once_rewrite_tac [th]) >>
        simp_tac (srw_ss()) []) >>
     `call_state_H = call_state` by
       (qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
        qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
        qpat_assum `call_state_H.vs_vars = ready.vs_vars` mp_tac >>
        qpat_assum `call_state.vs_vars = ready.vs_vars` mp_tac >>
        qpat_assum `Abbrev (u_call = _)`
          (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[venomStateTheory.update_var_def,
             venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
     qpat_assum `call_state_H = call_state`
       (fn eq => qpat_assum
          `_ ==> state_rel H func cenv cx
            (SND (adopt_call_outcome rq outcome es1)) call_state_H`
          (mp_tac o SUBS [eq])) >> simp[]) >>
  `sc.cs_next_var <= s7.cs_next_var` by
    (qspecl_then [`flags.rcf_max_outsize`,`sc`] mp_tac
       exprLoweringPropsTheory.ci_mono_compile_raw_call_outbuf >>
     qpat_assum `compile_raw_call_outbuf _ sc = _`
       (fn th => rewrite_tac [th]) >>
     simp_tac (srw_ss()) [ci_mono_def] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at sc x ==> x <> q_call` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at s7 x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sc` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `not_fresh_at s7 x` mp_tac >>
     qpat_assum `~not_fresh_at s7 q_call` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `~not_fresh_at sc q_call` by
    (qpat_assum `!x. not_fresh_at sc x ==> x <> q_call`
       (qspec_then `q_call` mp_tac) >> simp_tac (srw_ss()) []) >>
  `not_local_ptr cenv mid.scopes q_call` by
    (irule exprSimOperandsTheory.fresh_not_local_ptr >> qexists_tac `sc` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `u_call.vs_memory = call_state.vs_memory /\
   u_call.vs_allocas = ready.vs_allocas /\
   u_call.vs_alloca_next = ready.vs_alloca_next /\
   u_call.vs_fmp = ready.vs_fmp /\
   u_call.vs_call_ctx = ready.vs_call_ctx /\
   u_call.vs_immutables = ready.vs_immutables /\
   u_call.vs_labels = ready.vs_labels /\
   u_call.vs_current_bb = ready.vs_current_bb /\
   u_call.vs_halted = ready.vs_halted` by
    (simp_tac (srw_ss()) [Abbr `u_call`,update_var_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `call_inst.inst_outputs = [q_call]` by
    simp_tac (srw_ss()) [Abbr `call_inst`,venomInstTheory.mk_inst_def] >>
  `call_inst.inst_opcode = CALL ==> eval_operand value_op ready = SOME vw` by
    (simp_tac (srw_ss()) [Abbr `call_inst`,venomInstTheory.mk_inst_def] >>
     qpat_assum `~flags.rcf_is_static ==> _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `flags.rcf_is_static` >> simp[]) >>
  qspecl_then [`call_inst`,`gas_op`,`addr`,`value_op`,`dp`,`dl`,
    `op`,`Lit (n2w flags.rcf_max_outsize)`,`q_call`,`ready`,`gw`,`aw`,`vw`,
    `n2w (b+32):256 word`,`n2w (LENGTH (bs:word8 list)):256 word`,
    `n2w (w2n (w_alloc:256 word)+32):256 word`,`n2w flags.rcf_max_outsize:256 word`,
    `u_call`,`PG`,`G_ready`,`tn_ready`] mp_tac
    (Q.GENL [`inst`,`gas`,`addr`,`value`,`ao`,`az`,`ro`,`rz`,`out`,`s`,
       `gw`,`dw`,`vw`,`aw`,`an`,`rw`,`rn`,`u`,`PG`,`G`,`tn`]
       bodyFullExtCallGhostTheory.extcall_call_ghost_frame) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `!x. not_fresh_at sc x ==> lookup_var x u_call = lookup_var x ready` by
    (qx_gen_tac `x` >> disch_tac >>
     `x <> q_call` by
       (qpat_assum `!x. not_fresh_at sc x ==> x <> q_call`
          (qspec_then `x` irule) >> first_assum ACCEPT_TAC) >>
     qpat_assum `call_state.vs_vars = ready.vs_vars`
       (fn vars => qpat_assum `x <> q_call`
         (fn fresh => simp_tac bool_ss
           [Abbr `u_call`,lookup_var_update_var,lookup_var_def,
            boolTheory.COND_CLAUSES,vars,fresh]))) >>
  `~(call_inst.inst_opcode = CALL /\ ~ready.vs_call_ctx.cc_static /\
      u_call.vs_requests <> ready.vs_requests /\
      u_call.vs_outcomes <> ready.vs_outcomes /\
      (HD ready.vs_outcomes).co_success) ==>
    u_call.vs_accounts = ready.vs_accounts /\
    u_call.vs_transient = ready.vs_transient` by
    (qpat_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _`
       (mp_then Any mp_tac oracleCallStepPtrTheory.exec_ext_call_storage_cases) >>
     simp_tac (srw_ss()) [Abbr `call_inst`,venomInstTheory.mk_inst_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `flags.rcf_is_static` >> simp[] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stor_taint_ok_at (DF H) tn_call u_call` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       access_ok _ _ _ _ _ /\ _`
       (qspec_then `H` (fn th => qpat_assum
         `valid_horizon cx st0 H mid.storage_trace`
         (strip_assume_tac o MATCH_MP th))) >>
     simp_tac bool_ss [Abbr `tn_call`] >>
     irule bodyFullExtCallGhostTheory.extcall_call_storage_ghost >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp_tac (srw_ss()) [Abbr `call_inst`,venomInstTheory.mk_inst_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `flags.rcf_is_static` >> simp[]) >>
  `lo <= w2n (w_alloc:256 word)` by
    (qpat_assum `allocas_from lo allocated`
       (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
     disch_then (fn th => qpat_assum
       `FLOOKUP allocated.vs_allocas sc.cs_next_id = SOME _`
       (ACCEPT_TAC o MATCH_MP (Q.SPECL
         [`sc.cs_next_id`,`w2n (w_alloc:256 word)`,
          `((flags.rcf_max_outsize+31) DIV 32)*32+32`] th)))) >>
  `allocas_from lo u_call` by
    (qpat_assum `allocas_from lo allocated`
       (fn th => simp_tac bool_ss [ptrDisciplineTheory.allocas_from_def,
          ASSUME ``u_call.vs_allocas = ready.vs_allocas``,
          ASSUME ``ready.vs_allocas = allocated.vs_allocas``] >>
        ACCEPT_TAC (REWRITE_RULE [ptrDisciplineTheory.allocas_from_def] th))) >>
  `lo <= u_call.vs_alloca_next` by decide_tac >>
  `!x. not_fresh_at sc x ==>
    lookup_var x u_call = lookup_var x ready /\
    FLOOKUP G_call x = FLOOKUP G_ready x /\
    op_taint tn_call (Var x) = op_taint tn_ready (Var x)` by
    (qx_gen_tac `x` >> disch_tac >> conj_tac >- res_tac >>
     qpat_assum `!x. x <> q_call ==> FLOOKUP _ x = FLOOKUP G_ready x /\ _`
       (qspec_then `x` mp_tac) >>
     impl_tac
     >- (qpat_assum `!x. not_fresh_at sc x ==> x <> q_call`
           (qspec_then `x` irule) >> first_assum ACCEPT_TAC) >>
     disch_then (fn th =>
       simp_tac bool_ss [Abbr `G_call`,Abbr `tn_call`] >> ACCEPT_TAC th)) >>
  `!a k. a+k <= w2n (w_alloc:256 word)+32 \/
      w2n w_alloc+32+MIN flags.rcf_max_outsize (LENGTH outcome.co_returnData) <= a ==>
    mem_bytes_at a k u_call.vs_memory = mem_bytes_at a k ready.vs_memory` by
    (qpat_assum `!a k. _ ==> mem_bytes_at a k call_state.vs_memory = _`
       (fn th => PURE_REWRITE_TAC [ASSUME ``u_call.vs_memory = call_state.vs_memory``] >>
         ACCEPT_TAC th)) >>
  `!j. j < w2n (w_alloc:256 word)+32 \/
      w2n w_alloc+32+MIN flags.rcf_max_outsize (LENGTH outcome.co_returnData) <= j ==>
    (j IN tn_call.t_mem <=> j IN tn_ready.t_mem)` by
    (qx_gen_tac `j` >> disch_tac >>
     `~(w2n (w_alloc:256 word)+32 <= j /\
        j < w2n w_alloc+32+MIN flags.rcf_max_outsize (LENGTH outcome.co_returnData))`
       by decide_tac >>
     `u_call.vs_returndata = outcome.co_returnData` by
       simp_tac (srw_ss()) [Abbr `u_call`,update_var_def,
         ASSUME ``call_state.vs_returndata = outcome.co_returnData``] >>
     qpat_assum `Abbrev (tn_call = _)`
       (fn th => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     qpat_assum `(step_taint call_inst ready u_call tn_ready).t_mem = _`
       (fn th => PURE_REWRITE_TAC [th] >> simp_tac (srw_ss()) [
         ASSUME ``w2n (n2w (w2n (w_alloc:256 word)+32):256 word) = w2n w_alloc+32``,
         ASSUME ``w2n (n2w flags.rcf_max_outsize:256 word) = flags.rcf_max_outsize``,
         ASSUME ``u_call.vs_returndata = outcome.co_returnData``,
         ASSUME ``~(w2n (w_alloc:256 word)+32 <= j /\
           j < w2n w_alloc+32+MIN flags.rcf_max_outsize (LENGTH outcome.co_returnData))``])) >>
  `!name b len. local_region cenv mid.scopes ready name b len ==>
    w2n (w_alloc:256 word)+32+MIN flags.rcf_max_outsize (LENGTH outcome.co_returnData) <= b \/
    b+len <= w2n w_alloc+32` by
    (qpat_assum `!name a len. local_region cenv mid.scopes ready name a len ==> _`
       (fn th => ACCEPT_TAC (REWRITE_RULE [regions_disjoint_def] th))) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx mid G_call tn_call u_call` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       ghost_inv_at _ _ _ _ _ _ _ _ ready`
       (qspec_then `H` (fn th => qpat_assum
          `valid_horizon cx st0 H mid.storage_trace`
          (assume_tac o MATCH_MP th))) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       stor_taint_ok_at _ tn_call u_call`
       (qspec_then `H` (fn th => qpat_assum
          `valid_horizon cx st0 H mid.storage_trace`
          (assume_tac o MATCH_MP th))) >>
     qspecl_then [`DF H`,`lo`,`d`,`cenv`,`cx`,`mid`,`G_ready`,`tn_ready`,
       `ready`,`sc`,`func`,`w2n (w_alloc:256 word)+32`,
       `MIN flags.rcf_max_outsize (LENGTH outcome.co_returnData)`,
       `u_call`,`G_call`,`tn_call`] mp_tac
       (Q.GENL [`D`,`lo`,`d`,`cenv`,`cx`,`es`,`G`,`tn`,`s`,`sa`,`func`,
          `start`,`nb`,`z`,`H`,`tf`]
          bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_inv_at) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         rpt strip_tac >> res_tac >> decide_tac) >>
     disch_then ACCEPT_TAC) >>
  `(SND (adopt_call_outcome rq outcome es1)).scopes = mid.scopes /\
   (SND (adopt_call_outcome rq outcome es1)).immutables = mid.immutables` by
    (simp[rawCallMemoryFramePtrTheory.oracle_adoption_locals] >>
     qpat_assum `take_call_outcome _ _ _ mid = _`
       (mp_then Any mp_tac vyperCallOutcomeTheory.take_call_outcome_frame) >>
     disch_then (fn th => once_rewrite_tac [th]) >> simp[]) >>
  qabbrev_tac `ee_call = SND (adopt_call_outcome rq outcome es1) with gas_obs := []` >>
  `ee_call.scopes = mid.scopes /\ ee_call.immutables = mid.immutables` by
    simp[Abbr `ee_call`] >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `!H. valid_horizon _ _ H
       (SND (adopt_call_outcome rq outcome es1)).storage_trace ==>
       valid_horizon cx st0 H mid.storage_trace` mp_tac >>
     simp_tac (srw_ss()) [Abbr `ee_call`]) >>
  `!id a n. local_region cenv ee_call.scopes call_state id a n <=>
    local_region cenv mid.scopes ready id a n` by
    simp_tac (srw_ss()) [local_region_def,lookup_var_def,
      ASSUME ``ee_call.scopes = mid.scopes``,
      ASSUME ``call_state.vs_vars = ready.vs_vars``] >>
  `immutable_alloca_sep func cenv cx ee_call call_state` by
    (qspecl_then [`func`,`cenv`,`cx`,`mid`,`ee_call`,`ready`,`call_state`]
       mp_tac immutable_alloca_sep_fields >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         rpt strip_tac >> qexists_tac `id` >> res_tac) >> disch_then ACCEPT_TAC) >>
  `immutable_base_zero cenv call_state` by
    (qspecl_then [`cenv`,`ready`,`call_state`] mp_tac immutable_base_zero_frame >>
     simp_tac (srw_ss()) [lookup_var_def,
       ASSUME ``call_state.vs_vars = ready.vs_vars``] >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee_call u_call` by
    (qx_gen_tac `H` >> disch_tac >>
     `valid_horizon cx st0 H mid.storage_trace` by res_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid ready`
       (qspec_then `H` (fn th => qpat_assum
         `valid_horizon cx st0 H mid.storage_trace`
         (assume_tac o MATCH_MP th))) >>
     `state_rel H func cenv cx ee_call call_state` by
       (qpat_assum `Abbrev (ee_call = _)`
          (fn ab => let val eq = REWRITE_RULE [markerTheory.Abbrev_def] ab
                        val guard = SIMP_RULE (srw_ss()) [eq]
                          (ASSUME ``valid_horizon cx st0 H ee_call.storage_trace``)
                    in PURE_REWRITE_TAC [eq,state_rel_gas_obs] >>
                       qpat_assum `!H. valid_horizon _ _ H
                         (SND (adopt_call_outcome rq outcome es1)).storage_trace ==>
                         state_rel H func cenv cx
                           (SND (adopt_call_outcome rq outcome es1)) call_state`
                         (fn th => ACCEPT_TAC (MATCH_MP (Q.SPEC `H` th) guard))
                    end)) >>
     qspecl_then [`H`,`func`,`cenv`,`cx`,`mid`,`ready`,`ee_call`,`call_state`,`ctx`]
       mp_tac stmt_state_rel_allocas_frame >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> disch_tac >>
     qspecl_then [`H`,`func`,`cenv`,`cx`,`ee_call`,`call_state`,`q_call`,
       `if outcome.co_success then 1w else 0w`,`ctx`] mp_tac
       stmt_state_rel_update_var >>
     impl_tac
     >- (conj_tac >- first_assum ACCEPT_TAC >>
         PURE_REWRITE_TAC [ASSUME ``ee_call.scopes = mid.scopes``] >>
         first_assum ACCEPT_TAC) >>
     simp_tac (srw_ss()) [Abbr `u_call`]) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee_call s_call` by
    (qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee_call u_call` mp_tac >>
     simp_tac (srw_ss()) [Abbr `s_call`,stmt_state_rel_inst_idx]) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee_call G_call tn_call s_call` by
    (qx_gen_tac `H` >> disch_tac >>
     `valid_horizon cx st0 H mid.storage_trace` by res_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       ghost_inv_at (DF H) lo d cenv cx mid G_call tn_call u_call`
       (qspec_then `H` (fn th => qpat_assum
         `valid_horizon cx st0 H mid.storage_trace`
         (assume_tac o MATCH_MP th))) >>
     qpat_assum `Abbrev (s_call = _)`
       (fn th => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     PURE_REWRITE_TAC [ghostPcTransportPtrTheory.ghost_inv_at_inst_idx] >>
     qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid G_call tn_call u_call`
       (fn th => REWRITE_TAC [ghost_inv_at_def] >>
        PURE_REWRITE_TAC [ASSUME ``ee_call.scopes = mid.scopes``] >>
        ACCEPT_TAC (REWRITE_RULE [ghost_inv_at_def] th))) >>
  `(mid with gas_obs := []) = mid` by
    (qpat_assum `mid.gas_obs = []`
       (fn th => once_rewrite_tac [GSYM th]) >> simp_tac (srw_ss()) []) >>
  `eval_raw_call cx flags target bs amount source_gas mid =
    (FST (eval_raw_call cx flags target bs amount source_gas mid),ee_call)` by
    (qpat_assum `!tail. eval_raw_call _ _ _ _ _ _ _ = _`
       (qspec_then `[]` mp_tac) >>
     simp_tac (srw_ss()) [Abbr `ee_call`,
       ASSUME ``(mid with gas_obs := []) = mid``] >>
     disch_then (fn th => PURE_ONCE_REWRITE_TAC [th] >>
       simp_tac (srw_ss()) [])) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    storage_well_formed_on cx ee_call (FST H)` by
    (qx_gen_tac `H` >> disch_tac >>
     `valid_horizon cx st0 H mid.storage_trace` by res_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid t /\
       storage_well_formed_on cx mid (FST H) /\ _`
       (qspec_then `H` (fn th => qpat_assum
         `valid_horizon cx st0 H mid.storage_trace`
         (strip_assume_tac o MATCH_MP th))) >>
     qpat_assum `eval_raw_call _ _ _ _ _ _ mid = _`
       (mp_then (Pat `eval_raw_call _ _ _ _ _ _ _ = _`) mp_tac
          vyperFiniteStoragePreservationTheory.eval_raw_call_preserves_storage_well_formed_on) >>
     disch_then irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     mp_tac (REWRITE_RULE [valid_horizon_def]
       (ASSUME ``valid_horizon cx st0 H ee_call.storage_trace``)) >>
     simp_tac (srw_ss()) []) >>
  `wb_frame cenv es mid sa s0 ready` by
    (qspecl_then [`cenv`,`es`,`mid`,`sa`,`s0`,`t`,`sc`,`ready`] mp_tac
       exprSimWordArgsTheory.wb_frame_readonly_tail >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
         >- (rpt strip_tac >>
             qpat_assum `!x. not_fresh_at sc x ==>
                lookup_var x ready = lookup_var x t /\ _`
                (qspec_then `z` mp_tac) >> simp[]) >>
         rpt strip_tac >>
         PURE_REWRITE_TAC [ASSUME ``ready.vs_allocas = allocated.vs_allocas``] >>
         qpat_assum `!aid e. FLOOKUP t.vs_allocas aid = SOME e ==> _`
           (drule_then ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `!aid a n. aid < sc.cs_next_id /\
    FLOOKUP ready.vs_allocas aid = SOME (a,n) ==>
    mem_bytes_at a n u_call.vs_memory = mem_bytes_at a n ready.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `alloca_inv ready`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [venomMemDefsTheory.alloca_inv_def]) >>
     disch_then (qspecl_then [`aid`,`sc.cs_next_id`,`a`,`n`,
       `w2n (w_alloc:256 word)`,`((flags.rcf_max_outsize+31) DIV 32)*32+32`]
       mp_tac o REWRITE_RULE [venomMemDefsTheory.allocas_non_overlapping_def]) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
     strip_tac >>
     qpat_assum `!a k. _ ==> mem_bytes_at a k u_call.vs_memory = _` irule >>
     `MIN flags.rcf_max_outsize (LENGTH outcome.co_returnData) <= flags.rcf_max_outsize`
       by simp_tac (srw_ss()) [] >> decide_tac) >>
  `!name a n. local_region cenv mid.scopes ready name a n ==>
    mem_bytes_at a n u_call.vs_memory = mem_bytes_at a n ready.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `!name a len. local_region cenv mid.scopes ready name a len ==> _`
       (drule_then (mp_tac o REWRITE_RULE [regions_disjoint_def])) >>
     strip_tac >>
     qpat_assum `!a k. _ ==> mem_bytes_at a k u_call.vs_memory = _` irule >>
     decide_tac) >>
  `wb_frame cenv es mid sa s0 u_call` by
    (mp_tac (Q.INST [`s` |-> `ready`,`t` |-> `u_call`,`sm` |-> `sc`,
       `scopes` |-> `mid.scopes`,`es'` |-> `mid`] wb_frame_allocating_tail) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         rpt strip_tac >>
         PURE_REWRITE_TAC [ASSUME ``u_call.vs_allocas = ready.vs_allocas``] >>
         first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  `wb_frame cenv es ee_call sa s0 s_call` by
    (qpat_assum `wb_frame cenv es mid sa s0 u_call`
       (fn th =>
        simp_tac bool_ss [Abbr `s_call`,wb_frame_def,locals_kept_def,
          popped_kept_def,lookup_var_def,venomStateTheory.venom_state_accfupds,
          ASSUME ``ee_call.scopes = mid.scopes``] >>
        ACCEPT_TAC (REWRITE_RULE [wb_frame_def,locals_kept_def,
          popped_kept_def,lookup_var_def] th))) >>
  `~is_terminator call_inst.inst_opcode` by
    (simp_tac bool_ss [Abbr `call_inst`,venomInstTheory.mk_inst_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `flags.rcf_is_static` >>
     simp[venomInstTheory.is_terminator_def]) >>
  `alloca_history func s_call` by
    (qspecl_then [`func`,`ready`,`bb_call`,`call_inst`,`u_call`] mp_tac
       allocaHistoryTheory.alloca_history_base_step >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> FIRST
          [PURE_REWRITE_TAC [ASSUME ``ready.vs_current_bb = s7.cs_current_bb``] >>
           first_assum ACCEPT_TAC,
           PURE_REWRITE_TAC [ASSUME ``ready.vs_inst_idx = LENGTH s7.cs_current_insts``] >>
           simp_tac bool_ss [Abbr `call_inst`] >>
           qpat_assum `get_instruction bb_call (LENGTH s7.cs_current_insts) = _`
             (fn th => POP_ASSUM_LIST (K ALL_TAC) >> mp_tac th) >>
           Cases_on `flags.rcf_is_static` >> simp[]]) >>
     PURE_REWRITE_TAC [ASSUME ``~is_terminator call_inst.inst_opcode``] >>
     simp_tac bool_ss [Abbr `s_call`]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G_call tn_call` by
    (irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
     qexistsl_tac [`G_ready`,`tn_ready`] >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC)
     >~ [`not_fresh_at sa (* sg *)`]
     >- (qx_gen_tac `x` >> disch_tac >>
         `not_fresh_at sc x` by res_tac >>
         qpat_assum `!x. not_fresh_at sc x ==>
           lookup_var x u_call = lookup_var x ready /\ _`
           (qspec_then `x` mp_tac) >>
         impl_tac >- first_assum ACCEPT_TAC >>
         strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
     simp_tac bool_ss [Abbr `tn_call`] >> first_assum ACCEPT_TAC) >>
  `out_alloc_cs.cs_next_var <= s7.cs_next_var` by
    (qspecl_then [`ADD`,`[ov;Lit 32w]`,`out_alloc_cs`] mp_tac ci_mono_emit_op >>
     qpat_assum `emit_op ADD [ov;Lit 32w] out_alloc_cs = _`
       (fn th => PURE_REWRITE_TAC [th]) >>
     simp_tac (srw_ss()) [ci_mono_def] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `not_fresh_at s7 out_var` by
    (irule not_fresh_at_mono >> qexists_tac `out_alloc_cs` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `~not_fresh_at out_alloc_cs out_name` by
    (simp_tac (srw_ss()) [Abbr `out_name`,not_fresh_at_def] >>
     qexists_tac `out_alloc_cs.cs_next_var` >> simp_tac (srw_ss()) []) >>
  `out_var <> out_name /\ out_var <> q_call` by
    (qpat_assum `not_fresh_at out_alloc_cs out_var` mp_tac >>
     qpat_assum `~not_fresh_at out_alloc_cs out_name` mp_tac >>
     qpat_assum `not_fresh_at s7 out_var` mp_tac >>
     qpat_assum `~not_fresh_at s7 q_call` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `lookup_var out_var ready = SOME w_alloc` by
    simp_tac (srw_ss()) [Abbr `ready`,Abbr `out_update`,lookup_var_set_inst_idx,
      lookup_var_update_var,ASSUME ``(out_var:string) <> out_name``,
      ASSUME ``lookup_var out_var allocated = SOME (w_alloc:256 word)``] >>
  `FLOOKUP G_ready out_var = FLOOKUP G_alloc out_var /\
   op_taint tn_ready (Var out_var) = op_taint tn_alloc (Var out_var)` by
    (qpat_assum `!p. p <> out_name ==> FLOOKUP G_ready p = _ /\ _`
       (qspec_then `out_var` irule) >> first_assum ACCEPT_TAC) >>
  `ptr_covers G_ready tn_ready out_var ready
     (((flags.rcf_max_outsize+31) DIV 32)*32+32)` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`G_alloc`,`allocated`,`tn_alloc`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     PURE_REWRITE_TAC [ASSUME ``lookup_var out_var ready = SOME (w_alloc:256 word)``,
       ASSUME ``lookup_var out_var allocated = SOME (w_alloc:256 word)``] >> REFL_TAC) >>
  `lookup_var out_var s_call = SOME w_alloc /\
   FLOOKUP G_call out_var = FLOOKUP G_ready out_var /\
   op_taint tn_call (Var out_var) = op_taint tn_ready (Var out_var)` by
    (`lookup_var out_var call_state = lookup_var out_var ready` by
       (PURE_REWRITE_TAC [lookup_var_def,
         ASSUME ``call_state.vs_vars = ready.vs_vars``] >> REFL_TAC) >>
     conj_tac
     >- simp_tac (srw_ss()) [Abbr `s_call`,Abbr `u_call`,lookup_var_set_inst_idx,
          lookup_var_update_var,
          ASSUME ``(out_var:string) <> q_call``,
          ASSUME ``lookup_var out_var call_state = lookup_var out_var ready``,
          ASSUME ``lookup_var out_var ready = SOME (w_alloc:256 word)``] >>
     qpat_assum `!x. x <> q_call ==> FLOOKUP _ x = FLOOKUP G_ready x /\ _`
       (qspec_then `out_var` mp_tac) >>
     PURE_REWRITE_TAC [ASSUME ``(out_var:string) <> q_call``] >>
     qpat_assum `Abbrev (G_call = _)`
       (fn th => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     qpat_assum `Abbrev (tn_call = _)`
       (fn th => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     simp_tac bool_ss []) >>
  `ptr_covers G_call tn_call out_var s_call
     (((flags.rcf_max_outsize+31) DIV 32)*32+32)` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`G_ready`,`ready`,`tn_ready`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     PURE_REWRITE_TAC [ASSUME ``lookup_var out_var ready = SOME (w_alloc:256 word)``,
       ASSUME ``lookup_var out_var s_call = SOME (w_alloc:256 word)``] >> REFL_TAC) >>
  `LENGTH outcome.co_returnData < dimword(:256)` by
    (qspecl_then [`mid`,`target`,`bs`,
       `if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount`,`rq`,`outcome`,`es1`]
       mp_tac (Q.GENL [`es`,`target`,`data`,`value_opt`,`rq`,`outcome`,`es1`]
         take_call_outcome_returnData_length) >>
     impl_tac >- (conj_tac
     >- (qpat_assum `expr_sim_inv cenv cx env mid`
           (fn th => POP_ASSUM_LIST (K ALL_TAC) >> mp_tac th) >>
         simp[exprSimHypsDefsTheory.expr_sim_inv_def]) >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `u_call.vs_returndata = outcome.co_returnData` by
    simp_tac (srw_ss()) [Abbr `u_call`,update_var_def,
      ASSUME ``call_state.vs_returndata = outcome.co_returnData``] >>
  `s_call.vs_returndata = outcome.co_returnData` by
    simp_tac (srw_ss()) [Abbr `s_call`,Abbr `u_call`,update_var_def,
      ASSUME ``call_state.vs_returndata = outcome.co_returnData``] >>
  `mem_bytes_at (w2n (w_alloc:256 word)+32)
      (LENGTH (TAKE flags.rcf_max_outsize s_call.vs_returndata)) s_call.vs_memory =
    TAKE flags.rcf_max_outsize s_call.vs_returndata` by
    (simp_tac (srw_ss()) [ASSUME ``u_call.vs_returndata = outcome.co_returnData``,
       Abbr `s_call`,ASSUME ``u_call.vs_memory = call_state.vs_memory``,
       ASSUME ``call_state.vs_memory =
         (write_memory_with_expansion (w2n (w_alloc:256 word)+32)
           (TAKE flags.rcf_max_outsize outcome.co_returnData) ready).vs_memory``,
       valueEncodingPropsTheory.write_memory_mem_bytes_at_same]) >>
  `!i. w2n (w_alloc:256 word)+32 <= i /\
      i < w2n w_alloc+32+LENGTH (TAKE flags.rcf_max_outsize s_call.vs_returndata) ==>
    i NOTIN tn_call.t_mem` by
    (qx_gen_tac `i` >> disch_tac >>
     `w2n (w_alloc:256 word)+32 <= i /\
      i < w2n w_alloc+32+MIN flags.rcf_max_outsize (LENGTH outcome.co_returnData)` by
       (qpat_assum `w2n (w_alloc:256 word)+32 <= i /\ _` mp_tac >>
        PURE_REWRITE_TAC [ASSUME ``s_call.vs_returndata = outcome.co_returnData``] >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac (srw_ss()) [listTheory.LENGTH_TAKE_EQ,arithmeticTheory.MIN_ALT]) >>
     `u_call.vs_returndata = outcome.co_returnData` by
       simp_tac (srw_ss()) [Abbr `u_call`,update_var_def,
         ASSUME ``call_state.vs_returndata = outcome.co_returnData``] >>
     qpat_assum `Abbrev (tn_call = _)`
       (fn th => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     qpat_assum `(step_taint call_inst ready u_call tn_ready).t_mem = _`
       (fn th => PURE_REWRITE_TAC [th] >> simp_tac (srw_ss()) [
         ASSUME ``w2n (n2w (w2n (w_alloc:256 word)+32):256 word) = w2n w_alloc+32``,
         ASSUME ``w2n (n2w flags.rcf_max_outsize:256 word) = flags.rcf_max_outsize``,
         ASSUME ``u_call.vs_returndata = outcome.co_returnData``,
         ASSUME ``w2n (w_alloc:256 word)+32 <= i /\
           i < w2n w_alloc+32+MIN flags.rcf_max_outsize (LENGTH outcome.co_returnData)``])) >>
  `~s_call.vs_halted /\
   s_call.vs_current_bb = call_cs.cs_current_bb /\
   s_call.vs_inst_idx = LENGTH call_cs.cs_current_insts /\
   allocas_from lo s_call /\ lo <= s_call.vs_alloca_next /\
   s0.vs_alloca_next <= s_call.vs_alloca_next` by
    (simp_tac (srw_ss()) [Abbr `s_call`] >>
     PURE_REWRITE_TAC [ASSUME ``u_call.vs_halted = ready.vs_halted``,
       ASSUME ``u_call.vs_current_bb = ready.vs_current_bb``,
       ASSUME ``call_cs.cs_current_bb = s7.cs_current_bb``] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G,tn) [] (OK s_call,G_call,tn_call)` by
    (qx_gen_tac `H` >> disch_tac >>
     `valid_horizon cx st0 H mid.storage_trace` by res_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       gas_origin_ptr_edge _ (ready,G_ready,tn_ready) [] (OK s_call,G_call,tn_call)`
       (qspec_then `H` (fn th => assume_tac (MATCH_MP th
          (ASSUME ``valid_horizon cx st0 H mid.storage_trace``)))) >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`G_ready`,`ready`,`tn_ready`] >> conj_tac
     >- (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
         qexistsl_tac [`G_alloc`,`allocated`,`tn_alloc`] >> conj_tac
         >- (qpat_assum `!D. gas_origin_ptr_path (D,lo,_,_,_,_) (t,G,tn) [] _`
               (qspec_then `DF H` ACCEPT_TAC)) >>
         qpat_assum `!D lo explicit. allocas_from lo allocated ==> _`
           (qspecl_then [`DF H`,`lo`,`gas_explicit_sites ctx shadow_ctx`] irule) >>
         first_assum ACCEPT_TAC) >>
     qpat_assum `gas_origin_ptr_edge _ (ready,G_ready,tn_ready) [] _`
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
          (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules))) >>
     disch_then (qspecl_then [`[]`,`OK s_call`,`G_call`,`tn_call`] mp_tac) >>
     PURE_REWRITE_TAC [listTheory.APPEND] >>
     disch_then irule >>
     irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `compile_alloc_buffer _ sc = (out_buffer,out_alloc_cs)`
    (mp_then Any mp_tac abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape) >>
  strip_tac >>
  qpat_assum `emit_op ALLOCA _ sc = (out_buffer.buf_operand,out_alloc_cs)`
    (mp_then Any mp_tac emitHelperPropsTheory.emitted_insts_emit_op) >> strip_tac >>
  `out_var = STRING #"%" (toString sc.cs_next_var)` by
    (qpat_assum `out_buffer.buf_operand = Var out_var` mp_tac >>
     qpat_assum `out_buffer.buf_operand = Var (STRING #"%" (toString sc.cs_next_var))` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) []) >>
  `not_local_ptr cenv ee_call.scopes out_var` by
    (PURE_REWRITE_TAC [ASSUME ``out_var = STRING #"%" (toString sc.cs_next_var)``] >>
     qspecl_then [`cenv`,`sc`,`ee_call.scopes`,`sc.cs_next_var`] mp_tac
       local_ptrs_reserved_fresh >>
     impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> decide_tac) >>
     disch_then ACCEPT_TAC) >>
  `s7.cs_next_var <= call_cs.cs_next_var /\
   s7.cs_next_id <= call_cs.cs_next_id` by
    (qpat_assum `ci_mono s7 call_cs`
       (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [] >>
     rpt strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  `out_alloc_cs.cs_next_id <= s7.cs_next_id` by
    (qspecl_then [`ADD`,`[ov;Lit 32w]`,`out_alloc_cs`] mp_tac ci_mono_emit_op >>
     qpat_assum `emit_op ADD [ov;Lit 32w] out_alloc_cs = _`
       (fn th => PURE_REWRITE_TAC [th]) >>
     simp_tac (srw_ss()) [ci_mono_def] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `sc.cs_next_id < call_cs.cs_next_id /\
   sa.cs_next_var <= call_cs.cs_next_var` by decide_tac >>
  `local_ptrs_reserved cenv call_cs` by
    (qspecl_then [`cenv`,`sc`,`call_cs`] mp_tac local_ptrs_reserved_next_var >>
     impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> decide_tac) >>
     disch_then ACCEPT_TAC) >>
  `not_fresh_at call_cs out_var` by
    (irule not_fresh_at_mono >> qexists_tac `s7` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `safe_operand call_cs ov /\ safe_operand call_cs (Var q_call)` by
    (PURE_REWRITE_TAC [ASSUME ``ov = Var out_var``] >>
     simp_tac (srw_ss()) [exprSafeOperandTheory.safe_operand_def] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `FLOOKUP s_call.vs_allocas sc.cs_next_id =
    SOME (w2n (w_alloc:256 word),32+((flags.rcf_max_outsize+31) DIV 32)*32)` by
    (simp_tac (srw_ss()) [Abbr `s_call`,
       ASSUME ``u_call.vs_allocas = ready.vs_allocas``,
       ASSUME ``FLOOKUP ready.vs_allocas sc.cs_next_id =
         SOME (w2n (w_alloc:256 word),((flags.rcf_max_outsize+31) DIV 32)*32+32)``,
       arithmeticTheory.ADD_COMM]) >>
  (Cases_on `flags.rcf_revert_on_failure`
   >- suspend "positiveRevert" >> suspend "positiveTuple")
QED

Resume raw_call_positive_full_finish[positiveTuple]:
  `ann = TupleT [BaseT BoolT;BaseT (BytesT (Dynamic flags.rcf_max_outsize))]` by
    (qpat_assum `ann = raw_call_return_type flags` mp_tac >>
     simp_tac (srw_ss()) [vyperTypeSystemTheory.raw_call_return_type_def,
       ASSUME ``~flags.rcf_revert_on_failure``,
       ASSUME ``flags.rcf_max_outsize <> 0``]) >>
  qpat_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ s7 = (result,sb)`
    (fn th => mp_tac (MATCH_MP rawCallShapePtrTheory.raw_call_nonrevert_code_groups
       (CONJ (SIMP_RULE (srw_ss()) [ASSUME ``~flags.rcf_revert_on_failure``] th)
         (ASSUME ``fn_has_code s7 sb func``)))) >>
  disch_then (qx_choosel_then [`tuple_ok`,`tuple_call_cs`] strip_assume_tac) >>
  `tuple_ok = Var q_call /\ tuple_call_cs = call_cs` by
    (qpat_assum `(case _ of DelegateCall => _ | StaticCall => _ | RegularCall => _) s7 = _`
       mp_tac >>
     qpat_assum `(if (if flags.rcf_is_static then StaticCall else RegularCall) = StaticCall
       then _ else _) s7 = (Var q_call,call_cs)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `flags.rcf_is_static` >> simp[]) >>
  qpat_x_assum `tuple_ok = Var q_call` SUBST_ALL_TAC >>
  qpat_x_assum `tuple_call_cs = call_cs` SUBST_ALL_TAC >>
  qpat_assum `(if flags.rcf_max_outsize > 0 then _ else _) call_cs = (result,sb)`
    (mp_tac o SIMP_RULE (srw_ss()) [arithmeticTheory.GREATER_DEF,
       ASSUME ``0 < flags.rcf_max_outsize``]) >>
  disch_then (mp_then Any mp_tac rawCallShapePtrTheory.raw_call_tuple_suffix_steps) >>
  disch_then (qx_choosel_then
    [`len_rds`,`len_rds_cs`,`len_cmp`,`len_cmp_cs`,`len_cap`,`len_cap_cs`,
     `len_cs`,`tuple_buf`,`tuple_alloc_cs`,`tuple_store_cs`,`tuple_dst`,`tuple_add_cs`]
    strip_assume_tac) >>
  `(do rds <- emit_op RETURNDATASIZE [];
       cmp <- emit_op LT [rds;Lit (n2w flags.rcf_max_outsize)];
       cap <- compile_select cmp rds (Lit (n2w flags.rcf_max_outsize));
       emit_void MSTORE [Var out_var;cap] od) call_cs = ((),len_cs)` by
    (simp_tac (srw_ss()) [GSYM (ASSUME ``ov = Var out_var``),
       compileEnvTheory.comp_bind_def,compileEnvTheory.comp_ignore_bind_def,
       boolTheory.LET_THM,pairTheory.pair_case_thm,pairTheory.UNCURRY_DEF,
       ASSUME ``emit_op RETURNDATASIZE [] call_cs = (len_rds,len_rds_cs)``,
       ASSUME ``emit_op LT [len_rds;Lit (n2w flags.rcf_max_outsize)]
         len_rds_cs = (len_cmp,len_cmp_cs)``,
       ASSUME ``compile_select len_cmp len_rds (Lit (n2w flags.rcf_max_outsize))
         len_cmp_cs = (len_cap,len_cap_cs)``,
       ASSUME ``emit_void MSTORE [ov;len_cap] len_cap_cs = ((),len_cs)``] >> REFL_TAC) >>
  `ci_mono call_cs len_rds_cs /\ ci_mono len_rds_cs len_cmp_cs /\
   ci_mono len_cmp_cs len_cap_cs /\ ci_mono len_cap_cs len_cs /\
   ci_mono len_cs tuple_alloc_cs /\ ci_mono tuple_alloc_cs tuple_store_cs /\
   ci_mono tuple_store_cs tuple_add_cs /\ ci_mono tuple_add_cs sb` by
    (qpat_assum `emit_op RETURNDATASIZE [] call_cs = _` mp_tac >>
     qpat_assum `emit_op LT _ len_rds_cs = _` mp_tac >>
     qpat_assum `compile_select _ _ _ len_cmp_cs = _` mp_tac >>
     qpat_assum `emit_void MSTORE _ len_cap_cs = _` mp_tac >>
     qpat_assum `compile_alloc_buffer _ len_cs = _` mp_tac >>
     qpat_assum `emit_void MSTORE _ tuple_alloc_cs = _` mp_tac >>
     qpat_assum `emit_op ADD _ tuple_store_cs = _` mp_tac >>
     qpat_assum `emit_void MCOPY _ tuple_add_cs = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> rpt conj_tac >>
     metis_tac[ci_mono_emit_op,ci_mono_compile_select,ci_mono_emit_void,
       ci_mono_compile_alloc_buffer,pairTheory.SND]) >>
  `cs_extends call_cs len_cs /\ cs_extends len_cs sb` by
    (qpat_assum `ci_mono call_cs len_rds_cs` mp_tac >>
     qpat_assum `ci_mono len_rds_cs len_cmp_cs` mp_tac >>
     qpat_assum `ci_mono len_cmp_cs len_cap_cs` mp_tac >>
     qpat_assum `ci_mono len_cap_cs len_cs` mp_tac >>
     qpat_assum `ci_mono len_cs tuple_alloc_cs` mp_tac >>
     qpat_assum `ci_mono tuple_alloc_cs tuple_store_cs` mp_tac >>
     qpat_assum `ci_mono tuple_store_cs tuple_add_cs` mp_tac >>
     qpat_assum `ci_mono tuple_add_cs sb` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [ci_mono_def] >> rpt strip_tac >>
     metis_tac[cs_extends_trans]) >>
  `fn_has_code call_cs len_cs func` by
    (qpat_assum `fn_has_code call_cs sb func` mp_tac >>
     qpat_assum `cs_extends call_cs len_cs` mp_tac >>
     qpat_assum `cs_extends len_cs sb` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[fn_has_code_split]) >>
  `LENGTH s_call.vs_returndata < dimword(:256)` by
    (PURE_REWRITE_TAC [ASSUME ``s_call.vs_returndata = outcome.co_returnData``] >>
     first_assum ACCEPT_TAC) >>
  `s_call.vs_alloca_next = allocated.vs_alloca_next` by
    simp_tac (srw_ss()) [Abbr `s_call`,
      ASSUME ``u_call.vs_alloca_next = ready.vs_alloca_next``,
      ASSUME ``ready.vs_alloca_next = allocated.vs_alloca_next``] >>
  `w2n (w_alloc:256 word)+32 <= s_call.vs_alloca_next` by decide_tac >>
  qspecl_then [`call_cs`,`len_cs`,`flags.rcf_max_outsize`,`out_var`,
    `((flags.rcf_max_outsize+31) DIV 32)*32+32`,`w_alloc`,`s_call`,
    `G_call`,`tn_call`,`lo`,`gas_explicit_sites ctx shadow_ctx`,`ctx`,`func`,`PG`]
    mp_tac bodyFullRawCallLengthTheory.raw_call_length_store_origin_ptr >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  disch_then (qx_choosel_then [`len_raw`,`s_len`,`G_len`,`tn_len`]
    strip_assume_tac) >>
  `MAP FDOM es.scopes = MAP FDOM ee_call.scopes` by
    (PURE_REWRITE_TAC [ASSUME ``ee_call.scopes = mid.scopes``] >>
     first_assum ACCEPT_TAC) >>
  qabbrev_tac `out_allocation_inst = mk_inst sc.cs_next_id ALLOCA
    [Lit (n2w (((flags.rcf_max_outsize+31) DIV 32)*32+32))] [out_var]` >>
  `MEM out_allocation_inst (fn_insts func)` by
    (simp_tac (srw_ss()) [Abbr `out_allocation_inst`,
       ASSUME ``out_var = STRING #"%" (toString sc.cs_next_var)``] >>
     first_assum ACCEPT_TAC) >>
  `out_allocation_inst.inst_opcode = ALLOCA /\
   out_allocation_inst.inst_outputs = [out_var] /\
   out_allocation_inst.inst_id = sc.cs_next_id` by
    simp_tac (srw_ss()) [Abbr `out_allocation_inst`,venomInstTheory.mk_inst_def] >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee_call s_len /\
    wb_frame cenv es ee_call sa s0 s_len /\
    s_len.vs_fmp = s_call.vs_fmp /\ s_len.vs_allocas = s_call.vs_allocas` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee_call s_call`
       (qspec_then `H` (fn th => assume_tac (MATCH_MP th
         (ASSUME ``valid_horizon cx st0 H ee_call.storage_trace``)))) >>
     `stmt_state_rel H ctx func cenv cx ee_call
       (s_call with vs_fmp := s_call.vs_fmp)` by
       (simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx ee_call s_call`
       (fn rel => let
          val horizon = hd (snd (strip_comb (concl rel)));
          val th = exprSimRawCallCalldataTheory.raw_call_output_prefix_ready;
          val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
            (free_vars (concl th)));
          val ith = INST_TYPE (match_type (type_of hv) (type_of horizon)) th;
          val ihv = valOf (List.find (fn v => fst (dest_var v) = "H")
            (free_vars (concl ith)));
        in qspecl_then [`ctx`,`func`,`cenv`,`cx`,`ee_call`,`es`,`sa`,`s0`,
          `call_cs`,`len_rds`,`len_rds_cs`,`len_cmp`,`len_cmp_cs`,`len_cap`,
          `len_cap_cs`,`len_cs`,`ov`,`s_call`,`w_alloc`,`s_call.vs_fmp`,
          `flags.rcf_max_outsize`,`out_allocation_inst`,`out_var`,
          `w2n (w_alloc:256 word)`,`32+((flags.rcf_max_outsize+31) DIV 32)*32`]
          mp_tac (SPEC horizon (GEN ihv ith)) end) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> FIRST
          [PURE_REWRITE_TAC [ASSUME ``ov = Var out_var``,eval_operand_def] >>
             first_assum ACCEPT_TAC,
           PURE_REWRITE_TAC [ASSUME ``out_allocation_inst.inst_id = sc.cs_next_id``] >>
             first_assum ACCEPT_TAC,
           ALL_TAC] >> decide_tac) >>
     disch_then (qx_choose_then `memory_len` strip_assume_tac) >>
     `memory_len = len_raw` by
       (qpat_assum `run_inst_seq (emitted_insts call_cs len_cs) s_call = OK memory_len` mp_tac >>
        qpat_assum `run_inst_seq (emitted_insts call_cs len_cs) s_call = OK len_raw` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) []) >>
     qpat_x_assum `memory_len = len_raw` SUBST_ALL_TAC >>
     qpat_assum `s_len = len_raw with vs_inst_idx := _` (fn th => PURE_REWRITE_TAC [th]) >>
     rpt conj_tac
     >- (PURE_REWRITE_TAC [stmt_state_rel_inst_idx] >>
         qpat_assum `stmt_state_rel H ctx func cenv cx ee_call
           (len_raw with vs_fmp := s_call.vs_fmp)` mp_tac >>
         PURE_REWRITE_TAC [GSYM (ASSUME ``len_raw.vs_fmp = s_call.vs_fmp``)] >>
         simp_tac (srw_ss()) [])
     >- (simp_tac bool_ss [wb_frame_def,locals_kept_def,popped_kept_def,
           lookup_var_def,venomStateTheory.venom_state_accfupds] >>
         qpat_assum `wb_frame cenv es ee_call sa s0 len_raw`
           (ACCEPT_TAC o REWRITE_RULE [wb_frame_def,locals_kept_def,
              popped_kept_def,lookup_var_def]))
     >> simp_tac bool_ss [venomStateTheory.venom_state_accfupds] >>
        first_assum ACCEPT_TAC) >>
  suspend "tupleAllocation"
QED

Resume raw_call_positive_full_finish[positiveRevert]:
  `ann = BaseT (BytesT (Dynamic flags.rcf_max_outsize))` by
    (qpat_assum `ann = raw_call_return_type flags` mp_tac >>
     simp_tac (srw_ss()) [vyperTypeSystemTheory.raw_call_return_type_def,
       ASSUME ``flags.rcf_revert_on_failure``,ASSUME ``flags.rcf_max_outsize <> 0``]) >>
  qpat_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ s7 = (result,sb)`
    (fn th => mp_tac (MATCH_MP rawCallShapePtrTheory.raw_call_reverting_code_groups
      (CONJ (SIMP_RULE (srw_ss()) [ASSUME ``flags.rcf_revert_on_failure``] th)
        (ASSUME ``fn_has_code s7 sb func``)))) >>
  disch_then (qx_choosel_then [`branch_ok`,`branch_call_cs`,`bad`,`label_cs`,
    `good`,`jump_cs`,`jumped_cs`,`fail_block`,`fail_cs`,`failed_cs`,
    `pass_block`,`pass_cs`] strip_assume_tac) >>
  `branch_ok = Var q_call /\ branch_call_cs = call_cs` by
    (qpat_assum `(case _ of DelegateCall => _ | StaticCall => _ | RegularCall => _) s7 = _`
       mp_tac >>
     qpat_assum `(if (if flags.rcf_is_static then StaticCall else RegularCall) = StaticCall
       then _ else _) s7 = (Var q_call,call_cs)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `flags.rcf_is_static` >> simp[]) >>
  qpat_x_assum `branch_ok = Var q_call` SUBST_ALL_TAC >>
  qpat_x_assum `branch_call_cs = call_cs` SUBST_ALL_TAC >>
  `eval_operand (Var q_call) s_call = SOME (if outcome.co_success then 1w else 0w)` by
    simp_tac (srw_ss()) [Abbr `s_call`,Abbr `u_call`,eval_operand_def,
      lookup_var_update_var,lookup_var_set_inst_idx] >>
  `op_taint tn_call (Var q_call) = {}` by
    (qpat_assum `(step_taint call_inst ready u_call tn_ready).t_var = _`
       (fn th => simp_tac (srw_ss()) [Abbr `tn_call`,ptrDisciplineTheory.op_taint_def,
          th,finite_mapTheory.FLOOKUP_UPDATE])) >>
  `!D. gas_origin_ptr_path
    (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (s_call,G_call,tn_call) []
    (OK (jump_to (if outcome.co_success then good else bad) s_call),G_call,tn_call)` by
    (gen_tac >>
     mp_tac (Q.INST [`sa` |-> `jump_cs`,`sb` |-> `jumped_cs`,
       `op` |-> `Var q_call`,`lt` |-> `good`,`lf` |-> `bad`,
       `b` |-> `outcome.co_success`,`s` |-> `s_call`,`G` |-> `G_call`,
       `tn` |-> `tn_call`,`D` |-> `D`,`lo` |-> `lo`,`ctx` |-> `ctx`,
       `func` |-> `func`,`PG` |-> `PG`,
       `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
       fragGasEmitCtrlTheory.emit_jnz_origin_ptr) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> FIRST
          [PURE_REWRITE_TAC [ASSUME ``jump_cs.cs_current_bb = call_cs.cs_current_bb``] >>
             first_assum ACCEPT_TAC,
           PURE_REWRITE_TAC [ASSUME ``jump_cs.cs_current_insts = call_cs.cs_current_insts``] >>
             first_assum ACCEPT_TAC]) >> disch_then ACCEPT_TAC) >>
  qabbrev_tac `s_jump = jump_to (if outcome.co_success then good else bad) s_call` >>
  `alloca_history func s_jump` by
    (qspecl_then [`func`,`s_call`,`s_jump`] mp_tac allocaHistoryTheory.alloca_history_jump >>
     impl_tac >- simp[Abbr `s_jump`,venomStateTheory.jump_to_def] >> simp[]) >>
  `allocas_from lo s_jump` by
    (simp_tac (srw_ss()) [Abbr `s_jump`,venomStateTheory.jump_to_def,
       ptrDisciplineTheory.allocas_from_def] >>
     qpat_assum `allocas_from lo s_call`
       (ACCEPT_TAC o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def])) >>
  `lo <= s_jump.vs_alloca_next /\ ~s_jump.vs_halted` by
    (simp_tac (srw_ss()) [Abbr `s_jump`,venomStateTheory.jump_to_def] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee_call s_jump` by
    (simp_tac (srw_ss()) [Abbr `s_jump`,stmt_state_rel_jump_to] >>
     first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G,tn) [] (OK s_jump,G_call,tn_call)` by
    (qx_gen_tac `H` >> disch_tac >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`G_call`,`s_call`,`tn_call`] >> conj_tac
     >- (qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
           gas_origin_ptr_path _ (t,G,tn) [] (OK s_call,G_call,tn_call)`
           (qspec_then `H` irule) >> first_assum ACCEPT_TAC) >>
     simp_tac bool_ss [Abbr `s_jump`] >>
     qpat_assum `!D. gas_origin_ptr_path _ (s_call,G_call,tn_call) [] _`
       (qspec_then `DF H` ACCEPT_TAC)) >>
  qpat_assum `new_block bad jumped_cs = (fail_block,fail_cs)`
    (strip_assume_tac o MATCH_MP emitHelperPropsTheory.new_block_props) >>
  qpat_assum `new_block good failed_cs = (pass_block,pass_cs)`
    (strip_assume_tac o MATCH_MP emitHelperPropsTheory.new_block_props) >>
  (Cases_on `outcome.co_success`
   >- suspend "positiveBytes" >> suspend "positiveFailure")
QED

Resume raw_call_positive_full_finish[positiveFailure]:
  `valid_horizon cx st0 (storage_trace_horizon ee_call.storage_trace)
    ee_call.storage_trace` by
    (simp_tac (srw_ss()) [Abbr `ee_call`] >>
     qpat_assum `storage_trace_domain cx st0
       (SND (adopt_call_outcome rq outcome es1)).storage_trace`
       (mp_tac o REWRITE_RULE [storage_trace_domain_def]) >> simp_tac bool_ss []) >>
  `stmt_state_rel (storage_trace_horizon ee_call.storage_trace)
    ctx func cenv cx ee_call s_jump` by
    (qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee_call s_jump`
       (qspec_then `storage_trace_horizon ee_call.storage_trace` irule) >>
     first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved cenv fail_cs` by
    (qspecl_then [`cenv`,`call_cs`,`fail_cs`] mp_tac local_ptrs_reserved_next_var >>
     impl_tac
     >- (conj_tac >- first_assum ACCEPT_TAC >>
         qpat_assum `ci_mono call_cs jump_cs` mp_tac >>
         qpat_assum `ci_mono jump_cs jumped_cs` mp_tac >>
         qpat_assum `ci_mono jumped_cs fail_cs` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [ci_mono_def] >>
         rpt strip_tac >> decide_tac) >> disch_then ACCEPT_TAC) >>
  `s_jump.vs_current_bb = fail_cs.cs_current_bb /\
   s_jump.vs_inst_idx = LENGTH fail_cs.cs_current_insts /\
   LENGTH s_jump.vs_returndata < dimword(:256)` by
    (simp_tac (srw_ss()) [Abbr `s_jump`,venomStateTheory.jump_to_def,
       ASSUME ``~outcome.co_success``,ASSUME ``fail_cs.cs_current_bb = bad``,
       ASSUME ``fail_cs.cs_current_insts = []``,
       ASSUME ``s_call.vs_returndata = outcome.co_returnData``] >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `stmt_state_rel (storage_trace_horizon ee_call.storage_trace)
    ctx func cenv cx ee_call s_jump` (fn rel =>
    mp_tac (Q.INST [`sa` |-> `fail_cs`,`sb` |-> `failed_cs`,
      `G` |-> `G_call`,`tn` |-> `tn_call`,`lo` |-> `lo`,
      `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,`PG` |-> `PG`]
      (PART_MATCH (find_term (fn tm =>
         same_const (fst (strip_comb tm)) ``stmt_state_rel``))
       bodyFullRawCallForwardTheory.raw_call_failure_tail_origin_ptr (concl rel)))) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`reverted`,`G_revert`,`tn_revert`] strip_assume_tac) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G,tn) [] (Abort Revert_abort reverted,G_revert,tn_revert)` by
    (qx_gen_tac `H` >> disch_tac >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`G_call`,`s_jump`,`tn_call`] >> conj_tac
     >- (qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
           gas_origin_ptr_path _ (t,G,tn) [] (OK s_jump,G_call,tn_call)`
           (qspec_then `H` irule) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!D. gas_origin_ptr_path _ (s_jump,G_call,tn_call) [] _`
       (qspec_then `DF H` ACCEPT_TAC)) >>
  `reverted.vs_returndata = outcome.co_returnData` by
    (PURE_REWRITE_TAC [ASSUME ``reverted.vs_returndata = s_jump.vs_returndata``] >>
     simp_tac (srw_ss()) [Abbr `s_jump`,venomStateTheory.jump_to_def,
       ASSUME ``s_call.vs_returndata = outcome.co_returnData``]) >>
  irule gas_outcome_full_exit >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G_revert`,`ee_call`,`Abort Revert_abort reverted`,
    `INR (Error (RevertData outcome.co_returnData))`,`tn_revert`] >>
  conj_tac
  >- (qpat_assum `!tail. eval_raw_call _ _ _ _ _ _ _ = _` mp_tac >>
      simp_tac (srw_ss()) [Abbr `ee_call`,ASSUME ``flags.rcf_revert_on_failure``,
        ASSUME ``~outcome.co_success``]) >>
  simp_tac (srw_ss()) [fragExecTheory.exit_result_def,exprSimDefsTheory.expr_exit_def,
    ASSUME ``reverted.vs_returndata = outcome.co_returnData``] >>
  first_assum ACCEPT_TAC
QED

Resume raw_call_positive_full_finish[tupleAllocation]:
  `storage_trace_domain cx st0 ee_call.storage_trace` by
    (simp_tac (srw_ss()) [Abbr `ee_call`] >> first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 (storage_trace_horizon ee_call.storage_trace)
    ee_call.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 ee_call.storage_trace`
       (mp_tac o REWRITE_RULE [storage_trace_domain_def]) >> simp_tac bool_ss []) >>
  qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee_call s_len /\ _`
    (qspec_then `storage_trace_horizon ee_call.storage_trace`
      (fn th => strip_assume_tac (MATCH_MP th
        (ASSUME ``valid_horizon cx st0 (storage_trace_horizon ee_call.storage_trace)
          ee_call.storage_trace``)))) >>
  `stmt_state_rel (storage_trace_horizon ee_call.storage_trace)
    ctx func cenv cx ee_call s_call` by
    (qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee_call s_call`
       (qspec_then `storage_trace_horizon ee_call.storage_trace` irule) >>
     first_assum ACCEPT_TAC) >>
  `alloca_inv s_call` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon ee_call.storage_trace)
       ctx func cenv cx ee_call s_call` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[stmt_state_rel_def]) >>
  `len_cs.cs_current_bb = call_cs.cs_current_bb /\
   len_cs.cs_current_insts = call_cs.cs_current_insts ++ emitted_insts call_cs len_cs` by
    (qpat_assum `(do rds <- emit_op RETURNDATASIZE []; _ od) call_cs = ((),len_cs)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[compileEnvTheory.comp_bind_def,compileEnvTheory.comp_ignore_bind_def,
       builtinSimpleTheory.compile_select_def,emitHelperTheory.emit_op_def,
       emitHelperTheory.emit_void_def,compileEnvTheory.fresh_id_def,
       compileEnvTheory.fresh_var_def,compileEnvTheory.emit_def,
       compileEnvTheory.comp_return_def,boolTheory.LET_THM,
       pairTheory.pair_case_thm,pairTheory.UNCURRY_DEF] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def,rich_listTheory.DROP_LENGTH_APPEND]) >>
  `alloca_history func s_len` by
    (qpat_assum `s_len = len_raw with vs_inst_idx := _` (fn th => PURE_REWRITE_TAC [th]) >>
     qspecl_then [`emitted_insts call_cs len_cs`,`call_cs`,`len_cs`,`s_call`,`len_raw`]
       mp_tac bodyFullUnwrapRunTheory.emitted_alloca_history >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       qpat_assum `EVERY _ (emitted_insts call_cs len_cs)`
         (fn th => POP_ASSUM_LIST (K ALL_TAC) >> mp_tac th) >>
       simp[listTheory.EVERY_MEM]) >> disch_then ACCEPT_TAC) >>
  qpat_assum `s_len = (mstore _ _ s_call) with <|vs_vars := _;vs_inst_idx := _|>`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [boolTheory.LET_THM,venomStateTheory.mstore_def,pairTheory.PAIR_EQ] o
      Q.AP_TERM `\z. (z.vs_halted,z.vs_alloca_next,z.vs_inst_idx)`) >>
  `~s_len.vs_halted /\ allocas_from lo s_len /\
   lo <= s_len.vs_alloca_next /\
   s_len.vs_inst_idx = LENGTH len_cs.cs_current_insts` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`allocas_from lo s_call`,`~s_call.vs_halted`,
        `lo <= s_call.vs_alloca_next`,
        `s_len.vs_halted = s_call.vs_halted`,
        `s_len.vs_alloca_next = s_call.vs_alloca_next`,
        `s_len.vs_allocas = s_call.vs_allocas`,
        `s_len.vs_inst_idx = LENGTH len_cs.cs_current_insts`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [ptrDisciplineTheory.allocas_from_def]) >>
  `call_cs.cs_next_var <= len_cs.cs_next_var /\
   call_cs.cs_next_id <= len_cs.cs_next_id` by
    (qpat_assum `ci_mono call_cs len_rds_cs` mp_tac >>
     qpat_assum `ci_mono len_rds_cs len_cmp_cs` mp_tac >>
     qpat_assum `ci_mono len_cmp_cs len_cap_cs` mp_tac >>
     qpat_assum `ci_mono len_cap_cs len_cs` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [ci_mono_def] >>
     rpt strip_tac >> decide_tac) >>
  `local_ptrs_reserved cenv len_cs` by
    (qspecl_then [`cenv`,`call_cs`,`len_cs`] mp_tac local_ptrs_reserved_next_var >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  `fn_has_code len_cs tuple_alloc_cs func` by
    (qpat_assum `fn_has_code call_cs sb func` mp_tac >>
     qpat_assum `cs_extends call_cs len_cs` mp_tac >>
     qpat_assum `ci_mono len_cs tuple_alloc_cs` mp_tac >>
     qpat_assum `ci_mono tuple_alloc_cs tuple_store_cs` mp_tac >>
     qpat_assum `ci_mono tuple_store_cs tuple_add_cs` mp_tac >>
     qpat_assum `ci_mono tuple_add_cs sb` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [ci_mono_def] >>
     rpt strip_tac >> metis_tac[fn_has_code_mid,cs_extends_trans,cs_extends_refl]) >>
  `64+((flags.rcf_max_outsize+31) DIV 32)*32 < dimword(:256)` by
    (qpat_assum `expr_body_pre cenv cx env (Call ann _ _ _) es` mp_tac >>
     PURE_REWRITE_TAC [ASSUME ``ann = TupleT [BaseT BoolT;
       BaseT (BytesT (Dynamic flags.rcf_max_outsize))]``] >>
     disch_then (ACCEPT_TAC o MATCH_MP rawCallResultLayoutPtrTheory.raw_call_tuple_pre_capacity)) >>
  mp_tac (Q.INST [`n` |-> `64+((flags.rcf_max_outsize+31) DIV 32)*32`,
    `sa` |-> `len_cs`,`sb` |-> `tuple_alloc_cs`,`buf` |-> `tuple_buf`,
    `H` |-> `storage_trace_horizon ee_call.storage_trace`,
    `es` |-> `ee_call`,`s` |-> `s_len`,`PG` |-> `PG`,
    `G` |-> `G_len`,`tn` |-> `tn_len`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (INST_TYPE [alpha |-> ``:256``,beta |-> ``:256``,gamma |-> ``:256``]
      alloc_buffer_origin_ptr_path)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`tuple_var`,`tuple_word`,`s_tuple`,`G_tuple`,`tn_tuple`]
    strip_assume_tac) >>
  suspend "tupleStore"
QED

Resume raw_call_positive_full_finish[tupleStore]:
  `lookup_var q_call s_call = SOME (bool_to_word outcome.co_success)` by
    (simp_tac (srw_ss()) [Abbr `s_call`,Abbr `u_call`,
       lookup_var_update_var,lookup_var_set_inst_idx] >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `outcome.co_success` >>
     simp[venomExecSemanticsTheory.bool_to_word_def]) >>
  `op_taint tn_call (Var q_call) = {}` by
    (qpat_assum `(step_taint call_inst ready u_call tn_ready).t_var = _`
       (fn th => simp_tac (srw_ss()) [Abbr `tn_call`,ptrDisciplineTheory.op_taint_def,
          th,finite_mapTheory.FLOOKUP_UPDATE])) >>
  qpat_assum `s_tuple with <|vs_vars := s_len.vs_vars;vs_allocas := _;
    vs_alloca_next := _;vs_inst_idx := _|> = s_len`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [pairTheory.PAIR_EQ] o
      Q.AP_TERM `\z. (z.vs_memory,z.vs_halted,z.vs_returndata)`) >>
  `not_fresh_at len_cs out_var /\ not_fresh_at len_cs q_call` by
    (rpt conj_tac >> irule not_fresh_at_mono >> qexists_tac `call_cs` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `not_fresh_at tuple_alloc_cs out_var /\ not_fresh_at tuple_alloc_cs q_call` by
    (rpt conj_tac >> (irule not_fresh_at_mono >> qexists_tac `len_cs` >>
     conj_tac
     >- (qpat_assum `ci_mono len_cs tuple_alloc_cs`
           (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [ci_mono_def])) >>
     first_assum ACCEPT_TAC)) >>
  `lookup_var out_var s_tuple = SOME w_alloc /\
   eval_operand (Var q_call) s_tuple = SOME (bool_to_word outcome.co_success) /\
   op_taint tn_tuple (Var q_call) = {}` by
    (qpat_assum `!x. not_fresh_at len_cs x ==> lookup_var x s_tuple = _ /\ _`
       (qspec_then `out_var` assume_tac) >>
     qpat_assum `!x. not_fresh_at len_cs x ==> lookup_var x s_tuple = _ /\ _`
       (qspec_then `q_call` assume_tac) >>
     qpat_assum `!x. not_fresh_at call_cs x ==> lookup_var x s_len = _ /\ _`
       (qspec_then `out_var` assume_tac) >>
     qpat_assum `!x. not_fresh_at call_cs x ==> lookup_var x s_len = _ /\ _`
       (qspec_then `q_call` assume_tac) >>
     map_every (fn q => qpat_assum q mp_tac)
       [`not_fresh_at len_cs out_var`,`not_fresh_at len_cs q_call`,
        `not_fresh_at call_cs out_var`,`not_fresh_at call_cs q_call`,
        `lookup_var out_var s_call = SOME w_alloc`,
        `lookup_var q_call s_call = SOME (bool_to_word outcome.co_success)`,
        `op_taint tn_call (Var q_call) = {}`,
        `not_fresh_at len_cs out_var ==> lookup_var out_var s_tuple = _ /\ _`,
        `not_fresh_at len_cs q_call ==> lookup_var q_call s_tuple = _ /\ _`,
        `not_fresh_at call_cs out_var ==> lookup_var out_var s_len = _ /\ _`,
        `not_fresh_at call_cs q_call ==> lookup_var q_call s_len = _ /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [eval_operand_def] >> rpt strip_tac >> gvs[]) >>
  `ptr_covers G_tuple tn_tuple out_var s_tuple
    (((flags.rcf_max_outsize+31) DIV 32)*32+32)` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`G_len`,`s_len`,`tn_len`] >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `!x. not_fresh_at len_cs x ==> lookup_var x s_tuple = _ /\ _`
       (qspec_then `out_var` mp_tac) >>
     simp_tac (srw_ss()) [ASSUME ``not_fresh_at len_cs out_var``]) >>
  `(do emit_void MSTORE [Var tuple_var;Var q_call];
       d <- emit_op ADD [Var tuple_var;Lit 32w];
       emit_void MCOPY [d;Var out_var;
         Lit (n2w (32+((flags.rcf_max_outsize+31) DIV 32)*32))] od)
    tuple_alloc_cs = ((),sb)` by
    (simp_tac (srw_ss()) [GSYM (ASSUME ``tuple_buf.buf_operand = Var tuple_var``),
       GSYM (ASSUME ``ov = Var out_var``),compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,boolTheory.LET_THM,
       pairTheory.pair_case_thm,pairTheory.UNCURRY_DEF,
       ASSUME ``emit_void MSTORE [tuple_buf.buf_operand;Var q_call]
         tuple_alloc_cs = ((),tuple_store_cs)``,
       ASSUME ``emit_op ADD [tuple_buf.buf_operand;Lit 32w]
         tuple_store_cs = (tuple_dst,tuple_add_cs)``,
       ASSUME ``emit_void MCOPY [tuple_dst;ov;
         Lit (n2w (32+((flags.rcf_max_outsize+31) DIV 32)*32))]
         tuple_add_cs = ((),sb)``] >> REFL_TAC) >>
  `fn_has_code tuple_alloc_cs sb func` by
    (qpat_assum `fn_has_code call_cs sb func` mp_tac >>
     qpat_assum `cs_extends call_cs len_cs` mp_tac >>
     qpat_assum `cs_extends len_cs sb` mp_tac >>
     qpat_assum `ci_mono len_cs tuple_alloc_cs` mp_tac >>
     qpat_assum `ci_mono tuple_alloc_cs tuple_store_cs` mp_tac >>
     qpat_assum `ci_mono tuple_store_cs tuple_add_cs` mp_tac >>
     qpat_assum `ci_mono tuple_add_cs sb` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [ci_mono_def] >>
     rpt strip_tac >> metis_tac[fn_has_code_mid,cs_extends_trans,cs_extends_refl]) >>
  `sc.cs_next_id < len_cs.cs_next_id` by decide_tac >>
  `FLOOKUP s_len.vs_allocas sc.cs_next_id =
    SOME (w2n (w_alloc:256 word),32+((flags.rcf_max_outsize+31) DIV 32)*32)` by
    (PURE_REWRITE_TAC [ASSUME ``s_len.vs_allocas = s_call.vs_allocas``] >>
     first_assum ACCEPT_TAC) >>
  `regions_disjoint (w2n (tuple_word:256 word))
    (64+((flags.rcf_max_outsize+31) DIV 32)*32)
    (w2n (w_alloc:256 word)) (32+((flags.rcf_max_outsize+31) DIV 32)*32)` by
    (qpat_assum `!aid b len. aid < len_cs.cs_next_id /\
       FLOOKUP s_len.vs_allocas aid = SOME (b,len) ==> _`
       (qspecl_then [`sc.cs_next_id`,`w2n (w_alloc:256 word)`,
         `32+((flags.rcf_max_outsize+31) DIV 32)*32`] irule) >>
     qexists_tac `sc` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `w2n (w_alloc:256 word)+32+((flags.rcf_max_outsize+31) DIV 32)*32 <=
    s_len.vs_alloca_next` by
    (qpat_assum `s_len.vs_alloca_next = s_call.vs_alloca_next`
       (fn th => PURE_REWRITE_TAC [th]) >> decide_tac) >>
  `val_wf (BaseTV (BytesT (Dynamic flags.rcf_max_outsize)))
    (BytesV (TAKE flags.rcf_max_outsize s_call.vs_returndata))` by
    (POP_ASSUM_LIST (K ALL_TAC) >>
     qspec_then `flags.rcf_max_outsize` mp_tac exprSimPropsTheory.le_word_size_mul >>
     simp[valueEncodingDefsTheory.val_wf_def,valueEncodingTheory.type_memory_size_def,
       listTheory.LENGTH_TAKE_EQ] >> decide_tac) >>
  `val_footprint (BaseTV (BytesT (Dynamic flags.rcf_max_outsize)))
      (BytesV (TAKE flags.rcf_max_outsize s_call.vs_returndata)) <=
    32+((flags.rcf_max_outsize+31) DIV 32)*32` by
    (qpat_assum `flags.rcf_max_outsize <= ((flags.rcf_max_outsize+31) DIV 32)*32` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rw[val_footprint_def,listTheory.LENGTH_TAKE_EQ] >> decide_tac) >>
  `!mem. mem_agree_outside tn_tuple.t_mem s_tuple.vs_memory mem ==>
    val_in_memory (BaseTV (BytesT (Dynamic flags.rcf_max_outsize)))
      (BytesV (TAKE flags.rcf_max_outsize s_call.vs_returndata)) (w2n w_alloc) mem` by
    (qspecl_then [`BaseTV (BytesT (Dynamic flags.rcf_max_outsize))`,
       `BytesV (TAKE flags.rcf_max_outsize s_call.vs_returndata)`,
       `w2n (w_alloc:256 word)`,`w2n (w_alloc:256 word)`,
       `32+((flags.rcf_max_outsize+31) DIV 32)*32`,
       `tn_len.t_mem`,`tn_tuple.t_mem`,`s_len.vs_memory`,`s_tuple.vs_memory`]
       mp_tac bodyPtrStructLitMonotoneRepresentationTheory.robust_val_in_memory_copy_transport_mono >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >| [
        PURE_REWRITE_TAC [ASSUME ``s_tuple.vs_memory = s_len.vs_memory``] >> REFL_TAC,
        qx_gen_tac `i` >> disch_tac >>
          qpat_assum `!i. i IN tn_tuple.t_mem <=> _`
            (qspec_then `w2n (w_alloc:256 word)+i` mp_tac) >>
          qpat_assum `w2n (w_alloc:256 word)+32+
            ((flags.rcf_max_outsize+31) DIV 32)*32 <= s_len.vs_alloca_next` mp_tac >>
          qpat_assum `i < 32+((flags.rcf_max_outsize+31) DIV 32)*32` mp_tac >>
          POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
          `~(s_len.vs_alloca_next <= w2n (w_alloc:256 word)+i)` by decide_tac >>
          fs[]]) >> disch_then ACCEPT_TAC) >>
  `w2n (w_alloc:256 word)+32+((flags.rcf_max_outsize+31) DIV 32)*32 <=
    s_tuple.vs_alloca_next` by decide_tac >>
  `~s_tuple.vs_halted` by
    (qpat_assum `s_tuple.vs_halted = s_len.vs_halted` mp_tac >>
     qpat_assum `~s_len.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]) >>
  `!x. Var q_call = Var x ==> not_fresh_at tuple_alloc_cs x` by
    simp_tac (srw_ss()) [ASSUME ``not_fresh_at tuple_alloc_cs q_call``] >>
  `ptr_covers G_tuple tn_tuple out_var s_tuple
    (32+((flags.rcf_max_outsize+31) DIV 32)*32)` by
    (`32+((flags.rcf_max_outsize+31) DIV 32)*32 =
       ((flags.rcf_max_outsize+31) DIV 32)*32+32` by decide_tac >>
     PURE_REWRITE_TAC [ASSUME ``32+((flags.rcf_max_outsize+31) DIV 32)*32 =
       ((flags.rcf_max_outsize+31) DIV 32)*32+32``] >> first_assum ACCEPT_TAC) >>
  qspecl_then [`tuple_alloc_cs`,`sb`,`tuple_var`,`out_var`,`Var q_call`,
    `tuple_word`,`w_alloc`,`outcome.co_success`,
    `((flags.rcf_max_outsize+31) DIV 32)*32`,`flags.rcf_max_outsize`,
    `s_call.vs_returndata`,`s_tuple`,`G_tuple`,`tn_tuple`,`lo`,
    `gas_explicit_sites ctx shadow_ctx`,`ctx`,`func`,`PG`]
    mp_tac bodyFullRawCallTupleStoreTheory.raw_call_tuple_store_origin_ptr >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  disch_then (qx_choosel_then [`tuple_raw`,`z_tuple`,`J_tuple`,`un_tuple`]
    strip_assume_tac) >>
  suspend "tuplePost"
QED

Resume raw_call_positive_full_finish[positiveBytes]:
  qpat_assum `(if flags.rcf_max_outsize > 0 then _ else _) pass_cs = (result,sb)`
    (mp_tac o SIMP_RULE (srw_ss()) [arithmeticTheory.GREATER_DEF,
      ASSUME ``0 < flags.rcf_max_outsize``]) >>
  disch_then (mp_then Any mp_tac rawCallShapePtrTheory.raw_call_bytes_suffix_steps) >>
  disch_then (qx_choosel_then
    [`len_rds`,`len_rds_cs`,`len_cmp`,`len_cmp_cs`,`len_cap`,`len_cap_cs`]
    strip_assume_tac) >>
  `call_cs.cs_next_var <= pass_cs.cs_next_var /\
   call_cs.cs_next_id <= pass_cs.cs_next_id` by
    (qpat_assum `ci_mono call_cs jump_cs` mp_tac >>
     qpat_assum `ci_mono jump_cs jumped_cs` mp_tac >>
     qpat_assum `ci_mono jumped_cs fail_cs` mp_tac >>
     qpat_assum `ci_mono fail_cs failed_cs` mp_tac >>
     qpat_assum `ci_mono failed_cs pass_cs` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [ci_mono_def] >>
     rpt strip_tac >> decide_tac) >>
  `local_ptrs_reserved cenv pass_cs` by
    (qspecl_then [`cenv`,`call_cs`,`pass_cs`] mp_tac local_ptrs_reserved_next_var >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  `not_fresh_at pass_cs out_var` by
    (irule not_fresh_at_mono >> qexists_tac `call_cs` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `safe_operand pass_cs ov` by
    (simp_tac (srw_ss()) [ASSUME ``ov = Var out_var``,
       exprSafeOperandTheory.safe_operand_def] >> first_assum ACCEPT_TAC) >>
  `sa.cs_next_var <= pass_cs.cs_next_var /\ sc.cs_next_id < pass_cs.cs_next_id` by
    decide_tac >>
  `s_jump.vs_allocas = s_call.vs_allocas /\
   s_jump.vs_returndata = s_call.vs_returndata /\
   s_jump.vs_memory = s_call.vs_memory /\
   s_jump.vs_alloca_next = s_call.vs_alloca_next` by
    simp_tac (srw_ss()) [Abbr `s_jump`,venomStateTheory.jump_to_def] >>
  `lookup_var out_var s_jump = SOME w_alloc` by
    (simp_tac (srw_ss()) [Abbr `s_jump`,venomStateTheory.jump_to_def,lookup_var_def] >>
     qpat_assum `lookup_var out_var s_call = SOME w_alloc`
       (ACCEPT_TAC o REWRITE_RULE [lookup_var_def])) >>
  `ptr_covers G_call tn_call out_var s_jump
    (((flags.rcf_max_outsize+31) DIV 32)*32+32)` by
    (simp_tac (srw_ss()) [Abbr `s_jump`,venomStateTheory.jump_to_def,
       ptr_covers_def,lookup_var_def] >>
     qpat_assum `ptr_covers G_call tn_call out_var s_call _`
       (ACCEPT_TAC o REWRITE_RULE [ptr_covers_def,lookup_var_def])) >>
  `mem_bytes_at (w2n (w_alloc:256 word)+32)
      (LENGTH (TAKE flags.rcf_max_outsize s_jump.vs_returndata)) s_jump.vs_memory =
    TAKE flags.rcf_max_outsize s_jump.vs_returndata` by
    (PURE_REWRITE_TAC [ASSUME ``s_jump.vs_returndata = s_call.vs_returndata``,
       ASSUME ``s_jump.vs_memory = s_call.vs_memory``] >> first_assum ACCEPT_TAC) >>
  `!i. w2n (w_alloc:256 word)+32 <= i /\
    i < w2n w_alloc+32+LENGTH (TAKE flags.rcf_max_outsize s_jump.vs_returndata) ==>
    i NOTIN tn_call.t_mem` by
    (PURE_REWRITE_TAC [ASSUME ``s_jump.vs_returndata = s_call.vs_returndata``] >>
     first_assum ACCEPT_TAC) >>
  `s_jump.vs_current_bb = pass_cs.cs_current_bb /\
   s_jump.vs_inst_idx = LENGTH pass_cs.cs_current_insts` by
    simp_tac (srw_ss()) [Abbr `s_jump`,venomStateTheory.jump_to_def,
      ASSUME ``outcome.co_success``,ASSUME ``pass_cs.cs_current_bb = good``,
      ASSUME ``pass_cs.cs_current_insts = []``] >>
  `wb_frame cenv es ee_call sa s0 s_jump` by
    (qpat_assum `wb_frame cenv es ee_call sa s0 s_call`
       (fn th => simp_tac bool_ss [Abbr `s_jump`,wb_frame_def,locals_kept_def,
          popped_kept_def,venomStateTheory.jump_to_def,lookup_var_def,
          venomStateTheory.venom_state_accfupds] >>
        ACCEPT_TAC (REWRITE_RULE [wb_frame_def,locals_kept_def,popped_kept_def,
          lookup_var_def] th))) >>
  `FLOOKUP s_jump.vs_allocas sc.cs_next_id =
    SOME (w2n (w_alloc:256 word),32+((flags.rcf_max_outsize+31) DIV 32)*32)` by
    (PURE_REWRITE_TAC [ASSUME ``s_jump.vs_allocas = s_call.vs_allocas``] >>
     first_assum ACCEPT_TAC) >>
  `(do rds <- emit_op RETURNDATASIZE [];
       cmp <- emit_op LT [rds;Lit (n2w flags.rcf_max_outsize)];
       cap <- compile_select cmp rds (Lit (n2w flags.rcf_max_outsize));
       emit_void MSTORE [Var out_var;cap] od) pass_cs = ((),sb)` by
    (simp_tac (srw_ss()) [GSYM (ASSUME ``ov = Var out_var``),
       compileEnvTheory.comp_bind_def,compileEnvTheory.comp_ignore_bind_def,
       boolTheory.LET_THM,pairTheory.pair_case_thm,pairTheory.UNCURRY_DEF,
       ASSUME ``emit_op RETURNDATASIZE [] pass_cs = (len_rds,len_rds_cs)``,
       ASSUME ``emit_op LT [len_rds;Lit (n2w flags.rcf_max_outsize)]
         len_rds_cs = (len_cmp,len_cmp_cs)``,
       ASSUME ``compile_select len_cmp len_rds (Lit (n2w flags.rcf_max_outsize))
         len_cmp_cs = (len_cap,len_cap_cs)``,
       ASSUME ``emit_void MSTORE [ov;len_cap] len_cap_cs = ((),sb)``] >> REFL_TAC) >>
  `s_jump.vs_returndata = outcome.co_returnData` by
    (PURE_REWRITE_TAC [ASSUME ``s_jump.vs_returndata = s_call.vs_returndata``,
       ASSUME ``s_call.vs_returndata = outcome.co_returnData``] >> REFL_TAC) >>
  `LENGTH s_jump.vs_returndata < dimword(:256)` by
    (PURE_REWRITE_TAC [ASSUME ``s_jump.vs_returndata = outcome.co_returnData``] >>
     first_assum ACCEPT_TAC) >>
  `s_jump.vs_alloca_next = allocated.vs_alloca_next` by
    simp_tac (srw_ss()) [Abbr `s_jump`,Abbr `s_call`,venomStateTheory.jump_to_def,
      ASSUME ``u_call.vs_alloca_next = ready.vs_alloca_next``,
      ASSUME ``ready.vs_alloca_next = allocated.vs_alloca_next``] >>
  `w2n (w_alloc:256 word)+32 <= s_jump.vs_alloca_next` by decide_tac >>
  qspecl_then [`pass_cs`,`sb`,`flags.rcf_max_outsize`,`out_var`,
    `((flags.rcf_max_outsize+31) DIV 32)*32+32`,`w_alloc`,`s_jump`,
    `G_call`,`tn_call`,`lo`,`gas_explicit_sites ctx shadow_ctx`,`ctx`,`func`,`PG`]
    mp_tac bodyFullRawCallLengthTheory.raw_call_length_store_origin_ptr >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  disch_then (qx_choosel_then [`len_raw`,`s_len`,`G_len`,`tn_len`]
    strip_assume_tac) >>
  `MAP FDOM es.scopes = MAP FDOM ee_call.scopes` by
    (PURE_REWRITE_TAC [ASSUME ``ee_call.scopes = mid.scopes``] >>
     first_assum ACCEPT_TAC) >>
  qabbrev_tac `out_allocation_inst = mk_inst sc.cs_next_id ALLOCA
    [Lit (n2w (((flags.rcf_max_outsize+31) DIV 32)*32+32))] [out_var]` >>
  `MEM out_allocation_inst (fn_insts func)` by
    (simp_tac (srw_ss()) [Abbr `out_allocation_inst`,
       ASSUME ``out_var = STRING #"%" (toString sc.cs_next_var)``] >>
     first_assum ACCEPT_TAC) >>
  `out_allocation_inst.inst_opcode = ALLOCA /\
   out_allocation_inst.inst_outputs = [out_var] /\
   out_allocation_inst.inst_id = sc.cs_next_id` by
    simp_tac (srw_ss()) [Abbr `out_allocation_inst`,venomInstTheory.mk_inst_def] >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee_call s_len /\
    wb_frame cenv es ee_call sa s0 s_len /\
    s_len.vs_fmp = s_jump.vs_fmp /\ s_len.vs_allocas = s_jump.vs_allocas` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee_call s_jump`
       (qspec_then `H` (fn th => assume_tac (MATCH_MP th
         (ASSUME ``valid_horizon cx st0 H ee_call.storage_trace``)))) >>
     `stmt_state_rel H ctx func cenv cx ee_call
       (s_jump with vs_fmp := s_jump.vs_fmp)` by
       (simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx ee_call s_jump`
       (fn rel => let
          val horizon = hd (snd (strip_comb (concl rel)));
          val th = exprSimRawCallCalldataTheory.raw_call_output_prefix_ready;
          val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
            (free_vars (concl th)));
          val ith = INST_TYPE (match_type (type_of hv) (type_of horizon)) th;
          val ihv = valOf (List.find (fn v => fst (dest_var v) = "H")
            (free_vars (concl ith)));
        in qspecl_then [`ctx`,`func`,`cenv`,`cx`,`ee_call`,`es`,`sa`,`s0`,
          `pass_cs`,`len_rds`,`len_rds_cs`,`len_cmp`,`len_cmp_cs`,`len_cap`,
          `len_cap_cs`,`sb`,`ov`,`s_jump`,`w_alloc`,`s_jump.vs_fmp`,
          `flags.rcf_max_outsize`,`out_allocation_inst`,`out_var`,
          `w2n (w_alloc:256 word)`,`32+((flags.rcf_max_outsize+31) DIV 32)*32`]
          mp_tac (SPEC horizon (GEN ihv ith)) end) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> FIRST
          [PURE_REWRITE_TAC [ASSUME ``ov = Var out_var``,eval_operand_def] >>
             first_assum ACCEPT_TAC,
           PURE_REWRITE_TAC [ASSUME ``out_allocation_inst.inst_id = sc.cs_next_id``] >>
             first_assum ACCEPT_TAC,
           ALL_TAC] >> decide_tac) >>
     disch_then (qx_choose_then `memory_len` strip_assume_tac) >>
     `memory_len = len_raw` by
       (qpat_assum `run_inst_seq (emitted_insts pass_cs sb) s_jump = OK memory_len` mp_tac >>
        qpat_assum `run_inst_seq (emitted_insts pass_cs sb) s_jump = OK len_raw` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) []) >>
     qpat_x_assum `memory_len = len_raw` SUBST_ALL_TAC >>
     qpat_assum `s_len = len_raw with vs_inst_idx := _` (fn th => PURE_REWRITE_TAC [th]) >>
     rpt conj_tac
     >- (PURE_REWRITE_TAC [stmt_state_rel_inst_idx] >>
         qpat_assum `stmt_state_rel H ctx func cenv cx ee_call
           (len_raw with vs_fmp := s_jump.vs_fmp)` mp_tac >>
         PURE_REWRITE_TAC [GSYM (ASSUME ``len_raw.vs_fmp = s_jump.vs_fmp``)] >>
         simp_tac (srw_ss()) [])
     >- (simp_tac bool_ss [wb_frame_def,locals_kept_def,popped_kept_def,
           lookup_var_def,venomStateTheory.venom_state_accfupds] >>
         qpat_assum `wb_frame cenv es ee_call sa s0 len_raw`
           (ACCEPT_TAC o REWRITE_RULE [wb_frame_def,locals_kept_def,
              popped_kept_def,lookup_var_def]))
     >> simp_tac bool_ss [venomStateTheory.venom_state_accfupds] >>
        first_assum ACCEPT_TAC) >>
  suspend "bytesPost"
QED

Resume raw_call_positive_full_finish[bytesPost]:
  `storage_trace_domain cx st0 ee_call.storage_trace` by
    (simp_tac (srw_ss()) [Abbr `ee_call`] >> first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 (storage_trace_horizon ee_call.storage_trace)
    ee_call.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 ee_call.storage_trace`
       (mp_tac o REWRITE_RULE [storage_trace_domain_def]) >> simp_tac bool_ss []) >>
  `stmt_state_rel (storage_trace_horizon ee_call.storage_trace)
    ctx func cenv cx ee_call s_jump` by
    (qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee_call s_jump`
       (qspec_then `storage_trace_horizon ee_call.storage_trace` irule) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee_call s_len /\ _`
    (qspec_then `storage_trace_horizon ee_call.storage_trace`
      (fn th => strip_assume_tac (MATCH_MP th
        (ASSUME ``valid_horizon cx st0 (storage_trace_horizon ee_call.storage_trace)
          ee_call.storage_trace``)))) >>
  `alloca_inv s_jump` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon ee_call.storage_trace)
       ctx func cenv cx ee_call s_jump` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[stmt_state_rel_def]) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee_call G_call tn_call s_jump` by
    (simp_tac (srw_ss()) [Abbr `s_jump`,ghost_inv_at_jump] >>
     first_assum ACCEPT_TAC) >>
  `sb.cs_current_bb = pass_cs.cs_current_bb /\
   sb.cs_current_insts = pass_cs.cs_current_insts ++ emitted_insts pass_cs sb` by
    (qpat_assum `(do rds <- emit_op RETURNDATASIZE []; _ od) pass_cs = ((),sb)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[compileEnvTheory.comp_bind_def,compileEnvTheory.comp_ignore_bind_def,
       builtinSimpleTheory.compile_select_def,emitHelperTheory.emit_op_def,
       emitHelperTheory.emit_void_def,compileEnvTheory.fresh_id_def,
       compileEnvTheory.fresh_var_def,compileEnvTheory.emit_def,
       compileEnvTheory.comp_return_def,boolTheory.LET_THM,
       pairTheory.pair_case_thm,pairTheory.UNCURRY_DEF] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def,rich_listTheory.DROP_LENGTH_APPEND]) >>
  `alloca_history func s_len` by
    (qpat_assum `s_len = len_raw with vs_inst_idx := _` (fn th => PURE_REWRITE_TAC [th]) >>
     qspecl_then [`emitted_insts pass_cs sb`,`pass_cs`,`sb`,`s_jump`,`len_raw`]
       mp_tac bodyFullUnwrapRunTheory.emitted_alloca_history >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       qpat_assum `EVERY _ (emitted_insts pass_cs sb)`
         (fn th => POP_ASSUM_LIST (K ALL_TAC) >> mp_tac th) >>
       simp[listTheory.EVERY_MEM]) >> disch_then ACCEPT_TAC) >>
  qpat_assum `s_len = (mstore _ _ s_jump) with <|vs_vars := _;vs_inst_idx := _|>`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [boolTheory.LET_THM,venomStateTheory.mstore_def,pairTheory.PAIR_EQ] o
      Q.AP_TERM `\z. (z.vs_halted,z.vs_alloca_next,z.vs_inst_idx,
        z.vs_accounts,z.vs_transient,z.vs_call_ctx,z.vs_immutables,z.vs_returndata)`) >>
  `~s_len.vs_halted /\ allocas_from lo s_len /\
   lo <= s_len.vs_alloca_next /\
   s_len.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`allocas_from lo s_jump`,`~s_jump.vs_halted`,
        `lo <= s_jump.vs_alloca_next`,
        `s_len.vs_halted = s_jump.vs_halted`,
        `s_len.vs_alloca_next = s_jump.vs_alloca_next`,
        `s_len.vs_allocas = s_jump.vs_allocas`,
        `s_len.vs_inst_idx = LENGTH sb.cs_current_insts`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [ptrDisciplineTheory.allocas_from_def]) >>
  `local_ptrs_rel func cenv ee_call.scopes s_jump` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon ee_call.storage_trace)
       ctx func cenv cx ee_call s_jump` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[stmt_state_rel_def,state_rel_def]) >>
  `!name lb lsz. local_region cenv ee_call.scopes s_jump name lb lsz ==>
    w2n (w_alloc:256 word)+32 <= lb \/ lb+lsz <= w2n w_alloc` by
    (rpt strip_tac >>
     qspecl_then [`func`,`cenv`,`ee_call.scopes`,`s_jump`,`out_allocation_inst`,
       `out_var`,`w2n (w_alloc:256 word)`,
       `32+((flags.rcf_max_outsize+31) DIV 32)*32`,`name`,`lb`,`lsz`]
       mp_tac localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       PURE_REWRITE_TAC [ASSUME ``out_allocation_inst.inst_id = sc.cs_next_id``] >>
       first_assum ACCEPT_TAC) >>
     PURE_REWRITE_TAC [regions_disjoint_def] >> strip_tac >> decide_tac) >>
  `s_len.vs_memory = (mstore (w2n w_alloc)
    (n2w (MIN (LENGTH s_jump.vs_returndata) flags.rcf_max_outsize)) s_jump).vs_memory` by
    (qpat_assum `s_len = (mstore _ _ s_jump) with <|vs_vars := _;vs_inst_idx := _|>`
       (mp_tac o SIMP_RULE (srw_ss()) [] o Q.AP_TERM `\z. z.vs_memory`) >>
     simp_tac bool_ss []) >>
  `!a k. a+k <= w2n (w_alloc:256 word) \/ w2n w_alloc+32 <= a ==>
    mem_bytes_at a k s_len.vs_memory = mem_bytes_at a k s_jump.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     PURE_REWRITE_TAC [ASSUME ``s_len.vs_memory = (mstore (w2n (w_alloc:256 word))
       (n2w (MIN (LENGTH s_jump.vs_returndata) flags.rcf_max_outsize)) s_jump).vs_memory``] >>
     irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
     first_assum ACCEPT_TAC) >>
  `!j. j < w2n (w_alloc:256 word) \/ w2n w_alloc+32 <= j ==>
    (j IN tn_len.t_mem <=> j IN tn_call.t_mem)` by
    (rpt gen_tac >> disch_tac >>
     PURE_REWRITE_TAC [ASSUME ``tn_len.t_mem = tn_call.t_mem DIFF
       {i | w2n (w_alloc:256 word) <= i /\ i < w2n w_alloc+32}``] >>
     `~(w2n (w_alloc:256 word) <= j /\ j < w2n w_alloc+32)` by decide_tac >>
     simp_tac (srw_ss()) [ASSUME ``~(w2n (w_alloc:256 word) <= j /\ j < w2n w_alloc+32)``]) >>
  `!x. not_fresh_at sc x ==>
    lookup_var x s_len = lookup_var x s_jump /\
    FLOOKUP G_len x = FLOOKUP G_call x /\
    op_taint tn_len (Var x) = op_taint tn_call (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at pass_cs x` by
       (irule not_fresh_at_mono >> qexists_tac `sc` >>
        conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `!x. not_fresh_at pass_cs x ==> lookup_var x s_len = _ /\ _`
       (qspec_then `x` irule) >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee_call G_len tn_len s_len` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       ghost_inv_at _ _ _ _ _ _ G_call tn_call s_jump`
       (qspec_then `H` (fn th => assume_tac (MATCH_MP th
         (ASSUME ``valid_horizon cx st0 H ee_call.storage_trace``)))) >>
     `stor_taint_ok_at (DF H) tn_len s_len` by
       (qpat_assum `ghost_inv_at (DF H) lo d cenv cx ee_call G_call tn_call s_jump`
          (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >>
        PURE_REWRITE_TAC [stor_taint_ok_at_def,
          ASSUME ``tn_len.t_stor = tn_call.t_stor``,
          ASSUME ``tn_len.t_trans = tn_call.t_trans``,
          ASSUME ``tn_len.t_imm = tn_call.t_imm``,
          ASSUME ``s_len.vs_accounts = s_jump.vs_accounts``,
          ASSUME ``s_len.vs_transient = s_jump.vs_transient``,
          ASSUME ``s_len.vs_call_ctx = s_jump.vs_call_ctx``,
          ASSUME ``s_len.vs_immutables = s_jump.vs_immutables``] >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss []) >>
     qspecl_then [`DF H`,`lo`,`d`,`cenv`,`cx`,`ee_call`,`G_call`,`tn_call`,
       `s_jump`,`sc`,`func`,`w2n (w_alloc:256 word)`,`32`,
       `s_len`,`G_len`,`tn_len`] mp_tac
       (Q.GENL [`D`,`lo`,`d`,`cenv`,`cx`,`es`,`G`,`tn`,`s`,`sa`,`func`,
          `start`,`nb`,`z`,`H`,`tf`]
          bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_inv_at) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       rpt strip_tac >> res_tac) >> disch_then ACCEPT_TAC) >>
  suspend "bytesResult"
QED

Resume raw_call_positive_full_finish[bytesResult]:
  `lookup_var out_var s_len = SOME w_alloc` by
    (qpat_assum `!x. not_fresh_at pass_cs x ==> lookup_var x s_len = _ /\ _`
       (qspec_then `out_var` mp_tac) >>
     simp_tac (srw_ss()) [ASSUME ``not_fresh_at pass_cs out_var``,
       ASSUME ``lookup_var out_var s_jump = SOME (w_alloc:256 word)``]) >>
  `val_wf (BaseTV (BytesT (Dynamic flags.rcf_max_outsize)))
    (BytesV (TAKE flags.rcf_max_outsize s_jump.vs_returndata))` by
    (POP_ASSUM_LIST (K ALL_TAC) >>
     qspec_then `flags.rcf_max_outsize` mp_tac exprSimPropsTheory.le_word_size_mul >>
     simp[valueEncodingDefsTheory.val_wf_def,valueEncodingTheory.type_memory_size_def,
       listTheory.LENGTH_TAKE_EQ] >> decide_tac) >>
  `val_in_memory (BaseTV (BytesT (Dynamic flags.rcf_max_outsize)))
    (BytesV (TAKE flags.rcf_max_outsize s_jump.vs_returndata))
    (w2n w_alloc) s_len.vs_memory` by
    (qpat_assum `!mem. mem_agree_outside tn_len.t_mem s_len.vs_memory mem ==> _`
       (qspec_then `s_len.vs_memory` irule) >>
     simp_tac (srw_ss()) [mem_agree_outside_def]) >>
  `!name lb lsz. local_region cenv ee_call.scopes s_len name lb lsz ==>
    w2n (w_alloc:256 word)+32+((flags.rcf_max_outsize+31) DIV 32)*32 <= lb \/
    lb+lsz <= w2n w_alloc` by
    (rpt strip_tac >>
     `alloca_inv s_len /\ local_ptrs_rel func cenv ee_call.scopes s_len` by
       (qpat_assum `stmt_state_rel (storage_trace_horizon ee_call.storage_trace)
          ctx func cenv cx ee_call s_len` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[stmt_state_rel_def,state_rel_def]) >>
     qspecl_then [`func`,`cenv`,`ee_call.scopes`,`s_len`,`out_allocation_inst`,
       `out_var`,`w2n (w_alloc:256 word)`,
       `32+((flags.rcf_max_outsize+31) DIV 32)*32`,`name`,`lb`,`lsz`]
       mp_tac localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       PURE_REWRITE_TAC [ASSUME ``out_allocation_inst.inst_id = sc.cs_next_id``,
         ASSUME ``s_len.vs_allocas = s_jump.vs_allocas``] >> first_assum ACCEPT_TAC) >>
     PURE_REWRITE_TAC [regions_disjoint_def] >> strip_tac >> decide_tac) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G_len tn_len` by
    (irule ghost_kept_at_clean_suffix >> qexistsl_tac [`G_call`,`tn_call`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qx_gen_tac `x` >> disch_tac >>
         `not_fresh_at pass_cs x` by
           (irule not_fresh_at_mono >> qexists_tac `sa` >>
            conj_tac >> first_assum ACCEPT_TAC) >>
         qpat_assum `!x. not_fresh_at pass_cs x ==> lookup_var x s_len = _ /\ _`
           (qspec_then `x` mp_tac) >>
         simp_tac (srw_ss()) [ASSUME ``not_fresh_at pass_cs x``] >>
         strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
     PURE_REWRITE_TAC [ASSUME ``tn_len.t_mem = tn_call.t_mem DIFF
       {i | w2n (w_alloc:256 word) <= i /\ i < w2n w_alloc+32}``] >>
     simp_tac (srw_ss()) []) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G,tn) [] (OK s_len,G_len,tn_len)` by
    (qx_gen_tac `H` >> disch_tac >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`G_call`,`s_jump`,`tn_call`] >> conj_tac
     >- (qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
           gas_origin_ptr_path _ (t,G,tn) [] (OK s_jump,G_call,tn_call)`
           (qspec_then `H` irule) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!D. gas_origin_ptr_path _ (s_jump,G_call,tn_call) [] _`
       (qspec_then `DF H` ACCEPT_TAC)) >>
  suspend "bytesValuePost"
QED

Resume raw_call_positive_full_finish[bytesValuePost]:
  `result = Var out_var` by
    (qpat_assum `result = ov` (fn result_eq =>
       qpat_assum `ov = Var out_var` (ACCEPT_TAC o TRANS result_eq))) >>
  `vv = LocatedValue ann (mk_ptr (Var out_var) LocMemory)` by
    simp_tac (srw_ss()) [ASSUME ``vv = (if flags.rcf_max_outsize = 0 then
      StackValue ann result else LocatedValue ann (mk_ptr result LocMemory))``,
      ASSUME ``flags.rcf_max_outsize <> 0``,ASSUME ``result = Var out_var``] >>
  `type_slot_size (BaseTV (BytesT (Dynamic flags.rcf_max_outsize))) <= dimword(:256)` by
    (qpat_assum `((flags.rcf_max_outsize+31) DIV 32)*32+32 < dimword(:256)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [vyperValueTheory.type_slot_size_def,
       vfmConstantsTheory.word_size_def] >> decide_tac) >>
  `~is_word_type ann` by
    simp_tac (srw_ss()) [ASSUME ``ann = BaseT (BytesT (Dynamic flags.rcf_max_outsize))``,
      compileEnvTheory.is_word_type_def] >>
  `evaluate_type (get_tenv cx) ann =
    SOME (BaseTV (BytesT (Dynamic flags.rcf_max_outsize)))` by
    simp_tac (srw_ss()) [ASSUME ``ann = BaseT (BytesT (Dynamic flags.rcf_max_outsize))``,
      vyperValueTheory.evaluate_type_def,boolTheory.LET_THM,
      ASSUME ``flags.rcf_max_outsize < dimword(:256)``,
      ASSUME ``type_slot_size (BaseTV (BytesT (Dynamic flags.rcf_max_outsize))) <= dimword(:256)``] >>
  `val_footprint (BaseTV (BytesT (Dynamic flags.rcf_max_outsize)))
    (BytesV (TAKE flags.rcf_max_outsize s_jump.vs_returndata)) <=
    32+((flags.rcf_max_outsize+31) DIV 32)*32` by
    (qpat_assum `flags.rcf_max_outsize <= ((flags.rcf_max_outsize+31) DIV 32)*32` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rw[val_footprint_def,listTheory.LENGTH_TAKE_EQ] >> decide_tac) >>
  `sc.cs_next_id < sb.cs_next_id` by
    (qpat_assum `ci_mono pass_cs sb` mp_tac >>
     qpat_assum `sc.cs_next_id < pass_cs.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ci_mono_def] >> rpt strip_tac >> decide_tac) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    vv_post H ctx func cenv cx (Call ann (RawCallTarget flags) args dflt)
      es sa sb s0 ee_call
      (Value (BytesV (TAKE flags.rcf_max_outsize s_jump.vs_returndata))) vv s_len` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee_call s_len /\ _`
       (qspec_then `H` (fn th => strip_assume_tac (MATCH_MP th
         (ASSUME ``valid_horizon cx st0 H ee_call.storage_trace``)))) >>
     `storage_well_formed_on cx ee_call (FST H)` by
       (qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
         storage_well_formed_on cx ee_call (FST H)`
         (qspec_then `H` irule) >> first_assum ACCEPT_TAC) >>
     PURE_REWRITE_TAC [ASSUME ``vv = LocatedValue ann (mk_ptr (Var out_var) LocMemory)``] >>
     qpat_assum `stmt_state_rel H ctx func cenv cx ee_call s_len`
       (fn rel => mp_tac (Q.INST
         [`e` |-> `Call ann (RawCallTarget flags) args dflt`,
          `es` |-> `es`,`sa` |-> `sa`,`sb` |-> `sb`,`s0` |-> `s0`,
          `tv` |-> `BaseTV (BytesT (Dynamic flags.rcf_max_outsize))`,
          `v` |-> `BytesV (TAKE flags.rcf_max_outsize s_jump.vs_returndata)`,
          `p` |-> `mk_ptr (Var out_var) LocMemory`,`w` |-> `w_alloc`,
          `aid` |-> `sc.cs_next_id`,`b` |-> `w2n (w_alloc:256 word)`,
          `sz` |-> `32+((flags.rcf_max_outsize+31) DIV 32)*32`]
         (PART_MATCH (find_term (fn tm =>
           same_const (fst (strip_comb tm)) ``stmt_state_rel``))
           exprSimHashTheory.vv_post_allocated_memory_intro (concl rel)))) >>
     impl_tac
     >- (simp_tac (srw_ss()) [post_value_type_def,vyperASTTheory.expr_type_def,
           ASSUME ``~is_word_type ann``,
           ASSUME ``evaluate_type (get_tenv cx) ann =
             SOME (BaseTV (BytesT (Dynamic flags.rcf_max_outsize)))``,
           contextTheory.mk_ptr_def,eval_operand_def,
           loweringPostsTheory.expr_has_effect_thm] >>
         PURE_REWRITE_TAC [ASSUME ``s_len.vs_allocas = s_jump.vs_allocas``] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
         >~ [`local_region (* sg *)`]
         >- (qx_genl_tac [`local_name`,`local_b`,`local_n`] >> disch_tac >>
             qpat_assum `!name lb lsz. local_region cenv ee_call.scopes s_len name lb lsz ==> _`
               (qspecl_then [`local_name`,`local_b`,`local_n`] mp_tac) >>
             impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> decide_tac) >>
         decide_tac) >>
     simp_tac (srw_ss()) [vyperASTTheory.expr_type_def]) >>
  suspend "bytesCapacity"
QED

Resume raw_call_positive_full_finish[bytesCapacity]:
  `w2n (w_alloc:256 word)+32+((flags.rcf_max_outsize+31) DIV 32)*32 <=
    s_len.vs_alloca_next` by
    (PURE_REWRITE_TAC [ASSUME ``s_len.vs_alloca_next = s_jump.vs_alloca_next``,
       ASSUME ``s_jump.vs_alloca_next = allocated.vs_alloca_next``] >> decide_tac) >>
  `val_store_size (BaseTV (BytesT (Dynamic flags.rcf_max_outsize)))
    (BytesV (TAKE flags.rcf_max_outsize s_jump.vs_returndata)) <=
    32+((flags.rcf_max_outsize+31) DIV 32)*32` by
    (irule raw_call_bytes_store_capacity >> POP_ASSUM_LIST (K ALL_TAC) >>
     rw[listTheory.LENGTH_TAKE_EQ] >> decide_tac) >>
  `vv_store_bound cx (expr_type (Call ann (RawCallTarget flags) args dflt))
    (lowered_value_type cenv (Call ann (RawCallTarget flags) args dflt)) ee_call
    (Value (BytesV (TAKE flags.rcf_max_outsize s_jump.vs_returndata))) vv s_len` by
    (qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       vv_post H ctx func cenv cx _ es sa sb s0 ee_call _ vv s_len`
       (qspec_then `storage_trace_horizon ee_call.storage_trace`
         (fn th => assume_tac (REWRITE_RULE
           [ASSUME ``vv = LocatedValue ann (mk_ptr (Var out_var) LocMemory)``]
           (MATCH_MP th (ASSUME ``valid_horizon cx st0
             (storage_trace_horizon ee_call.storage_trace) ee_call.storage_trace``))))) >>
     `lowered_value_type cenv (Call ann (RawCallTarget flags) args dflt) =
       expr_type (Call ann (RawCallTarget flags) args dflt)` by
       simp_tac (srw_ss()) [lowered_value_type_def,vyperASTTheory.expr_type_def] >>
     PURE_REWRITE_TAC [ASSUME ``vv = LocatedValue ann (mk_ptr (Var out_var) LocMemory)``,
       ASSUME ``lowered_value_type cenv (Call ann (RawCallTarget flags) args dflt) =
         expr_type (Call ann (RawCallTarget flags) args dflt)``] >>
     qpat_assum `vv_post (storage_trace_horizon ee_call.storage_trace)
       ctx func cenv cx _ es sa sb s0 ee_call _ (LocatedValue ann _) s_len`
       (fn post => assume_tac (SIMP_RULE (srw_ss()) [contextTheory.mk_ptr_def] post) >>
         mp_tac (Q.INST
         [`fw` |-> `w_alloc`,`ftv` |-> `BaseTV (BytesT (Dynamic flags.rcf_max_outsize))`]
         (PART_MATCH (find_term (fn tm =>
           same_const (fst (strip_comb tm)) ``vv_post``))
           exprSimMemDefsTheory.vv_store_bound_capacity (concl post)))) >>
     impl_tac >- (simp_tac (srw_ss()) [vyperASTTheory.expr_type_def,
       post_value_type_def,contextTheory.mk_ptr_def,eval_operand_def,
       valueEncodingTheory.type_memory_size_def,vfmConstantsTheory.word_size_def] >>
       rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
     disch_then ACCEPT_TAC) >>
  `val_store_size (BaseTV (BytesT (Dynamic flags.rcf_max_outsize)))
    (BytesV (TAKE flags.rcf_max_outsize s_jump.vs_returndata)) <=
    ((flags.rcf_max_outsize+31) DIV 32)*32+32` by decide_tac >>
  `ptr_val_ok cx ann (BytesV (TAKE flags.rcf_max_outsize s_jump.vs_returndata))
    (Var out_var) G_len tn_len s_len` by
    (mp_tac (Q.INST [`cx` |-> `cx`,`ty` |-> `ann`,
       `tv` |-> `BaseTV (BytesT (Dynamic flags.rcf_max_outsize))`,
       `v` |-> `BytesV (TAKE flags.rcf_max_outsize s_jump.vs_returndata)`,
       `p` |-> `out_var`,`G` |-> `G_len`,`tn` |-> `tn_len`,`s` |-> `s_len`,
       `capacity` |-> `((flags.rcf_max_outsize+31) DIV 32)*32+32`]
       rawCallBufferPtrTheory.ptr_val_ok_from_covers) >>
     impl_tac
     >- (simp_tac (srw_ss()) [ASSUME ``~is_word_type ann``] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> rpt strip_tac >>
         `w = w_alloc` by
           (qpat_assum `lookup_var out_var s_len = SOME w` mp_tac >>
            PURE_REWRITE_TAC [ASSUME ``lookup_var out_var s_len = SOME (w_alloc:256 word)``] >>
            simp_tac (srw_ss()) []) >>
         qpat_x_assum `w = w_alloc` SUBST_ALL_TAC >>
         qpat_assum `!mem. mem_agree_outside tn_len.t_mem s_len.vs_memory mem ==> _`
           irule >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  `ptr_vv_ok cx (post_value_type cenv (Call ann (RawCallTarget flags) args dflt))
    (Value (BytesV (TAKE flags.rcf_max_outsize s_jump.vs_returndata))) vv ee_call
    G_len tn_len s_len` by
    (qpat_assum `ptr_val_ok cx ann _ (Var out_var) G_len tn_len s_len` mp_tac >>
     PURE_REWRITE_TAC [ASSUME ``vv = LocatedValue ann (mk_ptr (Var out_var) LocMemory)``] >>
     simp_tac (srw_ss()) [ptr_vv_ok_def,ptr_val_ok_def,contextTheory.mk_ptr_def,
       post_value_type_def,vyperASTTheory.expr_type_def,read_result_def,
       vyperStateTheory.return_def,ASSUME ``ann = BaseT (BytesT (Dynamic flags.rcf_max_outsize))``,
       compileEnvTheory.is_word_type_def]) >>
  `ptr_buf_ok cenv (Call ann (RawCallTarget flags) args dflt) (Var out_var) G_len s_len` by
    (mp_tac (Q.INST [`G` |-> `G_len`,`tn` |-> `tn_len`,`p` |-> `out_var`,
       `s` |-> `s_len`,`cenv` |-> `cenv`,
       `e` |-> `Call ann (RawCallTarget flags) args dflt`,
       `capacity` |-> `((flags.rcf_max_outsize+31) DIV 32)*32+32`]
       rawCallBufferPtrTheory.ptr_buf_ok_from_covers) >>
     impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
       simp_tac (srw_ss()) [ASSUME ``ann = BaseT (BytesT (Dynamic flags.rcf_max_outsize))``,
         rawCallResultLayoutPtrTheory.raw_call_bytes_type_capacity] >> decide_tac) >>
     disch_then ACCEPT_TAC) >>
  suspend "bytesFinish"
QED

Resume raw_call_positive_full_finish[bytesFinish]:
  `ee_call with gas_obs := [] = ee_call` by simp_tac (srw_ss()) [Abbr `ee_call`] >>
  `s0.vs_alloca_next <= s_len.vs_alloca_next` by
    (PURE_REWRITE_TAC [ASSUME ``s_len.vs_alloca_next = s_jump.vs_alloca_next``,
       ASSUME ``s_jump.vs_alloca_next = allocated.vs_alloca_next``] >> decide_tac) >>
  irule gas_outcome_full_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G_len`,`ee_call`,
    `INL (Value (BytesV (TAKE flags.rcf_max_outsize s_jump.vs_returndata)))`,
    `s_len`,`tn_len`] >> conj_tac
  >- (PURE_REWRITE_TAC [ASSUME ``s_jump.vs_returndata = outcome.co_returnData``] >>
      qpat_assum `!tail. eval_raw_call _ _ _ _ _ _ _ = _` mp_tac >>
      simp_tac (srw_ss()) [Abbr `ee_call`,ASSUME ``flags.rcf_revert_on_failure``,
        ASSUME ``outcome.co_success``,ASSUME ``flags.rcf_max_outsize <> 0``]) >>
  PURE_REWRITE_TAC [ASSUME ``ee_call with gas_obs := [] = ee_call``] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
    vv_post H ctx func cenv cx _ es sa sb s0 ee_call _ vv s_len`
    (qspec_then `H` (fn th => assume_tac (MATCH_MP th
      (ASSUME ``valid_horizon cx st0 H ee_call.storage_trace``)))) >>
  qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
    ghost_inv_at _ _ _ _ _ _ G_len tn_len s_len`
    (qspec_then `H` (fn th => assume_tac (MATCH_MP th
      (ASSUME ``valid_horizon cx st0 H ee_call.storage_trace``)))) >>
  conj_tac
  >- (qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
        gas_origin_ptr_path _ (t,G,tn) [] (OK s_len,G_len,tn_len)`
        (qspec_then `H` irule) >> first_assum ACCEPT_TAC) >>
  BETA_TAC >>
  qexists_tac `Value (BytesV (TAKE flags.rcf_max_outsize s_jump.vs_returndata))` >>
  simp_tac (srw_ss()) [] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `ptr_vv_ok cx _ _ vv ee_call G_len tn_len s_len` mp_tac >>
    simp_tac (srw_ss()) [ASSUME ``vv = LocatedValue ann (mk_ptr (Var out_var) LocMemory)``,
      contextTheory.vv_location_def,contextTheory.mk_ptr_def,
      ASSUME ``ptr_buf_ok cenv (Call ann (RawCallTarget flags) args dflt)
        (Var out_var) G_len s_len``] >> decide_tac
QED

Resume raw_call_positive_full_finish[tuplePost]:
  `storage_trace_domain cx st0 ee_call.storage_trace` by
    (simp_tac (srw_ss()) [Abbr `ee_call`] >> first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 (storage_trace_horizon ee_call.storage_trace)
    ee_call.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 ee_call.storage_trace`
       (mp_tac o REWRITE_RULE [storage_trace_domain_def]) >> simp_tac bool_ss []) >>
  `stmt_state_rel (storage_trace_horizon ee_call.storage_trace)
    ctx func cenv cx ee_call s_call` by
    (qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee_call s_call`
       (qspec_then `storage_trace_horizon ee_call.storage_trace` irule) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee_call s_len /\ _`
    (qspec_then `storage_trace_horizon ee_call.storage_trace`
      (fn th => strip_assume_tac (MATCH_MP th
        (ASSUME ``valid_horizon cx st0 (storage_trace_horizon ee_call.storage_trace)
          ee_call.storage_trace``)))) >>
  `alloca_inv s_call` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon ee_call.storage_trace)
       ctx func cenv cx ee_call s_call` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[stmt_state_rel_def]) >>
  `len_cs.cs_current_bb = call_cs.cs_current_bb /\
   len_cs.cs_current_insts = call_cs.cs_current_insts ++ emitted_insts call_cs len_cs` by
    (qpat_assum `(do rds <- emit_op RETURNDATASIZE []; _ od) call_cs = ((),len_cs)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[compileEnvTheory.comp_bind_def,compileEnvTheory.comp_ignore_bind_def,
       builtinSimpleTheory.compile_select_def,emitHelperTheory.emit_op_def,
       emitHelperTheory.emit_void_def,compileEnvTheory.fresh_id_def,
       compileEnvTheory.fresh_var_def,compileEnvTheory.emit_def,
       compileEnvTheory.comp_return_def,boolTheory.LET_THM,
       pairTheory.pair_case_thm,pairTheory.UNCURRY_DEF] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def,rich_listTheory.DROP_LENGTH_APPEND]) >>
  `alloca_history func s_len` by
    (qpat_assum `s_len = len_raw with vs_inst_idx := _` (fn th => PURE_REWRITE_TAC [th]) >>
     qspecl_then [`emitted_insts call_cs len_cs`,`call_cs`,`len_cs`,`s_call`,`len_raw`]
       mp_tac bodyFullUnwrapRunTheory.emitted_alloca_history >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       qpat_assum `EVERY _ (emitted_insts call_cs len_cs)`
         (fn th => POP_ASSUM_LIST (K ALL_TAC) >> mp_tac th) >>
       simp[listTheory.EVERY_MEM]) >> disch_then ACCEPT_TAC) >>
  qpat_assum `s_len = (mstore _ _ s_call) with <|vs_vars := _;vs_inst_idx := _|>`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [boolTheory.LET_THM,venomStateTheory.mstore_def,pairTheory.PAIR_EQ] o
      Q.AP_TERM `\z. (z.vs_halted,z.vs_alloca_next,z.vs_inst_idx,
        z.vs_accounts,z.vs_transient,z.vs_call_ctx,z.vs_immutables,z.vs_returndata)`) >>
  `~s_len.vs_halted /\ allocas_from lo s_len /\
   lo <= s_len.vs_alloca_next /\
   s_len.vs_inst_idx = LENGTH len_cs.cs_current_insts` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`allocas_from lo s_call`,`~s_call.vs_halted`,
        `lo <= s_call.vs_alloca_next`,
        `s_len.vs_halted = s_call.vs_halted`,
        `s_len.vs_alloca_next = s_call.vs_alloca_next`,
        `s_len.vs_allocas = s_call.vs_allocas`,
        `s_len.vs_inst_idx = LENGTH len_cs.cs_current_insts`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [ptrDisciplineTheory.allocas_from_def]) >>
  `local_ptrs_rel func cenv ee_call.scopes s_call` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon ee_call.storage_trace)
       ctx func cenv cx ee_call s_call` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[stmt_state_rel_def,state_rel_def]) >>
  `!name lb lsz. local_region cenv ee_call.scopes s_call name lb lsz ==>
    w2n (w_alloc:256 word)+32 <= lb \/ lb+lsz <= w2n w_alloc` by
    (rpt strip_tac >>
     qspecl_then [`func`,`cenv`,`ee_call.scopes`,`s_call`,`out_allocation_inst`,
       `out_var`,`w2n (w_alloc:256 word)`,
       `32+((flags.rcf_max_outsize+31) DIV 32)*32`,`name`,`lb`,`lsz`]
       mp_tac localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       PURE_REWRITE_TAC [ASSUME ``out_allocation_inst.inst_id = sc.cs_next_id``] >>
       first_assum ACCEPT_TAC) >>
     PURE_REWRITE_TAC [regions_disjoint_def] >> strip_tac >> decide_tac) >>
  `s_len.vs_memory = (mstore (w2n w_alloc)
    (n2w (MIN (LENGTH s_call.vs_returndata) flags.rcf_max_outsize)) s_call).vs_memory` by
    (qpat_assum `s_len = (mstore _ _ s_call) with <|vs_vars := _;vs_inst_idx := _|>`
       (mp_tac o SIMP_RULE (srw_ss()) [] o Q.AP_TERM `\z. z.vs_memory`) >>
     simp_tac bool_ss []) >>
  `!a k. a+k <= w2n (w_alloc:256 word) \/ w2n w_alloc+32 <= a ==>
    mem_bytes_at a k s_len.vs_memory = mem_bytes_at a k s_call.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     PURE_REWRITE_TAC [ASSUME ``s_len.vs_memory = (mstore (w2n (w_alloc:256 word))
       (n2w (MIN (LENGTH s_call.vs_returndata) flags.rcf_max_outsize)) s_call).vs_memory``] >>
     irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
     first_assum ACCEPT_TAC) >>
  `!j. j < w2n (w_alloc:256 word) \/ w2n w_alloc+32 <= j ==>
    (j IN tn_len.t_mem <=> j IN tn_call.t_mem)` by
    (rpt gen_tac >> disch_tac >>
     PURE_REWRITE_TAC [ASSUME ``tn_len.t_mem = tn_call.t_mem DIFF
       {i | w2n (w_alloc:256 word) <= i /\ i < w2n w_alloc+32}``] >>
     `~(w2n (w_alloc:256 word) <= j /\ j < w2n w_alloc+32)` by decide_tac >>
     simp_tac (srw_ss()) [ASSUME ``~(w2n (w_alloc:256 word) <= j /\ j < w2n w_alloc+32)``]) >>
  `!x. not_fresh_at sc x ==>
    lookup_var x s_len = lookup_var x s_call /\
    FLOOKUP G_len x = FLOOKUP G_call x /\
    op_taint tn_len (Var x) = op_taint tn_call (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at call_cs x` by
       (irule not_fresh_at_mono >> qexists_tac `sc` >>
        conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `!x. not_fresh_at call_cs x ==> lookup_var x s_len = _ /\ _`
       (qspec_then `x` irule) >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee_call G_len tn_len s_len` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       ghost_inv_at _ _ _ _ _ _ G_call tn_call s_call`
       (qspec_then `H` (fn th => assume_tac (MATCH_MP th
         (ASSUME ``valid_horizon cx st0 H ee_call.storage_trace``)))) >>
     `stor_taint_ok_at (DF H) tn_len s_len` by
       (qpat_assum `ghost_inv_at (DF H) lo d cenv cx ee_call G_call tn_call s_call`
          (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >>
        PURE_REWRITE_TAC [stor_taint_ok_at_def,
          ASSUME ``tn_len.t_stor = tn_call.t_stor``,
          ASSUME ``tn_len.t_trans = tn_call.t_trans``,
          ASSUME ``tn_len.t_imm = tn_call.t_imm``,
          ASSUME ``s_len.vs_accounts = s_call.vs_accounts``,
          ASSUME ``s_len.vs_transient = s_call.vs_transient``,
          ASSUME ``s_len.vs_call_ctx = s_call.vs_call_ctx``,
          ASSUME ``s_len.vs_immutables = s_call.vs_immutables``] >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss []) >>
     qspecl_then [`DF H`,`lo`,`d`,`cenv`,`cx`,`ee_call`,`G_call`,`tn_call`,
       `s_call`,`sc`,`func`,`w2n (w_alloc:256 word)`,`32`,
       `s_len`,`G_len`,`tn_len`] mp_tac
       (Q.GENL [`D`,`lo`,`d`,`cenv`,`cx`,`es`,`G`,`tn`,`s`,`sa`,`func`,
          `start`,`nb`,`z`,`H`,`tf`]
          bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_inv_at) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       rpt strip_tac >> res_tac) >> disch_then ACCEPT_TAC) >>
  suspend "tupleLengthKept"
QED

Resume raw_call_positive_full_finish[tupleLengthKept]:
  `sa.cs_next_var <= len_cs.cs_next_var /\ sc.cs_next_var <= len_cs.cs_next_var` by
    decide_tac >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G_len tn_len` by
    (irule ghost_kept_at_clean_suffix >> qexistsl_tac [`G_call`,`tn_call`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qx_gen_tac `x` >> disch_tac >>
         `not_fresh_at call_cs x` by
           (irule not_fresh_at_mono >> qexists_tac `sa` >>
            conj_tac >> first_assum ACCEPT_TAC) >>
         qpat_assum `!x. not_fresh_at call_cs x ==> lookup_var x s_len = _ /\ _`
           (qspec_then `x` mp_tac) >>
         simp_tac (srw_ss()) [ASSUME ``not_fresh_at call_cs x``] >>
         strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
     PURE_REWRITE_TAC [ASSUME ``tn_len.t_mem = tn_call.t_mem DIFF
       {i | w2n (w_alloc:256 word) <= i /\ i < w2n w_alloc+32}``] >>
     simp_tac (srw_ss()) []) >>
  `!x. not_fresh_at sc x ==>
    lookup_var x s_tuple = lookup_var x s_len /\
    FLOOKUP G_tuple x = FLOOKUP G_len x /\
    op_taint tn_tuple (Var x) = op_taint tn_len (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at len_cs x` by
       (irule not_fresh_at_mono >> qexists_tac `sc` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `!x. not_fresh_at len_cs x ==> lookup_var x s_tuple = _ /\ _`
       (qspec_then `x` irule) >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee_call s_tuple /\
    ghost_inv_at (DF H) lo d cenv cx ee_call G_tuple tn_tuple s_tuple` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee_call s_len /\ _`
       (qspec_then `H` (fn th => strip_assume_tac (MATCH_MP th
         (ASSUME ``valid_horizon cx st0 H ee_call.storage_trace``)))) >>
     qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       ghost_inv_at _ _ _ _ _ _ G_len tn_len s_len`
       (qspec_then `H` (fn th => assume_tac (MATCH_MP th
         (ASSUME ``valid_horizon cx st0 H ee_call.storage_trace``)))) >>
     conj_tac
     >- (qpat_assum `!H'. stmt_state_rel H' ctx func cenv cx ee_call s_len ==>
           stmt_state_rel H' ctx func cenv cx ee_call s_tuple`
           (qspec_then `H` irule) >> first_assum ACCEPT_TAC) >>
     mp_tac (Q.INST [`D` |-> `DF (H:(bool # 256 word # type_value) list # num list)`,
       `H` |-> `H:(bool # 256 word # type_value) list # num list`,
       `sa` |-> `sc`,`es` |-> `ee_call`,`s` |-> `s_len`,`t` |-> `s_tuple`,
       `G` |-> `G_len`,`tn` |-> `tn_len`,`G'` |-> `G_tuple`,`tn'` |-> `tn_tuple`,
       `e` |-> `w2n (tuple_word:256 word)+(64+((flags.rcf_max_outsize+31) DIV 32)*32)`]
       (INST_TYPE [alpha |-> ``:256``] alloc_buffer_ghost_inv_at)) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       rpt strip_tac >> res_tac) >> disch_then ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G_tuple tn_tuple` by
    (mp_tac (Q.INST [`es0` |-> `es`,`sk` |-> `sa`,`s` |-> `s_len`,
       `G` |-> `G_len`,`tn` |-> `tn_len`,`G'` |-> `G_tuple`,`tn'` |-> `tn_tuple`,
       `e` |-> `w2n (tuple_word:256 word)+(64+((flags.rcf_max_outsize+31) DIV 32)*32)`]
       (INST_TYPE [alpha |-> ``:num # num``] alloc_buffer_ghost_kept_at)) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >|
       [qx_gen_tac `x` >> disch_tac >>
          `not_fresh_at len_cs x` by
            (irule not_fresh_at_mono >> qexists_tac `sa` >>
             conj_tac >> first_assum ACCEPT_TAC) >>
          qpat_assum `!x. not_fresh_at len_cs x ==> lookup_var x s_tuple = _ /\ _`
            (qspec_then `x` mp_tac) >>
          simp_tac (srw_ss()) [ASSUME ``not_fresh_at len_cs x``] >>
          strip_tac >> conj_tac >> first_assum ACCEPT_TAC,
        qx_genl_tac [`old_id`,`old_b`,`old_n`] >> strip_tac >>
          `old_b+old_n <= t.vs_alloca_next` by
            (qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) ==> _`
              (qspecl_then [`old_id`,`old_b`,`old_n`] mp_tac) >>
             impl_tac >- first_assum ACCEPT_TAC >> disch_then ACCEPT_TAC) >>
          decide_tac,
        qx_genl_tac [`old_name`,`old_b`,`old_n`] >> disch_tac >>
          `old_b+old_n <= t.vs_alloca_next` by
            (qpat_assum `!name b sz. local_region cenv es.scopes s0 name b sz ==> _`
              (qspecl_then [`old_name`,`old_b`,`old_n`] mp_tac) >>
             impl_tac >- first_assum ACCEPT_TAC >> disch_then ACCEPT_TAC) >>
          decide_tac]) >> disch_then ACCEPT_TAC) >>
  suspend "tupleCopyFrames"
QED

Resume raw_call_positive_full_finish[tupleCopyFrames]:
  qpat_assum `z_tuple = (mcopy _ _ _ (mstore _ _ s_tuple))
    with <|vs_vars := _;vs_inst_idx := _|>`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [boolTheory.LET_THM,venomExecSemanticsTheory.mcopy_def,
       venomStateTheory.mstore_def,venomStateTheory.write_memory_with_expansion_def,
       pairTheory.PAIR_EQ] o
      Q.AP_TERM `\z. (z.vs_halted,z.vs_alloca_next,z.vs_allocas,z.vs_inst_idx,
        z.vs_accounts,z.vs_transient,z.vs_call_ctx,z.vs_immutables)`) >>
  `z_tuple.vs_memory =
    (mcopy (w2n tuple_word+32) (w2n w_alloc)
      (32+((flags.rcf_max_outsize+31) DIV 32)*32)
      (mstore (w2n tuple_word) (bool_to_word outcome.co_success) s_tuple)).vs_memory` by
    (qpat_assum `z_tuple = (mcopy _ _ _ (mstore _ _ s_tuple))
       with <|vs_vars := _;vs_inst_idx := _|>`
       (mp_tac o SIMP_RULE (srw_ss()) [] o Q.AP_TERM `\z. z.vs_memory`) >>
     simp_tac (srw_ss()) []) >>
  `exprSimStorageCopy$copy_static z_tuple = exprSimStorageCopy$copy_static s_tuple` by
    (qpat_assum `z_tuple = (mcopy _ _ _ (mstore _ _ s_tuple))
       with <|vs_vars := _;vs_inst_idx := _|>`
       (mp_tac o Q.AP_TERM `exprSimStorageCopy$copy_static`) >>
     simp_tac (srw_ss()) [exprSimStorageCopyTheory.copy_static_def,
       venomExecSemanticsTheory.mcopy_def,venomStateTheory.mstore_def,
       venomStateTheory.write_memory_with_expansion_def,boolTheory.LET_THM]) >>
  `LENGTH s_tuple.vs_memory <= LENGTH z_tuple.vs_memory` by
    (PURE_REWRITE_TAC [ASSUME ``z_tuple.vs_memory =
       (mcopy (w2n (tuple_word:256 word)+32) (w2n (w_alloc:256 word))
         (32+((flags.rcf_max_outsize+31) DIV 32)*32)
         (mstore (w2n tuple_word) (bool_to_word outcome.co_success) s_tuple)).vs_memory``] >>
     irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists_tac `LENGTH (mstore (w2n tuple_word)
       (bool_to_word outcome.co_success) s_tuple).vs_memory` >> conj_tac
     >- (irule exprSimAbiEncodeMemoryLengthTheory.abi_encode_mstore_memory_length) >>
     irule exprSimAbiEncodeMemoryLengthTheory.abi_encode_mcopy_memory_length) >>
  `!a k. a+k <= w2n (tuple_word:256 word) \/
    w2n tuple_word+(64+((flags.rcf_max_outsize+31) DIV 32)*32) <= a ==>
    mem_bytes_at a k z_tuple.vs_memory = mem_bytes_at a k s_tuple.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     PURE_REWRITE_TAC [ASSUME ``z_tuple.vs_memory =
       (mcopy (w2n (tuple_word:256 word)+32) (w2n (w_alloc:256 word))
         (32+((flags.rcf_max_outsize+31) DIV 32)*32)
         (mstore (w2n tuple_word) (bool_to_word outcome.co_success) s_tuple)).vs_memory``] >>
     irule EQ_TRANS >> qexists_tac
       `mem_bytes_at a k (mstore (w2n tuple_word)
         (bool_to_word outcome.co_success) s_tuple).vs_memory` >> conj_tac
     >- (irule valueEncodingPropsTheory.mcopy_mem_bytes_at_disjoint >> decide_tac) >>
     irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `!j. j < w2n (tuple_word:256 word) \/
    w2n tuple_word+(64+((flags.rcf_max_outsize+31) DIV 32)*32) <= j ==>
    (j IN un_tuple.t_mem <=> j IN tn_tuple.t_mem)` by
    (qx_gen_tac `j` >> disch_tac >>
     `~(w2n (tuple_word:256 word) <= j /\ j < w2n tuple_word+32) /\
      ~(w2n tuple_word+32 <= j /\
        j < w2n tuple_word+32+(32+((flags.rcf_max_outsize+31) DIV 32)*32))` by
       decide_tac >>
     `!i. i < 32+((flags.rcf_max_outsize+31) DIV 32)*32 ==>
       j <> w2n (tuple_word:256 word)+32+i` by (rpt strip_tac >> decide_tac) >>
     qpat_assum `un_tuple.t_mem = _` (fn th => PURE_REWRITE_TAC [th]) >>
     map_every (fn q => qpat_assum q mp_tac)
       [`~(w2n (tuple_word:256 word) <= j /\ j < w2n tuple_word+32)`,
        `~(w2n (tuple_word:256 word)+32 <= j /\
          j < w2n tuple_word+32+(32+((flags.rcf_max_outsize+31) DIV 32)*32))`,
        `!i. i < 32+((flags.rcf_max_outsize+31) DIV 32)*32 ==> j <> _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [pred_setTheory.IN_UNION,pred_setTheory.IN_DIFF,
       pred_setTheory.GSPECIFICATION] >> metis_tac[]) >>
  suspend "tupleCopyState"
QED

Resume raw_call_positive_full_finish[tupleCopyState]:
  qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee_call s_tuple /\ _`
    (qspec_then `storage_trace_horizon ee_call.storage_trace`
      (fn th => strip_assume_tac (MATCH_MP th
        (ASSUME ``valid_horizon cx st0 (storage_trace_horizon ee_call.storage_trace)
          ee_call.storage_trace``)))) >>
  `alloca_inv s_tuple /\ local_ptrs_rel func cenv ee_call.scopes s_tuple` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon ee_call.storage_trace)
       ctx func cenv cx ee_call s_tuple` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[stmt_state_rel_def,state_rel_def]) >>
  `sc.cs_next_var <= tuple_alloc_cs.cs_next_var` by
    (qpat_assum `ci_mono len_cs tuple_alloc_cs` mp_tac >>
     qpat_assum `sc.cs_next_var <= len_cs.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ci_mono_def] >> rpt strip_tac >> decide_tac) >>
  `!x. not_fresh_at sc x ==> not_fresh_at tuple_alloc_cs x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sc` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at tuple_alloc_cs x ==> lookup_var x z_tuple = lookup_var x s_tuple` by
    (qx_gen_tac `x` >> disch_tac >>
     qpat_assum `!x. not_fresh_at tuple_alloc_cs x ==> lookup_var x z_tuple = _ /\ _`
       (qspec_then `x` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> first_assum ACCEPT_TAC) >>
  qspecl_then [`64+((flags.rcf_max_outsize+31) DIV 32)*32`,`len_cs`,
    `tuple_alloc_cs`,`tuple_buf`,`func`] mp_tac exprSimAllocTheory.buffer_alloc_code >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> disch_then assume_tac >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee_call z_tuple` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee_call s_tuple /\ _`
       (qspec_then `H` (fn th => strip_assume_tac (MATCH_MP th
         (ASSUME ``valid_horizon cx st0 H ee_call.storage_trace``)))) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx ee_call s_tuple`
       (fn rel => mp_tac (Q.INST [`sa` |-> `sc`,`sh` |-> `tuple_alloc_cs`,
         `t` |-> `z_tuple`,`b` |-> `w2n (tuple_word:256 word)`,
         `n` |-> `64+((flags.rcf_max_outsize+31) DIV 32)*32`,
         `aid` |-> `len_cs.cs_next_id`,
         `p` |-> `STRING #"%" (toString len_cs.cs_next_var)`]
         (PART_MATCH (find_term (fn tm =>
           same_const (fst (strip_comb tm)) ``stmt_state_rel``))
           bodyPtrMakeArrayCopyStateFrameTheory.literal_copy_window_stmt_state_rel
           (concl rel)))) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  `sb.cs_current_bb = tuple_alloc_cs.cs_current_bb /\
   sb.cs_current_insts = tuple_alloc_cs.cs_current_insts ++ emitted_insts tuple_alloc_cs sb` by
    (qpat_assum `(do emit_void MSTORE [Var tuple_var;Var q_call]; _ od)
       tuple_alloc_cs = ((),sb)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[compileEnvTheory.comp_bind_def,compileEnvTheory.comp_ignore_bind_def,
       emitHelperTheory.emit_op_def,emitHelperTheory.emit_void_def,
       compileEnvTheory.fresh_id_def,compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def,compileEnvTheory.comp_return_def,boolTheory.LET_THM,
       pairTheory.pair_case_thm,pairTheory.UNCURRY_DEF] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def,rich_listTheory.DROP_LENGTH_APPEND]) >>
  `alloca_history func z_tuple` by
    (qpat_assum `z_tuple = tuple_raw with vs_inst_idx := _`
       (fn th => PURE_REWRITE_TAC [th]) >>
     qspecl_then [`emitted_insts tuple_alloc_cs sb`,`tuple_alloc_cs`,`sb`,
       `s_tuple`,`tuple_raw`] mp_tac bodyFullUnwrapRunTheory.emitted_alloca_history >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       qpat_assum `EVERY _ (emitted_insts tuple_alloc_cs sb)`
         (fn th => POP_ASSUM_LIST (K ALL_TAC) >> mp_tac th) >>
       simp[listTheory.EVERY_MEM]) >> disch_then ACCEPT_TAC) >>
  `~z_tuple.vs_halted /\ allocas_from lo z_tuple /\
   lo <= z_tuple.vs_alloca_next /\
   z_tuple.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`~s_tuple.vs_halted`,`allocas_from lo s_tuple`,
        `lo <= s_len.vs_alloca_next`,`s_len.vs_alloca_next <= s_tuple.vs_alloca_next`,
        `z_tuple.vs_halted = s_tuple.vs_halted`,
        `z_tuple.vs_alloca_next = s_tuple.vs_alloca_next`,
        `z_tuple.vs_allocas = s_tuple.vs_allocas`,
        `z_tuple.vs_inst_idx = LENGTH sb.cs_current_insts`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [ptrDisciplineTheory.allocas_from_def] >>
     rpt strip_tac >> res_tac >> decide_tac) >>
  `lo <= w2n (tuple_word:256 word)` by
    (qpat_assum `allocas_from lo s_tuple`
       (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
     disch_then (fn th => qpat_assum
       `FLOOKUP s_tuple.vs_allocas len_cs.cs_next_id = SOME _`
       (ACCEPT_TAC o MATCH_MP (Q.SPECL [`len_cs.cs_next_id`,
         `w2n (tuple_word:256 word)`,`64+((flags.rcf_max_outsize+31) DIV 32)*32`] th)))) >>
  suspend "tupleCopyGhost"
QED

Resume raw_call_positive_full_finish[tupleCopyGhost]:
  `!name b len. local_region cenv ee_call.scopes s_tuple name b len ==>
    w2n (tuple_word:256 word)+(64+((flags.rcf_max_outsize+31) DIV 32)*32) <= b \/
    b+len <= w2n tuple_word` by
    (qpat_assum `!name b len. local_region cenv ee_call.scopes s_tuple name b len ==>
       regions_disjoint _ _ b len` mp_tac >>
     PURE_REWRITE_TAC [regions_disjoint_def] >> simp_tac (srw_ss()) []) >>
  `!x. not_fresh_at sc x ==>
    lookup_var x z_tuple = lookup_var x s_tuple /\
    FLOOKUP J_tuple x = FLOOKUP G_tuple x /\
    op_taint un_tuple (Var x) = op_taint tn_tuple (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at tuple_alloc_cs x` by
       (qpat_assum `!x. not_fresh_at sc x ==> not_fresh_at tuple_alloc_cs x`
         (qspec_then `x` irule) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!x. not_fresh_at tuple_alloc_cs x ==> lookup_var x z_tuple = _ /\ _`
       (qspec_then `x` irule) >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee_call J_tuple un_tuple z_tuple` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee_call s_tuple /\ _`
       (qspec_then `H` (fn th => strip_assume_tac (MATCH_MP th
         (ASSUME ``valid_horizon cx st0 H ee_call.storage_trace``)))) >>
     `stor_taint_ok_at (DF H) un_tuple z_tuple` by
       (qpat_assum `ghost_inv_at (DF H) lo d cenv cx ee_call G_tuple tn_tuple s_tuple`
          (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >>
        PURE_REWRITE_TAC [stor_taint_ok_at_def,
          ASSUME ``un_tuple.t_stor = tn_tuple.t_stor``,
          ASSUME ``un_tuple.t_trans = tn_tuple.t_trans``,
          ASSUME ``un_tuple.t_imm = tn_tuple.t_imm``,
          ASSUME ``z_tuple.vs_accounts = s_tuple.vs_accounts``,
          ASSUME ``z_tuple.vs_transient = s_tuple.vs_transient``,
          ASSUME ``z_tuple.vs_call_ctx = s_tuple.vs_call_ctx``,
          ASSUME ``z_tuple.vs_immutables = s_tuple.vs_immutables``] >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss []) >>
     qspecl_then [`DF H`,`lo`,`d`,`cenv`,`cx`,`ee_call`,`G_tuple`,`tn_tuple`,
       `s_tuple`,`sc`,`func`,`w2n (tuple_word:256 word)`,
       `64+((flags.rcf_max_outsize+31) DIV 32)*32`,`z_tuple`,`J_tuple`,`un_tuple`]
       mp_tac (Q.GENL [`D`,`lo`,`d`,`cenv`,`cx`,`es`,`G`,`tn`,`s`,`sa`,`func`,
         `start`,`nb`,`z`,`H`,`tf`]
         bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_inv_at) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       rpt strip_tac >> res_tac) >> disch_then ACCEPT_TAC) >>
  suspend "tupleRetained"
QED

Resume raw_call_positive_full_finish[tupleRetained]:
  `len_cs.cs_next_var <= tuple_alloc_cs.cs_next_var` by
    (qpat_assum `ci_mono len_cs tuple_alloc_cs`
       (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss []) >>
  `!x. not_fresh_at len_cs x ==>
    lookup_var x z_tuple = lookup_var x s_len` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at tuple_alloc_cs x` by
       (irule not_fresh_at_mono >> qexists_tac `len_cs` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `!x. not_fresh_at len_cs x ==> lookup_var x s_tuple = _ /\ _`
       (qspec_then `x` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     qpat_assum `!x. not_fresh_at tuple_alloc_cs x ==> lookup_var x z_tuple = lookup_var x s_tuple`
       (qspec_then `x` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     PURE_REWRITE_TAC [ASSUME ``lookup_var x s_tuple = lookup_var x s_len``] >>
     simp_tac (srw_ss()) []) >>
  `!aid entry. FLOOKUP s_len.vs_allocas aid = SOME entry ==>
    FLOOKUP z_tuple.vs_allocas aid = SOME entry` by
    (rpt gen_tac >> disch_tac >>
     PURE_REWRITE_TAC [ASSUME ``z_tuple.vs_allocas = s_tuple.vs_allocas``] >>
     qpat_assum `!aid e. FLOOKUP s_len.vs_allocas aid = SOME e ==> _`
       (qspecl_then [`aid`,`entry`] mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> disch_then ACCEPT_TAC) >>
  `!aid a n. aid < len_cs.cs_next_id /\
    FLOOKUP s_len.vs_allocas aid = SOME (a,n) ==>
    mem_bytes_at a n z_tuple.vs_memory = mem_bytes_at a n s_len.vs_memory` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!aid b len. aid < len_cs.cs_next_id /\
       FLOOKUP s_len.vs_allocas aid = SOME (b,len) ==> _`
       (qspecl_then [`aid`,`a`,`n`] mp_tac) >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
     PURE_REWRITE_TAC [regions_disjoint_def] >> strip_tac >>
     PURE_REWRITE_TAC [GSYM (ASSUME ``s_tuple.vs_memory = s_len.vs_memory``)] >>
     qpat_assum `!a k. _ ==> mem_bytes_at a k z_tuple.vs_memory = _` irule >>
     decide_tac) >>
  `!name a n. local_region cenv ee_call.scopes s_len name a n ==>
    local_region cenv ee_call.scopes s_tuple name a n` by
    (rpt gen_tac >> disch_tac >>
     qspecl_then [`cenv`,`ee_call.scopes`,`len_cs`,`ee_call.scopes`,
       `s_len`,`s_tuple`,`name`,`a`,`n`] mp_tac exprSimPropsTheory.local_region_frame_fwd >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
       >- simp_tac (srw_ss()) [] >>
       qx_genl_tac [`x`,`word`] >> strip_tac >>
       qpat_assum `!x. not_fresh_at len_cs x ==> lookup_var x s_tuple = _ /\ _`
         (qspec_then `x` mp_tac) >>
       impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
       PURE_REWRITE_TAC [ASSUME ``lookup_var x s_tuple = lookup_var x s_len``] >>
       first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  `!name a n. local_region cenv ee_call.scopes s_len name a n ==>
    mem_bytes_at a n z_tuple.vs_memory = mem_bytes_at a n s_len.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     `local_region cenv ee_call.scopes s_tuple name a n` by
       (qpat_assum `!name a n. local_region cenv ee_call.scopes s_len name a n ==> _`
         (qspecl_then [`name`,`a`,`n`] mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> disch_then ACCEPT_TAC) >>
     qpat_assum `!name b len. local_region cenv ee_call.scopes s_tuple name b len ==>
       regions_disjoint _ _ b len`
       (qspecl_then [`name`,`a`,`n`] mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     PURE_REWRITE_TAC [regions_disjoint_def] >> strip_tac >>
     PURE_REWRITE_TAC [GSYM (ASSUME ``s_tuple.vs_memory = s_len.vs_memory``)] >>
     qpat_assum `!a k. _ ==> mem_bytes_at a k z_tuple.vs_memory = _` irule >> decide_tac) >>
  `wb_frame cenv es ee_call sa s0 z_tuple` by
    (mp_tac (Q.INST [`s` |-> `s_len`,`t` |-> `z_tuple`,`sm` |-> `len_cs`,
       `scopes` |-> `ee_call.scopes`,`es'` |-> `ee_call`] wb_frame_allocating_tail) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
     disch_then ACCEPT_TAC) >>
  suspend "tupleKept"
QED

Resume raw_call_positive_full_finish[tupleKept]:
  `!x. not_fresh_at sa x ==>
    FLOOKUP J_tuple x = FLOOKUP G_tuple x /\
    op_taint un_tuple (Var x) = op_taint tn_tuple (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at sc x` by
       (qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sc x`
          (qspec_then `x` irule) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!x. not_fresh_at sc x ==> lookup_var x z_tuple = _ /\ _`
       (qspec_then `x` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp_tac bool_ss []) >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < sa.cs_next_id ==>
    regions_disjoint (w2n (tuple_word:256 word))
      (64+((flags.rcf_max_outsize+31) DIV 32)*32) off sz` by
    (rpt gen_tac >> strip_tac >>
     `FLOOKUP s_len.vs_allocas aid = SOME (off,sz)` by
       (qpat_assum `wb_frame cenv es ee_call sa s0 s_len`
          (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [wb_frame_def]) >>
        disch_then (qspecl_then [`aid`,`(off,sz)`] mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> disch_then ACCEPT_TAC) >>
     qpat_assum `!aid b len. aid < len_cs.cs_next_id /\
       FLOOKUP s_len.vs_allocas aid = SOME (b,len) ==> regions_disjoint _ _ b len`
       (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
     impl_tac >- (conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `!name off sz. local_region cenv es.scopes s0 name off sz ==>
    local_region cenv ee_call.scopes s_len name off sz` by
    (rpt gen_tac >> disch_tac >>
     qspecl_then [`cenv`,`es.scopes`,`sa`,`ee_call.scopes`,
       `s0`,`s_len`,`name`,`off`,`sz`] mp_tac exprSimPropsTheory.local_region_frame_fwd >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       qpat_assum `wb_frame cenv es ee_call sa s0 s_len`
         (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [wb_frame_def])) >>
     disch_then ACCEPT_TAC) >>
  `!name off sz. local_region cenv es.scopes s0 name off sz ==>
    regions_disjoint (w2n (tuple_word:256 word))
      (64+((flags.rcf_max_outsize+31) DIV 32)*32) off sz` by
    (rpt gen_tac >> disch_tac >>
     `local_region cenv ee_call.scopes s_len name off sz` by
       (qpat_assum `!name off sz. local_region cenv es.scopes s0 name off sz ==> _`
         (qspecl_then [`name`,`off`,`sz`] mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> disch_then ACCEPT_TAC) >>
     `local_region cenv ee_call.scopes s_tuple name off sz` by
       (qpat_assum `!name a n. local_region cenv ee_call.scopes s_len name a n ==>
          local_region cenv ee_call.scopes s_tuple name a n`
         (qspecl_then [`name`,`off`,`sz`] mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> disch_then ACCEPT_TAC) >>
     qpat_assum `!name b len. local_region cenv ee_call.scopes s_tuple name b len ==>
       regions_disjoint _ _ b len`
       (qspecl_then [`name`,`off`,`sz`] mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> disch_then ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 J_tuple un_tuple` by
    (mp_tac (Q.INST [`Gi` |-> `G0`,`ti` |-> `tn0`,
       `G` |-> `G_tuple`,`tn` |-> `tn_tuple`,
       `H` |-> `J_tuple`,`tf` |-> `un_tuple`]
       (INST_TYPE [alpha |-> ``:num # num``]
         bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_kept_at)) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >|
       [qx_genl_tac [`aid`,`off`,`sz`,`i`] >> strip_tac >>
          qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
            aid < sa.cs_next_id ==> regions_disjoint _ _ off sz`
            (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
          impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
          PURE_REWRITE_TAC [regions_disjoint_def] >> disch_tac >>
          qpat_assum `!j. _ ==> (j IN un_tuple.t_mem <=> j IN tn_tuple.t_mem)`
            (qspec_then `i` mp_tac) >>
          impl_tac >- decide_tac >> simp_tac bool_ss [ASSUME ``i IN un_tuple.t_mem``],
        qx_genl_tac [`name`,`off`,`sz`,`i`] >> strip_tac >>
          qpat_assum `!name off sz. local_region cenv es.scopes s0 name off sz ==>
            regions_disjoint _ _ off sz`
            (qspecl_then [`name`,`off`,`sz`] mp_tac) >>
          impl_tac >- first_assum ACCEPT_TAC >>
          PURE_REWRITE_TAC [regions_disjoint_def] >> disch_tac >>
          qpat_assum `!j. _ ==> (j IN un_tuple.t_mem <=> j IN tn_tuple.t_mem)`
            (qspec_then `i` mp_tac) >>
          impl_tac >- decide_tac >> simp_tac bool_ss [ASSUME ``i IN un_tuple.t_mem``],
        qx_gen_tac `i` >> strip_tac >>
          qpat_assum `!j. _ ==> (j IN un_tuple.t_mem <=> j IN tn_tuple.t_mem)`
            (qspec_then `i` mp_tac) >>
          impl_tac >- decide_tac >> simp_tac bool_ss [ASSUME ``i IN un_tuple.t_mem``]]) >>
     disch_then ACCEPT_TAC) >>
  suspend "tupleValue"
QED

Resume raw_call_positive_full_finish[tupleValue]:
  `lookup_var tuple_var z_tuple = SOME tuple_word` by
    (qpat_assum `!x. not_fresh_at tuple_alloc_cs x ==> lookup_var x z_tuple = lookup_var x s_tuple`
       (qspec_then `tuple_var` mp_tac) >>
     simp_tac (srw_ss()) [ASSUME ``not_fresh_at tuple_alloc_cs tuple_var``,
       ASSUME ``lookup_var tuple_var s_tuple = SOME (tuple_word:256 word)``]) >>
  `val_wf (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic flags.rcf_max_outsize))])
    (ArrayV (TupleV [BoolV outcome.co_success;
      BytesV (TAKE flags.rcf_max_outsize s_call.vs_returndata)]))` by
    (POP_ASSUM_LIST (K ALL_TAC) >>
     qspec_then `flags.rcf_max_outsize` mp_tac exprSimPropsTheory.le_word_size_mul >>
     simp[valueEncodingDefsTheory.val_wf_def,valueEncodingTheory.type_memory_size_def,
       listTheory.LENGTH_TAKE_EQ] >> decide_tac) >>
  `val_in_memory (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic flags.rcf_max_outsize))])
    (ArrayV (TupleV [BoolV outcome.co_success;
      BytesV (TAKE flags.rcf_max_outsize s_call.vs_returndata)]))
    (w2n tuple_word) z_tuple.vs_memory` by
    (qpat_assum `!mem. mem_agree_outside un_tuple.t_mem z_tuple.vs_memory mem ==> _`
       (qspec_then `z_tuple.vs_memory` irule) >>
     simp_tac (srw_ss()) [mem_agree_outside_def]) >>
  `!name lb lsz. local_region cenv ee_call.scopes z_tuple name lb lsz ==>
    w2n (tuple_word:256 word)+(64+((flags.rcf_max_outsize+31) DIV 32)*32) <= lb \/
    lb+lsz <= w2n tuple_word` by
    (rpt gen_tac >> disch_tac >>
     `local_region cenv ee_call.scopes s_tuple name lb lsz` by
       (qspecl_then [`func`,`cenv`,`ee_call.scopes`,`s_tuple`,`sc`,
         `ee_call.scopes`,`z_tuple`,`name`,`lb`,`lsz`] mp_tac
         exprSimPropsTheory.local_region_frame >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
          >- simp_tac (srw_ss()) [] >>
          qx_genl_tac [`x`,`word`] >> strip_tac >>
          qpat_assum `!x. not_fresh_at sc x ==> lookup_var x z_tuple = _ /\ _`
            (qspec_then `x` mp_tac) >>
          impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
          PURE_REWRITE_TAC [ASSUME ``lookup_var x z_tuple = lookup_var x s_tuple``] >>
          first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
     qpat_assum `!name b len. local_region cenv ee_call.scopes s_tuple name b len ==>
       w2n (tuple_word:256 word)+(64+((flags.rcf_max_outsize+31) DIV 32)*32) <= b \/
       b+len <= w2n tuple_word`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> disch_then ACCEPT_TAC) >>
  `val_store_size (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic flags.rcf_max_outsize))])
    (ArrayV (TupleV [BoolV outcome.co_success;
      BytesV (TAKE flags.rcf_max_outsize s_call.vs_returndata)])) <=
    64+((flags.rcf_max_outsize+31) DIV 32)*32` by
    (irule raw_call_tuple_store_capacity >> POP_ASSUM_LIST (K ALL_TAC) >>
     rw[listTheory.LENGTH_TAKE_EQ] >> decide_tac) >>
  suspend "tupleValuePost"
QED

Resume raw_call_positive_full_finish[tupleValuePost]:
  `result = Var tuple_var` by
    (qpat_assum `result = tuple_buf.buf_operand` (fn result_eq =>
       qpat_assum `tuple_buf.buf_operand = Var tuple_var` (ACCEPT_TAC o TRANS result_eq))) >>
  `vv = LocatedValue ann (mk_ptr (Var tuple_var) LocMemory)` by
    simp_tac (srw_ss()) [ASSUME ``vv = (if flags.rcf_max_outsize = 0 then
      StackValue ann result else LocatedValue ann (mk_ptr result LocMemory))``,
      ASSUME ``flags.rcf_max_outsize <> 0``,ASSUME ``result = Var tuple_var``] >>
  `type_slot_size (BaseTV (BytesT (Dynamic flags.rcf_max_outsize))) <= dimword(:256) /\
   type_slot_size (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic flags.rcf_max_outsize))]) <= dimword(:256)` by
    (qpat_assum `64+((flags.rcf_max_outsize+31) DIV 32)*32 < dimword(:256)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [vyperValueTheory.type_slot_size_def,
       vfmConstantsTheory.word_size_def] >> decide_tac) >>
  `~is_word_type ann` by
    simp_tac (srw_ss()) [ASSUME ``ann = TupleT [BaseT BoolT;
      BaseT (BytesT (Dynamic flags.rcf_max_outsize))]``,compileEnvTheory.is_word_type_def] >>
  `evaluate_type (get_tenv cx) ann =
    SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic flags.rcf_max_outsize))])` by
    simp_tac (srw_ss()) [ASSUME ``ann = TupleT [BaseT BoolT;
      BaseT (BytesT (Dynamic flags.rcf_max_outsize))]``,
      vyperValueTheory.evaluate_type_def,boolTheory.LET_THM,
      ASSUME ``flags.rcf_max_outsize < dimword(:256)``,
      ASSUME ``type_slot_size (BaseTV (BytesT (Dynamic flags.rcf_max_outsize))) <= dimword(:256)``,
      ASSUME ``type_slot_size (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic flags.rcf_max_outsize))]) <= dimword(:256)``] >>
  `val_footprint (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic flags.rcf_max_outsize))])
    (ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE flags.rcf_max_outsize s_call.vs_returndata)])) <=
    64+((flags.rcf_max_outsize+31) DIV 32)*32` by
    (irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists_tac `val_store_size
       (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic flags.rcf_max_outsize))])
       (ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE flags.rcf_max_outsize s_call.vs_returndata)]))` >>
     conj_tac >- ACCEPT_TAC (Q.SPECL
       [`TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic flags.rcf_max_outsize))]`,
        `ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE flags.rcf_max_outsize s_call.vs_returndata)])`]
       exprSimPropsTheory.val_footprint_le_store_size) >> first_assum ACCEPT_TAC) >>
  `tuple_alloc_cs.cs_next_id = len_cs.cs_next_id+1` by
    (qpat_assum `compile_alloc_buffer _ len_cs = (tuple_buf,tuple_alloc_cs)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[contextTheory.compile_alloc_buffer_def,emitHelperTheory.emit_op_def,
       compileEnvTheory.comp_bind_def,compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def,
       compileEnvTheory.fresh_var_def,compileEnvTheory.fresh_id_def,
       compileEnvTheory.emit_def,boolTheory.LET_THM,pairTheory.pair_case_thm] >>
     rpt strip_tac >> gvs[]) >>
  `len_cs.cs_next_id < sb.cs_next_id` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`tuple_alloc_cs.cs_next_id = len_cs.cs_next_id+1`,
        `ci_mono tuple_alloc_cs tuple_store_cs`,`ci_mono tuple_store_cs tuple_add_cs`,
        `ci_mono tuple_add_cs sb`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ci_mono_def] >> rpt strip_tac >> decide_tac) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    vv_post H ctx func cenv cx (Call ann (RawCallTarget flags) args dflt)
      es sa sb s0 ee_call
      (Value (ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE flags.rcf_max_outsize s_call.vs_returndata)]))) vv z_tuple` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee_call z_tuple`
       (qspec_then `H` (fn th => strip_assume_tac (MATCH_MP th
         (ASSUME ``valid_horizon cx st0 H ee_call.storage_trace``)))) >>
     `storage_well_formed_on cx ee_call (FST H)` by
       (qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
         storage_well_formed_on cx ee_call (FST H)`
         (qspec_then `H` irule) >> first_assum ACCEPT_TAC) >>
     PURE_REWRITE_TAC [ASSUME ``vv = LocatedValue ann (mk_ptr (Var tuple_var) LocMemory)``] >>
     qpat_assum `stmt_state_rel H ctx func cenv cx ee_call z_tuple`
       (fn rel => mp_tac (Q.INST
         [`e` |-> `Call ann (RawCallTarget flags) args dflt`,
          `es` |-> `es`,`sa` |-> `sa`,`sb` |-> `sb`,`s0` |-> `s0`,
          `tv` |-> `TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic flags.rcf_max_outsize))]`,
          `v` |-> `ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE flags.rcf_max_outsize s_call.vs_returndata)])`,
          `p` |-> `mk_ptr (Var tuple_var) LocMemory`,`w` |-> `tuple_word`,
          `aid` |-> `len_cs.cs_next_id`,`b` |-> `w2n (tuple_word:256 word)`,
          `sz` |-> `64+((flags.rcf_max_outsize+31) DIV 32)*32`]
         (PART_MATCH (find_term (fn tm =>
           same_const (fst (strip_comb tm)) ``stmt_state_rel``))
           exprSimHashTheory.vv_post_allocated_memory_intro (concl rel)))) >>
     impl_tac
     >- (simp_tac (srw_ss()) [post_value_type_def,vyperASTTheory.expr_type_def,
           ASSUME ``~is_word_type ann``,
           ASSUME ``evaluate_type (get_tenv cx) ann =
             SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic flags.rcf_max_outsize))])``,
           contextTheory.mk_ptr_def,eval_operand_def,
           loweringPostsTheory.expr_has_effect_thm] >>
         PURE_REWRITE_TAC [ASSUME ``z_tuple.vs_allocas = s_tuple.vs_allocas``] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
     simp_tac (srw_ss()) [vyperASTTheory.expr_type_def]) >>
  suspend "tupleCapacity"
QED

Resume raw_call_positive_full_finish[tupleCapacity]:
  `w2n (tuple_word:256 word)+64+((flags.rcf_max_outsize+31) DIV 32)*32 <=
    z_tuple.vs_alloca_next` by
    (PURE_REWRITE_TAC [ASSUME ``z_tuple.vs_alloca_next = s_tuple.vs_alloca_next``] >> decide_tac) >>
  `vv_store_bound cx (expr_type (Call ann (RawCallTarget flags) args dflt))
    (lowered_value_type cenv (Call ann (RawCallTarget flags) args dflt)) ee_call
    (Value (ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE flags.rcf_max_outsize s_call.vs_returndata)]))) vv z_tuple` by
    (qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
       vv_post H ctx func cenv cx _ es sa sb s0 ee_call _ vv z_tuple`
       (qspec_then `storage_trace_horizon ee_call.storage_trace`
         (fn th => assume_tac (REWRITE_RULE
           [ASSUME ``vv = LocatedValue ann (mk_ptr (Var tuple_var) LocMemory)``]
           (MATCH_MP th (ASSUME ``valid_horizon cx st0
             (storage_trace_horizon ee_call.storage_trace) ee_call.storage_trace``))))) >>
     `lowered_value_type cenv (Call ann (RawCallTarget flags) args dflt) =
       expr_type (Call ann (RawCallTarget flags) args dflt)` by
       simp_tac (srw_ss()) [lowered_value_type_def,vyperASTTheory.expr_type_def] >>
     PURE_REWRITE_TAC [ASSUME ``vv = LocatedValue ann (mk_ptr (Var tuple_var) LocMemory)``,
       ASSUME ``lowered_value_type cenv (Call ann (RawCallTarget flags) args dflt) =
         expr_type (Call ann (RawCallTarget flags) args dflt)``] >>
     qpat_assum `vv_post (storage_trace_horizon ee_call.storage_trace)
       ctx func cenv cx _ es sa sb s0 ee_call _ (LocatedValue ann _) z_tuple`
       (fn post => assume_tac (SIMP_RULE (srw_ss()) [contextTheory.mk_ptr_def] post) >>
         mp_tac (Q.INST
         [`fw` |-> `tuple_word`,`ftv` |-> `TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic flags.rcf_max_outsize))]`]
         (PART_MATCH (find_term (fn tm =>
           same_const (fst (strip_comb tm)) ``vv_post``))
           exprSimMemDefsTheory.vv_store_bound_capacity (concl post)))) >>
     impl_tac >- (simp_tac (srw_ss()) [vyperASTTheory.expr_type_def,
       post_value_type_def,contextTheory.mk_ptr_def,eval_operand_def,
       valueEncodingTheory.type_memory_size_def,vfmConstantsTheory.word_size_def] >>
       rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
     disch_then ACCEPT_TAC) >>
  `val_store_size (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic flags.rcf_max_outsize))])
    (ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE flags.rcf_max_outsize s_call.vs_returndata)])) <=
    ((flags.rcf_max_outsize+31) DIV 32)*32+64` by decide_tac >>
  `ptr_val_ok cx ann (ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE flags.rcf_max_outsize s_call.vs_returndata)]))
    (Var tuple_var) J_tuple un_tuple z_tuple` by
    (mp_tac (Q.INST [`cx` |-> `cx`,`ty` |-> `ann`,
       `tv` |-> `TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic flags.rcf_max_outsize))]`,
       `v` |-> `ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE flags.rcf_max_outsize s_call.vs_returndata)])`,
       `p` |-> `tuple_var`,`G` |-> `J_tuple`,`tn` |-> `un_tuple`,`s` |-> `z_tuple`,
       `capacity` |-> `64+((flags.rcf_max_outsize+31) DIV 32)*32`]
       rawCallBufferPtrTheory.ptr_val_ok_from_covers) >>
     impl_tac
     >- (simp_tac (srw_ss()) [ASSUME ``~is_word_type ann``] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> rpt strip_tac >>
         `w = tuple_word` by
           (qpat_assum `lookup_var tuple_var z_tuple = SOME w` mp_tac >>
            PURE_REWRITE_TAC [ASSUME ``lookup_var tuple_var z_tuple = SOME (tuple_word:256 word)``] >>
            simp_tac (srw_ss()) []) >>
         qpat_x_assum `w = tuple_word` SUBST_ALL_TAC >>
         qpat_assum `!mem. mem_agree_outside un_tuple.t_mem z_tuple.vs_memory mem ==> _`
           irule >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  `ptr_vv_ok cx (post_value_type cenv (Call ann (RawCallTarget flags) args dflt))
    (Value (ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE flags.rcf_max_outsize s_call.vs_returndata)]))) vv ee_call
    J_tuple un_tuple z_tuple` by
    (qpat_assum `ptr_val_ok cx ann _ (Var tuple_var) J_tuple un_tuple z_tuple` mp_tac >>
     PURE_REWRITE_TAC [ASSUME ``vv = LocatedValue ann (mk_ptr (Var tuple_var) LocMemory)``] >>
     simp_tac (srw_ss()) [ptr_vv_ok_def,ptr_val_ok_def,contextTheory.mk_ptr_def,
       post_value_type_def,vyperASTTheory.expr_type_def,read_result_def,
       vyperStateTheory.return_def,ASSUME ``ann = TupleT [BaseT BoolT;BaseT (BytesT (Dynamic flags.rcf_max_outsize))]``,
       compileEnvTheory.is_word_type_def]) >>
  `ptr_buf_ok cenv (Call ann (RawCallTarget flags) args dflt) (Var tuple_var) J_tuple z_tuple` by
    (mp_tac (Q.INST [`G` |-> `J_tuple`,`tn` |-> `un_tuple`,`p` |-> `tuple_var`,
       `s` |-> `z_tuple`,`cenv` |-> `cenv`,
       `e` |-> `Call ann (RawCallTarget flags) args dflt`,
       `capacity` |-> `64+((flags.rcf_max_outsize+31) DIV 32)*32`]
       rawCallBufferPtrTheory.ptr_buf_ok_from_covers) >>
     impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
       simp_tac (srw_ss()) [ASSUME ``ann = TupleT [BaseT BoolT;BaseT (BytesT (Dynamic flags.rcf_max_outsize))]``,
         rawCallResultLayoutPtrTheory.raw_call_tuple_type_capacity] >> decide_tac) >>
     disch_then ACCEPT_TAC) >>
  suspend "tupleFinish"
QED

Resume raw_call_positive_full_finish[tupleFinish]:
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (s_len,G_len,tn_len) [] (OK z_tuple,J_tuple,un_tuple)` by
    (qx_gen_tac `D` >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`G_tuple`,`s_tuple`,`tn_tuple`] >> conj_tac
     >- (qpat_assum `!D. gas_origin_ptr_path _ (s_len,G_len,tn_len) [] _`
           (qspec_then `D` ACCEPT_TAC)) >>
     qpat_assum `!D. gas_origin_ptr_path _ (s_tuple,G_tuple,tn_tuple) [] _`
       (qspec_then `D` ACCEPT_TAC)) >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (s_call,G_call,tn_call) [] (OK z_tuple,J_tuple,un_tuple)` by
    (qx_gen_tac `D` >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`G_len`,`s_len`,`tn_len`] >> conj_tac
     >- (qpat_assum `!D. gas_origin_ptr_path _ (s_call,G_call,tn_call) [] _`
           (qspec_then `D` ACCEPT_TAC)) >>
     qpat_assum `!D. gas_origin_ptr_path _ (s_len,G_len,tn_len) [] (OK z_tuple,J_tuple,un_tuple)`
       (qspec_then `D` ACCEPT_TAC)) >>
  `!H. valid_horizon cx st0 H ee_call.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G,tn) [] (OK z_tuple,J_tuple,un_tuple)` by
    (qx_gen_tac `H` >> disch_tac >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`G_call`,`s_call`,`tn_call`] >> conj_tac
     >- (qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
           gas_origin_ptr_path _ (t,G,tn) [] (OK s_call,G_call,tn_call)`
           (qspec_then `H` irule) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!D. gas_origin_ptr_path _ (s_call,G_call,tn_call) [] (OK z_tuple,J_tuple,un_tuple)`
       (qspec_then `DF H` ACCEPT_TAC)) >>
  `ee_call with gas_obs := [] = ee_call` by simp_tac (srw_ss()) [Abbr `ee_call`] >>
  `s0.vs_alloca_next <= z_tuple.vs_alloca_next` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`s0.vs_alloca_next <= t.vs_alloca_next`,
        `t.vs_alloca_next <= allocated.vs_alloca_next`,
        `s_call.vs_alloca_next = allocated.vs_alloca_next`,
        `s_len.vs_alloca_next = s_call.vs_alloca_next`,
        `s_len.vs_alloca_next <= s_tuple.vs_alloca_next`,
        `z_tuple.vs_alloca_next = s_tuple.vs_alloca_next`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  irule gas_outcome_full_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`J_tuple`,`ee_call`,
    `INL (Value (ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE flags.rcf_max_outsize s_call.vs_returndata)])))`,
    `z_tuple`,`un_tuple`] >> conj_tac
  >- (PURE_REWRITE_TAC [ASSUME ``s_call.vs_returndata = outcome.co_returnData``] >>
      qpat_assum `!tail. eval_raw_call _ _ _ _ _ _ _ = _` mp_tac >>
      simp_tac (srw_ss()) [Abbr `ee_call`,ASSUME ``~flags.rcf_revert_on_failure``,
        ASSUME ``flags.rcf_max_outsize <> 0``]) >>
  PURE_REWRITE_TAC [ASSUME ``ee_call with gas_obs := [] = ee_call``] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
    vv_post H ctx func cenv cx _ es sa sb s0 ee_call _ vv z_tuple`
    (qspec_then `H` (fn th => assume_tac (MATCH_MP th
      (ASSUME ``valid_horizon cx st0 H ee_call.storage_trace``)))) >>
  qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
    ghost_inv_at _ _ _ _ _ _ J_tuple un_tuple z_tuple`
    (qspec_then `H` (fn th => assume_tac (MATCH_MP th
      (ASSUME ``valid_horizon cx st0 H ee_call.storage_trace``)))) >>
  conj_tac
  >- (qpat_assum `!H. valid_horizon _ _ H ee_call.storage_trace ==>
        gas_origin_ptr_path _ (t,G,tn) [] (OK z_tuple,J_tuple,un_tuple)`
        (qspec_then `H` irule) >> first_assum ACCEPT_TAC) >>
  BETA_TAC >>
  qexists_tac `Value (ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE flags.rcf_max_outsize s_call.vs_returndata)]))` >>
  simp_tac (srw_ss()) [] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `ptr_vv_ok cx _ _ vv ee_call J_tuple un_tuple z_tuple` mp_tac >>
    simp_tac (srw_ss()) [ASSUME ``vv = LocatedValue ann (mk_ptr (Var tuple_var) LocMemory)``,
      contextTheory.vv_location_def,contextTheory.mk_ptr_def,
      ASSUME ``ptr_buf_ok cenv (Call ann (RawCallTarget flags) args dflt)
        (Var tuple_var) J_tuple z_tuple``] >> decide_tac
QED

Resume raw_call_positive_full_finish[positiveStatic]:
  `cx.txn.is_static /\ amount <> 0 /\ ~flags.rcf_is_static` by metis_tac[] >>
  `eval_operand value_op ready = SOME vw /\ vw <> 0w` by
    (conj_tac
     >- (qpat_assum `~flags.rcf_is_static ==>
           eval_operand value_op ready = SOME vw /\ _` mp_tac >>
         simp_tac bool_ss [ASSUME ``~flags.rcf_is_static``]) >>
     qpat_assum `~flags.rcf_is_static ==>
       eval_operand value_op t = SOME vw /\ w2n vw = amount`
       (mp_tac o SIMP_RULE bool_ss [ASSUME ``~flags.rcf_is_static``]) >>
     qpat_assum `amount <> 0` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]) >>
  `call_inst.inst_opcode = CALL /\ call_inst.inst_operands =
    [gas_op;addr;value_op;dp;dl;op;Lit (n2w flags.rcf_max_outsize)]` by
    simp_tac (srw_ss()) [Abbr `call_inst`,venomInstTheory.mk_inst_def,
      ASSUME ``~flags.rcf_is_static``] >>
  `ready.vs_call_ctx.cc_static` by
    simp_tac bool_ss [ASSUME ``ready.vs_call_ctx.cc_static = cx.txn.is_static``,
      ASSUME ``cx.txn.is_static``] >>
  drule_all extCallOracleStepTheory.call_static_value_abort >> strip_tac >>
  `!tail. eval_raw_call cx flags target bs amount source_gas
      (mid with gas_obs := tail) =
    (INR (Error (RuntimeError "write in static context")),mid with gas_obs := tail)` by
    (gen_tac >> irule rawCallSourceActionPtrTheory.raw_call_static_value_abort >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `lookup_block ready.vs_current_bb func.fn_blocks = SOME bb_call /\
   get_instruction bb_call ready.vs_inst_idx = SOME call_inst` by
    (simp_tac bool_ss [ASSUME ``ready.vs_current_bb = s7.cs_current_bb``,
       ASSUME ``ready.vs_inst_idx = LENGTH s7.cs_current_insts``,Abbr `call_inst`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `get_instruction bb_call (LENGTH s7.cs_current_insts) = _` mp_tac >>
     simp_tac (srw_ss()) [ASSUME ``~flags.rcf_is_static``]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (ready,G_ready,tn_ready) []
      (Abort ExHalt_abort (halt_state (set_returndata [] ready)),G_ready,tn_ready)` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       access_ok _ _ _ _ _ /\ _`
       (qspec_then `H` (fn th => strip_assume_tac (MATCH_MP th
         (ASSUME ``valid_horizon cx st0 H mid.storage_trace``)))) >>
     `ptr_inst_ok (DF H) lo 0 ctx func G_ready tn_ready call_inst ready` by
       (map_every (fn q => qpat_assum q mp_tac)
          [`call_inst.inst_opcode = CALL`,
           `access_ok lo G_ready func call_inst ready`,
           `taint_ok func tn_ready call_inst ready`,`allocas_from lo ready`,
           `~ctx_has_dalloca ctx`,`stor_taint_ok_at (DF H) tn_ready ready`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        irule callStepPtrTheory.ptr_inst_ok_call >>
        simp[] >> fs[bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
     map_every (fn q => qpat_assum q mp_tac)
       [`lookup_block ready.vs_current_bb func.fn_blocks = SOME bb_call`,
        `get_instruction bb_call ready.vs_inst_idx = SOME call_inst`,
        `~ready.vs_halted`,`call_inst.inst_opcode = CALL`,
        `step_inst_base call_inst ready =
          Abort ExHalt_abort (halt_state (set_returndata [] ready))`,
        `inst_mem_below_frontier call_inst ready`,
        `ptr_inst_ok (DF H) lo 0 ctx func G_ready tn_ready call_inst ready`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     irule (Q.INST [`i` |-> `call_inst`,`bb` |-> `bb_call`]
       fragGasEmitCtrlTheory.exit_inst_origin_ptr) >>
     simp[fragExecTheory.exit_result_def,venomExecSemanticsTheory.step_inst_non_invoke,
       memSafeRunTheory.mem_safe_step_non_invoke,memSafeRunTheory.inst_dload_in_section_def,
       gasEventsTheory.gas_events_step_def,gasCountTheory.gas_count_step_def]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G,tn) []
      (Abort ExHalt_abort (halt_state (set_returndata [] ready)),G_ready,tn_ready)` by
    (qx_gen_tac `H` >> disch_tac >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`G_ready`,`ready`,`tn_ready`] >> conj_tac
     >- (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
         qexistsl_tac [`G_alloc`,`allocated`,`tn_alloc`] >> conj_tac
         >- (qpat_assum `!D. gas_origin_ptr_path (D,lo,_,_,_,_) (t,G,tn) [] _`
               (qspec_then `DF H` ACCEPT_TAC)) >>
         qpat_assum `!D lo explicit. allocas_from lo allocated ==> _`
           (qspecl_then [`DF H`,`lo`,`gas_explicit_sites ctx shadow_ctx`] irule) >>
         first_assum ACCEPT_TAC) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       gas_origin_ptr_path _ (ready,G_ready,tn_ready) [] _`
       (qspec_then `H` irule) >> first_assum ACCEPT_TAC) >>
  irule gas_outcome_full_exit >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G_ready`,`mid`,
    `Abort ExHalt_abort (halt_state (set_returndata [] ready))`,
    `INR (Error (RuntimeError "write in static context"))`,`tn_ready`] >>
  simp_tac (srw_ss()) [fragExecTheory.exit_result_def,exprSimDefsTheory.expr_exit_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Finalise raw_call_positive_full_finish
