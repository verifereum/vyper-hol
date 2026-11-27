Theory bodyFullExtCallKeywordPackedCut
Ancestors
  bodyFullExtCallRequestPostGasPacking bodyFullExtCallKeywordPackingRows
  bodyFullExtCallPackingReady bodyFullExtCallPacking bodyFullRawCallGas
  bodyFullExtCallKeywordList bodyFullExtCallAddressOwnedPrefix
  exprSimExtCallCase gasShadowCompile exprLowering
  gasShadowCompileHelpers gasShadowCompileStmtHelpers
  entryReachBodyFirstEmissionExprSupport entryReachBodyFirstEmissionExpr
  externalEntryShape gasShadowState gasShadowCompileConvert list
  bodyInvSplit[qualified] exprSimHypsDefs[qualified]
Libs
  pairLib

(* The source is already at eval_ext_call.  Separate the optional generated
   GAS from the physical ABI packing, which consumes no gas observations. *)
Theorem extcall_request_keyword_packed_cut:
  (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
  expr_body_pre_mods mods cenv cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) (addr::tail) dr) es /\
  xs = TAKE (LENGTH ats) tail /\
  arg_types_fit (MAP expr_type xs) ats /\ ext_call_opts_ok stat opts /\
  MAP expr_type kw_es = MAP (ext_call_kw_type rt) opts /\
  (!e st. MEM e xs /\ expr_sim_inv_mods mods cenv cx env st ==> expr_body_pre_mods mods cenv cx env e st) /\
  (!e st. MEM e kw_es /\ expr_sim_inv_mods mods cenv cx env st ==> expr_body_pre_mods mods cenv cx env e st) /\
  lower_value compile_expr cenv (BaseT AddressT) addr sa = (ao,s1) /\
  compile_ext_call_args compile_expr cenv kw_es
    (MAP (lowered_value_type cenv) xs) xs s1 = (av,s2) /\
  compile_ext_call_kwargs compile_expr cenv rt opts kw_es s2 = ((vo,go,def),s3) /\
  (case go of SOME g => (g,s3) | NONE => emit_op GAS [] s3) = (gas,s5) /\
  (case shadow_go of SOME g => (g,shadow_s3) | NONE => emit_op GAS [] shadow_s3) =
    (gas',s5') /\ shadow_go = go /\
  compile_external_call_kwargs cenv ao av (MAP (lowered_value_type cenv) xs)
    (abi_size_bound cenv.ce_struct_fields (TupleT (MAP (lowered_value_type cenv) xs)))
    (cenv.ce_method_id fname ats)
    (abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt))
    (abi_static_size cenv.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt))
    (type_memory_bytes cenv rt) stat
    (case vo of SOME v => v | NONE => Lit 0w) gas skip
    (IS_SOME def) (case def of SOME (d,dt) => d | NONE => Lit 0w)
    rt (case def of SOME (d,dt) => dt | NONE => rt)
    (type_to_abi_dec_info cenv.ce_struct_fields cenv
      (if needs_external_call_wrap rt then TupleT [rt] else rt)) s5 = (result,sb) /\
  vv = (if rt = NoneT then StackValue ann result else LocatedValue ann (mk_ptr result LocMemory)) /\
  fn_has_code s3 s5 func /\ fn_has_code shadow_s3 s5' shadow_func /\
  fn_has_code s5 sb func /\ fn_inst_ids_distinct func /\
  gas_shadow_state s3 shadow_s3 /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  ci_mono sa s1 /\ ci_mono s1 s2 /\ local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s2 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  eval_exprs cx [addr] (es with gas_obs := obs1) = (INL [v],mid) /\
  eval_exprs cx xs (mid with gas_obs := obs2) = (INL vs,ee) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  dest_AddressV v = SOME (w2w (aw:256 word) : 160 word) /\
  eval_operand ao u = SOME aw /\ safe_operand s1 ao /\
  ptr_val_ok cx (BaseT AddressT) v ao G1 tn1 t /\
  expr_sim_inv_mods mods cenv cx env mid /\ expr_sim_inv_mods mods cenv cx env ee /\
  LENGTH av = LENGTH xs /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  wb_frame cenv mid ee s1 t u /\
  (!x w. not_fresh_at s1 x /\ lookup_var x t = SOME w ==> lookup_var x u = SOME w) /\
  (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee u /\
    expr_post H ctx func cenv cx addr es sa s1 s0 mid v ao t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
    ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2 /\
    LIST_REL (\(e,sv) v.
      (?si se ss vv raw copy.
        compile_expr cenv (expr_type e) e si = (vv,se) /\
        compile_snapshot_vv cenv copy
          (ext_call_arg_value (lowered_value_type cenv e) vv) se = (sv,ss) /\
        (~copy ==> ~exprs_can_mutate cenv kw_es) /\
        (copy /\ ~is_word_type (lowered_value_type cenv e) ==>
          ?p w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var p /\
            eval_operand (vv_operand sv) u = SOME w /\
            evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
            val_wf tv v /\ FLOOKUP u.vs_allocas se.cs_next_id = SOME (w2n w,type_memory_size tv) /\
            se.cs_next_id < ss.cs_next_id /\
            (!n b sz. local_region cenv ee.scopes u n b sz ==>
              regions_disjoint (w2n w) (type_memory_size tv) b sz)) /\
        s1.cs_next_var <= si.cs_next_var /\ s1.cs_next_id <= si.cs_next_id /\
        se.cs_next_var <= s2.cs_next_var /\ se.cs_next_id <= s2.cs_next_id /\
        ss.cs_next_var <= s2.cs_next_var /\ ss.cs_next_id <= s2.cs_next_id /\
        local_ptrs_reserved cenv si /\
        (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
        (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
        ((?tag op0. sv = StackValue tag op0) \/
         (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
           ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
         (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
           ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
           lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
        read_result cx raw ee = (INL v,ee) /\
        vv_holds cenv cx (lowered_value_type cenv e) raw sv ee u /\
        vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv u /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G2 tn2 u /\
        vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv u) /\
      vv_storage_live H cx sv ee u /\
      (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
        ptr_buf_ok cenv e op G2 u) /\
      (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand G2 u) /\
      (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
        !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand sv) u = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem))) (ZIP (xs,av)) vs) /\
  storage_trace_domain cx st0 ke.storage_trace /\ ke.gas_obs = [] /\
  (!tail. eval_exprs cx kw_es
    (ee with gas_obs := gas_explicit kw_marks u.vs_gas_readings ++ tail) =
    (INL kws,ke with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ke.storage_trace ==>
    expr_sim_inv_mods mods cenv cx env ke /\
    stmt_state_rel H ctx func cenv cx ke z /\ storage_well_formed_on cx ke (FST H) /\
    z.vs_current_bb = s3.cs_current_bb /\ z.vs_inst_idx = LENGTH s3.cs_current_insts /\
    ~z.vs_halted /\ alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx ke G3 tn3 z /\
    ghost_kept_at lo cenv ee s2 G2 tn2 u G3 tn3 /\
    return_buf_frame d cenv s3 z /\ wb_frame cenv ee ke s2 u z /\
    (!x w. not_fresh_at s2 x /\ lookup_var x u = SOME w ==> lookup_var x z = SOME w) /\
    (!aid b. FLOOKUP u.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
    z.vs_labels = u.vs_labels /\
    (case ext_call_kwarg EKGas opts kws of NONE => go = NONE
     | SOME gv => ?op w. go = SOME op /\ eval_operand op z = SOME w /\
         (!x. op = Var x ==> not_fresh_at s3 x) /\
         dest_NumV gv = SOME (w2n w) /\ op_taint tn3 op = {}) /\
    (case ext_call_kwarg EKValue opts kws of NONE => vo = NONE
     | SOME vi => ?op w. vo = SOME op /\ eval_operand op z = SOME w /\
         (!x. op = Var x ==> not_fresh_at s3 x) /\
         dest_NumV vi = SOME (w2n w) /\ op_taint tn3 op = {}) /\
    (case ext_call_kwarg EKDefault opts kws of NONE => def = NONE
     | SOME dv => ?e op dt. def = SOME (op,dt) /\
         ext_call_kwarg EKDefault opts kw_es = SOME e /\
         (!x. op = Var x ==> not_fresh_at s3 x) /\
         if is_word_type rt then
           dt = rt /\ expr_val_rel cx rt dv op z /\ ptr_val_ok cx rt dv op G3 tn3 z
         else dt = lowered_value_type cenv e /\ ptr_val_ok cx dt dv op G3 tn3 z /\
              ptr_mem_ok cx dt dv op G3 tn3 z /\ ptr_buf_ok cenv e op G3 z /\
              (!w. eval_operand op z = SOME w /\ type_memory_bytes cenv dt <> 0 ==>
                w2n w + type_memory_bytes cenv dt <= z.vs_alloca_next) /\
              (?w aid tv. eval_operand op z = SOME w /\
                evaluate_type (get_tenv cx) dt = SOME tv /\ val_wf tv dv /\
                FLOOKUP z.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
                aid < s3.cs_next_id))) ==>
  ?sp sr u_ret value buf off len hasdef defop dt target value_opt n zg Gg tng gw.
    comp_ignore_bind
      (if rt = NoneT /\ ~skip then compile_extcodesize_check ao else comp_return ())
      (comp_bind
        (if stat then emit_op STATICCALL [gas;ao;off;len;buf;Lit (n2w
          (abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt)))]
         else emit_op CALL [gas;ao;value;off;len;buf;Lit (n2w
          (abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt)))])
        (\success. comp_bind (fresh_label "extcall_fail") (\fail_lbl.
         comp_bind (fresh_label "extcall_cont") (\cont_lbl.
         comp_ignore_bind (emit_inst JNZ [success;Label cont_lbl;Label fail_lbl] [])
         (comp_ignore_bind (new_block fail_lbl)
         (comp_bind (emit_op RETURNDATASIZE []) (\rds.
         comp_bind (compile_alloc_buffer 0) (\fb.
         comp_ignore_bind (emit_void RETURNDATACOPY [fb.buf_operand;Lit 0w;rds])
         (comp_ignore_bind (emit_inst REVERT [fb.buf_operand;rds] [])
           (new_block cont_lbl)))))))))) sp = (u_ret,sr) /\
    (if rt = NoneT then comp_return (Lit 0w)
     else if hasdef then
       comp_bind (compile_alloc_buffer (type_memory_bytes cenv rt)) (\r.
         compile_default_return_path cenv rt dt buf r.buf_operand defop ao skip
           (abi_static_size cenv.ce_struct_fields
             (if needs_external_call_wrap rt then TupleT [rt] else rt))
           (abi_size_bound cenv.ce_struct_fields
             (if needs_external_call_wrap rt then TupleT [rt] else rt))
           (type_to_abi_dec_info cenv.ce_struct_fields cenv
             (if needs_external_call_wrap rt then TupleT [rt] else rt)))
     else comp_bind (compile_alloc_buffer (type_memory_bytes cenv rt)) (\r.
       comp_bind (compile_return_value_decode
         (abi_static_size cenv.ce_struct_fields
           (if needs_external_call_wrap rt then TupleT [rt] else rt))
         (abi_size_bound cenv.ce_struct_fields
           (if needs_external_call_wrap rt then TupleT [rt] else rt))) (\hi.
       comp_ignore_bind
         (compile_abi_decode_to_buf r.buf_operand (Lit 0w) MLOAD buf hi
           (type_to_abi_dec_info cenv.ce_struct_fields cenv
             (if needs_external_call_wrap rt then TupleT [rt] else rt)))
         (comp_return r.buf_operand)))) sr = (result,sb) /\
    fn_has_code sp sr func /\ fn_has_code sr sb func /\
    LENGTH vs = LENGTH ats /\ LENGTH kws = LENGTH opts /\
    dest_AddressV v = SOME target /\
    value_opt = (if stat then NONE else
      case ext_call_kwarg EKValue opts kws of NONE => SOME 0 | SOME x => dest_NumV x) /\
    ~z.vs_halted /\ ~zg.vs_halted /\
    (!H. valid_horizon cx st0 H ke.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (z,G3,tn3) (REPLICATE n F) (OK zg,Gg,tng)) /\
    (?calldata t Gf tf.
      build_ext_calldata (get_tenv cx) fname ats vs = SOME calldata /\
      extcall_request_ready st0 ctx func cenv cx rt es sa s0 sp stat
        ao value gas buf off len
        (abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt))
        target value_opt calldata hasdef defop dt (ext_call_kwarg EKDefault opts kws) ke t /\
      (IS_SOME (ext_call_kwarg EKDefault opts kws) /\ ~is_word_type dt ==>
        ?w aid tv. eval_operand defop t = SOME w /\
          evaluate_type (get_tenv cx) dt = SOME tv /\
          FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\ aid < sp.cs_next_id) /\
      (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (zg,Gg,tng) [] (OK t,Gf,tf)) /\
      alloca_history func t /\ allocas_from lo t /\
      lo <= t.vs_alloca_next /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      (!H. valid_horizon cx st0 H ke.storage_trace ==> ghost_inv_at (DF H) lo d cenv cx ke Gf tf t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf /\
      eval_operand gas t = SOME gw /\
      (!g. OPTION_BIND (ext_call_kwarg EKGas opts kws) dest_NumV = SOME g ==> g = w2n gw) /\
      EVERY (\p. op_taint tf p = {}) [ao;value;gas;buf;off;len;defop] /\
      (!ao az. eval_operand off t = SOME ao /\ eval_operand len t = SOME az ==>
        (az <> 0w ==> (?p. off = Var p /\ ptr_covers Gf tf p t (w2n az)) /\
                      w2n ao + w2n az <= t.vs_alloca_next) /\
        (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tf.t_mem)) /\
      (abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt) <> 0 ==>
        ?p. buf = Var p /\ ptr_covers Gf tf p t
          (abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt))) /\
      (!dv. ext_call_kwarg EKDefault opts kws = SOME dv /\ ~is_word_type dt ==>
        ptr_mem_ok cx dt dv defop Gf tf t /\
        (type_memory_bytes cenv dt <> 0 ==>
          (?p. defop = Var p /\ ptr_covers Gf tf p t (type_memory_bytes cenv dt)) /\
          (!w. eval_operand defop t = SOME w ==>
            w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ke.storage_trace) ke.storage_trace` by
    (qpat_assum `storage_trace_domain _ _ ke.storage_trace`
       (mp_tac o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def]) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H ke.storage_trace ==> expr_sim_inv _ _ _ ke /\ _`
    (qspec_then `storage_trace_horizon ke.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_exprs cx kw_es (ee with gas_obs := gas_explicit kw_marks u.vs_gas_readings) =
     (INL kws,ke)` by
    (`ke with gas_obs := [] = ke` by simp[vyperStateTheory.evaluation_state_component_equality] >>
     qpat_assum `!tail. eval_exprs cx kw_es _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
     asm_rewrite_tac[]) >>
  `storage_trace_frame (eval_exprs cx kw_es)` by
    simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  `?extra. ke.storage_trace = ee.storage_trace ++ extra` by
    (drule_all vyperStorageTraceTheory.storage_trace_frame_prefix >> simp[]) >>
  `!H. valid_horizon cx st0 H ke.storage_trace ==>
       valid_horizon cx st0 H ee.storage_trace` by
    metis_tac[gasOutcomeFullTheory.valid_horizon_append] >>
  `!H. valid_horizon cx st0 H ke.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ke z /\
       storage_well_formed_on cx ke (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx ke G3 tn3 z` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!h. valid_horizon _ _ h ke.storage_trace ==> expr_sim_inv _ _ _ ke /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ci_mono s2 s3` by
    (`!ks ys a. ci_mono a (SND (compile_ext_call_kwargs compile_expr cenv rt ks ys a))` by
       (Induct >> Cases_on `ys` >> rpt strip_tac >>
        simp[compile_ext_call_kwargs_def, exprLoweringPropsTheory.ci_mono_comp_return] >>
        ho_match_mp_tac exprLoweringPropsTheory.ci_mono_bind >> conj_tac
        >- simp[exprLoweringPropsTheory.ci_mono_compile_ext_call_kwarg,
                cj 1 stmtLoweringMonoTheory.ci_mono_compile_expr_sa] >>
        rpt strip_tac >> simp[pairTheory.UNCURRY] >>
        ho_match_mp_tac exprLoweringPropsTheory.ci_mono_bind >>
        simp[pairTheory.UNCURRY, exprLoweringPropsTheory.ci_mono_comp_return]) >>
     pop_assum (qspecl_then [`opts`,`kw_es`,`s2`] mp_tac) >> simp[]) >>
  `s2.cs_next_var <= s3.cs_next_var /\ s2.cs_next_id <= s3.cs_next_id` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `ci_mono s3 s5` by
    (Cases_on `go` >> fs[]
     >- (qspec_then `GAS` (qspecl_then [`[]`,`s3`] mp_tac)
           exprLoweringPropsTheory.ci_mono_emit_op >> simp[]) >>
     fs[exprLoweringPropsTheory.ci_mono_refl]) >>
  `local_ptrs_reserved cenv s3 /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s3 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s3 x)` by
    (conj_tac
     >- (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
         qexists_tac `s2` >> simp[]) >>
     conj_tac >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `s2` >> simp[]) >>
  suspend "generated_gas"
QED

Resume extcall_request_keyword_packed_cut[generated_gas]:
  qabbrev_tac `source_gas = ext_call_kwarg EKGas opts kws` >>
  `(!g. go = SOME g ==> ?w. eval_operand g z = SOME w /\ op_taint tn3 g = {} /\
       (!n. OPTION_BIND source_gas dest_NumV = SOME n ==> n = w2n w)) /\
   (!n. OPTION_BIND source_gas dest_NumV = SOME n ==> IS_SOME go)` by
    (qpat_assum `case source_gas of NONE => go = NONE | SOME x =>
         ?op w. go = SOME op /\ _ /\ _ /\ dest_NumV x = SOME (w2n w) /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `source_gas` >> simp[] >>
     strip_tac >> simp[] >> qexists `w` >> simp[]) >>
  `?zg Gg tng gw n.
     eval_operand gas zg = SOME gw /\ op_taint tng gas = {} /\
     (!k. OPTION_BIND source_gas dest_NumV = SOME k ==> k = w2n gw) /\
     ~zg.vs_halted /\ zg.vs_current_bb = s5.cs_current_bb /\
     zg.vs_inst_idx = LENGTH s5.cs_current_insts /\ alloca_history func zg /\
     zg.vs_memory = z.vs_memory /\ zg.vs_allocas = z.vs_allocas /\
     zg.vs_alloca_next = z.vs_alloca_next /\ zg.vs_fmp = z.vs_fmp /\
     zg.vs_labels = z.vs_labels /\
     tng.t_mem = tn3.t_mem /\ tng.t_stor = tn3.t_stor /\
     tng.t_trans = tn3.t_trans /\ tng.t_imm = tn3.t_imm /\
     (!x. not_fresh_at s3 x ==> lookup_var x zg = lookup_var x z /\
       FLOOKUP Gg x = FLOOKUP G3 x /\ op_taint tng (Var x) = op_taint tn3 (Var x)) /\
     (!H. valid_horizon cx st0 H ke.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (z,G3,tn3) (REPLICATE n F) (OK zg,Gg,tng) /\
       ghost_inv_at (DF H) lo d cenv cx ke Gg tng zg /\
       stmt_state_rel H ctx func cenv cx ke zg /\
       storage_well_formed_on cx ke (FST H) /\
       ghost_kept_at lo cenv ke s3 G3 tn3 z Gg tng)` by
    (Cases_on `go`
     >- (mp_tac (Q.INST [`go` |-> `NONE`, `shadow_go` |-> `NONE`,
           `sa` |-> `s3`, `sb` |-> `s5`, `shadow_sa` |-> `shadow_s3`, `shadow_sb` |-> `s5'`,
           `shadow_gas` |-> `gas'`, `s` |-> `z`, `G` |-> `G3`, `tn` |-> `tn3`,
           `es` |-> `ke`] raw_call_optional_gas_joint) >>
         (impl_tac >-
           (qpat_assum `(case NONE of NONE => _ | SOME _ => _) = (gas,s5)`
              (assume_tac o SIMP_RULE std_ss []) >>
            qpat_assum `shadow_go = NONE` (fn eq =>
              qpat_assum `(case shadow_go of NONE => _ | SOME _ => _) = (gas',s5')`
                (assume_tac o SIMP_RULE std_ss [eq])) >>
            simp_tac std_ss [] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
            qpat_assum `!H. valid_horizon _ _ H ke.storage_trace ==>
                stmt_state_rel _ _ _ _ _ ke z /\ storage_well_formed_on _ _ _ /\ _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> metis_tac[])) >>
         disch_then (qx_choose_then `zg0` (qx_choose_then `Gg0`
           (qx_choose_then `tng0` (qx_choose_then `gw0`
             (strip_assume_tac o SIMP_RULE (srw_ss()) []))))) >>
         qexistsl [`zg0`,`Gg0`,`tng0`,`gw0`,`1`] >>
         `!k. OPTION_BIND source_gas dest_NumV <> SOME k` by
           (qpat_assum `!k. OPTION_BIND source_gas dest_NumV = SOME k ==> IS_SOME NONE` mp_tac >>
            simp_tac std_ss [optionTheory.IS_SOME_DEF]) >>
         `REPLICATE 1 F = [F]` by EVAL_TAC >>
         pop_assum (fn th => rewrite_tac [th]) >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         pure_once_asm_rewrite_tac[] >> simp[venomStateTheory.update_var_def] >>
         qpat_assum `!k. OPTION_BIND source_gas dest_NumV <> SOME k` (fn th => simp_tac std_ss [th])) >>
     qpat_assum `(case SOME _ of NONE => _ | SOME _ => _) = (gas,s5)` mp_tac >>
     simp_tac std_ss [] >> disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) >>
     qpat_assum `!g. SOME _ = SOME g ==> _` (qspec_then `gas` mp_tac) >>
     simp_tac std_ss [] >> strip_tac >>
     qexistsl [`z`,`G3`,`tn3`,`w`,`0`] >>
     simp[bodyPtrDefsTheory.ghost_kept_at_def,fragGasOriginPtrTheory.gas_origin_ptr_path_rules]) >>
  suspend "packing_rows"
QED

Resume extcall_request_keyword_packed_cut[packing_rows]:
  `!x. not_fresh_at s2 x ==> not_fresh_at s3 x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `wb_frame cenv ee ke s2 u zg` by
    (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
     qexistsl_tac [`s3`,`z`] >> simp[]) >>
  `ghost_kept_at lo cenv ee s2 G2 tn2 u Gg tng` by
    (pure_rewrite_tac[bodyPtrDefsTheory.ghost_kept_at_def] >>
     qpat_assum `tng.t_mem = tn3.t_mem` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `ghost_kept_at lo cenv ee s2 G2 tn2 u G3 tn3`
       (strip_assume_tac o PURE_REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >>
     conj_tac >- (qx_gen_tac `x` >> disch_tac >>
       qpat_assum `!y. not_fresh_at s3 y ==> lookup_var y zg = _ /\ _`
         (qspec_then `x` mp_tac) >>
       qpat_assum `!y. not_fresh_at s2 y ==> FLOOKUP G3 y = _ /\ _`
         (qspec_then `x` mp_tac) >> simp[]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `(!x w. not_fresh_at s2 x /\ lookup_var x u = SOME w ==> lookup_var x zg = SOME w) /\
   (!aid row. FLOOKUP u.vs_allocas aid = SOME row ==> FLOOKUP zg.vs_allocas aid = SOME row) /\
   u.vs_alloca_next <= zg.vs_alloca_next /\ zg.vs_labels = u.vs_labels` by simp[] >>
  `s2.cs_next_var <= s5.cs_next_var /\ s2.cs_next_id <= s5.cs_next_id` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `!H. valid_horizon cx st0 H ke.storage_trace ==>
       valid_horizon cx st0 H ee.storage_trace /\
       stmt_state_rel H ctx func cenv cx ke zg /\
       ghost_inv_at (DF H) lo d cenv cx ke Gg tng zg` by
    (gen_tac >> disch_tac >> conj_tac >- simp[] >>
     qpat_assum `!H. valid_horizon _ _ H ke.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       drule >> simp[]) >>
  `~exprs_can_mutate cenv kw_es ==>
     ke.scopes = ee.scopes /\ ke.immutables = ee.immutables /\
     (!tr. get_storage cx ke tr = get_storage cx ee tr)` by
    (strip_tac >>
     `get_module_code cx NONE = SOME tops` by
       (qpat_assum `body_inv tops ctx cenv cx`
          (ACCEPT_TAC o cj 3 o REWRITE_RULE [bodySimTheory.body_inv_def])) >>
     `EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal))
        (int_calls_exprs kw_es)` by
       (simp[bodyStorageCasesTheory.body_exprs_main_calls_every, listTheory.EVERY_MEM] >>
        rpt strip_tac >>
        `expr_body_pre cenv cx env e ee` by
          (qpat_assum `!e st. MEM e kw_es /\ _ ==> _`
             (qspecl_then [`e`,`ee`] mp_tac) >> simp[]) >>
        qpat_assum `expr_body_pre cenv cx env e ee`
          (mp_tac o Q.SPEC `c` o REWRITE_RULE [listTheory.EVERY_MEM] o cj 8 o
           REWRITE_RULE [exprSimHypsDefsTheory.expr_body_pre_def]) >>
        simp[]) >>
     drule_all targetPureWalkSourceTheory.nonmutating_exprs_source_frame >>
     simp[vyperMachineFrameTheory.machine_frame_def] >> strip_tac >>
     gen_tac >> Cases_on `tr` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  `MAP FDOM ke.scopes = MAP FDOM ee.scopes` by
    (qpat_assum `eval_exprs cx kw_es (ee with gas_obs := _) = (INL kws,ke)`
       (mp_tac o MATCH_MP
         vyperEvalExprPreservesScopesDomTheory.eval_exprs_preserves_scopes_dom) >>
     simp[]) >>
  mp_tac (Q.INST [`sa` |-> `s1`, `sb` |-> `s2`, `se` |-> `s5`, `svs` |-> `av`,
           `kw_es` |-> `kw_es`, `env` |-> `env`,
           `pos` |-> `ee`, `ee` |-> `ke`, `t` |-> `zg`, `Gp` |-> `G2`,
           `tp` |-> `tn2`, `G` |-> `Gg`, `tn` |-> `tng`]
    extcall_keyword_packing_rows) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >~ [`?H. valid_horizon cx st0 H ke.storage_trace`]
     >- (qexists_tac `storage_trace_horizon ke.storage_trace` >> first_assum ACCEPT_TAC) >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ ee u /\ _`
       mp_tac >>
     simp[NoAsms, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM])) >>
  disch_then (mk_asm "packing_rows") >>
  suspend "buffer_layout"
QED

Resume extcall_request_keyword_packed_cut[buffer_layout]:
  qpat_assum `compile_external_call_kwargs _ ao av _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s5 = _`
    (mp_tac o MATCH_MP extcall_request_buffer_layout) >>
  disch_then (qx_choosel_then [`ba`,`sb1`,`sb2`,`len`,`sb3`,`off`,`sp`,`sr`,`u_ret`]
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `cs_extends s5 sb1 /\ cs_extends sb1 sb2 /\ cs_extends sb3 sp` by
    (conj_tac
     >- (qpat_assum `compile_alloc_buffer _ s5 = _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[cj 1 compile_alloc_buffer_labels,pairTheory.SND]) >>
     conj_tac
     >- (qpat_assum `emit_void _ _ sb1 = _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[cj 1 emit_void_labels,pairTheory.SND]) >>
     qpat_assum `emit_op _ _ sb3 = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[cj 1 emit_op_labels,pairTheory.SND]) >>
  sg `cs_extends sb2 sb3`
  >- (qpat_assum `(if av = [] then _ else _) sb2 = (_,sb3)`
        (SUBST1_TAC o GSYM o REWRITE_RULE [pairTheory.SND] o
         AP_TERM ``SND : operand # compile_state -> compile_state``) >>
      POP_ASSUM_LIST (K ALL_TAC) >> IF_CASES_TAC >> simp[comp_return_labels] >>
      qmatch_goalsub_abbrev_tac `SND (f sb2)` >>
      sg `!s. cs_extends s (SND (f s)) /\
             EVERY (isPREFIX "@") (added_labels s (SND (f s)))`
      >- (gen_tac >> simp[Abbr `f`] >>
          rpt (FIRST [irule comp_bind_labels, irule comp_ignore_bind_labels] >>
            conj_tac >> rpt gen_tac >> BETA_TAC >>
            simp[emit_op_labels,compile_abi_encode_values_to_buf_labels])) >>
      first_x_assum (qspec_then `sb2` (ACCEPT_TAC o CONJUNCT1))) >>
  sg `cs_extends sp sr`
  >- (qpat_assum `comp_ignore_bind _ _ sp = (_,sr)`
        (SUBST1_TAC o GSYM o REWRITE_RULE [pairTheory.SND] o
         AP_TERM ``SND : string # compile_state -> compile_state``) >>
      POP_ASSUM_LIST (K ALL_TAC) >> qmatch_goalsub_abbrev_tac `SND (f sp)` >>
      sg `!s. cs_extends s (SND (f s)) /\
             EVERY (isPREFIX "@") (added_labels s (SND (f s)))`
      >- (gen_tac >> simp[Abbr `f`] >>
          rpt (FIRST [irule fresh_label_bind_labels >> rpt gen_tac >> disch_tac,
                      irule comp_bind_labels >> conj_tac >> rpt gen_tac,
                      irule comp_ignore_bind_labels >> conj_tac >> rpt gen_tac] >>
            BETA_TAC >> simp[emit_inst_labels,emit_op_labels,emit_void_labels,
                             compile_alloc_buffer_labels]) >>
          TRY (irule new_block_action_labels >> simp[]) >>
          IF_CASES_TAC >> simp[emit_op_labels,comp_return_labels,compile_extcodesize_check_labels]) >>
      first_x_assum (qspec_then `sp` (ACCEPT_TAC o CONJUNCT1))) >>
  sg `cs_extends sr sb`
  >- (qpat_assum `(if rt = NoneT then _ else _) sr = (_,sb)`
        (SUBST1_TAC o GSYM o REWRITE_RULE [pairTheory.SND] o
         AP_TERM ``SND : operand # compile_state -> compile_state``) >>
      POP_ASSUM_LIST (K ALL_TAC) >> IF_CASES_TAC >> simp[comp_return_labels] >>
      IF_CASES_TAC >>
      (qmatch_goalsub_abbrev_tac `SND (f sr)` >>
       sg `!s. cs_extends s (SND (f s)) /\
              EVERY (isPREFIX "@") (added_labels s (SND (f s)))`
       >- (gen_tac >> simp[Abbr `f`] >>
           rpt (FIRST [irule comp_bind_labels, irule comp_ignore_bind_labels] >>
             conj_tac >> rpt gen_tac >> BETA_TAC >>
             simp[compile_alloc_buffer_labels,compile_default_return_path_labels,
                  compile_return_value_decode_labels,compile_abi_decode_labels,comp_return_labels])) >>
       first_x_assum (qspec_then `sr` (ACCEPT_TAC o CONJUNCT1)))) >>
  sg `fn_has_code s5 sb1 func /\ fn_has_code sb1 sb2 func /\
      fn_has_code sb2 sb3 func /\ fn_has_code sb3 sp func /\
      fn_has_code sp sr func /\ fn_has_code sr sb func`
  >- (qpat_assum `fn_has_code s5 sb func` mp_tac >>
      POP_ASSUM_LIST (map_every assume_tac o
        List.filter (can (match_term ``cs_extends (a:compile_state) b``) o concl)) >>
      disch_tac >> rpt conj_tac >> irule fragExecTheory.fn_has_code_mid >>
      simp[] >> qexistsl [`sb`,`s5`] >>
      metis_tac[compileEnvTheory.cs_extends_refl,compileEnvTheory.cs_extends_trans]) >>
  suspend "packed"
QED

Resume extcall_request_keyword_packed_cut[packed]:
  qabbrev_tac `tys = MAP (lowered_value_type cenv) xs` >>
  qabbrev_tac `rty = if needs_external_call_wrap rt then TupleT [rt] else rt` >>
  qabbrev_tac `cap = abi_size_bound cenv.ce_struct_fields rty` >>
  qabbrev_tac `value_op = option_CASE vo (Lit 0w) I` >>
  qabbrev_tac `value_opt = if stat then NONE else
    option_CASE (ext_call_kwarg EKValue opts kws) (SOME 0) dest_NumV` >>
  qabbrev_tac `def_op = case def of NONE => Lit 0w | SOME (dop,dt) => dop` >>
  qabbrev_tac `def_ty = case def of NONE => rt | SOME (dop,dt) => dt` >>
  qabbrev_tac `has_def = IS_SOME def` >>
  qabbrev_tac `pack_h = storage_trace_horizon ke.storage_trace` >>
  qabbrev_tac `entry_h = storage_trace_horizon es.storage_trace` >>
  `storage_trace_frame (eval_exprs cx [addr])` by
    simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  `?obs. mid.storage_trace = es.storage_trace ++ obs` by
    (drule_all vyperStorageTraceTheory.storage_trace_frame_prefix >> simp[]) >>
  `valid_horizon cx st0 entry_h es.storage_trace` by
    (`storage_trace_domain cx st0 es.storage_trace` by
       (qpat_assum `mid.storage_trace = es.storage_trace ++ obs` (fn eq =>
          qpat_assum `storage_trace_domain cx st0 mid.storage_trace`
            (ACCEPT_TAC o MATCH_MP vyperStorageFootprintTheory.storage_trace_domain_prefix o
             PURE_REWRITE_RULE [eq]))) >>
     qpat_assum `storage_trace_domain cx st0 es.storage_trace`
       (mp_tac o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def]) >>
     simp[NoAsms, Abbr `entry_h`]) >>
  `valid_horizon cx st0 pack_h ee.storage_trace` by simp[Abbr `pack_h`] >>
  qpat_assum `!K. valid_horizon _ _ K ee.storage_trace ==> stmt_state_rel _ _ _ _ _ ee u /\ _`
    (qspec_then `pack_h` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH vs = LENGTH ats` by
    (qpat_assum `eval_exprs cx xs _ = (INL vs,ee)`
       (mp_tac o MATCH_MP vyperInterpreterTheory.eval_exprs_length) >>
     qpat_assum `arg_types_fit (MAP expr_type xs) ats`
       (mp_tac o MATCH_MP listTheory.LIST_REL_LENGTH o
        REWRITE_RULE [vyperTypeArgFitsTheory.arg_types_fit_LIST_REL]) >>
     simp[]) >>
  `LENGTH kws = LENGTH opts` by
    (qpat_assum `eval_exprs cx kw_es _ = (INL kws,ke)`
       (mp_tac o MATCH_MP vyperInterpreterTheory.eval_exprs_length) >>
     qpat_assum `MAP expr_type kw_es = _`
       (mp_tac o AP_TERM ``LENGTH : type list -> num``) >> simp[]) >>
  mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
    (Q.INST [`H0` |-> `entry_h`, `H` |-> `pack_h`,
      `t0` |-> `t`, `target` |-> `w2w (aw:256 word) : 160 word`,
      `obs3` |-> `gas_explicit kw_marks u.vs_gas_readings`]
      (INST_TYPE [alpha |-> ``:160``] extcall_request_post_gas_packing)))) >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (asm "packing_rows" ACCEPT_TAC) >> TRY REFL_TAC
     >~ [`compile_alloc_buffer _ s5 = _`]
     >- (qpat_assum `compile_alloc_buffer _ s5 = _` mp_tac >>
         simp[NoAsms, Abbr `tys`, Abbr `cap`, Abbr `rty`])
     >~ [`(if av = [] then _ else _) sb2 = _`]
     >- (qpat_assum `(if av = [] then _ else _) sb2 = _` mp_tac >>
         simp[NoAsms, Abbr `tys`, listTheory.MAP_MAP_o, combinTheory.o_DEF])
     >~ [`stmt_state_rel entry_h _ _ _ _ es s0`]
     >- (qpat_assum `!K. valid_horizon _ _ K es.storage_trace ==> _`
           (qspec_then `entry_h` mp_tac) >> simp[])
     >- (rpt strip_tac >> qpat_assum
           `!K. valid_horizon _ _ K ke.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
           drule >> simp[])
     >~ [`rt = NoneT ==> _`]
     >- (qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _`
           (mp_tac o REWRITE_RULE [exprSimHypsDefsTheory.expr_body_pre_def,
             cj 13 vyperTypeSystemTheory.well_typed_expr_def]) >>
         strip_tac >> simp[vyperTypeExtCallSoundnessTheory.ext_call_kwarg_not_mem]) >>
     simp[Abbr `source_gas`, Abbr `pack_h`])) >>
  disch_then (mk_asm "packed") >>
  qexistsl [`sp`,`sr`,`u_ret`,`value_op`,`ba.buf_operand`,`off`,`len`,
            `has_def`,`def_op`,`def_ty`,`w2w (aw:256 word) : 160 word`,
            `value_opt`,`n`,`zg`,`Gg`,`tng`,`gw`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `comp_ignore_bind _ _ sp = (_,sr)` mp_tac >>
      simp[NoAsms, Abbr `value_op`, Abbr `cap`, Abbr `rty`] >>
      POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `vo` >> simp[combinTheory.I_THM])
  >- (simp[NoAsms, Abbr `value_opt`] >> Cases_on `ext_call_kwarg EKValue opts kws` >> simp[NoAsms])
  >- (rpt strip_tac >> qpat_assum
        `!H. valid_horizon _ _ H ke.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
        drule >> simp[]) >>
  asm "packed" mp_tac >>
  simp[NoAsms, Abbr `value_op`, Abbr `value_opt`, Abbr `has_def`, Abbr `def_op`,
       Abbr `def_ty`, Abbr `cap`, Abbr `rty`, Abbr `source_gas`]
QED

Finalise extcall_request_keyword_packed_cut
