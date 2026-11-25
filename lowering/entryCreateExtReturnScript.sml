(* First-exit geometry of external-call return handling. *)
Theory entryCreateExtReturn
Ancestors
  entryCreateEffectFocus entryCreateFocusSpec createSizeDecodeCode extcallReturnDecoderCode
  exprSimExtCallCase abiDecoderVarSequence compileEnv exprLowering
  createSizeCutCode list pair venomInst entryReturnMarkerJoin bodyFullExtCallReturn bodyFullIfExpReach entryReturnMarkerResources entryReturnResourceTransport abiDecodeValidJoint abiDecodeRejectJoint irSupply fragExec fragGasOriginPtr exprLoweringProps bodySim fragFuel entryCreateIntervalLayout vyperInterpreter vyperState words finite_map bodyPtrDefs loweringPosts

Theorem extcall_return_decoder_cut:
  compile_abi_decode_to_buf dst pos MLOAD src hi info a = ((),b) /\
  fn_has_code a b func /\ body_inv tops ctx ce cx /\
  MEM func ctx.ctx_functions ==>
  create_operand_cut a b E ctx func tops cx st0 source (es,s)
Proof
  strip_tac >>
  `create_cut_code {} a b` by
    (mp_tac (Q.INST [`dst` |-> `dst`, `src` |-> `pos`, `load` |-> `MLOAD`,
                     `bop` |-> `src`, `hi` |-> `hi`, `info` |-> `info`]
       create_decode_to_buf_cut_code) >>
     simp[create_cut_targets_def] >> disch_then (qspec_then `a` mp_tac) >>
     qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ a = _`
       (fn th => simp_tac bool_ss [th,pairTheory.SND])) >>
  `EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code a b)` by
    (drule return_decoder_frag_code >>
     simp[EVERY_MEM] >> disch_tac >> gen_tac >> disch_tac >>
     first_x_assum drule >> simp[abi_decoder_reentry_opcode_def] >>
     strip_tac >> simp[]) >>
  irule create_effect_suffix_cut >> metis_tac[]
QED

Theorem extcall_return_void_scope_cut:
  extcall_returned st0 ctx func ce cx NoneT es sa s0 sr addr buf cap
    target has_default default_op default_ty default_opt returnData ee t /\
  comp_return (Lit 0w) sr = (op,sb) ==>
  create_operand_full_scope sr sb E ctx func t [] (OK t) /\
  create_operand_cut sr sb E ctx func tops cx st0 source (ee,t)
Proof
  simp[comp_return_def, extcall_returned_def] >> strip_tac >>
  `create_operand_at sr t` by simp[create_operand_at_def] >>
  fs[create_operand_cut_def] >> metis_tac[create_operand_empty_scope]
QED

Theorem extcall_return_scoped_cut:
  let e = Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt;
      rt = if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type;
      mn = abi_static_size cenv.ce_struct_fields rt;
      info = type_to_abi_dec_info cenv.ce_struct_fields cenv rt
  in
  expr_body_pre cenv cx env e es /\ body_inv tops ctx cenv cx /\
  cap = abi_size_bound cenv.ce_struct_fields rt /\
  (if ret_type = NoneT then comp_return (Lit 0w)
   else if has_default then
     comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
       (\r. compile_default_return_path cenv ret_type default_ty
         buf_op r.buf_operand default_op addr_op skip mn cap info)
   else comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
     (\r. comp_bind (compile_return_value_decode mn cap)
       (\hi. comp_ignore_bind
         (compile_abi_decode_to_buf r.buf_operand (Lit 0w) MLOAD buf_op hi info)
         (comp_return r.buf_operand)))) sr = (result_op,sb) /\
  vv = (if ret_type = NoneT then StackValue ann result_op
        else LocatedValue ann (mk_ptr result_op LocMemory)) /\
  fn_has_code sr sb func /\ fn_inst_ids_distinct func /\
  ALL_DISTINCT (fn_labels func) /\
  (ret_type <> NoneT /\ has_default ==> create_layout sr sb) /\
  (ret_type <> NoneT /\ ~has_default ==>
    !suffix k. sr.cs_next_label <= k ==> sr.cs_current_bb <> fresh_label_output suffix k) /\
  local_ptrs_reserved cenv sa /\ MEM func ctx.ctx_functions /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr_op buf_op
    cap target has_default default_op default_ty default_opt returnData ee t /\
  (IS_SOME default_opt /\ ~is_word_type default_ty ==>
    ?w aid tv. eval_operand default_op t = SOME w /\
      evaluate_type (get_tenv cx) default_ty = SOME tv /\
      FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\ aid < sr.cs_next_id) /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at (DF H) lo d cenv cx ee G tn t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  EVERY (\op. op_taint tn op = {}) [addr_op; buf_op; default_op] /\
  (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
    ptr_mem_ok cx default_ty dv default_op G tn t /\
    (type_memory_bytes cenv default_ty <> 0 ==>
      ?x b sz w. default_op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
        eval_operand default_op t = SOME w /\ b <= w2n w /\
        w2n w + type_memory_bytes cenv default_ty <= b + sz /\
        w2n w + type_memory_bytes cenv default_ty <= t.vs_alloca_next)) /\
  (cap <> 0 ==>
    ?v b sz ro. buf_op = Var v /\ FLOOKUP G v = SOME (b,sz) /\
      eval_operand buf_op t = SOME ro /\ b <= w2n ro /\ w2n ro + cap <= b + sz /\
      (!i. w2n ro <= i /\ i < w2n ro + MIN cap (LENGTH returnData) ==> i NOTIN tn.t_mem)) ==>
  (!source. create_operand_cut sr sb explicit ctx func tops cx st0 source (ee,t)) /\
  ?res r G' tn'.
    (!tail.
      (case (if returnData = [] then default_opt else NONE) of
         SOME default_v =>
           do accounts' <- get_accounts;
              check (skip \/ ext_call_has_code target accounts') "ExtCall target has no code";
              return (Value default_v)
           od
       | NONE =>
           do ret_val <- lift_sum_runtime
                (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
              return (Value ret_val)
           od) (ee with gas_obs := tail) = (res, ee with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (r,G',tn') /\
       create_operand_full_scope sr sb explicit ctx func t [] r /\
       ((?t'. r = OK t' /\ ?tv. res = INL tv /\
          vv_post H ctx func cenv cx e es sa sb s0 (ee with gas_obs := []) tv vv t' /\
          vv_store_bound cx (expr_type e) (lowered_value_type cenv e)
            (ee with gas_obs := []) tv vv t' /\
          t'.vs_current_bb = sb.cs_current_bb /\ t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t' /\ s0.vs_alloca_next <= t'.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) G' tn' t' /\
          ptr_vv_ok cx (post_value_type cenv e) tv vv (ee with gas_obs := []) G' tn' t' /\
          (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
            ?val. read_result cx tv (ee with gas_obs := []) = (INL val, (ee with gas_obs := [])) /\
              !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) t' = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn'.t_mem t'.vs_memory mem ==>
                    val_in_memory rt val (w2n w) mem)) /\
          (!t'' op. vv = StackValue t'' op /\ ~is_word_type (post_value_type cenv e) ==>
            ptr_buf_ok cenv e op G' t') /\
          (!t'' p. vv = LocatedValue t'' p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv e p.ptr_operand G' t') /\
          vv_own cenv cx (post_value_type cenv e) sa sb (ee with gas_obs := []) tv vv t' /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn') \/
        (exit_result r /\ expr_exit res r)))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all (SIMP_RULE bool_ss [LET_THM] extcall_return_layout) >> strip_tac >>
  conj_tac
  >- (gen_tac >> irule create_effect_suffix_cut >> simp[] >> goal_assum drule) >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by fs[body_inv_def] >>
  `no_phi_fn func` by
    (simp[no_phi_fn_def, EVERY_MEM] >> rpt strip_tac >>
     irule body_inv_no_phi >> qexistsl_tac [`cenv`,`ctx`,`cx`,`func`,`tops`] >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE) (frag_code sr sb)` by fs[EVERY_MEM] >>
  `lookup_function func.fn_name ctx.ctx_functions = SOME func /\ create_operand_at sr t` by
    fs[extcall_returned_def,stmt_state_rel_def,alloca_room_def,create_operand_at_def] >>
  qabbrev_tac `id = SUC (FOLDL MAX 0 (MAP (\i. i.inst_id) (fn_insts func)))` >>
  `!i. MEM i (fn_insts func) ==> i.inst_id <> id` by
    (rpt strip_tac >>
     `MEM i.inst_id (MAP (\i. i.inst_id) (fn_insts func))` by (simp[MEM_MAP] >> qexists_tac `i` >> simp[]) >>
     `i.inst_id <= FOLDL MAX 0 (MAP (\i. i.inst_id) (fn_insts func))` by
       (irule foldl_max_bound >> simp[]) >>
     fs[Abbr `id`]) >>
  qabbrev_tac `obsfn = return_marker_fn func sb.cs_current_bb (LENGTH sb.cs_current_insts) id` >>
  qabbrev_tac `obsctx = return_marker_ctx ctx func sb.cs_current_bb (LENGTH sb.cs_current_insts) id` >>
  `return_resource_agree ctx func obsctx obsfn` by
    simp[Abbr `obsctx`,Abbr `obsfn`,extcall_return_marker_agree] >>
  `fn_has_code sr sb obsfn /\ fn_inst_ids_distinct obsfn /\ MEM obsfn obsctx.ctx_functions` by
    simp[Abbr `obsctx`,Abbr `obsfn`,extcall_return_marker_code,
         return_marker_distinct,return_marker_function_mem] >>
  `extcall_returned st0 obsctx obsfn cenv cx ret_type es sa s0 sr addr_op buf_op
     cap target has_default default_op default_ty default_opt returnData ee t` by
    (drule_then (fn th => simp[GSYM th]) extcall_returned_transport) >>
  `alloca_history obsfn t` by
    (simp[Abbr `obsfn`] >> irule (iffRL return_marker_history) >>
     fs[create_operand_at_def]) >>
  mp_tac extcall_return_full >>
  (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC abi_valid_allocated_joint)) >>
  (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC abi_malformed_allocated_joint)) >>
  disch_then (drule_at (Pat `extcall_returned _ obsctx obsfn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_all_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `res` (qx_choose_then `r` (qx_choose_then `J` (qx_choose_then `tau` strip_assume_tac)))))) >>
  qexistsl_tac [`res`,`r`,`J`,`tau`] >> (conj_tac >- first_assum ACCEPT_TAC) >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then (CONJUNCTS_THEN2 assume_tac (mk_asm "observed_post"))) >>
  `(case r of OK u => create_operand_at sb u | _ => exit_result r)` by
    (asm "observed_post" strip_assume_tac
     >- gvs[create_operand_at_def] >> Cases_on `r` >> gvs[exit_result_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (r,J,tau) /\
   create_operand_full_scope sr sb explicit ctx func t [] r` by
    (irule extcall_return_marker_path >> simp[] >> qexists_tac `id` >>
     fs[Abbr `obsctx`, Abbr `obsfn`]) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  asm "observed_post" strip_assume_tac
  >- (disj1_tac >> goal_assum (drule_at Any) >>
      rename1 `res = INL value` >> qexists_tac `value` >>
      (conj_tac >- first_assum ACCEPT_TAC) >>
      rename1 `r = OK u` >>
      `alloca_history func u` by
        (qpat_assum `alloca_history obsfn u` mp_tac >>
         simp_tac bool_ss [Abbr `obsfn`] >>
         dep_rewrite.DEP_REWRITE_TAC [return_marker_history] >> simp[]) >>
      qpat_x_assum `vv = _` (SUBST_ALL_TAC o SYM) >>
      drule_then (fn th => pure_rewrite_tac[th]) extcall_return_post_transport >>
      asm_rewrite_tac[]) >>
  simp[]
QED
