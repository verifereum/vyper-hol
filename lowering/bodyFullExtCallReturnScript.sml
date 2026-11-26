(* Counted return handling after the successful external call. *)
Theory bodyFullExtCallReturn
Ancestors
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  bodyFullExtCallReturnSizedDecode bodyFullExtCallReturnSizeRoute
  bodyFullExtCallReturnDefaultValue bodyFullExtCallReturnVoid
  bodyFullExtCallReturnSource extcallReturnEntryBridge extcallReturnDefaultRouting
  extcallReturnDefaultControlJoint extcallReturnInterface
  exprExtReturnDecodeMetadata exprExtReturnDecodeCoherence
  bodyFullAllocaFresh fragGasEmitCtrl exprSimBopRestWordIterate
  exprSimExtCallCase exprSimWordArgs exprSafeOperand abiCallerAllocation
  abiCallerLocalScratch stateRelProj freshWrites allocaHistory fragGasOriginPtr
  abiValidAllocatedContract abiMalformedRecursiveInterface abiReturnPrefixTransport
  abiDecodePtrMemberFrame exprLoweringProps emitHelperProps fragExec
  loweringPosts loweringStateRelDefs[qualified,ignore_grammar] bodyPtrDefs
  exprSimMemDefs exprSimDefs compileEnv context exprLowering
  ptrDiscipline venomState venomMemDefs vyperInterpreter vyperState vyperABI
  vyperABIValid vyperAST words finite_map pred_set list createSizeExit

Theorem extcall_return_full:
  (!H0 ce env sf ty tv v ctx func cenv cx es st en source hi pos output
    B L xs p d dstid live ceiling s G tn lo PG.
    abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
      st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s /\
    abi_decode_ptr_window G tn s source (n2w B) L /\
    ptr_covers G tn output s (type_memory_bytes ce ty) /\
    op_prov G pos = NONE /\ op_prov G hi = NONE /\
    op_taint tn pos = {} /\ op_taint tn hi = {} /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
    ?u G' tn'.
      abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
        d (type_memory_bytes ce ty) s u /\
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK u,G',tn')) /\
      ptr_covers G' tn' output u (type_memory_bytes ce ty) /\
      abi_decode_ptr_window G' tn' u source (n2w B) L /\
      (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
         val_in_memory tv v d mem) /\
      (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
      tn'.t_imm = tn.t_imm /\
      (!a. ~(d <= a /\ a < d+type_memory_bytes ce ty) /\
           ~abi_malformed_site_range
              (abi_malformed_scratch_sites st en func) s u a 1 ==>
           (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
      alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next) ==>
  (!H0 ce env sf ty tv ctx func cenv cx es st en source hi pos output
    B L xs p d dstid live ceiling s G tn lo PG bytes.
    abi_decoder_coherent ce env sf ty tv /\
    abi_decode_bytes_widths env ty /\
    compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
      (type_to_abi_dec_info sf ce ty) st = ((),en) /\
    fn_has_code st en func /\ fn_inst_ids_distinct func /\
    (?av. has_type (vyper_to_abi_type env ty) av) /\
    assignable_type env ty /\ type_memory_size tv < dimword (:256) /\
    abi_size_bound sf ty < dimword (:256) /\
    abi_malformed_entry H0 ctx func cenv cx es st
      (abi_malformed_scratch_sites st en func) dstid live
      (Var source) hi pos (Var output) B L xs p d (type_memory_bytes ce ty) s /\
    (case type_to_abi_dec_info sf ce ty of DecPrimWord clamp => p+32 <= L | _ => T) /\
    fresh_vars_wrt ceiling s /\ en.cs_next_var <= ceiling.cs_next_var /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    bytes = (if is_dynamic (vyper_to_abi_type env ty) then DROP p xs
      else TAKE (static_length (vyper_to_abi_type env ty)) (DROP p xs)) /\
    ~(vyper_decode_valid_enc (vyper_to_abi_type env ty) bytes /\
      abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bytes)) /\
    abi_decode_ptr_window G tn s source (n2w B) L /\
    ptr_covers G tn output s (type_memory_bytes ce ty) /\
    op_prov G pos = NONE /\ op_prov G hi = NONE /\
    op_taint tn pos = {} /\ op_taint tn hi = {} /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
    ?u G' tn'.
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Abort Revert_abort u,G',tn'))) ==>
  !DF lo d explicit ctx PG func cenv cx env es ann is_static skip fname
   arg_types ret_type opts args dflt st0 sa sb s0 G0 tn0 sr result_op vv
   addr_op buf_op cap target has_default default_op default_ty default_opt
   returnData ee t G tn.
    expr_body_pre cenv cx env
      (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
         args dflt) es /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    cap = abi_size_bound cenv.ce_struct_fields
            (if needs_external_call_wrap ret_type
             then TupleT [ret_type] else ret_type) /\
    (if ret_type = NoneT then comp_return (Lit 0w)
     else if has_default then
       comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
         (\r. compile_default_return_path cenv ret_type default_ty
                buf_op r.buf_operand default_op addr_op skip
                (abi_static_size cenv.ce_struct_fields
                   (if needs_external_call_wrap ret_type
                    then TupleT [ret_type] else ret_type))
                cap
                (type_to_abi_dec_info cenv.ce_struct_fields cenv
                   (if needs_external_call_wrap ret_type
                    then TupleT [ret_type] else ret_type)))
     else
       comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
         (\r. comp_bind (compile_return_value_decode
                     (abi_static_size cenv.ce_struct_fields
                        (if needs_external_call_wrap ret_type
                         then TupleT [ret_type] else ret_type)) cap)
         (\hi_op. comp_ignore_bind
            (compile_abi_decode_to_buf r.buf_operand (Lit 0w) MLOAD
               buf_op hi_op
               (type_to_abi_dec_info cenv.ce_struct_fields cenv
                  (if needs_external_call_wrap ret_type
                   then TupleT [ret_type] else ret_type)))
            (comp_return r.buf_operand)))) sr = (result_op, sb) /\
    vv = (if ret_type = NoneT then StackValue ann result_op
          else LocatedValue ann (mk_ptr result_op LocMemory)) /\
    fn_has_code sr sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    MEM func ctx.ctx_functions /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr_op buf_op
      cap target has_default default_op default_ty default_opt returnData ee t /\
    (IS_SOME default_opt /\ ~is_word_type default_ty ==>
      ?w aid tv. eval_operand default_op t = SOME w /\
        evaluate_type (get_tenv cx) default_ty = SOME tv /\
        FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
        aid < sr.cs_next_id) /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at (DF H) lo d cenv cx ee G tn t) /\
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
       eval_operand buf_op t = SOME ro /\ b <= w2n ro /\
       w2n ro + cap <= b + sz /\
       (!i. w2n ro <= i /\ i < w2n ro + MIN cap (LENGTH returnData) ==>
            i NOTIN tn.t_mem)) ==>
    ?res r G' tn'.
      (!tail.
        (case (if returnData = [] then default_opt else NONE) of
         SOME default_v =>
           do accounts' <- get_accounts;
              check (skip \/ ext_call_has_code target accounts')
                    "ExtCall target has no code";
              return (Value default_v)
           od
       | NONE =>
           do ret_val <- lift_sum_runtime
                (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
              return (Value ret_val)
           od) (ee with gas_obs := tail) =
          (res, ee with gas_obs := tail)) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
          (t, G, tn) [] (r, G', tn') /\
        ((?t'. r = OK t' /\ ?tv. res = INL tv /\
         vv_post H ctx func cenv cx
           (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
              args dflt) es sa sb s0 (ee with gas_obs := []) tv vv t' /\
         vv_store_bound cx
           (expr_type
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
                 args dflt))
           (lowered_value_type cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
                 args dflt)) (ee with gas_obs := []) tv vv t' /\
         t'.vs_current_bb = sb.cs_current_bb /\
         t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
         alloca_history func t' /\ s0.vs_alloca_next <= t'.vs_alloca_next /\
         ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) G' tn' t' /\
         ptr_vv_ok cx
           (post_value_type cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
                 args dflt)) tv vv (ee with gas_obs := []) G' tn' t' /\
         (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
          ?val. read_result cx tv (ee with gas_obs := []) = (INL val, (ee with gas_obs := [])) /\
                !rt w. evaluate_type (get_tenv cx)
                         (post_value_type cenv
                            (Call ann (ExtCall is_static skip
                               (fname,arg_types,ret_type) opts) args dflt)) =
                         SOME rt /\
                       eval_operand (vv_operand vv) t' = SOME w ==>
                       w2n w + type_memory_size rt <= lo /\
                       (!mem. mem_agree_outside tn'.t_mem t'.vs_memory mem ==>
                              val_in_memory rt val (w2n w) mem)) /\
         (!t'' op. vv = StackValue t'' op /\
            ~is_word_type (post_value_type cenv
               (Call ann (ExtCall is_static skip (fname,arg_types,ret_type)
                  opts) args dflt)) ==>
            ptr_buf_ok cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type)
                 opts) args dflt) op G' t') /\
         (!t'' p. vv = LocatedValue t'' p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
                 args dflt) p.ptr_operand G' t') /\
         vv_own cenv cx
           (post_value_type cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
                 args dflt)) sa sb (ee with gas_obs := []) tv vv t' /\
         ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn') \/
         (exit_result r /\ create_size_exit_ok ctx res r /\ expr_exit res r)))
Proof
  disch_then (mk_asm "valid") >> disch_then (mk_asm "reject") >>
  rpt gen_tac >> strip_tac >>
  rename1 `expr_body_pre cenv cx env (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt) es` >>
  Cases_on `ret_type = NoneT`
  >- (drule extcall_return_type_bounds >> strip_tac >>
      `result_op = Lit 0w` by
        (gvs[comp_return_def]) >>
      `vv = StackValue NoneT (Lit 0w)` by simp[] >>
      `!tv z. vv_own cenv cx
        (post_value_type cenv (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts)
          args dflt)) sa sb (ee with gas_obs := []) tv vv z` by
        (simp[post_value_type_def, expr_type_def, vv_own_def,
              expr_val_own_def, eval_operand_def] >>
         rpt strip_tac >> Cases_on `v` >>
         simp[val_footprint_def, valueEncodingTheory.type_memory_size_def]) >>
      qpat_assum `!tv z. vv_own _ _ (post_value_type _ _) _ _ _ tv _ z`
        (fn th => pure_rewrite_tac [th, boolTheory.AND_CLAUSES]) >>
      match_mp_tac extcall_return_step_void >>
      goal_assum (drule_at (Pat `extcall_returned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      qexists_tac `env` >> gvs[] >> rpt strip_tac >>
      qpat_x_assum `!dv. default_opt = SOME dv /\ _ ==> _`
        (drule_all_then strip_assume_tac) >>
      qpat_x_assum `type_memory_bytes cenv default_ty <> 0 ==> _`
        (drule_then strip_assume_tac) >>
      goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `has_default /\ returnData = []`
  >- (match_mp_tac extcall_return_full_default_value >>
      goal_assum (drule_at (Pat `extcall_returned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      qexists_tac `env` >> gvs[]) >>
  qspecl_then [`cx`,`ret_type`,`returnData`,`default_opt`,`skip`,`target`,`ee`]
    (qx_choose_then `res` assume_tac) extcall_return_source_tail >>
  qexists_tac `res` >> simp[] >>
  Cases_on `?H. valid_horizon cx st0 H ee.storage_trace`
  >- suspend "has_horizon" >>
  qexistsl_tac [`OK t`,`G`,`tn`] >>
  qpat_assum `~(?H. valid_horizon cx st0 H _)`
    (mp_tac o CONV_RULE NOT_EXISTS_CONV) >>
  disch_then (fn th => gen_tac >> simp_tac bool_ss [th])
QED

Resume extcall_return_full[has_horizon]:
      drule extcall_return_type_bounds >> strip_tac >>
      `?actual_tv. evaluate_type (get_tenv cx) ret_type = SOME actual_tv` by
        (drule exprSimHypsTheory.expr_body_pre_type_evaluates >>
         simp[expr_type_def, optionTheory.IS_SOME_EXISTS]) >>
      `type_memory_bytes cenv ret_type = type_memory_size actual_tv` by
        (drule_all extcall_return_memory_size >> simp[]) >>
      `type_memory_size actual_tv + 64 < dimword (:256)` by
        (drule_all extcall_return_store_bound >> simp[]) >>
      `type_memory_bytes cenv ret_type < dimword (:256)` by decide_tac >>
      namedCases_on `compile_alloc_buffer (type_memory_bytes cenv ret_type) sr`
        ["buf ar"] >>
      `cs_extends sr ar` by
        (mp_tac (Q.SPECL [`type_memory_bytes cenv ret_type`, `sr`]
          ci_mono_compile_alloc_buffer) >> simp[ci_mono_def]) >>
      `cs_extends ar sb` by
        (qpat_x_assum `(if ret_type = NoneT then _ else _) sr = _` mp_tac >>
         (Cases_on `has_default` >>
          simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
               IgnAsm `type_memory_bytes cenv ret_type = type_memory_size actual_tv`])
         >- (disch_tac >>
             qpat_assum `compile_default_return_path _ _ _ _ _ _ _ _ _ _ _ ar = _`
               (SUBST1_TAC o SYM o REWRITE_RULE [pairTheory.SND] o AP_TERM ``SND : operand # compile_state -> compile_state``) >>
             simp[REWRITE_RULE[ci_mono_def] ci_mono_compile_default_return_path]) >>
         pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
         disch_then (SUBST_ALL_TAC o GSYM o CONJUNCT2) >>
         irule cs_extends_trans >> qexists_tac `cs'` >>
         conj_tac
         >- (qpat_assum `compile_return_value_decode _ _ ar = _`
               (SUBST1_TAC o SYM o REWRITE_RULE [pairTheory.SND] o AP_TERM ``SND : operand # compile_state -> compile_state``) >>
             simp[REWRITE_RULE[ci_mono_def] ci_mono_compile_return_value_decode]) >>
         qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ cs' = _`
           (SUBST1_TAC o SYM o REWRITE_RULE [pairTheory.SND] o AP_TERM ``SND : unit # compile_state -> compile_state``) >>
         simp[REWRITE_RULE[ci_mono_def] (cj 1 ci_mono_compile_abi_decode)]) >>
      `fn_has_code sr ar func` by
        (irule fn_has_code_mid >> simp[] >>
         qexistsl_tac [`sb`,`sr`] >> simp[cs_extends_refl]) >>
      drule_all bodyFullExtCallReturnDefaultValueTheory.extcall_default_return_alloc_cut >>
      disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
      qhdtm_assum `extcall_returned`
        (strip_assume_tac o REWRITE_RULE [extcall_returned_def]) >>
      qabbrev_tac `rt = if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type` >>
      qabbrev_tac `rtv = if needs_external_call_wrap ret_type then TupleTV [actual_tv] else actual_tv` >>
      `rt = (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type) /\
       rtv = (if needs_external_call_wrap ret_type then TupleTV [actual_tv] else actual_tv)` by
        simp[Abbr `rt`, Abbr `rtv`] >>
      drule_all extcallReturnDefaultTypesTheory.return_default_wrapped_types >> strip_tac >>
      drule_all extcallReturnDefaultTypesTheory.return_default_decode_bounds >> strip_tac >>
      `cap < dimword (:256)` by
        (qpat_assum `rt = _` (fn th => fs[GSYM th])) >>
      `?tys. rt = TupleT tys` by
        (qpat_assum `rt = _` (SUBST1_TAC) >>
         PURE_REWRITE_TAC [needs_external_call_wrap_extcall] >>
         Cases_on `ret_type` >> simp[] >> IF_CASES_TAC >> simp[]) >>
      `cap <> 0` by
        (rename1 `rt = TupleT tys` >>
         `0 < abi_static_size cenv.ce_struct_fields rt` suffices_by
           (qpat_assum `cap = abi_size_bound _ rt` mp_tac >>
            qpat_assum `abi_static_size _ rt <= _` mp_tac >> decide_tac) >>
         qpat_x_assum `rt = TupleT tys` SUBST_ALL_TAC >>
         qpat_assum `assignable_type (get_tenv cx) (TupleT tys)` mp_tac >>
         qpat_assum `abi_decoder_coherent _ _ _ (TupleT tys) _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         Cases_on `tys` >>
         simp[vyperTypeSystemTheory.assignable_type_def,
              abiDecoderCoherenceTheory.abi_decoder_coherent_tuple_iff] >>
         strip_tac >> Cases_on `tvs` >> gvs[] >> strip_tac >>
         rename1 `abi_decoder_coherent _ _ _ hd _` >>
         `0 < abi_embedded_static_size cenv.ce_struct_fields hd` by
           (irule exprSimAbiDecodeComplexOutcomeTheory.abi_decode_assignable_embedded_head_positive >>
            goal_assum (drule_at Any) >> simp[SF SFY_ss]) >>
         simp[abi_static_size_def, GSYM abi_embedded_static_size_def]) >>
      `(if returnData = [] then default_opt else NONE) = NONE` by
        (qhdtm_assum `extcall_default_ready` mp_tac >>
         qpat_assum `~(has_default /\ returnData = [])` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         Cases_on `default_opt` >> simp[extcall_default_ready_def] >> metis_tac[]) >>
      `!tail. bind (lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ret_type returnData))
         (\v. return (Value v)) (ee with gas_obs := tail) = (res,ee with gas_obs := tail)` by
        (qpat_assum `!tail. (case _ of NONE => _ | SOME _ => _) _ = _` mp_tac >>
         simp_tac bool_ss [optionTheory.option_case_def] >>
         qpat_assum `(if returnData = [] then default_opt else NONE) = NONE`
           (fn th => simp_tac bool_ss [th,optionTheory.option_case_def])) >>
      drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
      `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ar x) /\
       (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ar x)` by
        (conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
         simp[not_fresh_at_mono] >> decide_tac) >>
      `local_ptrs_reserved cenv ar` by
        (irule local_ptrs_reserved_next_var >> qexists_tac `sr` >> simp[]) >>
      `fn_has_code ar sb func` by
        (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`,`sr`] >> simp[cs_extends_refl]) >>
      Q.SUBGOAL_THEN `result_op = Var q /\
       ?k hi hs de p Gp tp.
         compile_return_value_decode (abi_static_size cenv.ce_struct_fields rt) cap k = (hi,hs) /\
         compile_abi_decode_to_buf buf.buf_operand (Lit 0w) MLOAD buf_op hi
           (type_to_abi_dec_info cenv.ce_struct_fields cenv rt) hs = ((),de) /\
         fn_has_code k hs func /\ fn_has_code hs de func /\ ci_mono ar k /\
         (de = sb \/ ?xl cj old. emit_inst JMP [Label xl] [] de = ((),cj) /\
            fn_has_code de cj func /\ new_block xl cj = (old,sb)) /\
         (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK p,Gp,tp)) /\
         ~p.vs_halted /\ p.vs_current_bb = k.cs_current_bb /\
         p.vs_inst_idx = LENGTH k.cs_current_insts /\ p.vs_returndata = returnData /\
         p.vs_allocas = a.vs_allocas /\ p.vs_alloca_next = a.vs_alloca_next /\
         p.vs_memory = a.vs_memory /\ alloca_history func p /\ allocas_from lo p /\
         tp.t_mem = tm.t_mem /\
         (!x. not_fresh_at ar x ==> lookup_var x p = lookup_var x a /\
           FLOOKUP Gp x = FLOOKUP J x /\ op_taint tp (Var x) = op_taint tm (Var x)) /\
         (!H. valid_horizon cx st0 H ee.storage_trace ==>
           stmt_state_rel H ctx func cenv cx ee p /\
           storage_well_formed_on cx ee (FST H) /\
           ghost_inv_at (DF H) lo d cenv cx ee Gp tp p) /\
         ghost_kept_at lo cenv es sa G0 tn0 s0 Gp tp /\ wb_frame cenv es ee sa s0 p`
        (CONJUNCTS_THEN2 assume_tac (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS))) >-
      (reverse (Cases_on `has_default`)
         >- (qpat_x_assum `(if ret_type = NoneT then _ else _) sr = _` mp_tac >>
             qpat_assum `ret_type <> NoneT` (fn nr =>
               qpat_assum `compile_alloc_buffer _ sr = _` (fn al =>
                 simp_tac (srw_ss()) [nr, al, comp_bind_def, comp_ignore_bind_def,
                                     comp_return_def, LET_THM, pairTheory.UNCURRY])) >>
             namedCases_on `compile_return_value_decode (abi_static_size cenv.ce_struct_fields rt) cap ar`
               ["hi hs"] >>
             qpat_assum `compile_return_value_decode _ _ ar = (hi,hs)`
               (fn th => simp_tac (srw_ss()) [th]) >>
             namedCases_on `compile_abi_decode_to_buf buf.buf_operand (Lit 0w) MLOAD buf_op hi
               (type_to_abi_dec_info cenv.ce_struct_fields cenv rt) hs` ["ignored de"] >>
             Cases_on `ignored` >>
             qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ hs = ((),de)`
               (fn th => simp_tac (srw_ss()) [th]) >>
             disch_then (CONJUNCTS_THEN2 assume_tac SUBST_ALL_TAC) >>
             `cs_extends ar hs` by
               (qpat_assum `compile_return_value_decode _ _ ar = _`
                  (SUBST1_TAC o SYM o REWRITE_RULE [pairTheory.SND] o AP_TERM ``SND : operand # compile_state -> compile_state``) >>
                simp[REWRITE_RULE[ci_mono_def] ci_mono_compile_return_value_decode]) >>
             `cs_extends hs sb` by
               (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ hs = _`
                  (SUBST1_TAC o SYM o REWRITE_RULE [pairTheory.SND] o AP_TERM ``SND : unit # compile_state -> compile_state``) >>
                simp[REWRITE_RULE[ci_mono_def] (cj 1 ci_mono_compile_abi_decode)]) >>
             `fn_has_code ar hs func /\ fn_has_code hs sb func` by
               (conj_tac >> irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`,`ar`] >> simp[cs_extends_refl]) >>
             conj_tac >-
               (qpat_assum `buf.buf_operand = result_op` (SUBST1_TAC o SYM) >>
                first_assum ACCEPT_TAC) >>
             qexistsl_tac [`ar`,`hi`,`hs`,`sb`,`a`,`J`,`tm`] >> gvs[ci_mono_refl]) >>
         `returnData <> []` by
           (qpat_assum `~(T /\ returnData = [])` mp_tac >> simp_tac bool_ss []) >>
         `compile_default_return_path cenv ret_type default_ty buf_op buf.buf_operand
            default_op addr_op skip (abi_static_size cenv.ce_struct_fields rt) cap
            (type_to_abi_dec_info cenv.ce_struct_fields cenv rt) ar = (result_op,sb)` by
           (qpat_x_assum `(if ret_type = NoneT then _ else _) sr = _` mp_tac >>
            simp[comp_bind_def, IgnAsm `type_memory_bytes cenv ret_type = type_memory_size actual_tv`]) >>
         drule return_default_path_intervals >> strip_tac >>
         drule_all return_default_intervals_code >> strip_tac >>
         `LENGTH a.vs_returndata < dimword (:256)` by simp[] >>
         `ctx_has_dalloca ctx ==> allocas_below_fmp a` by
        (qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
           (qx_choose_then `Hroom` assume_tac) >>
         qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ a /\ _`
           (drule_then (ACCEPT_TAC o MATCH_MP
             bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o CONJUNCT1))) >>
         drule_at (Pat `emit_op RETURNDATASIZE _ ar = _`)
           (INST_TYPE [alpha |-> ``:256``] return_default_shell_entry) >>
         disch_then (drule_all_then (qspecl_then [`tm`,`explicit`,`PG`,`J`]
           (qx_choose_then `u` (qx_choose_then `J'` (qx_choose_then `tm'` (fn th =>
             let
               val clauses = CONJUNCTS th
               val frame_start = length clauses - 4
             in
               EVERY (map assume_tac (List.take (clauses, frame_start)) @
                 ListPair.mapEq (fn (name, clause) => markerLib.mk_asm name clause)
                   (["shell_state", "shell_ghost", "shell_kept", "shell_writeback"],
                    List.drop (clauses, frame_start)))
             end)))))) >>
         conj_tac >-
           (qpat_assum `result_op = buf.buf_operand` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
         `ci_mono de ck` by
           (qpat_assum `(if skip then _ else _) de = ((),ck)` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `skip` >-
              simp[comp_return_def,ci_mono_refl] >>
            simp[compile_extcodesize_check_def,comp_bind_def] >>
            pairarg_tac >> simp[] >> strip_tac >>
            metis_tac[ci_mono_emit_op,ci_mono_emit_void,ci_mono_trans,pairTheory.SND]) >>
         `ci_mono ar cs` by
           (map_every (fn (mid,eq,th) => irule ci_mono_trans >> qexists_tac mid >> conj_tac >-
              (qpat_assum eq mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[th,pairTheory.SND]))
              [(`a1`,`emit_op RETURNDATASIZE _ ar = _`,ci_mono_emit_op),
               (`a2`,`emit_op ISZERO _ a1 = _`,ci_mono_emit_op),
               (`a3`,`fresh_label _ a2 = _`,ci_mono_fresh_label),
               (`a4`,`fresh_label _ a3 = _`,ci_mono_fresh_label),
               (`a5`,`fresh_label _ a4 = _`,ci_mono_fresh_label),
               (`a6`,`emit_inst JNZ _ _ a5 = _`,ci_mono_emit_inst),
               (`ds`,`new_block _ a6 = _`,ci_mono_new_block),
               (`de`,`compile_store_memory _ _ _ _ _ ds = _`,ci_mono_compile_store_memory)] >>
            irule ci_mono_trans >> qexists_tac `ck` >> conj_tac >- first_assum ACCEPT_TAC >>
            irule ci_mono_trans >> qexists_tac `dj` >> conj_tac >-
              (qpat_assum `emit_inst JMP _ _ ck = _` mp_tac >>
               POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ci_mono_emit_inst,pairTheory.SND]) >>
            qpat_assum `new_block cl dj = _` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ci_mono_new_block,pairTheory.SND]) >>
         every_drule_then strip_assume_tac new_block_props >>
         `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK u,J',tm')` by
           (qx_gen_tac `D` >>
            qpat_assum `!D. gas_origin_ptr_path _ (t,G,tn) [] (OK a,J,tm)`
              (qspec_then `D` mp_tac) >>
            qpat_assum `!D. gas_origin_ptr_path _ (a,J,tm) [] (OK u,J',tm')`
              (qspec_then `D` mp_tac) >>
            POP_ASSUM_LIST (K ALL_TAC) >>
            metis_tac[gas_origin_ptr_path_append,listTheory.APPEND]) >>
         `!H. valid_horizon cx st0 H ee.storage_trace ==>
            stmt_state_rel H ctx func cenv cx ee u /\ storage_well_formed_on cx ee (FST H) /\
            ghost_inv_at (DF H) lo d cenv cx ee J' tm' u` by
           (qx_gen_tac `h` >> strip_tac >>
            qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ a /\ _`
              (drule_then strip_assume_tac) >>
            simp[markerLib.L "shell_state", markerLib.L "shell_ghost"]) >>
         `ghost_kept_at lo cenv es sa G0 tn0 s0 J' tm' /\ wb_frame cenv es ee sa s0 u` by
           simp[markerLib.L "shell_kept", markerLib.L "shell_writeback"] >>
         qexistsl_tac [`cs`,`hi`,`hs`,`he`,`u`,`J'`,`tm'`] >>
         simp[IgnAsm `result_op = buf.buf_operand`,allocas_from_def] >>
         conj_tac >- (disj2_tac >> qexistsl_tac [`xl`,`cj`,`old3`] >> simp[]) >>
         first_assum (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp p` by
        (qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
           (qx_choose_then `Hroom` assume_tac) >>
         qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ p /\ _`
           (drule_then (ACCEPT_TAC o MATCH_MP
             bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o CONJUNCT1))) >>
      drule_at (Pat `compile_return_value_decode _ _ _ = _`)
        extcall_return_size_route >>
      disch_then (drule_all_then mp_tac) >>
      Cases_on `LENGTH returnData < abi_static_size cenv.ce_struct_fields rt`
      >- (qpat_assum `LENGTH returnData < abi_static_size _ rt`
            (fn th => simp_tac bool_ss [th]) >>
          disch_then (qx_choose_then `az` (qx_choose_then `aG` (qx_choose_then `atn` assume_tac))) >>
          Cases_on `evaluate_abi_decode_return (get_tenv cx) ret_type returnData`
          >- (`abi_static_size cenv.ce_struct_fields rt <= LENGTH returnData` by
                (drule_all extcallReturnDefaultTypesTheory.return_default_source_success >>
                 qpat_assum `rt = (if needs_external_call_wrap ret_type then _ else _)`
                   (fn th => pure_rewrite_tac [GSYM th]) >>
                 qpat_assum `abi_static_size _ rt = abi_static_length _`
                   (fn th => pure_rewrite_tac [GSYM th]) >>
                 strip_tac >> first_assum ACCEPT_TAC) >>
              `F` by
                (qpat_assum `LENGTH returnData < abi_static_size _ rt` mp_tac >>
                 qpat_assum `abi_static_size _ rt <= LENGTH returnData` mp_tac >>
                 decide_tac)) >>
          qexistsl_tac [`Abort Revert_abort az`,`aG`,`atn`] >>
          gen_tac >> disch_tac >> conj_tac >- simp[] >>
          qpat_x_assum `!tail. bind _ _ (ee with gas_obs := tail) = _`
            (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss())
              [bind_def,lift_sum_runtime_def,raise_def])) >>
          gvs[create_size_exit_ok_non_exhalt,expr_exit_def,exit_result_def]) >>
      qpat_assum `~(LENGTH returnData < abi_static_size _ rt)`
        (fn th => simp_tac bool_ss [th]) >>
      `abi_static_size cenv.ce_struct_fields rt <= LENGTH returnData` by decide_tac >>
      qpat_assum `cap <> 0 ==> _` (drule_then
        (qx_choose_then `source` (qx_choose_then `prov_base` (qx_choose_then `span`
          (qx_choose_then `rw` (map_every assume_tac o CONJUNCTS)))))) >>
      `rw = ro` by
        (qpat_assum `eval_operand buf_op t = SOME rw` mp_tac >>
         qpat_assum `eval_operand buf_op t = SOME ro`
           (fn th => pure_rewrite_tac [th,optionTheory.SOME_11]) >>
         disch_then (ACCEPT_TAC o SYM)) >>
      qpat_x_assum `rw = ro` SUBST_ALL_TAC >>
      disch_then (qspecl_then
        [`abi_malformed_scratch_sites hs de func`,`type_memory_bytes cenv ret_type`,
         `live`,`ee`,`sr.cs_next_id`,`Var q`,`w2n w`,`cx`,`cenv`,`Var source`,`w2n ro`]
        (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tu` strip_assume_tac)))) >>
      `k.cs_next_id <= hs.cs_next_id /\ k.cs_next_var <= hs.cs_next_var` by
        (qpat_assum `compile_return_value_decode _ _ k = _`
          (SUBST1_TAC o SYM o REWRITE_RULE [pairTheory.SND] o AP_TERM ``SND : operand # compile_state -> compile_state``) >>
         simp[REWRITE_RULE[ci_mono_def] ci_mono_compile_return_value_decode]) >>
      qpat_assum `ci_mono ar k` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
      `not_fresh_at sr source` by
        (qpat_assum `EVERY (safe_operand sr) _` mp_tac >>
         qpat_assum `buf_op = Var source`
           (fn th => simp_tac (srw_ss()) [th,safe_operand_def])) >>
      `not_fresh_at ar source` by
        (irule not_fresh_at_mono >> qexists_tac `sr` >> simp[]) >>
      `not_fresh_at k source /\ not_fresh_at k q` by
        (conj_tac >> irule not_fresh_at_mono >> qexists_tac `ar` >> simp[]) >>
      `local_ptrs_reserved cenv k` by
        (irule local_ptrs_reserved_next_var >> qexists_tac `ar` >> simp[]) >>
      qpat_assum `?H. valid_horizon cx st0 H _` (qx_choose_then `H0` assume_tac) >>
      `alloca_inv t /\ alloca_inv p` by
        (conj_tac >- (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
         qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ p /\ _`
           (drule_then strip_assume_tac) >>
         drule_at (Pat `stmt_state_rel _ _ _ _ _ _ p`) stmt_state_rel_local_ptrs_alloca >> simp[]) >>
      `lookup_var source p = lookup_var source t /\ FLOOKUP Gp source = FLOOKUP G source /\
       op_taint tp (Var source) = op_taint tn (Var source)` by
        (qpat_assum `!x. not_fresh_at ar x ==> lookup_var x p = lookup_var x a /\ _`
           (qspec_then `source` (drule_then strip_assume_tac)) >>
         qpat_assum `!x. not_fresh_at sr x ==> lookup_var x a = lookup_var x t /\ _`
           (qspec_then `source` (drule_then strip_assume_tac)) >> asm_rewrite_tac[]) >>
      `lookup_var q p = SOME w /\ ptr_covers Gp tp q p (type_memory_bytes cenv ret_type)` by
        (qpat_assum `!x. not_fresh_at ar x ==> lookup_var x p = lookup_var x a /\ _`
           (qspec_then `q` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
         conj_tac >- asm_rewrite_tac[] >>
         irule decoderGhostFramePtrTheory.ptr_covers_frame >>
         goal_assum (drule_at (Pat `ptr_covers J tm q a _`)) >> asm_rewrite_tac[]) >>
      `abi_malformed_destination func cenv ee.scopes sr.cs_next_id
         (w2n w) (type_memory_bytes cenv ret_type) p` by
        (drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
         simp[abi_malformed_destination_def] >>
         qexistsl_tac [`mk_inst sr.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv ret_type))]
               [STRING #"%" (toString sr.cs_next_var)]`,
           `STRING #"%" (toString sr.cs_next_var)`] >>
         simp[venomInstTheory.mk_inst_def] >> irule local_ptrs_reserved_fresh >>
         qexists_tac `sr` >> simp[]) >>
      `!H. valid_horizon cx st0 H ee.storage_trace ==>
         abi_return_decode_ready H ctx func cenv cx ee k (abi_malformed_scratch_sites hs de func)
           sr.cs_next_id live (Var source) (Var q) (w2n ro) cap returnData (w2n w)
           (type_memory_bytes cenv ret_type) p` by
        (gen_tac >> strip_tac >>
         qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ p /\ _`
           (drule_then strip_assume_tac) >>
         simp_tac bool_ss [abi_return_decode_ready_def] >>
         ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
         conj_tac >-
           (simp_tac bool_ss [abi_malformed_allocated_window_def] >>
            conj_tac >-
              (qexists_tac `buf_size` >> conj_tac >-
                 (qpat_assum `p.vs_allocas = a.vs_allocas` SUBST1_TAC >>
                  first_assum irule >> first_assum ACCEPT_TAC) >>
               simp_tac (srw_ss()) [listTheory.LENGTH_TAKE_EQ] >> decide_tac) >>
            conj_tac >-
              (simp_tac (srw_ss()) [listTheory.LENGTH_TAKE_EQ] >> decide_tac) >>
            qpat_assum `p.vs_memory = a.vs_memory` SUBST1_TAC >>
            qpat_assum `a.vs_memory = t.vs_memory` SUBST1_TAC >>
            first_assum ACCEPT_TAC) >>
         conj_tac >- (irule abi_malformed_scratch_sites_older >> decide_tac) >>
         conj_tac >- decide_tac >>
         conj_tac >- (irule abi_malformed_scratch_sites_older >> decide_tac) >>
         ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
         conj_tac >-
           (simp[eval_operand_def] >>
            qpat_assum `eval_operand buf_op t = SOME ro` mp_tac >>
            qpat_assum `buf_op = Var source`
              (fn th => simp_tac (srw_ss()) [th,eval_operand_def])) >>
         conj_tac >- simp[eval_operand_def] >>
         simp[listTheory.EVERY_DEF,abiDecoderReentryTheory.abi_decoder_operand_live_def,
              abiDecoderReentryTheory.abi_decoder_older_vars_def,
              GSYM loweringStateRelDefsTheory.not_fresh_at_def]) >>
      `!H. valid_horizon cx st0 H ee.storage_trace ==>
        abi_malformed_entry H ctx func cenv cx ee hs (abi_malformed_scratch_sites hs de func)
          sr.cs_next_id live (Var source) hi (Lit 0w) (Var q) (w2n ro)
          (LENGTH (TAKE cap returnData)) (TAKE cap returnData) 0 (w2n w)
          (type_memory_bytes cenv ret_type) u` by
        (gen_tac >> strip_tac >> first_assum irule >> first_assum irule >> simp[]) >>
      `lookup_var source u = lookup_var source t /\ FLOOKUP Gu source = FLOOKUP G source /\
       op_taint tu (Var source) = op_taint tn (Var source)` by
        (qpat_assum `!x. not_fresh_at k x ==> lookup_var x u = lookup_var x p /\ _`
           (qspec_then `source` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> asm_rewrite_tac[]) >>
      `!i. i < t.vs_alloca_next ==> (i IN tu.t_mem <=> i IN tn.t_mem)` by
        (qpat_assum `tu.t_mem = tp.t_mem` SUBST1_TAC >>
         qpat_assum `tp.t_mem = tm.t_mem` SUBST1_TAC >>
         qpat_assum `!i. i IN tm.t_mem <=> _` (fn th => pure_rewrite_tac [th]) >>
         gen_tac >> strip_tac >>
         `~(t.vs_alloca_next <= i)` by decide_tac >> asm_rewrite_tac[]) >>
      `ptr_covers Gu tu q u (type_memory_bytes cenv ret_type)` by
        (first_assum irule >> asm_rewrite_tac[]) >>
      `sa.cs_next_var <= k.cs_next_var /\ sa.cs_next_var <= hs.cs_next_var /\
       sa.cs_next_id <= hs.cs_next_id /\ sr.cs_next_id < sb.cs_next_id` by
        (`hs.cs_next_id <= de.cs_next_id` by
           (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ hs = _`
              (SUBST1_TAC o SYM o REWRITE_RULE [pairTheory.SND] o AP_TERM ``SND : unit # compile_state -> compile_state``) >>
            simp[REWRITE_RULE[ci_mono_def] (cj 1 ci_mono_compile_abi_decode)]) >>
         `de.cs_next_id <= sb.cs_next_id` by
           (qpat_assum `de = sb \/ _` strip_assume_tac >- simp[] >>
            qpat_assum `emit_inst JMP _ _ de = _` mp_tac >>
            qpat_assum `new_block _ _ = (_,sb)` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >>
            metis_tac[ci_mono_emit_inst,ci_mono_new_block,ci_mono_trans,ci_mono_def,pairTheory.SND]) >>
         qpat_assum `sa.cs_next_var <= sr.cs_next_var` mp_tac >>
         qpat_assum `sa.cs_next_id <= sr.cs_next_id` mp_tac >>
         qpat_assum `ar.cs_next_var = sr.cs_next_var + 1` mp_tac >>
         qpat_assum `ar.cs_next_id = sr.cs_next_id + 1` mp_tac >>
         qpat_assum `ar.cs_next_var <= k.cs_next_var` mp_tac >>
         qpat_assum `ar.cs_next_id <= k.cs_next_id` mp_tac >>
         qpat_assum `k.cs_next_var <= hs.cs_next_var` mp_tac >>
         qpat_assum `k.cs_next_id <= hs.cs_next_id` mp_tac >>
         qpat_assum `hs.cs_next_id <= de.cs_next_id` mp_tac >>
         qpat_assum `de.cs_next_id <= sb.cs_next_id` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
      `alloca_history func u /\ wb_frame cenv es ee sa s0 u /\
       s0.vs_alloca_next <= u.vs_alloca_next` by
        (conj_tac >- (first_assum irule >> asm_rewrite_tac[]) >>
         conj_tac >- (first_assum irule >> asm_rewrite_tac[]) >>
         decide_tac) >>
      `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
       (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x)` by
        (conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      `!H. valid_horizon cx st0 H ee.storage_trace ==>
       storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ee Gu tu u` by
        (gen_tac >> strip_tac >>
         qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ p /\ _`
           (drule_then strip_assume_tac) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         first_assum irule >> asm_rewrite_tac[]) >>
      `ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu` by
        (irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
         goal_assum (drule_at (Pat `ghost_kept_at lo cenv es sa G0 tn0 s0 Gp tp`)) >>
         reverse conj_tac >- asm_rewrite_tac[pred_setTheory.SUBSET_REFL] >>
         qx_gen_tac `x` >> strip_tac >>
         `not_fresh_at k x` by
           (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
         qpat_assum `!x. not_fresh_at k x ==> lookup_var x u = lookup_var x p /\ _`
           (qspec_then `x` mp_tac) >> simp[]) >>
      `compile_abi_decode_to_buf (Var q) (Lit 0w) MLOAD (Var source) hi
         (type_to_abi_dec_info cenv.ce_struct_fields cenv rt) hs = ((),de)` by
        (qpat_assum `compile_abi_decode_to_buf buf.buf_operand _ _ buf_op _ _ hs = _` mp_tac >>
         qpat_assum `buf.buf_operand = Var q` (fn bo =>
           qpat_assum `buf_op = Var source` (fn src => rewrite_tac [bo,src]))) >>
      suspend "after_size"
QED

Resume extcall_return_full[after_size]:
      asm "valid" (fn valid => asm "reject" (fn reject =>
        qpat_assum `rt = (if needs_external_call_wrap ret_type then _ else _)` (fn wrap =>
          qpat_assum `type_memory_bytes cenv rt = type_memory_bytes cenv ret_type` (fn bytes =>
            drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ hs = _`)
              (SIMP_RULE bool_ss [LET_THM,GSYM wrap,bytes]
                (MATCH_MP (MATCH_MP extcall_return_sized_decode valid) reject)))))) >>
      `eval_operand (Var source) t = SOME ro /\ op_taint tn (Var source) = {}` by
        (qpat_assum `buf_op = Var source` (SUBST1_TAC o SYM) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qpat_assum `EVERY (\op. op_taint tn op = {}) _`
           (strip_assume_tac o BETA_RULE o REWRITE_RULE [listTheory.EVERY_DEF]) >>
         first_assum ACCEPT_TAC) >>
      map_every (fn pat => disch_then (fn th => qpat_assum pat (mp_then Any mp_tac th)))
        [`!H. valid_horizon _ _ H _ ==> abi_malformed_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`,
         `eval_operand (Var source) t = SOME ro`, `op_taint tn (Var source) = {}`,
         `expr_body_pre _ _ _ _ es`, `wb_frame cenv es ee sa s0 u`,
         `ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu`,
         `!H. valid_horizon cx st0 H _ ==> storage_well_formed_on cx ee (FST H) /\ ghost_inv_at _ lo d cenv cx ee Gu tu u`,
         `evaluate_type (get_tenv cx) ret_type = SOME actual_tv`,
         `valid_horizon cx st0 H0 _`, `sr.cs_next_id < sb.cs_next_id`,
         `FLOOKUP t.vs_allocas live = SOME (w2n ro,buf_size)`,
         `FLOOKUP G source = SOME (prov_base,span)`] >>
      disch_then (qspec_then `PG` mp_tac) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      reverse (Cases_on `evaluate_abi_decode_return (get_tenv cx) ret_type returnData`) >>
      simp_tac bool_ss [sumTheory.sum_case_def]
      >- suspend "decode_reject" >>
      suspend "decode_success"
QED

Resume extcall_return_full[decode_reject]:
      disch_then (qx_choose_then `z` (qx_choose_then `Gd` (qx_choose_then `td` assume_tac))) >>
          qexistsl_tac [`Abort Revert_abort z`,`Gd`,`td`] >>
          qx_gen_tac `H` >> disch_tac >> conj_tac >-
            (qpat_assum `!D. gas_origin_ptr_path _ (t,G,tn) [] (OK u,Gu,tu)`
               (qspec_then `DF H` mp_tac) >>
             qpat_assum `!D explicit. gas_origin_ptr_path _ (u,Gu,tu) [] (Abort Revert_abort z,Gd,td)`
               (qspecl_then [`DF H`,`explicit`] mp_tac) >>
             POP_ASSUM_LIST (K ALL_TAC) >>
             metis_tac[gas_origin_ptr_path_append,listTheory.APPEND]) >>
          qpat_x_assum `!tail. bind _ _ (ee with gas_obs := tail) = _`
            (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss())
              [bind_def,lift_sum_runtime_def,raise_def])) >>
          qpat_x_assum `INR _ = res` (SUBST1_TAC o SYM) >>
          simp[create_size_exit_ok_non_exhalt,expr_exit_def,exit_result_def]
QED

Resume extcall_return_full[decode_success]:
      disch_then (qx_choose_then `z` (qx_choose_then `Gd` (qx_choose_then `td` strip_assume_tac))) >>
      qpat_x_assum `!tail. bind _ _ (ee with gas_obs := tail) = _`
        (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss())
          [bind_def,lift_sum_runtime_def,return_def])) >>
      `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,Gd,td)` by
        (qx_gen_tac `D` >>
         qpat_assum `!D. gas_origin_ptr_path _ (t,G,tn) [] (OK u,Gu,tu)`
           (qspec_then `D` mp_tac) >>
         qpat_assum `!D explicit. gas_origin_ptr_path _ (u,Gu,tu) [] (OK z,Gd,td)`
           (qspecl_then [`D`,`explicit`] mp_tac) >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         metis_tac[gas_origin_ptr_path_append,listTheory.APPEND]) >>
      `allocas_from lo z` by
        (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ z /\ _`
           (qspec_then `H0` mp_tac) >>
         impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
         qpat_assum `ghost_inv_at _ _ _ _ _ ee Gd td z`
           (FIRST o map ACCEPT_TAC o CONJUNCTS o REWRITE_RULE [ghost_inv_at_def])) >>
      Q_TAC (fn tm => SUBGOAL_THEN tm
        (qx_choose_then `zf` (map_every assume_tac o CONJUNCTS)))
        `?zf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK zf,Gd,td)) /\
              zf.vs_current_bb = sb.cs_current_bb /\ zf.vs_inst_idx = LENGTH sb.cs_current_insts /\
              (zf = z \/ ?xl. zf = jump_to xl z)` >-
        (qpat_assum `de = sb \/ _` strip_assume_tac
         >- (qexists_tac `z` >> simp[]) >>
         rename1 `emit_inst JMP [Label xl] [] de = ((),cj)` >>
         qexists_tac `jump_to xl z` >>
         conj_tac >-
           (qx_gen_tac `D` >>
            `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,Gd,td) []
                 (OK (jump_to xl z),Gd,td)` by
              (irule emit_jmp_origin_ptr >>
               simp[] >> conj_tac >-
               (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
                  vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ z /\ _`
                 (drule_then (ACCEPT_TAC o MATCH_MP
                   bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o
                   CONJUNCT1 o REWRITE_RULE [vv_post_def] o CONJUNCT1))) >>
               qexistsl_tac [`de`,`cj`] >> simp[]) >>
            qpat_assum `!D. gas_origin_ptr_path _ (t,G,tn) [] (OK z,Gd,td)`
              (qspec_then `D` mp_tac) >>
            qpat_assum `gas_origin_ptr_path _ (z,Gd,td) [] _` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >>
            metis_tac[gas_origin_ptr_path_append,listTheory.APPEND]) >>
         drule_then strip_assume_tac new_block_props >>
         rpt conj_tac >- simp[jump_to_def] >- simp[jump_to_def] >>
         disj2_tac >> qexists_tac `xl` >> REFL_TAC) >>
      `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
      qexistsl_tac [`OK zf`,`Gd`,`td`] >>
      suspend "success_post"
QED

Resume extcall_return_full[success_post]:
      qx_gen_tac `Hpost` >> disch_tac >> conj_tac >- simp[] >>
      disj1_tac >> qexists_tac `zf` >> conj_tac >- REFL_TAC >>
      qexists_tac `Value x` >>
      simp[contextTheory.mk_ptr_def,vv_location_def] >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ z /\ _`
        (qspec_then `Hpost` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `ann = ret_type` (fn th =>
        simp_tac bool_ss [th,post_value_type_def,contextTheory.mk_ptr_def]) >>
      strip_tac >>
      qpat_x_assum `zf = z \/ _` (DISJ_CASES_THEN2 SUBST1_TAC strip_assume_tac)
      >- simp[] >>
      qpat_x_assum `zf = jump_to _ z` SUBST1_TAC >>
      conj_tac >- simp[rest_word_vv_post_jump] >>
      conj_tac >-
        (let val defs = [vv_store_bound_def,eval_operand_def,lookup_var_def,jump_to_def]
         in SIMP_TAC (srw_ss()) defs >>
            qpat_assum `vv_store_bound _ _ _ ee _ _ z`
              (ACCEPT_TAC o SIMP_RULE (srw_ss()) defs)
         end) >>
      conj_tac >-
        (irule alloca_history_jump >> simp[jump_to_def] >> qexists_tac `z` >> simp[]) >>
      conj_tac >- simp[jump_to_def] >>
      conj_tac >-
        (qpat_assum `ee with gas_obs := [] = ee` (SUBST1_TAC o SYM) >>
         simp[ghost_inv_at_jump_to]) >>
      conj_tac >-
        (let val defs = [ptr_vv_ok_def,ptr_mem_ok_def,eval_operand_def,lookup_var_def,jump_to_def]
         in SIMP_TAC (srw_ss()) defs >>
            qpat_assum `ptr_vv_ok _ _ _ _ ee Gd td z`
              (ACCEPT_TAC o SIMP_RULE (srw_ss()) defs)
         end) >>
      conj_tac >-
        (let val defs = [ptr_buf_ok_def,eval_operand_def,lookup_var_def,jump_to_def]
         in SIMP_TAC (srw_ss()) defs >>
            qpat_assum `ptr_buf_ok _ _ _ Gd z`
              (ACCEPT_TAC o SIMP_RULE (srw_ss()) defs)
         end) >>
      `!n b sz. local_region cenv ee.scopes (jump_to xl z) n b sz <=>
                 local_region cenv ee.scopes z n b sz` by
        (rpt gen_tac >> irule loweringStateRelDefsTheory.local_region_lookup_cong >>
         simp[lookup_var_def,jump_to_def]) >>
      (let val defs = [vv_own_def,eval_operand_def,lookup_var_def,jump_to_def]
       in qpat_assum `!n b sz. local_region _ _ (jump_to _ z) n b sz <=> _`
            (fn th => SIMP_TAC (srw_ss()) [vv_own_def,th]) >>
          SIMP_TAC (srw_ss()) defs >>
          qpat_assum `vv_own _ _ _ _ _ ee _ _ z`
            (ACCEPT_TAC o SIMP_RULE (srw_ss()) defs)
       end)
QED

Finalise extcall_return_full
