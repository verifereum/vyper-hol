(* Counted empty-data default return. *)
Theory bodyFullExtCallReturnDefaultValue
Ancestors
  extcallReturnDefaultControlJoint extcallReturnDefaultTypes
  exprSimExtCallCase bodyFullAllocaFresh stateRelProj
  abiCallerAllocation abiCallerLocalScratch exprSimWordArgs
  fragGasOriginPtr bodyPtrDefs loweringPosts loweringStateRelDefs
  codegenRel compileEnv context venomState venomMemDefs finite_map words
  exprSafeOperand ptrDiscipline logStoreDataOriginPtr
  bodyFullExtCallDefaultCopy bodyFullExtCallDefaultBytesStore
  bodyPtrBopRepresentationFrame bodyPtrBopHashFootprint
  actualAllocExec exprSimIfExpWidenedCounted bodyFullExtCallPrecheck
  bodyFullUnwrapSlotPost exprSimHash extcallReturnInterface createSizeExit
  annassignRelayoutPost[qualified,ignore_grammar]
  aggregateEvaluatedLayout[qualified,ignore_grammar]
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  exprSimHypsDefs[qualified]

Theorem extcall_default_copy_ghost_local[local]:
  typed_copy_state_frame ds off n u z /\
  ghost_inv_at D lo d cenv cx ee Gu tu u /\
  local_ptrs_rel func cenv ee.scopes u /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x u /\
    FLOOKUP Gc x = FLOOKUP Gu x /\ op_taint tc (Var x) = op_taint tu (Var x)) /\
  (!name b len. local_region cenv ee.scopes u name b len ==>
    off + n <= b \/ b + len <= off) /\
  (!i. ~(off <= i /\ i < off + n) ==> (i IN tc.t_mem <=> i IN tu.t_mem)) /\
  tc.t_stor = tu.t_stor /\ tc.t_trans = tu.t_trans /\ tc.t_imm = tu.t_imm /\
  lo <= off ==>
  ghost_inv_at D lo d cenv cx ee Gc tc z
Proof
  strip_tac >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [typedMemoryCopyTheory.typed_copy_state_frame_def, venom_state_component_equality]) >>
  `stor_taint_ok_at D tc z` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ _ Gu tu u`
       (mp_tac o REWRITE_RULE[ghost_inv_at_def]) >> simp[stor_taint_ok_at_def]) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ _ Gu tu u`
       (strip_assume_tac o REWRITE_RULE[ghost_inv_at_def]) >>
     simp[] >> rewrite_tac[allocas_from_def] >>
     qpat_assum `z.vs_allocas = u.vs_allocas` SUBST1_TAC >>
     qpat_assum `allocas_from lo u` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  irule bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_inv_at >>
  simp[] >> qexistsl_tac [`Gu`,`func`,`n`,`u`,`sa`,`off`,`tu`] >>
  qpat_assum `typed_copy_frame _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[typedMemoryCopyTheory.typed_copy_frame_def]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[] >>
  rpt strip_tac >>
  TRY (qpat_assum `!name b len. local_region _ _ _ name b len ==> _`
    (drule_then strip_assume_tac) >> decide_tac) >>
  TRY (qpat_assum `!a k. _ ==> mem_bytes_at a k z.vs_memory = _`
    irule >> decide_tac) >>
  qpat_assum `!i. _ ==> (i IN tc.t_mem <=> _)` irule >> decide_tac
QED

(* Keep the frame and the new destination at the actual ALLOCA endpoint. *)
Theorem extcall_default_return_alloc_cut[local]:
  extcall_returned st0 ctx func cenv cx rt es sa s0 sr addr src cap target
    has_default dop dt dopt bs ee t /\
  compile_alloc_buffer n sr = (buf,ar) /\ fn_has_code sr ar func /\
  fn_inst_ids_distinct func /\ n < dimword (:256) /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee G tn t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) ==>
  ?q w a J tm.
    buf.buf_operand = Var q /\ not_fresh_at ar q /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK a,J,tm)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee a /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee J tm a) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 J tm /\ wb_frame cenv es ee sa s0 a /\
    ~a.vs_halted /\ a.vs_current_bb = ar.cs_current_bb /\
    a.vs_inst_idx = LENGTH ar.cs_current_insts /\ a.vs_returndata = bs /\
    alloca_history func a /\ allocas_from lo a /\ t.vs_alloca_next <= a.vs_alloca_next /\
    a.vs_memory = t.vs_memory /\ a.vs_accounts = t.vs_accounts /\
    lookup_var q a = SOME w /\ ptr_covers J tm q a n /\
    FLOOKUP a.vs_allocas sr.cs_next_id = SOME (w2n w,n) /\
    FLOOKUP J q = SOME (w2n w,n) /\
    w2n w + n < dimword (:256) /\ w2n w + n <= a.vs_alloca_next /\
    (!aid e. FLOOKUP t.vs_allocas aid = SOME e ==> FLOOKUP a.vs_allocas aid = SOME e) /\
    (!aid b len. aid < sr.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) n b len) /\
    (!name b len. local_region cenv ee.scopes a name b len ==>
      regions_disjoint (w2n w) n b len) /\
    (!x. not_fresh_at sr x ==>
      lookup_var x a = lookup_var x t /\ FLOOKUP J x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!i. i IN tm.t_mem <=> i IN tn.t_mem \/
      (t.vs_alloca_next <= i /\ i < w2n w + n))
Proof
  simp[extcall_returned_def] >> strip_tac >>
  rename1 `valid_horizon cx st0 H0 ee.storage_trace` >>
  `ghost_inv_at (DF H0) lo d cenv cx ee G tn t` by metis_tac[] >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx ee t`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``]
    (SPEC_ALL alloc_buffer_origin_ptr_path_exact)) >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`]
    (qx_choose_then `q` (qx_choose_then `w` (qx_choose_then `a`
      (qx_choose_then `J` (qx_choose_then `tm` strip_assume_tac)))))) >>
  `a.vs_halted = t.vs_halted /\ a.vs_memory = t.vs_memory /\
   a.vs_accounts = t.vs_accounts /\ a.vs_returndata = t.vs_returndata` by
    (qpat_assum `a with <| vs_vars := _; vs_allocas := _;
                           vs_alloca_next := _; vs_inst_idx := _ |> = t`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `wb_frame cenv es ee sa s0 a` by
    (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
     goal_assum (drule_at Any) >> qexists_tac `sr` >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`q`, `w`, `a`, `J`, `tm`] >> simp[] >>
  conj_tac >- suspend "horizon" >> suspend "kept"
QED
Resume extcall_default_return_alloc_cut[horizon]:
  qx_gen_tac `h` >> strip_tac >>
  `local_ptrs_rel func cenv ee.scopes t` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  irule alloc_buffer_ghost_inv_at_locals >> simp[] >>
  qexistsl_tac [`G`, `w2n w + n`, `func`, `t`, `sr`, `tn`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> simp[]) >>
  gvs[]
QED
Resume extcall_default_return_alloc_cut[kept]:
  `local_ptrs_rel func cenv ee.scopes t /\ alloca_inv t` by
    metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `!aid b len. FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
     b + len <= t.vs_alloca_next` by
    (rpt strip_tac >> irule abi_caller_allocation_end >> simp[] >>
     qexistsl_tac [`len`, `aid`, `b`] >>
     fs[wb_frame_def]) >>
  `!name b len. local_region cenv es.scopes s0 name b len ==>
     b + len <= t.vs_alloca_next` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes t name b len` by
       (irule exprSimPropsTheory.local_region_frame_fwd >>
        qexistsl_tac [`s0`, `sa`, `es.scopes`] >> fs[wb_frame_def]) >>
     drule_all abi_caller_local_end >> simp[]) >>
  `!x. not_fresh_at sa x ==>
        FLOOKUP J x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at sr x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     qpat_assum `!x. not_fresh_at sr x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  conj_tac
  >- (irule alloc_buffer_ghost_kept_at >>
      qexistsl_tac [`G`, `w2n w + n`, `t`, `tn`] >>
      rpt conj_tac >> rpt strip_tac >> simp[] >>
      FIRST_PROVE
        [qpat_assum `!aid b len. FLOOKUP s0.vs_allocas aid = SOME (b,len) ==> _`
           (drule_then ACCEPT_TAC),
         qpat_assum `!name b len. local_region cenv es.scopes s0 name b len ==> _`
           (drule_then ACCEPT_TAC),
         qpat_assum `!x. not_fresh_at sa x ==> _`
           (drule_then strip_assume_tac) >> simp[]]) >>
  asm_rewrite_tac[]
QED
Finalise extcall_default_return_alloc_cut

fun default_value_fmp_at state =
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `horizon` (fn horizon =>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
        stmt_state_rel H ctx func cenv cx ee ^state /\ _`
        (ACCEPT_TAC o
         MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o
         CONJUNCT1 o (fn related => MATCH_MP related horizon))));

Theorem extcall_return_full_default_value:
  !mods DF lo d explicit ctx PG func cenv cx env es ann is_static skip fname
   arg_types ret_type opts args dflt st0 sa sb s0 G0 tn0 sr result_op vv
   addr_op buf_op cap target has_default default_op default_ty default_opt
   returnData ee t G tn.
    ret_type <> NoneT /\ has_default /\ returnData = [] /\
    expr_body_pre_mods mods cenv cx env
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
                            (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
                               args dflt)) =
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
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type)
                 opts) args dflt) p.ptr_operand G' t') /\
         vv_own cenv cx
           (post_value_type cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
                 args dflt)) sa sb (ee with gas_obs := []) tv vv t' /\
         ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn') \/
         (exit_result r /\ create_size_exit_ok ctx res r /\ expr_exit res r)))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[comp_bind_def] >> pairarg_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ sr = (buf,ar)` >>
  drule extcallReturnDefaultRoutingTheory.return_default_path_intervals >> strip_tac >>
  qpat_assum `extcall_returned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [extcall_returned_def]) >>
  Cases_on `default_opt` >- gvs[extcall_default_ready_def] >>
  rename1 `extcall_default_ready cx ret_type T default_op default_ty (SOME dv) t` >>
  qpat_x_assum `extcall_default_ready _ _ _ _ _ _ _` mp_tac >>
  simp[extcall_default_ready_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qexists_tac `if skip \/ ext_call_has_code target ee.accounts then INL (Value dv)
    else INR (Error (RuntimeError "ExtCall target has no code"))` >>
  simp[vyperStateTheory.get_accounts_def, vyperStateTheory.bind_def,
    vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
    vyperStateTheory.check_def, vyperStateTheory.assert_def,
    COND_RAND, COND_RATOR] >>
  Cases_on `?H. valid_horizon cx st0 H ee.storage_trace`
  >- suspend "entry" >>
  metis_tac[]
QED
Resume extcall_return_full_default_value[entry]:
  `cs_extends sr ar /\ cs_extends ar sb` by
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,
      exprLoweringPropsTheory.ci_mono_compile_default_return_path,
      exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
  `fn_has_code sr ar func /\ fn_has_code ar sb func` by
    metis_tac[fragExecTheory.fn_has_code_mid, cs_extends_refl] >>
  drule_all extcallReturnDefaultRoutingTheory.return_default_intervals_code >> strip_tac >>
  `type_memory_bytes cenv ret_type = type_memory_size rtv` by
    metis_tac[extcallReturnInterfaceTheory.extcall_return_memory_size] >>
  `type_memory_size rtv + 64 < dimword (:256)` by
    metis_tac[extcallReturnInterfaceTheory.extcall_return_store_bound] >>
  `type_memory_bytes cenv ret_type < dimword (:256)` by decide_tac >>
  drule_all extcall_default_return_alloc_cut >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  rename1 `lookup_var q a = SOME dw` >>
  `LENGTH a.vs_returndata < dimword (:256)` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp a` by (default_value_fmp_at ``a:venom_state``) >>
  drule_all (INST_TYPE [alpha |-> ``:256``]
    extcallReturnDefaultControlJointTheory.return_default_shell_entry) >>
  disch_then (qspecl_then [`tm`, `explicit`, `PG`, `J`]
    (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tu` (fn th =>
      let
        val clauses = CONJUNCTS th
        val frame_start = length clauses - 4
      in
        EVERY (map assume_tac (List.take (clauses, frame_start)) @
          ListPair.mapEq (fn (name, clause) => mk_asm name clause)
            (["shell_state", "shell_ghost", "shell_kept", "shell_writeback"],
             List.drop (clauses, frame_start)))
      end))))) >>
  `ds.cs_current_bb = dl /\ ds.cs_current_insts = []` by
    (qpat_assum `new_block dl a6 = (old1,ds)`
       (strip_assume_tac o MATCH_MP emitHelperPropsTheory.new_block_props) >> simp[]) >>
  `u.vs_current_bb = ds.cs_current_bb /\ u.vs_inst_idx = LENGTH ds.cs_current_insts` by simp[] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK u,Gu,tu)` by
    (gen_tac >> qpat_assum `!D. gas_origin_ptr_path _ (t,G,tn) _ _` (qspec_then `D` mp_tac) >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`a`, `J`, `tm`, `[]`, `OK u`, `Gu`, `tu`] mp_tac) >> simp[]) >>
  `sr.cs_next_var <= ar.cs_next_var /\ sr.cs_next_id <= ar.cs_next_id` by
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,
      exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
  `sa.cs_next_var <= ar.cs_next_var` by decide_tac >>
  `local_ptrs_reserved cenv ar` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sr` >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at ar x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ar x` by
    metis_tac[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ar x` by
    metis_tac[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee u /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee Gu tu u` by
    (qx_gen_tac `h` >> strip_tac >>
     `stmt_state_rel h ctx func cenv cx ee a /\
      storage_well_formed_on cx ee (FST h) /\ ghost_inv_at (DF h) lo d cenv cx ee J tm a` by
       (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ a /\ _`
         (qspec_then `h` mp_tac) >> simp[]) >>
     simp[markerLib.L "shell_state", markerLib.L "shell_ghost"]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu /\ wb_frame cenv es ee sa s0 u` by
    simp[markerLib.L "shell_kept", markerLib.L "shell_writeback"] >>
  `!x. not_fresh_at sr x ==>
    lookup_var x u = lookup_var x t /\ FLOOKUP Gu x = FLOOKUP G x /\
    op_taint tu (Var x) = op_taint tn (Var x)` by
    (qx_gen_tac `x` >> strip_tac >>
     `not_fresh_at ar x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sr` >> simp[]) >>
     qpat_assum `!x. not_fresh_at sr x ==> _` (qspec_then `x` assume_tac) >>
     qpat_assum `!x. not_fresh_at ar x ==> _` (qspec_then `x` assume_tac) >> fs[]) >>
  `op_taint tm (Var q) = {}` by
    qpat_assum `ptr_covers J tm q a _`
      (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [ptr_covers_def]) >>
  `lookup_var q u = SOME dw /\ FLOOKUP Gu q = SOME (w2n dw,type_memory_bytes cenv ret_type) /\
   ptr_covers Gu tu q u (type_memory_bytes cenv ret_type)` by
    (qpat_assum `!x. not_fresh_at ar x ==> _` (qspec_then `q` mp_tac) >>
     simp[ptr_covers_def]) >>
  `!op. safe_operand sr op ==>
     eval_operand op u = eval_operand op t /\ op_taint tu op = op_taint tn op` by
    (Cases_on `op` >> simp[safe_operand_def, eval_operand_def, op_taint_def] >>
     strip_tac >>
     qpat_assum `!x. not_fresh_at sr x ==> _` (drule_then strip_assume_tac) >>
     fs[op_taint_def]) >>
  `eval_operand addr_op u = SOME aw /\ op_taint tu addr_op = {} /\
   eval_operand default_op u = SOME w /\ op_taint tu default_op = {} /\
   (!x. default_op = Var x ==> not_fresh_at sr x)` by
    (qpat_assum `EVERY (safe_operand sr) _` (strip_assume_tac o SRULE []) >>
     conj_tac
     >- (qpat_assum `!op. safe_operand sr op ==> _` (qspec_then `addr_op` mp_tac) >> simp[]) >>
     qpat_assum `!op. safe_operand sr op ==> _` (qspec_then `default_op` mp_tac) >>
     simp[] >> fs[safe_operand_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by (default_value_fmp_at ``u:venom_state``) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next /\ alloca_history func u` by
    (qpat_x_assum `?H. valid_horizon cx st0 H ee.storage_trace` strip_assume_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >>
     fs[ghost_inv_at_def]) >>
  `ar.cs_next_var <= ds.cs_next_var` by
    (`ar.cs_next_var <= a1.cs_next_var /\ a1.cs_next_var <= a2.cs_next_var` by
       metis_tac[exprLoweringPropsTheory.ci_mono_emit_op,
         exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
     `a2.cs_next_var = a3.cs_next_var /\ a3.cs_next_var = a4.cs_next_var /\
      a4.cs_next_var = a5.cs_next_var` by
       metis_tac[emitHelperPropsTheory.fresh_label_props] >>
     `a5.cs_next_var <= a6.cs_next_var` by
       metis_tac[exprLoweringPropsTheory.ci_mono_emit_inst,
         exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
     `ds.cs_next_var = a6.cs_next_var` by metis_tac[emitHelperPropsTheory.new_block_props] >>
     decide_tac) >>
  `!x. not_fresh_at ar x ==> not_fresh_at ds x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `ar` >> simp[]) >>
  `not_fresh_at ds q /\ (!x. default_op = Var x ==> not_fresh_at ds x) /\
   (!x. addr_op = Var x ==> not_fresh_at ds x)` by
    (qpat_assum `EVERY (safe_operand sr) _`
       (strip_assume_tac o SRULE [safe_operand_def]) >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `?p Gp tp.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK p,Gp,tp)) /\
    typed_copy_state_frame ds (w2n dw) (type_memory_size rtv) u p /\
    (!mem. mem_agree_outside tp.t_mem p.vs_memory mem ==>
      val_in_memory rtv dv (w2n dw) mem) /\
    (!x. not_fresh_at ds x ==>
      FLOOKUP Gp x = FLOOKUP Gu x /\ op_taint tp (Var x) = op_taint tu (Var x)) /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size rtv) ==>
      (i IN tp.t_mem <=> i IN tu.t_mem)) /\
    tp.t_stor = tu.t_stor /\ tp.t_trans = tu.t_trans /\ tp.t_imm = tu.t_imm /\
    ~p.vs_halted /\ p.vs_current_bb = de.cs_current_bb /\
    p.vs_inst_idx = LENGTH de.cs_current_insts` by suspend "payload" >>
  suspend "after_payload"
QED

Resume extcall_return_full_default_value[payload]:
  Cases_on `is_word_type ret_type` >- suspend "word_store" >>
  suspend "nonword_store"
QED

Resume extcall_return_full_default_value[word_store]:
  `default_ty = ret_type` by metis_tac[compileEnvTheory.type_widens_to_word] >>
  `type_memory_size rtv = 32` by metis_tac[abiValueEncodingTheory.abi_word_type_size] >>
  `w = typed_val_to_w256 rtv dv` by metis_tac[exprBopSimPropsTheory.expr_val_rel_typed, optionTheory.SOME_11] >>
  `type_memory_bytes cenv ret_type = 32` by metis_tac[] >>
  `compile_store_memory cenv default_op (Var q) ret_type ret_type ds = ((),de) /\
   eval_operand default_op u = SOME (typed_val_to_w256 rtv dv) /\
   w2n dw + 32 < dimword (:256) /\ w2n dw + 32 <= u.vs_alloca_next /\
   ptr_covers Gu tu q u 32` by gvs[] >>
  drule_all logStoreDataOriginPtrTheory.compile_store_memory_word_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `p` (qx_choose_then `Gp` (qx_choose_then `tp` strip_assume_tac)))) >>
  qexistsl_tac [`p`, `Gp`, `tp`] >> simp[] >> metis_tac[]
QED

Resume extcall_return_full_default_value[nonword_store]:
  `~is_word_type default_ty` by
    metis_tac[vyperTypeSystemTheory.type_widens_to_def,
              aggregateEvaluatedLayoutTheory.arg_type_fits_word_type] >>
  qpat_x_assum `!dv'. SOME dv = SOME dv' /\ _ ==> _`
    (qspec_then `dv` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  `ptr_mem_ok cx default_ty dv default_op Gu tu u` by
    (irule bodyPtrBopRepresentationFrameTheory.bop_ptr_mem_ok_frame >>
     qexistsl_tac [`G`, `t`, `tn`, `tv`] >>
     conj_tac
     >- (rpt strip_tac >> qpat_assum `!x. not_fresh_at sr x ==> _`
           (qspec_then `x` mp_tac) >> simp[]) >>
     gvs[] >> decide_tac) >>
  `type_memory_bytes cenv default_ty = type_memory_size tv` by
    (irule typedMemoryCopyTheory.typed_copy_memory_size >>
     qexists_tac `get_tenv cx` >>
     qpat_assum `expr_body_pre _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE
         [exprSimHypsDefsTheory.expr_body_pre_def,
          exprSimHypsDefsTheory.expr_sim_inv_def]) >>
     simp[] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `type_memory_size tv <> 0 ==>
     (?x. default_op = Var x /\ ptr_covers Gu tu x u (type_memory_size tv)) /\
     w2n w + type_memory_size tv <= u.vs_alloca_next` by
    (strip_tac >> qpat_x_assum `type_memory_bytes cenv default_ty <> 0 ==> _` mp_tac >>
     (impl_tac >- simp[]) >> strip_tac >>
     rename1 `default_op = Var src` >>
     `not_fresh_at sr src` by simp[] >>
     qpat_assum `!x. not_fresh_at sr x ==> _` (qspec_then `src` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     conj_tac >- (qexists_tac `src` >> gvs[ptr_covers_def, eval_operand_def]) >>
     gvs[] >> decide_tac) >>
  `compile_store_memory cenv default_op (Var q) ret_type default_ty ds = ((),de) /\
   ptr_covers Gu tu q u (type_memory_size rtv) /\
   w2n dw + type_memory_size rtv <= u.vs_alloca_next` by gvs[] >>
  Cases_on `is_bytestring_type ret_type` >- suspend "bytes_store" >>
  Cases_on `default_ty <> ret_type` >- suspend "widened_store" >>
  suspend "flat_store"
QED

Resume extcall_return_full_default_value[bytes_store]:
  `is_bytestring_type default_ty` by
    metis_tac[vyperTypeSystemTheory.type_widens_to_def,
              compileEnvTheory.arg_type_fits_bytestring_source] >>
  `type_memory_size tv <> 0` by
    (drule_all valueCopyBytesTheory.bytestring_type_value >> strip_tac >>
     gvs[valueEncodingTheory.type_memory_size_def, vfmConstantsTheory.word_size_def]) >>
  qpat_x_assum `type_memory_size tv <> 0 ==> _` mp_tac >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `default_op = Var src` >>
  `compile_store_memory cenv (Var src) (Var q) ret_type default_ty ds = ((),de) /\
   not_fresh_at ds src /\ lookup_var src u = SOME w` by
    gvs[eval_operand_def] >>
  `!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
      val_in_memory tv dv (w2n w) mem` by
    (rpt strip_tac >> drule_all bodyPtrBopHashFootprintTheory.ptr_mem_ok_robust >> simp[]) >>
  drule_all extcall_default_bytes_store_capacity_joint >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `p` (qx_choose_then `Gp` (qx_choose_then `tp` strip_assume_tac)))) >>
  qexistsl_tac [`p`,`Gp`,`tp`] >> simp[] >>
  conj_tac
  >- (simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
          typedMemoryCopyTheory.typed_copy_frame_def] >>
      conj_tac >- gvs[venom_state_component_equality] >>
      rpt strip_tac >> simp[]) >>
  qx_gen_tac `i` >> disch_tac >>
  `i < w2n dw \/ w2n dw + type_memory_size rtv <= i` by decide_tac >>
  qpat_assum `!i. i < w2n dw \/ _ ==> _` (qspec_then `i` mp_tac) >> simp[]
QED

Resume extcall_return_full_default_value[widened_store]:
  `0 < type_memory_size tv` by
    metis_tac[annassignRelayoutPostTheory.strict_widening_source_positive] >>
  `type_memory_size tv <> 0` by decide_tac >>
  qpat_x_assum `type_memory_size tv <> 0 ==> _`
    (drule_then strip_assume_tac) >>
  rename1 `default_op = Var src` >>
  `loweringStateRelDefs$regions_disjoint
     (w2n dw) (type_memory_size rtv) (w2n w) (type_memory_size tv)` by
    (`IS_SOME (SOME dv)` by simp[] >>
     qpat_assum `IS_SOME (SOME dv) /\ ~is_word_type default_ty ==> _`
       (drule_all_then (qx_choosel_then [`sw`,`aid`,`stv`] strip_assume_tac)) >>
     `sw = w` by
       (qpat_assum `eval_operand default_op t = SOME sw` mp_tac >>
        qpat_assum `eval_operand default_op t = SOME w`
          (fn th => simp[NoAsms,th])) >>
     `stv = tv` by
       (qpat_assum `evaluate_type (get_tenv cx) default_ty = SOME stv` mp_tac >>
        qpat_assum `evaluate_type (get_tenv cx) default_ty = SOME tv`
          (fn th => simp[NoAsms,th])) >>
     qpat_assum `!aid b len. aid < sr.cs_next_id /\ FLOOKUP t.vs_allocas aid = _ ==> _`
       (qspecl_then [`aid`,`w2n w`,`type_memory_size tv`] mp_tac) >>
     simp[]) >>
  `!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
       val_in_memory tv dv (w2n w) mem` by
    (rpt strip_tac >> drule_all bodyPtrBopHashFootprintTheory.ptr_mem_ok_robust >> simp[]) >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
       sz = type_memory_size rt) fields)` by
    (qhdtm_assum `expr_body_pre` mp_tac >>
     simp[NoAsms,exprSimHypsDefsTheory.expr_body_pre_def,
          exprSimHypsDefsTheory.expr_sim_inv_def] >>
     strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  `alloca_room ctx func u` by
    (qpat_x_assum `?H. valid_horizon _ _ H _` (qx_choose_then `h` assume_tac) >>
     qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `stmt_state_rel h _ _ _ _ _ u`
       (mp_then Any ACCEPT_TAC stateRelProjTheory.stmt_state_rel_alloca_room)) >>
  `u.vs_alloca_next < dimword (:256)` by
    (qpat_assum `alloca_room ctx func u`
       (ACCEPT_TAC o MATCH_MP exprLoweringPropsTheory.alloca_room_next_lt)) >>
  `w2n w + type_memory_size tv < dimword (:256) /\
   w2n dw + type_memory_size rtv < dimword (:256)` by decide_tac >>
  qpat_assum `default_op = Var src` SUBST_ALL_TAC >>
  `lookup_var src u = SOME w` by
    (qpat_assum `eval_operand (Var src) u = SOME w`
       (ACCEPT_TAC o REWRITE_RULE [eval_operand_def])) >>
  mp_tac (Q.INST
    [`xs` |-> `src`, `xd` |-> `q`, `dty` |-> `ret_type`, `sty` |-> `default_ty`,
     `sa` |-> `ds`, `sb` |-> `de`, `stv` |-> `tv`, `dtv` |-> `rtv`,
     `v` |-> `dv`, `tenv` |-> `get_tenv cx`, `s` |-> `u`,
     `G` |-> `Gu`, `tn` |-> `tu`, `sw` |-> `w`]
    logStoreDataOriginPtrTheory.compile_store_memory_origin_ptr_path) >>
  (impl_tac >-
     (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[] >>
      qpat_assum `loweringStateRelDefs$regions_disjoint _ _ _ _` mp_tac >>
      simp[NoAsms,loweringStateRelDefsTheory.regions_disjoint_def,DISJ_COMM])) >>
  disch_then (qx_choosel_then [`p`,`Gp`,`tp`] strip_assume_tac) >>
  qexistsl_tac [`p`,`Gp`,`tp`] >> simp[]
QED

Resume extcall_return_full_default_value[flat_store]:
  `default_ty = ret_type` by metis_tac[] >>
  `tv = rtv` by metis_tac[optionTheory.SOME_11] >>
  `alloca_room ctx func u` by
    (qpat_x_assum `?H. valid_horizon _ _ H _` (qx_choose_then `h` assume_tac) >>
     qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `stmt_state_rel h _ _ _ _ _ u`
       (mp_then Any ACCEPT_TAC stateRelProjTheory.stmt_state_rel_alloca_room)) >>
  `u.vs_alloca_next < dimword (:256)` by
    (fs[exprLoweringPropsTheory.alloca_room_def] >> decide_tac) >>
  `type_memory_size rtv <> 0 ==>
     (?x. default_op = Var x /\ ptr_covers Gu tu x u (type_memory_size rtv)) /\
     ptr_covers Gu tu q u (type_memory_size rtv) /\
     w2n w + type_memory_size rtv <= u.vs_alloca_next /\
     w2n dw + type_memory_size rtv <= u.vs_alloca_next /\
     u.vs_alloca_next < dimword (:256)` by gvs[] >>
  `compile_store_memory cenv default_op (Var q) ret_type ret_type ds = ((),de) /\
   ptr_mem_ok cx ret_type dv default_op Gu tu u` by gvs[] >>
  drule_all extcall_default_copy_capacity_joint >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `p` (qx_choose_then `Gp` (qx_choose_then `tp` strip_assume_tac)))) >>
  qexistsl_tac [`p`,`Gp`,`tp`] >> simp[] >> metis_tac[]
QED

Resume extcall_return_full_default_value[after_payload]:
  `eval_operand addr_op p = SOME aw` by
    (drule_all typedMemoryCopyTheory.typed_copy_state_frame_operand >> simp[]) >>
  `op_taint tp addr_op = {}` by
    (Cases_on `addr_op` >> fs[op_taint_def]) >>
  `p.vs_accounts = t.vs_accounts /\ p.vs_allocas = u.vs_allocas /\
   p.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `typed_copy_state_frame ds _ _ u p` mp_tac >>
     simp[NoAsms, typedMemoryCopyTheory.typed_copy_state_frame_def,
          venom_state_component_equality] >> strip_tac >> fs[]) >>
  `allocas_from lo p` by
    (rewrite_tac[allocas_from_def] >>
     qpat_assum `p.vs_allocas = u.vs_allocas` SUBST1_TAC >>
     qpat_assum `allocas_from lo u` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK p,Gp,tp)` by
    (gen_tac >> qpat_assum `!D. gas_origin_ptr_path _ (t,G,tn) [] (OK u,Gu,tu)`
       (qspec_then `D` mp_tac) >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`u`,`Gu`,`tu`,`[]`,`OK p`,`Gp`,`tp`] mp_tac) >> simp[]) >>
  `((n2w (LENGTH (lookup_account (w2w aw) p.vs_accounts).code) : bytes32) <> 0w
       <=> ext_call_has_code target ee.accounts)` by
    (`accounts_agree H cx.txn.target ee.accounts t.vs_accounts` by
       (drule stateRelProjTheory.stmt_state_rel_state_rel >>
        disch_then (strip_assume_tac o MATCH_MP accountsRelPropsTheory.state_rel_accounts) >> simp[]) >>
     qpat_assum `accounts_agree H _ _ _` (mp_tac o MATCH_MP accountsRelPropsTheory.accounts_agree_lookup) >>
     disch_then (qspec_then `target` strip_assume_tac) >>
     `LENGTH (lookup_account target ee.accounts).code <= 24576` by
       fs[vyperRuntimeAccountsTheory.accounts_runtime_well_typed_def,
          vyperRuntimeAccountsTheory.account_runtime_well_typed_def] >>
     `LENGTH (lookup_account target ee.accounts).code < dimword (:256)` by
       (simp[dimword_def] >> decide_tac) >>
     simp[vyperInterpreterTheory.ext_call_has_code_def, listTheory.NULL_EQ,
          n2w_11, listTheory.LENGTH_NIL]) >>
  `!x. not_fresh_at ds x ==> lookup_var x p = lookup_var x u` by
    (qpat_assum `typed_copy_state_frame ds _ _ u p`
       (strip_assume_tac o REWRITE_RULE [typedMemoryCopyTheory.typed_copy_state_frame_def]) >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `lookup_var q p = SOME dw /\ FLOOKUP Gp q = SOME (w2n dw,type_memory_bytes cenv ret_type) /\
   ptr_covers Gp tp q p (type_memory_bytes cenv ret_type)` by
    (qpat_assum `!x. not_fresh_at ds x ==> lookup_var x p = _`
       (qspec_then `q` mp_tac) >>
     qpat_assum `!x. not_fresh_at ds x ==> FLOOKUP Gp x = _ /\ _`
       (qspec_then `q` mp_tac) >>
     `op_taint tu (Var q) = {}` by fs[ptr_covers_def] >>
     simp[ptr_covers_def, SF CONJ_ss] >>
     qexists_tac `w2n dw` >> simp[arithmeticTheory.ADD_COMM]) >>
  `local_ptrs_reserved cenv ds` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `ar` >> simp[]) >>
  `!name b len. local_region cenv ee.scopes u name b len ==>
    w2n dw + type_memory_size rtv <= b \/ b + len <= w2n dw` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes a name b len` by
       (irule (iffLR local_region_lookup_cong) >>
        goal_assum (drule_at (Pat `local_region _ _ u _ _ _`)) >>
        rpt strip_tac >>
        `not_fresh_at ar p'` by metis_tac[local_ptrs_reserved_def] >>
        qpat_assum `!x. not_fresh_at ar x ==> lookup_var x u = _ /\ _`
          (drule_then strip_assume_tac) >> simp[]) >>
     qpat_assum `!name b len. local_region cenv ee.scopes a name b len ==> _`
       (drule_then mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def, arithmeticTheory.ADD_COMM]) >>
  drule_all actualAllocExecTheory.actual_alloc_buffer_site >> strip_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee p /\ storage_well_formed_on cx ee (FST H)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >> simp[] >>
     irule exprSimIfExpWidenedCountedTheory.typed_copy_semantic_frame >>
     goal_assum (drule_at (Pat `typed_copy_state_frame ds _ _ u p`)) >>
     goal_assum (drule_at (Pat `MEM _ (fn_insts func)`)) >>
     simp[venomInstTheory.mk_inst_def] >> rpt strip_tac >>
     qpat_assum `!name b len. local_region cenv ee.scopes u name b len ==> _`
       (drule_then strip_assume_tac) >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp p` by (default_value_fmp_at ``p:venom_state``) >>
  Cases_on `skip \/ ext_call_has_code target ee.accounts`
  >- suspend "default_success" >>
  `~skip /\ ~ext_call_has_code target ee.accounts` by metis_tac[] >>
  `compile_extcodesize_check addr_op de = ((),ck)` by fs[] >>
  drule_all bodyFullExtCallPrecheckTheory.extcall_codesize_checked_path >>
  disch_then (qspecl_then [`explicit`,`PG`,`Gp`] mp_tac) >>
  `(n2w (LENGTH (lookup_account (w2w aw) p.vs_accounts).code) : bytes32) = 0w` by metis_tac[] >>
  `LENGTH (lookup_account target t.vs_accounts).code MOD dimword (:256) = 0` by
    (qpat_assum `(n2w _ : bytes32) = 0w` (mp_tac o AP_TERM ``w2n:bytes32 -> num``) >>
     simp[w2n_n2w]) >>
  simp[LET_THM] >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString de.cs_next_var)` >>
  qabbrev_tac `z = revert_state (set_returndata []
    (update_var out 0w p with vs_inst_idx := SUC p.vs_inst_idx))` >>
  qabbrev_tac `Gcheck = Gp \\ out` >>
  qabbrev_tac `tcheck = tp with t_var := tp.t_var |+ (out,{})` >>
  qexistsl_tac [`Abort Revert_abort z`,`Gcheck`,`tcheck`] >>
  simp[create_size_exit_ok_non_exhalt, fragExecTheory.exit_result_def,
       exprSimDefsTheory.expr_exit_def] >>
  qx_gen_tac `H'` >> strip_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ (t,G,tn) [] (OK p,Gp,tp)`
    (qspec_then `DF H'` mp_tac) >>
  disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`p`,`Gp`,`tp`,`[]`,`Abort Revert_abort z`,`Gcheck`,`tcheck`] mp_tac) >>
  simp[] >> disch_then irule >>
  qpat_assum `!D. gas_origin_ptr_path _ (p,Gp,tp) [] _` (qspec_then `DF H'` mp_tac) >>
  simp[Abbr `z`, Abbr `Gcheck`, Abbr `tcheck`, Abbr `out`]
QED
Resume extcall_return_full_default_value[default_success]:
  qabbrev_tac `out = STRING #"%" (toString de.cs_next_var)` >>
  qabbrev_tac `cw:bytes32 = n2w (LENGTH (lookup_account (w2w aw) p.vs_accounts).code)` >>
  qabbrev_tac `checked = if skip then p else
    update_var out cw p with vs_inst_idx := LENGTH ck.cs_current_insts` >>
  qabbrev_tac `Gc = if skip then Gp else Gp \\ out` >>
  qabbrev_tac `tc = if skip then tp else tp with t_var := tp.t_var |+ (out,{})` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (p,Gp,tp) [] (OK checked,Gc,tc)` by
    (Cases_on `skip` >-
      (simp[Abbr `checked`, Abbr `Gc`, Abbr `tc`] >>
       gen_tac >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
     `compile_extcodesize_check addr_op de = ((),ck)` by fs[] >>
     `ext_call_has_code target ee.accounts` by
       (qpat_x_assum `F \/ ext_call_has_code _ _` mp_tac >> simp[NoAsms]) >>
     `cw <> 0w` by
       (qpat_assum `(_ : bytes32) <> 0w <=> ext_call_has_code _ _` mp_tac >>
        simp[Abbr `cw`]) >>
     `LENGTH (lookup_account target t.vs_accounts).code MOD dimword (:256) <> 0` by
       (strip_tac >> qpat_x_assum `cw <> 0w` mp_tac >>
        simp[Abbr `cw`, GSYM w2n_eq_0, w2n_n2w]) >>
     drule_all bodyFullExtCallPrecheckTheory.extcall_codesize_checked_path >>
     disch_then (qspecl_then [`explicit`,`PG`,`Gp`] mp_tac) >>
     qpat_assum `Abbrev (cw = _)` (SUBST1_TAC o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     simp[LET_THM, Abbr `checked`, Abbr `Gc`, Abbr `tc`, Abbr `out`]) >>
  `ck.cs_current_bb = de.cs_current_bb` by
    (qpat_assum `(if skip then _ else _) de = _` mp_tac >>
     Cases_on `skip` >>
     simp[NoAsms, exprLoweringTheory.compile_extcodesize_check_def,
          emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_var_def, fresh_id_def, emit_def] >>
     disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  `skip ==> ck = de` by
    (qpat_assum `(if skip then _ else _) de = _` mp_tac >>
     Cases_on `skip` >> simp[NoAsms, comp_return_def]) >>
  `~checked.vs_halted /\ checked.vs_current_bb = ck.cs_current_bb /\
   checked.vs_inst_idx = LENGTH ck.cs_current_insts /\ allocas_from lo checked` by
    (Cases_on `skip`
     >- (`ck = de` by metis_tac[] >> simp[Abbr `checked`]) >>
     simp[Abbr `checked`, update_var_def] >>
     simp[allocas_from_def, IgnAsm `p.vs_allocas = _`] >>
     qpat_assum `allocas_from lo p`
       (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `dj.cs_current_insts = ck.cs_current_insts ++ [mk_inst ck.cs_next_id JMP [Label xl] []] /\
   dj.cs_current_bb = ck.cs_current_bb` by metis_tac[emitHelperPropsTheory.emit_inst_extends] >>
  qpat_assum `fn_has_code ck dj func`
    (mp_then Any mp_tac fragExecTheory.fn_has_code_same_block) >>
  disch_then (qspec_then `[mk_inst ck.cs_next_id JMP [Label xl] []]` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `get_instruction bb (LENGTH ck.cs_current_insts) = SOME (mk_inst ck.cs_next_id JMP [Label xl] [])` by
    (qpat_assum `!i. i < _ ==> get_instruction bb _ = _` (qspec_then `0` mp_tac) >>
     simp[NoAsms, listTheory.EL, listTheory.LENGTH]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp checked` by
    (qpat_assum `Abbrev (checked = _)`
       (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp p` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `skip` >>
     simp[allocas_below_fmp_def, update_var_def] >> metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (checked,Gc,tc) []
      (OK (jump_to xl checked),Gc,tc)` by
    (gen_tac >> irule decoderNavigationPtrTheory.jump_origin_ptr_path >>
     simp[IgnAsm `ck.cs_current_bb = _`] >>
     qexists_tac `ck.cs_next_id` >> simp[]) >>
  qabbrev_tac `z = jump_to xl checked` >>
  `ds.cs_next_var <= de.cs_next_var` by
    (qpat_assum `compile_store_memory _ _ buf.buf_operand _ _ ds = _`
       (fn th => mp_tac (REWRITE_RULE [th] (Q.SPECL
         [`cenv`,`default_op`,`buf.buf_operand`,`ret_type`,`default_ty`,`ds`]
         exprLoweringPropsTheory.ci_mono_compile_store_memory))) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `!x. not_fresh_at ds x ==>
    lookup_var x z = lookup_var x p /\ FLOOKUP Gc x = FLOOKUP Gp x /\
    op_taint tc (Var x) = op_taint tp (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at de x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     `x <> out` by (simp[Abbr `out`] >> fs[not_fresh_at_def]) >>
     `out <> x` by metis_tac[] >>
     Cases_on `skip` >>
     simp[NoAsms, Abbr `z`, Abbr `checked`, Abbr `Gc`, Abbr `tc`,
          jump_to_def, lookup_var_def, update_var_def, op_taint_def,
          FLOOKUP_UPDATE, DOMSUB_FLOOKUP_THM] >>
     simp[]) >>
  `z.vs_memory = p.vs_memory /\ z.vs_allocas = u.vs_allocas /\
   z.vs_alloca_next = u.vs_alloca_next /\ z.vs_current_bb = sb.cs_current_bb /\
   z.vs_inst_idx = LENGTH sb.cs_current_insts /\
   tc.t_mem = tp.t_mem /\ tc.t_stor = tp.t_stor /\
   tc.t_trans = tp.t_trans /\ tc.t_imm = tp.t_imm` by
    (qpat_assum `new_block xl cj = _`
       (mp_then Any strip_assume_tac emitHelperPropsTheory.new_block_props) >>
     Cases_on `skip` >>
     simp[NoAsms, Abbr `z`, Abbr `checked`, Abbr `tc`, jump_to_def, update_var_def] >>
     simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,Gc,tc)` by
    (gen_tac >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (checked,Gc,tc) [] (OK z,Gc,tc)` by
       simp[Abbr `z`] >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (p,Gp,tp) [] (OK z,Gc,tc)` by
       (qpat_assum `!D. gas_origin_ptr_path _ (p,Gp,tp) [] (OK checked,Gc,tc)`
          (qspec_then `D` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
        disch_then (qspecl_then [`checked`,`Gc`,`tc`,`[]`,`OK z`,`Gc`,`tc`] mp_tac) >>
        simp[]) >>
     qpat_assum `!D. gas_origin_ptr_path _ (t,G,tn) [] (OK p,Gp,tp)`
       (qspec_then `D` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
     disch_then (qspecl_then [`p`,`Gp`,`tp`,`[]`,`OK z`,`Gc`,`tc`] mp_tac) >>
     simp[]) >>
  `!x. not_fresh_at ds x ==>
     lookup_var x z = lookup_var x u /\ FLOOKUP Gc x = FLOOKUP Gu x /\
     op_taint tc (Var x) = op_taint tu (Var x)` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at ds x ==> lookup_var x z = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `typed_copy_state_frame ds (w2n dw) (type_memory_size rtv) u z` by
    (qpat_assum `typed_copy_state_frame ds _ _ u p`
       (strip_assume_tac o SIMP_RULE (srw_ss())
         [typedMemoryCopyTheory.typed_copy_state_frame_def, venom_state_component_equality]) >>
     rewrite_tac[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
     conj_tac
     >- (Cases_on `skip` >>
         simp[NoAsms, Abbr `z`, Abbr `checked`, jump_to_def, update_var_def,
              venom_state_component_equality] >> simp[]) >>
     conj_tac >- (rpt strip_tac >> first_assum (drule_then strip_assume_tac) >> simp[]) >>
     qpat_assum `z.vs_memory = p.vs_memory` SUBST1_TAC >>
     qpat_assum `typed_copy_frame _ _ u.vs_memory p.vs_memory` ACCEPT_TAC) >>
  `lookup_var q z = SOME dw /\ FLOOKUP Gc q = SOME (w2n dw,type_memory_bytes cenv ret_type) /\
   ptr_covers Gc tc q z (type_memory_size rtv)` by
    (qpat_assum `!x. not_fresh_at ds x ==> lookup_var x z = _ /\ FLOOKUP Gc x = FLOOKUP Gu x /\ _`
       (qspec_then `q` mp_tac) >>
     qpat_assum `ptr_covers Gu tu q u _` mp_tac >> simp[ptr_covers_def]) >>
  `alloca_history func z` by
    (irule allocaHistoryTheory.alloca_history_jump >> conj_tac
     >- simp[NoAsms, Abbr `z`, jump_to_def] >> qexists_tac `u` >> simp[]) >>
  `local_ptrs_reserved cenv ds` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!name b len. local_region cenv ee.scopes z name b len <=>
     local_region cenv ee.scopes u name b len` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     rpt strip_tac >> rename1 `FLOOKUP cenv.ce_vars _ = SOME (PtrVar (Var v) _)` >>
     `not_fresh_at ds v` by metis_tac[local_ptrs_reserved_def] >>
     qpat_assum `!x. not_fresh_at ds x ==> lookup_var x z = _ /\ FLOOKUP Gc x = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `!b len. b + len <= w2n dw \/ w2n dw + type_memory_size rtv <= b ==>
     mem_bytes_at b len z.vs_memory = mem_bytes_at b len u.vs_memory` by
    (qpat_assum `typed_copy_state_frame ds _ _ u z`
       (strip_assume_tac o PURE_REWRITE_RULE
         [typedMemoryCopyTheory.typed_copy_state_frame_def, typedMemoryCopyTheory.typed_copy_frame_def]) >>
     first_assum ACCEPT_TAC) >>
  `!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size rtv) ==>
     (i IN tc.t_mem <=> i IN tu.t_mem)` by simp[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee z` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >>
     irule exprSimIfExpWidenedCountedTheory.typed_copy_semantic_frame >>
     goal_assum (drule_at (Pat `typed_copy_state_frame ds _ _ u z`)) >>
     goal_assum (drule_at (Pat `MEM _ (fn_insts func)`)) >>
     simp[venomInstTheory.mk_inst_def] >> rpt strip_tac >>
     qpat_assum `!name b len. local_region cenv ee.scopes u name b len ==> _`
       (drule_then strip_assume_tac) >> decide_tac) >>
  `!x. not_fresh_at sa x ==>
     lookup_var x z = lookup_var x u /\ FLOOKUP Gc x = FLOOKUP Gu x /\
     op_taint tc (Var x) = op_taint tu (Var x)` by
    (rpt strip_tac >> `not_fresh_at ds x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
        simp[] >> decide_tac) >>
     qpat_assum `!x. not_fresh_at ds x ==> lookup_var x z = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `lo <= w2n dw` by
    (qpat_assum `allocas_from lo u` (strip_assume_tac o REWRITE_RULE[allocas_from_def]) >>
     first_assum irule >> qexistsl_tac [`sr.cs_next_id`,`type_memory_bytes cenv ret_type`] >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee Gc tc z` by suspend "default_ghost" >>
  suspend "default_owned_post"
QED

Resume extcall_return_full_default_value[default_ghost]:
  qx_gen_tac `h` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `stmt_state_rel h _ _ _ _ _ u`
    (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
  irule extcall_default_copy_ghost_local >>
  goal_assum (drule_at (Pat `typed_copy_state_frame ds _ _ u z`)) >>
  goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ Gu tu u`)) >>
  goal_assum (drule_at (Pat `local_ptrs_rel func cenv ee.scopes u`)) >>
  qexists_tac `sa` >> simp[] >> rpt strip_tac >>
  qpat_assum `!name b len. local_region cenv ee.scopes u name b len ==> _`
    (drule_then strip_assume_tac) >> decide_tac
QED

Resume extcall_return_full_default_value[default_owned_post]:
  `!aid b len. aid < sr.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
    w2n dw + type_memory_size rtv <= b \/ b + len <= w2n dw` by
    (rpt strip_tac >>
     qpat_assum `!aid b len. aid < sr.cs_next_id /\ _ ==> regions_disjoint _ _ _ _`
       (drule_all_then mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def, arithmeticTheory.ADD_COMM]) >>
  `!name b len. local_region cenv ee.scopes t name b len ==>
    local_region cenv ee.scopes u name b len` by
    (rpt strip_tac >> irule (iffLR local_region_lookup_cong) >>
     goal_assum (drule_at (Pat `local_region _ _ t _ _ _`)) >>
     rpt strip_tac >> rename1 `FLOOKUP cenv.ce_vars _ = SOME (PtrVar (Var v) _)` >>
     `not_fresh_at sr v` by metis_tac[local_ptrs_reserved_def] >>
     qpat_assum `!x. not_fresh_at sr x ==> lookup_var x u = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `wb_frame cenv es ee sa s0 z` by suspend "default_writeback" >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gc tc` by suspend "default_kept" >>
  `sr.cs_next_id < sb.cs_next_id` by
    (`sr.cs_next_id < ar.cs_next_id` by
       (qpat_assum `compile_alloc_buffer _ sr = (buf,ar)`
          (mp_tac o MATCH_MP loweringHaltTheory.compile_alloc_buffer_parts) >> simp[]) >>
     `ar.cs_next_id <= sb.cs_next_id` by
       (qpat_assum `compile_default_return_path _ _ _ _ _ _ _ _ _ _ _ ar = (_,sb)` mp_tac >>
        metis_tac[exprLoweringPropsTheory.ci_mono_compile_default_return_path,
                  exprLoweringPropsTheory.ci_mono_def, pairTheory.SND]) >>
     decide_tac) >>
  `!mem. mem_agree_outside tc.t_mem z.vs_memory mem ==>
    val_in_memory rtv dv (w2n dw) mem` by
    (qpat_assum `!mem. mem_agree_outside tp.t_mem p.vs_memory mem ==> _` mp_tac >> simp[]) >>
  `val_in_memory rtv dv (w2n dw) z.vs_memory` by
    (first_assum irule >> simp[mem_agree_outside_def]) >>
  `val_store_size rtv dv <= type_memory_size rtv /\
   val_footprint rtv dv <= type_memory_size rtv` by
    simp[exprSimPropsTheory.val_store_size_le, exprSimPropsTheory.val_footprint_le] >>
  `is_word_type ret_type ==> mem_word_at (w2n dw) z.vs_memory = typed_val_to_w256 rtv dv` by
    metis_tac[exprSimPropsTheory.val_in_memory_word_type] >>
  `ann = ret_type` by
    (qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` mp_tac >>
     POP_ASSUM_LIST kall_tac >>
     simp[exprSimHypsDefsTheory.expr_body_pre_def,
          cj 13 vyperTypeSystemTheory.well_typed_expr_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `e = Call ann (ExtCall is_static' skip (fname,arg_types,ret_type) opts) args dflt` >>
  `lowered_value_type cenv e = ret_type /\ post_value_type cenv e = ret_type /\ expr_type e = ret_type /\
   expr_has_effect e` by
    simp[Abbr `e`, exprLoweringTheory.lowered_value_type_def, post_value_type_def,
         vyperASTTheory.expr_type_def, supportedExprTraverseTheory.expr_has_effect_def,
         Once supportedExprTraverseTheory.supported_expr_exists_def,
         supportedExprTraverseTheory.expr_effect_root_def] >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  qpat_assum `skip \/ ext_call_has_code target ee.accounts`
    (fn th => pure_rewrite_tac [th, COND_CLAUSES]) >>
  qexistsl_tac [`OK z`,`Gc`,`tc`] >> qx_gen_tac `h` >> strip_tac >>
  conj_tac >- simp[] >> disj1_tac >>
  simp[mk_ptr_def, vv_location_def] >>
  suspend "default_located"
QED

Resume extcall_return_full_default_value[default_located]:
  `!name b len. local_region cenv ee.scopes z name b len ==>
    w2n dw + type_memory_size rtv <= b \/ b + len <= w2n dw` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes u name b len` by
       (irule (iffLR local_region_lookup_cong) >>
        goal_assum (drule_at (Pat `local_region _ _ z _ _ _`)) >>
        rpt strip_tac >>
        rename1 `FLOOKUP cenv.ce_vars _ = SOME (PtrVar (Var v) _)` >>
        `not_fresh_at sa v` by metis_tac[local_ptrs_reserved_def] >>
        qpat_assum `!x. not_fresh_at sa x ==> lookup_var x z = _ /\ _`
          (drule_then strip_assume_tac) >> simp[]) >>
     qpat_assum `!name b len. local_region cenv ee.scopes u name b len ==> _`
       (drule_then ACCEPT_TAC)) >>
  `stmt_state_rel h ctx func cenv cx ee z` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ z`
       (drule_then ACCEPT_TAC)) >>
  `storage_well_formed_on cx ee (FST h)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `op_taint tc (Var q) = {}` by
    (qpat_assum `ptr_covers Gc tc q z _` (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[ptr_covers_def])) >>
  `FLOOKUP z.vs_allocas sr.cs_next_id = SOME (w2n dw,type_memory_size rtv)` by simp[] >>
  `w2n dw + type_memory_size rtv <= z.vs_alloca_next` by decide_tac >>
  `val_store_size rtv dv + w2n dw <= z.vs_alloca_next /\
    w2n dw + val_store_size rtv dv <= w2n dw + type_memory_size rtv` by decide_tac >>
  `?aid b sz. FLOOKUP a.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid /\
    aid < sb.cs_next_id /\ b <= w2n dw /\ w2n dw + val_footprint rtv dv <= b + sz /\
    (!n lb lsz. local_region cenv ee.scopes u n lb lsz ==> b + sz <= lb \/ lb + lsz <= b)` by
    (qexistsl_tac [`sr.cs_next_id`,`w2n dw`,`type_memory_size rtv`] >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!name b len. local_region cenv ee.scopes u name b len ==> w2n dw + _ <= b \/ _`
       (drule_then strip_assume_tac) >> decide_tac) >>
  simp[IgnAsm `z.vs_memory = p.vs_memory`, loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def,
       loweringPostsTheory.vv_at_def, loweringPostsTheory.vv_own_def,
       loweringPostsTheory.vv_place_ptr_def, exprSimMemDefsTheory.vv_store_bound_def,
       ptr_vv_ok_def, ptr_mem_ok_def, ptr_buf_ok_def, vyperStateTheory.read_result_def,
       vyperStateTheory.return_def, eval_operand_def] >>
  qpat_assum `wb_frame cenv es ee sa s0 a`
    (strip_assume_tac o REWRITE_RULE[wb_frame_def]) >>
  qpat_assum `wb_frame cenv es ee sa s0 z`
    (strip_assume_tac o REWRITE_RULE[wb_frame_def]) >>
  simp[IgnAsm `z.vs_memory = p.vs_memory`] >> rpt conj_tac >> rpt strip_tac >>
  simp[IgnAsm `z.vs_memory = p.vs_memory`] >>
  FIRST [disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >>
           rpt conj_tac >> first_assum ACCEPT_TAC,
         first_assum (drule_all_then ACCEPT_TAC),
         first_assum (drule_then ACCEPT_TAC)]
QED

Resume extcall_return_full_default_value[default_writeback]:
  irule exprSimHashTheory.wb_frame_allocating_tail >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`t`,`ee.scopes`,`sr`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      qpat_assum `!name b len. local_region cenv ee.scopes t name b len ==> _`
        (drule_then assume_tac) >>
      qpat_assum `!name b len. local_region cenv ee.scopes u name b len ==> _`
        (drule_then strip_assume_tac) >>
      qpat_assum `!b len. _ ==> mem_bytes_at b len z.vs_memory = _`
        (qspecl_then [`b`,`sz`] mp_tac) >> simp[])
  >- (rpt strip_tac >>
      `not_fresh_at ds x` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sr` >>
         simp[] >> decide_tac) >>
      qpat_assum `!x. not_fresh_at ds x ==> lookup_var x z = _ /\ _`
        (drule_then strip_assume_tac) >>
      qpat_assum `!x. not_fresh_at sr x ==> lookup_var x u = _ /\ _`
        (drule_then strip_assume_tac) >> simp[])
  >- (rpt strip_tac >>
      qpat_assum `!aid b len. aid < sr.cs_next_id /\ _ ==> _`
        (drule_all_then strip_assume_tac) >>
      qpat_assum `!b len. _ ==> mem_bytes_at b len z.vs_memory = _`
        (qspecl_then [`b`,`sz`] mp_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!aid e. FLOOKUP t.vs_allocas aid = SOME e ==> _`
    (drule_then assume_tac) >> simp[]
QED

Resume extcall_return_full_default_value[default_kept]:
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu`
    (strip_assume_tac o REWRITE_RULE[ghost_kept_at_def]) >>
  rewrite_tac[ghost_kept_at_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!x. not_fresh_at sa x ==> lookup_var x z = _ /\ FLOOKUP Gc x = _ /\ _`
        (drule_then strip_assume_tac) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by
        (qpat_assum `wb_frame cenv es ee sa s0 t`
           (strip_assume_tac o REWRITE_RULE[wb_frame_def]) >>
         first_assum (drule_then ACCEPT_TAC)) >>
      `w2n dw + type_memory_size rtv <= off \/ off + sz <= w2n dw` by
        (qpat_assum `!aid b len. aid < sr.cs_next_id /\ FLOOKUP t.vs_allocas aid = _ ==> _`
           (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[] >> decide_tac) >>
      `i IN tu.t_mem` by
        (qpat_assum `!i. _ ==> (i IN tc.t_mem <=> i IN tu.t_mem)`
           (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
      qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
        (qspecl_then [`aid`,`off`,`sz`,`i`] MATCH_MP_TAC) >>
      simp[] >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  `local_region cenv ee.scopes u n b sz` by
    (irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`s0`,`sa`,`es.scopes`] >>
     qpat_assum `wb_frame cenv es ee sa s0 u`
       (assume_tac o CONJUNCT1 o REWRITE_RULE[wb_frame_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `w2n dw + type_memory_size rtv <= b \/ b + sz <= w2n dw` by
    (qpat_assum `!name b len. local_region cenv ee.scopes u name b len ==> _`
       (drule_then ACCEPT_TAC)) >>
  `i IN tu.t_mem` by
    (qpat_assum `!i. _ ==> (i IN tc.t_mem <=> i IN tu.t_mem)`
       (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
  qpat_assum `!n b sz i. local_region cenv es.scopes s0 n b sz /\ _ ==> _`
    (qspecl_then [`n`,`b`,`sz`,`i`] mp_tac) >> simp[]
QED
Finalise extcall_return_full_default_value
