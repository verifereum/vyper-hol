(* The non-default branch of the linked external return. *)
Theory bodyExtReturnDecodeMods
Ancestors
  bodyExtReturnAllocMods bodyExtReturnLayoutMods bodyExtReturnDecodeRouteMods
  bodyExtReturnSizeWindowMods bodyExtReturnSizedPhysicalMods bodyExtReturnDecodedPostMods
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  fragGasEmitCtrl fragExec loweringHalt exprSimAlloc decoderGhostFramePtr
  abiReturnPrefixTransport abiMalformedRecursiveInterface abiDecoderReentry
  bodyFullUnwrapRun freshWrites exprSimExtCallCase exprLoweringProps exprSafeOperand
  bodyFullPostsMods bodyFullShadowBodyInv bodyPtrDefs ptrDiscipline
  stateRelProj abiCallerAllocation abiCallerLocalScratch bodyFullAllocaFresh
  loweringStateRelDefs loweringPosts compileEnv exprLowering context
  vyperInterpreter vyperABI vyperAST vyperState venomState venomMemDefs
  words finite_map pred_set list arithmetic
Libs monadsyntax

Theorem return_compile_alloc_interval[local]:
  ret_type <> NoneT /\
  compile_alloc_buffer (type_memory_bytes cenv ret_type) sr = (buf,ar) /\
  (if ret_type = NoneT then comp_return (Lit 0w)
   else if has_default then
     comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
       (\r. compile_default_return_path cenv ret_type default_ty
         buf_op r.buf_operand default_op addr_op skip
         (abi_static_size cenv.ce_struct_fields rt) cap
         (type_to_abi_dec_info cenv.ce_struct_fields cenv rt))
   else
     comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
       (\r. comp_bind (compile_return_value_decode
          (abi_static_size cenv.ce_struct_fields rt) cap)
         (\hi. comp_ignore_bind
           (compile_abi_decode_to_buf r.buf_operand (Lit 0w) MLOAD buf_op hi
             (type_to_abi_dec_info cenv.ce_struct_fields cenv rt))
           (comp_return r.buf_operand)))) sr = (result_op,sb) /\
  fn_has_code sr sb func ==>
  fn_has_code sr ar func /\ fn_has_code ar sb func /\
  ar.cs_next_id = sr.cs_next_id + 1 /\ ar.cs_next_var = sr.cs_next_var + 1
Proof
  strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `cs_extends ar sb` by
    (qpat_x_assum `(if ret_type = NoneT then _ else _) sr = _` mp_tac >>
     Cases_on `has_default` >> simp[comp_bind_def,comp_ignore_bind_def,comp_return_def] >-
       (strip_tac >>
        qpat_assum `compile_default_return_path _ _ _ _ _ _ _ _ _ _ _ ar = _` mp_tac >>
        rpt (pop_assum kall_tac) >>
        metis_tac[ci_mono_compile_default_return_path,ci_mono_def,pairTheory.SND]) >>
     pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
     irule cs_extends_trans >>
     rename1 `compile_return_value_decode _ _ ar = (_,hs)` >>
     qexists `hs` >> conj_tac
     >- (qpat_assum `compile_return_value_decode _ _ ar = _` mp_tac >>
         rpt (pop_assum kall_tac) >>
         metis_tac[ci_mono_compile_return_value_decode,ci_mono_def,pairTheory.SND]) >>
     (qpat_x_assum `sb = _` SUBST_ALL_TAC ORELSE
      qpat_x_assum `_ = sb` (SUBST_ALL_TAC o SYM)) >>
     qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ hs = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[cj 1 ci_mono_compile_abi_decode,ci_mono_def,pairTheory.SND]) >>
  `cs_extends sr ar` by
    (qpat_assum `compile_alloc_buffer _ sr = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[ci_mono_compile_alloc_buffer,ci_mono_def,pairTheory.SND]) >>
  conj_tac >- (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`,`sr`] >> simp[cs_extends_refl]) >>
  conj_tac >- (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`,`sr`] >> simp[cs_extends_refl]) >>
  simp[]
QED

Theorem extcall_return_decode_mods:
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
  !mods DF lo d explicit ctx PG func cenv cx env es ann is_static skip fname
   arg_types ret_type opts args dflt st0 sa sb s0 G0 tn0 sr result_op vv
   addr_op buf_op cap target has_default default_op default_ty default_opt
   returnData ee t G tn.
    expr_body_pre_mods mods cenv cx env
      (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
         args dflt) es /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    cap = abi_size_bound cenv.ce_struct_fields
      (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type) /\
    (if ret_type = NoneT then comp_return (Lit 0w)
     else if has_default then
       comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
         (\r. compile_default_return_path cenv ret_type default_ty
                buf_op r.buf_operand default_op addr_op skip
                (abi_static_size cenv.ce_struct_fields
                  (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type))
                cap (type_to_abi_dec_info cenv.ce_struct_fields cenv
                  (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)))
     else
       comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
         (\r. comp_bind (compile_return_value_decode
                     (abi_static_size cenv.ce_struct_fields
                        (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)) cap)
         (\hi_op. comp_ignore_bind
            (compile_abi_decode_to_buf r.buf_operand (Lit 0w) MLOAD buf_op hi_op
               (type_to_abi_dec_info cenv.ce_struct_fields cenv
                  (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)))
            (comp_return r.buf_operand)))) sr = (result_op,sb) /\
    vv = (if ret_type = NoneT then StackValue ann result_op
          else LocatedValue ann (mk_ptr result_op LocMemory)) /\
    fn_has_code sr sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ MEM func ctx.ctx_functions /\
    (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr_op buf_op
      cap target has_default default_op default_ty default_opt returnData ee t /\
    (IS_SOME default_opt /\ ~is_word_type default_ty ==>
      ?w aid tv. eval_operand default_op t = SOME w /\
        evaluate_type (get_tenv cx) default_ty = SOME tv /\
        FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\ aid < sr.cs_next_id) /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
       immutable_frame_mods func cenv cx ee t) /\
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
            i NOTIN tn.t_mem)) /\
    ret_type <> NoneT /\ ~(has_default /\ returnData = []) /\
    (?H. valid_horizon cx st0 H ee.storage_trace) ==>
    ?res r G' tn'.
      (!tail.
        (case (if returnData = [] then default_opt else NONE) of
         SOME default_v =>
           do accounts' <- get_accounts;
              check (skip \/ ext_call_has_code target accounts') "ExtCall target has no code";
              return (Value default_v) od
       | NONE =>
           do ret_val <- lift_sum_runtime
                (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
              return (Value ret_val) od) (ee with gas_obs := tail) =
          (res, ee with gas_obs := tail)) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
          (t, G, tn) [] (r, G', tn') /\
        ((?t'. r = OK t' /\ ?tv. res = INL tv /\
         vv_post_mods H ctx func cenv cx
           (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
              args dflt) es sa sb s0 (ee with gas_obs := []) tv vv t' /\
         vv_store_bound cx
           (expr_type (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts) args dflt))
           (lowered_value_type cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
                 args dflt)) (ee with gas_obs := []) tv vv t' /\
         t'.vs_current_bb = sb.cs_current_bb /\ t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
         alloca_history func t' /\ s0.vs_alloca_next <= t'.vs_alloca_next /\
         ghost_inv_at_mods (DF H) lo d cenv cx (ee with gas_obs := []) G' tn' t' /\
         ptr_vv_ok cx
           (post_value_type cenv (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts) args dflt))
           tv vv (ee with gas_obs := []) G' tn' t' /\
         (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
          ?val. read_result cx tv (ee with gas_obs := []) = (INL val, (ee with gas_obs := [])) /\
                !rt w. evaluate_type (get_tenv cx)
                         (post_value_type cenv (Call ann (ExtCall is_static skip
                               (fname,arg_types,ret_type) opts) args dflt)) = SOME rt /\
                       eval_operand (vv_operand vv) t' = SOME w ==>
                       w2n w + type_memory_size rt <= lo /\
                       (!mem. mem_agree_outside tn'.t_mem t'.vs_memory mem ==>
                              val_in_memory rt val (w2n w) mem)) /\
         (!t'' op. vv = StackValue t'' op /\
            ~is_word_type (post_value_type cenv
               (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts) args dflt)) ==>
            ptr_buf_ok cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts) args dflt) op G' t') /\
         (!t'' p. vv = LocatedValue t'' p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts) args dflt) p.ptr_operand G' t') /\
         vv_own cenv cx
           (post_value_type cenv (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts) args dflt))
           sa sb (ee with gas_obs := []) tv vv t' /\
         ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn') \/
         (exit_result r /\ expr_exit res r)))
Proof
  disch_then (mk_asm "valid") >> disch_then (mk_asm "reject") >>
  rpt gen_tac >> strip_tac >>
  drule_all_then (strip_assume_tac o SRULE[LET_THM]) extcall_return_layout_mods >>
  qabbrev_tac `rt = if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type` >>
  qabbrev_tac `rtv = if needs_external_call_wrap ret_type then TupleTV [actual_tv] else actual_tv` >>
  `rt = (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type) /\
   rtv = (if needs_external_call_wrap ret_type then TupleTV [actual_tv] else actual_tv)` by
    simp[Abbr `rt`,Abbr `rtv`] >>
  Cases_on `compile_alloc_buffer (type_memory_bytes cenv ret_type) sr` >>
  rename1 `compile_alloc_buffer _ sr = (buf,ar)` >>
  drule_all_then strip_assume_tac return_compile_alloc_interval >>
  `type_memory_bytes cenv ret_type < dimword (:256)` by decide_tac >>
  `immutable_frame_mods func cenv cx ee t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at_mods _ _ _ _ _ _ _ _ _ /\ _`
      (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  drule extcall_return_alloc_cut_mods >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (mp_tac o Q.INST [`DF` |-> `DF`, `d` |-> `d`, `explicit` |-> `explicit`, `PG` |-> `PG`] o SPEC_ALL) >>
  (impl_tac >- (simp[] >> goal_assum (drule_at Any))) >>
  strip_tac >>
  suspend "route"
QED

Resume extcall_return_decode_mods[route]:
  qhdtm_assum `extcall_returned` (strip_assume_tac o REWRITE_RULE[extcall_returned_def]) >>
  `(if returnData = [] then default_opt else NONE) = NONE` by
    (qhdtm_assum `extcall_default_ready` mp_tac >>
     qpat_assum `~(has_default /\ returnData = [])` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `default_opt` >> simp[extcall_default_ready_def] >> metis_tac[]) >>
  `immutable_frame_mods func cenv cx ee a` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ a /\ _`
      (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee a /\ storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee J tm a` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ a /\ _`
       (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  `sa.cs_next_id <= ar.cs_next_id /\ sa.cs_next_var <= ar.cs_next_var` by decide_tac >>
  `local_ptrs_reserved cenv ar` by
    (irule local_ptrs_reserved_next_var >> qexists `sr` >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ar x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ar x)` by
    (conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  drule_at (Pat `(if ret_type = NoneT then _ else _) sr = _`) extcall_decode_route_mods >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ sr = _`)) >>
  disch_then (drule_at (Pat `buf.buf_operand = Var q`)) >>
  disch_then (fn th => qpat_assum `ghost_kept_at _ _ _ _ _ _ _ J tm` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `wb_frame _ _ _ sa s0 a` (mp_then Any mp_tac th)) >>
  disch_then (mp_tac o Q.INST [`DF` |-> `DF`, `d` |-> `d`, `st0` |-> `st0`,
    `ctx` |-> `ctx`, `bs` |-> `returnData`, `t` |-> `t`, `G` |-> `G`, `tn` |-> `tn`,
    `explicit` |-> `explicit`, `PG` |-> `PG`, `cx` |-> `cx`] o SPEC_ALL) >>
  (impl_tac >- (asm_rewrite_tac[] >> goal_assum (drule_at Any))) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`k`,`hi`,`hs`,`de`,`p`,`Gp`,`tp`] (map_every assume_tac o CONJUNCTS))) >>
  suspend "window_entry"
QED

Resume extcall_return_decode_mods[window_entry]:
  `cap <> 0 /\ cap < dimword (:256)` by decide_tac >>
  qpat_assum `cap <> 0 ==> _` (drule_then
    (qx_choosel_then [`source`,`prov_base`,`span`,`rw`] (map_every assume_tac o CONJUNCTS))) >>
  rename1 `eval_operand buf_op t = SOME ro` >>
  `eval_operand (Var source) t = SOME ro /\ op_taint tn (Var source) = {} /\ not_fresh_at sr source` by
    (qpat_assum `EVERY (\op. op_taint tn op = {}) _` mp_tac >>
     qpat_assum `EVERY (safe_operand sr) _` mp_tac >>
     simp[safe_operand_def]) >>
  `rw = ro` by
    (qpat_assum `eval_operand buf_op t = SOME rw` mp_tac >> simp[]) >>
  qpat_x_assum `rw = ro` SUBST_ALL_TAC >>
  qpat_assum `ci_mono ar k` (strip_assume_tac o REWRITE_RULE[ci_mono_def]) >>
  `sa.cs_next_id <= k.cs_next_id /\ sa.cs_next_var <= k.cs_next_var /\
   sr.cs_next_id < k.cs_next_id` by decide_tac >>
  `not_fresh_at ar source /\ not_fresh_at k source /\ not_fresh_at k q` by
    (conj_tac >- (irule not_fresh_at_mono >> qexists `sr` >> simp[]) >>
     conj_tac >> irule not_fresh_at_mono >> qexists `ar` >> simp[]) >>
  `local_ptrs_reserved cenv k` by
    (irule local_ptrs_reserved_next_var >> qexists `ar` >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x)` by
    (conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `alloca_inv p /\ (ctx_has_dalloca ctx ==> allocas_below_fmp p)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ p /\ _`
      (drule_then strip_assume_tac) >>
     drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
     drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `alloca_inv t` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `lookup_var source p = lookup_var source t /\ FLOOKUP Gp source = FLOOKUP G source /\
   op_taint tp (Var source) = op_taint tn (Var source)` by
    (qpat_assum `!x. not_fresh_at ar x ==> lookup_var x p = lookup_var x a /\ _`
      (qspec_then `source` (drule_then strip_assume_tac)) >>
     qpat_assum `!x. not_fresh_at sr x ==> lookup_var x a = lookup_var x t /\ _`
      (qspec_then `source` (drule_then strip_assume_tac)) >> asm_rewrite_tac[]) >>
  `lookup_var q p = SOME w /\ ptr_covers Gp tp q p (type_memory_bytes cenv ret_type)` by
    (qpat_assum `!x. not_fresh_at ar x ==> lookup_var x p = lookup_var x a /\ _`
      (qspec_then `q` (drule_then strip_assume_tac)) >>
     conj_tac >- asm_rewrite_tac[] >>
     irule ptr_covers_frame >> goal_assum (drule_at (Pat `ptr_covers _ _ _ _ _`)) >> asm_rewrite_tac[]) >>
  FAIL_TAC "window entry"
QED

Finalise extcall_return_decode_mods
