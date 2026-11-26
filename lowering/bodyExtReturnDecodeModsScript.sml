(* The non-default branch of the linked external return. *)
Theory bodyExtReturnDecodeMods
Ancestors
  bodyExtReturnAllocMods bodyExtReturnLayoutMods bodyExtReturnDecodeRouteMods
  bodyExtReturnSizeWindowMods bodyExtReturnSizedPhysicalMods bodyExtReturnDecodedPostMods
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  fragGasOriginPtr fragGasEmitCtrl fragExec loweringHalt exprSimAlloc decoderGhostFramePtr
  abiReturnPrefixTransport abiMalformedRecursiveInterface abiDecoderReentry
  abiValidAllocatedContract emitHelperProps
  bodyFullUnwrapRun freshWrites exprSimDefs exprSimExtCallCase exprLoweringProps exprSafeOperand
  bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit bodyPtrDefs ptrDiscipline
  exprSimMemDefs allocaHistory
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

(* The jump at the end of decoding changes control, not the retained value. *)
Theorem return_decoded_jump_post[local]:
  vv_post_mods H ctx func cenv cx e es sa sb s0 ee (Value v)
    (LocatedValue ann (mk_ptr op LocMemory)) (jump_to lbl s) <=>
  vv_post_mods H ctx func cenv cx e es sa sb s0 ee (Value v)
    (LocatedValue ann (mk_ptr op LocMemory)) s
Proof
  simp[vv_post_mods_def, stmt_state_rel_jump_to,
       immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def,
       immutables_rel_def, immutable_alloca_sep_def, local_region_def,
       vv_holds_mods_def, vv_holds_def, vv_place_ptr_mods_def, vv_place_ptr_def,
       contextTheory.mk_ptr_def, vv_at_def, vv_own_def,
       locals_kept_def, popped_kept_def, pure_frame_def,
       eval_operand_def, lookup_var_def, jump_to_def]
QED

Theorem return_decoded_jump_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx ee G tn (jump_to lbl s) <=>
  ghost_inv_at_mods D lo d cenv cx ee G tn s
Proof
  simp[ghost_inv_at_mods_def,jump_to_def,ptr_covers_def,stor_taint_ok_at_def,
       lookup_var_def,allocas_from_def] >>
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  PairCases_on `x` >> simp[return_buf_ptr_def,ptr_covers_def,lookup_var_def]
QED

Theorem return_decoded_jump_value[local]:
  (vv_store_bound cx ty lt ee (Value v) (LocatedValue ann (mk_ptr op LocMemory)) (jump_to lbl s) <=>
   vv_store_bound cx ty lt ee (Value v) (LocatedValue ann (mk_ptr op LocMemory)) s) /\
  (ptr_vv_ok cx ty (Value v) (LocatedValue ann (mk_ptr op LocMemory)) ee G tn (jump_to lbl s) <=>
   ptr_vv_ok cx ty (Value v) (LocatedValue ann (mk_ptr op LocMemory)) ee G tn s) /\
  (ptr_buf_ok cenv e op G (jump_to lbl s) <=> ptr_buf_ok cenv e op G s) /\
  (vv_own cenv cx ty sa sb ee (Value v) (LocatedValue ann (mk_ptr op LocMemory)) (jump_to lbl s) <=>
   vv_own cenv cx ty sa sb ee (Value v) (LocatedValue ann (mk_ptr op LocMemory)) s)
Proof
  simp[vv_store_bound_def, ptr_vv_ok_def, ptr_buf_ok_def, ptr_mem_ok_def, vv_own_def,
       contextTheory.mk_ptr_def, local_region_def, eval_operand_def, lookup_var_def, jump_to_def]
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
  rename1 `mem_bytes_at (w2n ro) _ t.vs_memory = TAKE cap returnData` >>
  `rw = ro` by
    (qpat_assum `eval_operand buf_op t = SOME rw` mp_tac >>
     qpat_assum `eval_operand buf_op t = SOME ro`
       (fn th => pure_rewrite_tac[th,optionTheory.SOME_11]) >>
     disch_then (ACCEPT_TAC o SYM)) >>
  qpat_x_assum `rw = ro` SUBST_ALL_TAC >>
  `eval_operand (Var source) t = SOME ro /\ op_taint tn (Var source) = {} /\ not_fresh_at sr source` by
    (qpat_assum `buf_op = Var source` (SUBST1_TAC o SYM) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (qpat_assum `EVERY (\op. op_taint tn op = {}) _`
           (strip_assume_tac o BETA_RULE o REWRITE_RULE[listTheory.EVERY_DEF]) >>
         first_assum ACCEPT_TAC) >>
     qpat_assum `EVERY (safe_operand sr) _`
       (strip_assume_tac o REWRITE_RULE[listTheory.EVERY_DEF]) >>
     qpat_assum `safe_operand sr buf_op` mp_tac >>
     qpat_assum `buf_op = Var source` (fn th =>
       simp_tac bool_ss [th,safe_operand_def,operand_11,operand_distinct])) >>
  qpat_assum `ci_mono ar k` (strip_assume_tac o REWRITE_RULE[ci_mono_def]) >>
  `sa.cs_next_id <= k.cs_next_id /\ sa.cs_next_var <= k.cs_next_var /\
   sr.cs_next_id < k.cs_next_id /\ sr.cs_next_var <= ar.cs_next_var` by decide_tac >>
  `not_fresh_at ar source` by (irule not_fresh_at_mono >> qexists `sr` >> simp[]) >>
  `not_fresh_at k source /\ not_fresh_at k q` by
    (conj_tac >> irule not_fresh_at_mono >> qexists `ar` >> simp[]) >>
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
      (qspec_then `q` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     conj_tac
     >- (qpat_assum `lookup_var q p = lookup_var q a` (SUBST1_TAC) >> first_assum ACCEPT_TAC) >>
     irule ptr_covers_frame >>
     goal_assum (drule_at (Pat `ptr_covers J tm q a _`)) >> asm_rewrite_tac[]) >>
  `abi_malformed_destination func cenv ee.scopes sr.cs_next_id
     (w2n w) (type_memory_bytes cenv ret_type) p` by
    (drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
     simp[abi_malformed_destination_def] >>
     qexistsl_tac [`mk_inst sr.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv ret_type))]
          [STRING #"%" (toString sr.cs_next_var)]`, `STRING #"%" (toString sr.cs_next_var)`] >>
     simp[venomInstTheory.mk_inst_def] >> irule local_ptrs_reserved_fresh >>
     qexists `sr` >> simp[]) >>
  `s0.vs_alloca_next <= p.vs_alloca_next` by decide_tac >>
  `!i. i < t.vs_alloca_next ==> (i IN tp.t_mem <=> i IN tn.t_mem)` by
    (qpat_assum `tp.t_mem = tm.t_mem` SUBST1_TAC >>
     qpat_assum `!i. i IN tm.t_mem <=> _` (fn th => pure_rewrite_tac [th]) >>
     gen_tac >> strip_tac >>
     `~(t.vs_alloca_next <= i)` by decide_tac >> asm_rewrite_tac[]) >>
  `compile_abi_decode_to_buf (Var q) (Lit 0w) MLOAD (Var source) hi
     (type_to_abi_dec_info cenv.ce_struct_fields cenv rt) hs = ((),de)` by
    (qpat_assum `compile_abi_decode_to_buf buf.buf_operand _ _ buf_op _ _ hs = _` mp_tac >>
     qpat_assum `buf.buf_operand = Var q` (fn bo =>
       qpat_assum `buf_op = Var source` (fn src => rewrite_tac [bo,src]))) >>
  `k.cs_next_id <= hs.cs_next_id /\ k.cs_next_var <= hs.cs_next_var` by
    (qpat_assum `compile_return_value_decode _ _ k = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[ci_mono_compile_return_value_decode,ci_mono_def,pairTheory.SND]) >>
  `hs.cs_next_id <= de.cs_next_id` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ hs = ((),de)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[cj 1 ci_mono_compile_abi_decode,ci_mono_def,pairTheory.SND]) >>
  `de.cs_next_id <= sb.cs_next_id` by
    (qpat_assum `de = sb \/ _` strip_assume_tac >- simp[] >>
     qpat_assum `emit_inst JMP _ _ de = _` mp_tac >>
     qpat_assum `new_block _ _ = (_,sb)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[ci_mono_emit_inst,ci_mono_new_block,ci_mono_trans,ci_mono_def,pairTheory.SND]) >>
  `sr.cs_next_id < sb.cs_next_id` by decide_tac >>
  suspend "window_ready"
QED

Resume extcall_return_decode_mods[window_ready]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_return_decode_ready H ctx func cenv cx ee k (abi_malformed_scratch_sites hs de func)
      sr.cs_next_id live (Var source) (Var q) (w2n ro) cap returnData (w2n w)
      (type_memory_bytes cenv rt) p /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee Gp tp p` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ p /\ _`
       (drule_then strip_assume_tac) >>
     reverse conj_tac >- asm_rewrite_tac[] >>
     qpat_assum `type_memory_bytes cenv rt = type_memory_bytes cenv ret_type` SUBST1_TAC >>
     simp_tac bool_ss [abi_return_decode_ready_def] >>
     ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (simp_tac bool_ss [abi_malformed_allocated_window_def] >>
        conj_tac >-
          (qexists `buf_size` >> conj_tac >-
             (qpat_assum `p.vs_allocas = a.vs_allocas` SUBST1_TAC >>
              first_assum irule >> first_assum ACCEPT_TAC) >>
           simp_tac (srw_ss()) [listTheory.LENGTH_TAKE_EQ] >> decide_tac) >>
        conj_tac >- (simp_tac (srw_ss()) [listTheory.LENGTH_TAKE_EQ] >> decide_tac) >>
        qpat_assum `p.vs_memory = a.vs_memory` SUBST1_TAC >>
        qpat_assum `a.vs_memory = t.vs_memory` SUBST1_TAC >>
        first_assum ACCEPT_TAC) >>
     conj_tac >- (irule abi_malformed_scratch_sites_older >> decide_tac) >>
     conj_tac >- decide_tac >>
     conj_tac >- (irule abi_malformed_scratch_sites_older >> decide_tac) >>
     ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (qpat_assum `eval_operand (Var source) t = SOME ro` mp_tac >>
        qpat_assum `lookup_var source p = lookup_var source t` (fn th =>
          simp_tac (srw_ss()) [eval_operand_def,th])) >>
     conj_tac >- simp[eval_operand_def] >>
     simp[abi_decoder_operand_live_def,abi_decoder_older_vars_def,GSYM not_fresh_at_def]) >>
  `ptr_covers Gp tp q p (type_memory_bytes cenv rt)` by
    (qpat_assum `type_memory_bytes cenv rt = type_memory_bytes cenv ret_type` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `compile_return_value_decode _ _ k = _`
    (mp_then Any mp_tac extcall_size_window_kept_mods) >>
  map_every (fn pat => disch_then (fn th => qpat_assum pat (mp_then Any mp_tac th)))
    [`compile_abi_decode_to_buf (Var q) _ _ (Var source) _ _ hs = _`,
     `!D. gas_origin_ptr_path _ (t,G,tn) [] (OK p,Gp,tp)`,
     `ghost_kept_at lo cenv es sa G0 tn0 s0 Gp tp`, `wb_frame cenv es ee sa s0 p`,
     `evaluate_type (get_tenv cx) ret_type = SOME actual_tv`,
     `FLOOKUP G source = SOME (prov_base,span)`,
     `FLOOKUP t.vs_allocas live = SOME (w2n ro,buf_size)`,
     `!H. valid_horizon _ _ H _ ==>
         abi_return_decode_ready H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p /\ _`] >>
  disch_then (mp_tac o Q.INST [`sb` |-> `sb`] o SPEC_ALL) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  Cases_on `LENGTH returnData < abi_static_size cenv.ce_struct_fields rt`
  >- (qpat_assum `LENGTH returnData < _` (fn th => pure_rewrite_tac[th,COND_CLAUSES]) >>
      disch_then (qx_choosel_then [`err`,`z`,`Gf`,`tf`] strip_assume_tac) >>
      qexistsl_tac [`INR (Error (RuntimeError err))`,`Abort Revert_abort z`,`Gf`,`tf`] >>
      simp_tac (srw_ss()) [bind_def,lift_sum_runtime_def,raise_def,expr_exit_def,exit_result_def] >>
      asm_rewrite_tac[sumTheory.sum_case_def,optionTheory.option_case_def,
        bind_def,lift_sum_runtime_def,raise_def] >> simp_tac (srw_ss()) [raise_def]) >>
  qpat_assum `~(LENGTH returnData < _)` (fn th => pure_rewrite_tac[th,COND_CLAUSES]) >>
  disch_then (qx_choosel_then [`u`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "physical"
QED

Resume extcall_return_decode_mods[physical]:
  qpat_assum `!HH. valid_horizon _ _ HH _ ==> abi_malformed_entry HH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `lo <= u.vs_alloca_next` by
    (qhdtm_assum `ghost_inv_at_mods` (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >>
     first_assum ACCEPT_TAC) >>
  asm "valid" (fn valid => asm "reject" (fn reject =>
    qpat_assum `compile_abi_decode_to_buf (Var q) _ _ (Var source) _ _ hs = _`
      (mp_then Any mp_tac (GEN_ALL (MATCH_MP (MATCH_MP extcall_sized_physical_mods valid) reject))))) >>
  map_every (fn pat => disch_then (fn th => qpat_assum pat (mp_then Any mp_tac th)))
    [`abi_malformed_entry H ctx func cenv cx ee hs _ _ _ _ _ _ _ _ _ _ _ _ _ u`,
     `abi_decode_ptr_window Gf tf u source ro _`, `allocas_from lo u`,
     `rtv = (if needs_external_call_wrap ret_type then _ else _)`] >>
  disch_then (qspec_then `PG` mp_tac) >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `abi_size_bound cenv.ce_struct_fields rt = vyper_abi_size_bound _ _`
       (fn th => pure_rewrite_tac[GSYM th]) >>
     qpat_assum `cap = abi_size_bound cenv.ce_struct_fields rt`
       (fn th => pure_rewrite_tac[th]) >>
     (first_assum ACCEPT_TAC ORELSE REFL_TAC))) >>
  Cases_on `evaluate_abi_decode_return (get_tenv cx) ret_type returnData`
  >- (rename1 `evaluate_abi_decode_return _ _ _ = INL value` >>
      qpat_assum `evaluate_abi_decode_return _ _ _ = INL value`
        (fn th => pure_rewrite_tac[th,sumTheory.sum_case_def] >> CONV_TAC (DEPTH_CONV BETA_CONV)) >>
      disch_then (qx_choosel_then [`z`,`Gd`,`td`,`ceiling`] (map_every assume_tac o CONJUNCTS)) >>
      suspend "decoded") >>
  rename1 `evaluate_abi_decode_return _ _ _ = INR err` >>
  qpat_assum `evaluate_abi_decode_return _ _ _ = INR err`
    (fn th => pure_rewrite_tac[th,sumTheory.sum_case_def] >> CONV_TAC (DEPTH_CONV BETA_CONV)) >>
  disch_then (qx_choosel_then [`z`,`Gd`,`td`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`INR (Error (RuntimeError err))`,`Abort Revert_abort z`,`Gd`,`td`] >>
  conj_tac >- simp[bind_def,lift_sum_runtime_def,raise_def] >>
  qx_gen_tac `HH` >> disch_tac >> conj_tac
  >- (qpat_assum `!D. gas_origin_ptr_path _ (t,G,tn) [] (OK u,Gf,tf)`
        (qspec_then `DF HH` mp_tac) >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ (u,Gf,tf) [] (Abort Revert_abort z,Gd,td)`
        (qspecl_then [`DF HH`,`explicit`] mp_tac) >>
      rpt (pop_assum kall_tac) >> metis_tac[gas_origin_ptr_path_append,listTheory.APPEND]) >>
  simp_tac (srw_ss()) [expr_exit_def,exit_result_def]
QED

Resume extcall_return_decode_mods[decoded]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,Gd,td)` by
    (qx_gen_tac `D` >>
     qpat_assum `!D. gas_origin_ptr_path _ (t,G,tn) [] (OK u,Gf,tf)` (qspec_then `D` mp_tac) >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (u,Gf,tf) [] (OK z,Gd,td)`
       (qspecl_then [`D`,`explicit`] mp_tac) >>
     rpt (pop_assum kall_tac) >> metis_tac[gas_origin_ptr_path_append,listTheory.APPEND]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (qhdtm_assum `abi_valid_allocated_post` (mp_tac o REWRITE_RULE[abi_valid_allocated_post_def,
       abi_malformed_resource_post_def]) >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
     simp[]) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm
          (qx_choose_then `zf` (map_every assume_tac o CONJUNCTS)))
    `?zf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK zf,Gd,td)) /\
      zf.vs_current_bb = sb.cs_current_bb /\ zf.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (zf = z \/ ?xl. zf = jump_to xl z)`
  >- (qpat_assum `de = sb \/ _` strip_assume_tac
     >- (qexists `z` >> asm_rewrite_tac[]) >>
     rename1 `emit_inst JMP [Label xl] [] de = ((),cj)` >> qexists `jump_to xl z` >>
     conj_tac >-
       (qx_gen_tac `D` >>
        `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,Gd,td) [] (OK (jump_to xl z),Gd,td)` by
          (irule emit_jmp_origin_ptr >> asm_rewrite_tac[] >>
           qexistsl_tac [`de`,`cj`] >> asm_rewrite_tac[]) >>
        qpat_assum `!D. gas_origin_ptr_path _ (t,G,tn) [] (OK z,Gd,td)` (qspec_then `D` mp_tac) >>
        qpat_assum `gas_origin_ptr_path _ (z,Gd,td) [] _` mp_tac >>
        rpt (pop_assum kall_tac) >> metis_tac[gas_origin_ptr_path_append,listTheory.APPEND]) >>
     drule_then strip_assume_tac new_block_props >>
     rpt conj_tac >- simp[jump_to_def] >- simp[jump_to_def] >>
     disj2_tac >> qexists `xl` >> REFL_TAC) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `vv = LocatedValue ann (mk_ptr (Var q) LocMemory)` by simp[] >>
  qexistsl_tac [`INL (Value value)`,`OK zf`,`Gd`,`td`] >>
  conj_tac >- simp[bind_def,lift_sum_runtime_def,return_def] >>
  qx_gen_tac `Hpost` >> disch_tac >> conj_tac >- asm_rewrite_tac[] >>
  disj1_tac >> qexists `zf` >> conj_tac >- REFL_TAC >> qexists `Value value` >>
  suspend "linked_post"
QED

Resume extcall_return_decode_mods[linked_post]:
  qpat_assum `!HH. valid_horizon _ _ HH _ ==> abi_malformed_entry HH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `Hpost` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `gas_origin_ptr_path (DF Hpost,lo,explicit,ctx,func,PG) (u,Gf,tf) [] (OK z,Gd,td)` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ (u,Gf,tf) [] (OK z,Gd,td)`
      (qspecl_then [`DF Hpost`,`explicit`] ACCEPT_TAC)) >>
  qpat_assum `abi_valid_allocated_post _ _ _ _ _ _ _ hs de _ _ _ _ u z`
    (mp_then Any mp_tac extcall_decoded_post_mods) >>
  map_every (fn pat => disch_then (fn th => qpat_assum pat (mp_then Any mp_tac th)))
    [`compile_abi_decode_to_buf (Var q) _ _ (Var source) _ _ hs = _`,
     `evaluate_abi_decode_return _ ret_type returnData = INL value`,
     `abi_malformed_entry Hpost ctx func cenv cx ee hs _ _ _ _ _ _ _ _ _ _ _ _ _ u`,
     `gas_origin_ptr_path (DF Hpost,lo,explicit,ctx,func,PG) (u,Gf,tf) [] (OK z,Gd,td)`,
     `ghost_inv_at_mods (DF Hpost) lo d cenv cx ee Gf tf u`,
     `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf`, `sr.cs_next_id < sb.cs_next_id`,
     `evaluate_type (get_tenv cx) ret_type = SOME actual_tv`, `ann = ret_type`] >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE asm_rewrite_tac[]))) >>
  (* These binders occur only in the result: select the source call at this cut. *)
  disch_then (qspecl_then [`is_static'`,`skip`,`opts`,`fname`,`dflt`,`args`,`arg_types`]
    (map_every assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) [post_value_type_def])) >>
  qpat_assum `ee with gas_obs := [] = ee` SUBST1_TAC >>
  qpat_assum `vv = LocatedValue ann (mk_ptr (Var q) LocMemory)` SUBST1_TAC >>
  `vv_location (LocatedValue ann (mk_ptr (Var q) LocMemory)) = SOME LocMemory` by
    simp_tac (srw_ss()) [vv_location_def,contextTheory.mk_ptr_def] >>
  `(mk_ptr (Var q) LocMemory).ptr_operand = Var q` by simp_tac (srw_ss()) [contextTheory.mk_ptr_def] >>
  qpat_x_assum `ann = ret_type` SUBST_ALL_TAC >>
  qpat_assum `vv_location (LocatedValue _ _) = SOME LocMemory`
    (fn loc => qpat_assum `(mk_ptr (Var q) LocMemory).ptr_operand = Var q`
      (fn op_eq => simp_tac (srw_ss()) [loc,op_eq,post_value_type_def])) >>
  qpat_x_assum `zf = z \/ _` (DISJ_CASES_THEN2 SUBST_ALL_TAC strip_assume_tac)
  >- asm_rewrite_tac[] >>
  qpat_x_assum `zf = jump_to _ z` SUBST_ALL_TAC >>
  rename1 `jump_to xl z` >>
  `alloca_history func (jump_to xl z)` by
    (irule alloca_history_jump >> simp_tac (srw_ss()) [jump_to_def] >>
     qexists `z` >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[return_decoded_jump_post,return_decoded_jump_ghost,return_decoded_jump_value] >>
  simp_tac (srw_ss()) [jump_to_def] >> first_assum ACCEPT_TAC
QED

Finalise extcall_return_decode_mods
