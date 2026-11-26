(* The linked continuation after an external request has returned. *)
Theory bodyExtReturnMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv exprBodyPreProps exprSimExtCallCase
  fragGasOriginPtr bodyPtrDefs exprSimMemDefs loweringPosts exprLowering
  compileEnv context vyperInterpreter vyperAST vyperState vyperABI
  venomState valueEncoding valueEncodingDefs vyperTypeSystem
  bodyExtReturnDecodeMods bodyExtReturnDefaultMods bodyFullExtCallReturnSource
  createSizeExit
Libs monadsyntax

Theorem extcall_return_void_mods[local]:
  expr_body_pre_mods mods cenv cx env
    (Call ann (ExtCall stat skip (fname,arg_types,NoneT) opts) args dflt) es /\
  extcall_returned st0 ctx func cenv cx NoneT es sa s0 sr addr buf cap target
    has_default default_op default_ty default_opt bs ee t /\
  immutable_frame_mods func cenv cx ee t /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t) ==>
  (!tail. (case (if bs = [] then default_opt else NONE) of
     SOME v => do accounts' <- get_accounts;
                  check (skip \/ ext_call_has_code target accounts')
                    "ExtCall target has no code";
                  return (Value v) od
   | NONE => do v <- lift_sum_runtime
                      (evaluate_abi_decode_return (get_tenv cx) NoneT bs);
                return (Value v) od) (ee with gas_obs := tail) =
     (INL (Value NoneV),ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK t,G,tn) /\
    vv_post_mods H ctx func cenv cx
      (Call ann (ExtCall stat skip (fname,arg_types,NoneT) opts) args dflt)
      es sa sr s0 ee (Value NoneV) (StackValue NoneT (Lit 0w)) t /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t)
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  `ann = NoneT` by fs[Once well_typed_expr_def] >>
  qpat_x_assum `ann = NoneT` SUBST_ALL_TAC >>
  fs[extcall_returned_def,extcall_default_ready_def] >>
  `default_opt = NONE` by (Cases_on `default_opt` >> fs[]) >>
  conj_tac
  >- simp[evaluate_abi_decode_return_def,needs_external_call_wrap_def,
          evaluate_abi_decode_returndata_def,vyper_abi_size_bound_def,
          vyper_valid_enc_returndata_def,decode_abi_value_def,vyper_is_dynamic_def,
          vyper_decode_valid_enc_def,bind_def,return_def,lift_sum_runtime_def] >>
  rpt gen_tac >> strip_tac >>
  simp[gas_origin_ptr_path_rules,vv_post_mods_def,vv_holds_mods_def,
       vv_place_ptr_mods_def,vv_place_ptr_def,vv_holds_def,vv_at_def,
       post_value_type_def,expr_type_def] >>
  fs[wb_frame_def, read_result_def, return_def, expr_val_rel_def,
     expr_val_at_def, eval_operand_def, is_word_type_def, val_in_memory_def,
     val_footprint_def, type_memory_size_def, val_wf_def] >>
  first_assum ACCEPT_TAC
QED

Theorem extcall_return_full_mods:
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
    immutable_frame_mods func cenv cx ee t /\
    (IS_SOME default_opt /\ ~is_word_type default_ty ==>
      ?w aid tv. eval_operand default_op t = SOME w /\
        evaluate_type (get_tenv cx) default_ty = SOME tv /\
        FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\ aid < sr.cs_next_id) /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t) /\
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
            ~is_word_type (post_value_type cenv (Call ann (ExtCall is_static skip
               (fname,arg_types,ret_type) opts) args dflt)) ==>
            ptr_buf_ok cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts) args dflt)
              op G' t') /\
         (!t'' p. vv = LocatedValue t'' p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts) args dflt)
              p.ptr_operand G' t') /\
         vv_own cenv cx
           (post_value_type cenv (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts) args dflt))
           sa sb (ee with gas_obs := []) tv vv t' /\
         ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn') \/
         (exit_result r /\ create_size_exit_ok ctx res r /\ expr_exit res r)))
Proof
  disch_then (mk_asm "valid") >> disch_then (mk_asm "reject") >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ret_type = NoneT` >- suspend "void" >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
       immutable_frame_mods func cenv cx ee t` by
    (gen_tac >> disch_tac >> simp[] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
       (drule_then ACCEPT_TAC)) >>
  Cases_on `has_default /\ returnData = []`
  >- (simp_tac bool_ss [GSYM RIGHT_EXISTS_AND_THM] >>
      match_mp_tac (GEN_ALL (CONV_RULE (DEPTH_CONV BETA_CONV)
        (REWRITE_RULE[LET_THM] extcall_return_default_mods))) >>
      goal_assum (drule_at (Pat `extcall_returned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      qexistsl_tac [`result_op`,`mods`,`env`] >> asm_rewrite_tac[]) >>
  Cases_on `?H. valid_horizon cx st0 H ee.storage_trace`
  >- suspend "decode" >>
  qpat_assum `~(?H. valid_horizon cx st0 H _)` (mp_tac o CONV_RULE NOT_EXISTS_CONV) >>
  disch_then (fn th => simp_tac bool_ss [th]) >>
  irule extcall_return_source_tail
QED

Resume extcall_return_full_mods[void]:
  `ann = NoneT` by
    (drule expr_body_pre_mods_well_typed >> simp[Once well_typed_expr_def]) >>
  gvs[comp_return_def] >>
  drule_all extcall_return_void_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`INL (Value NoneV)`,`OK t`,`G`,`tn`] >>
  asm_rewrite_tac[] >>
  gen_tac >> disch_tac >>
  qhdtm_assum `extcall_returned` (strip_assume_tac o REWRITE_RULE[extcall_returned_def]) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  simp[vv_location_def, expr_type_def, post_value_type_def,
       is_word_type_def, vv_store_bound_def, ptr_vv_ok_def, ptr_val_ok_def,
       vv_own_def, expr_val_own_def, read_result_def, return_def,
       type_memory_size_def, val_footprint_def] >>
  simp[lowered_value_type_def, ptr_buf_ok_def, ptr_mem_ok_def,
       type_memory_bytes_def, eval_operand_def, ptrDisciplineTheory.op_taint_def,
       exprSimPropsTheory.val_store_size_def, type_memory_size_def,
       val_in_memory_def, val_footprint_def, expr_type_def]
QED

Resume extcall_return_full_mods[decode]:
  asm "valid" (fn th => mp_tac (MATCH_MP extcall_return_decode_mods th)) >>
  disch_then (fn th => asm "reject" (match_mp_tac o MATCH_MP th)) >>
  goal_assum (drule_at (Pat `extcall_returned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`mods`,`env`,`result_op`] >> asm_rewrite_tac[]
QED

Finalise extcall_return_full_mods
