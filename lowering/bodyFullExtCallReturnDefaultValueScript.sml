(* Direct empty-data default return, with one endpoint before the horizon. *)
Theory bodyFullExtCallReturnDefaultValue
Ancestors
  bodyFullPreds bodySimFull gasOutcomeFull exprSimExtCallCase bodyPtrDefs
  bufferAllocationJoint extcallReturnDefaultControlJoint extcallReturnDefaultMemoryJoint
  extcallReturnDefaultTypes extcallReturnDefaultOwnership
  extcallReturnDefaultIntervals extcallReturnDefaultStore
  ptrDiscipline gasShadow exprSimHypsDefs exprLowering
  vyperInterpreter vyperAST list emitHelper extcallReturnDefaultRouting compileEnv
  exprLoweringProps codegenRel exprSimAlloc loweringHalt fragExec
  loweringStateRelDefs extcallReturnInterface exprSafeOperand venomState
  bodyPtrBopRepresentationFrame extcallReturnDefaultWordJoint
  bodyFullUnwrapSlotPost bodyFullShared

Theorem return_default_alloc_state[local]:
  compile_alloc_buffer n a = (buf,b) /\
  run_inst_seq (emitted_insts a b) s = OK r /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv a /\ n < dimword (:256) /\
  stmt_state_rel H ctx func cenv cx ee s ==>
  stmt_state_rel H ctx func cenv cx ee r
Proof
  metis_tac[return_default_alloc_resources]
QED

Theorem extcall_default_value_posts[local]:
  evaluate_type (get_tenv cx) ty = SOME rtv /\
  value_has_type rtv dv /\ val_wf rtv dv /\
  type_memory_bytes cenv ty = type_memory_size rtv /\
  stmt_state_rel H ctx func cenv cx ee z /\
  storage_well_formed_on cx ee (FST H) /\
  wb_frame cenv es ee sa s0 z /\
  op = Var dst /\ eval_operand op z = SOME dw /\
  ptr_covers G tn dst z (type_memory_size rtv) /\
  w2n dw + type_memory_size rtv <= z.vs_alloca_next /\
  FLOOKUP z.vs_allocas aid = SOME (b,sz) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  b <= w2n dw /\ w2n dw + type_memory_size rtv <= b+sz /\
  (!name lb lsz. local_region cenv ee.scopes z name lb lsz ==>
     b+sz <= lb \/ lb+lsz <= b) /\
  (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
     val_in_memory rtv dv (w2n dw) mem) ==>
  vv_post H ctx func cenv cx
    (Call ty (ExtCall stat skip (fname,arg_types,ty) opts) args dflt)
    es sa sb s0 ee (Value dv)
    (LocatedValue ty (mk_ptr op LocMemory)) z /\
  vv_store_bound cx ty ty ee (Value dv)
    (LocatedValue ty (mk_ptr op LocMemory)) z /\
  ptr_vv_ok cx ty (Value dv)
    (LocatedValue ty (mk_ptr op LocMemory)) ee G tn z /\
  ptr_buf_ok cenv
    (Call ty (ExtCall stat skip (fname,arg_types,ty) opts) args dflt) op G z
Proof
  strip_tac >>
  `val_in_memory rtv dv (w2n dw) z.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `val_store_size rtv dv <= type_memory_size rtv /\
   val_footprint rtv dv <= type_memory_size rtv` by
    metis_tac[exprSimPropsTheory.val_store_size_le,
      exprSimPropsTheory.val_footprint_le] >>
  `w2n dw + val_store_size rtv dv <= z.vs_alloca_next /\
   w2n dw + val_footprint rtv dv <= b+sz` by decide_tac >>
  `is_word_type ty ==> mem_word_at (w2n dw) z.vs_memory = typed_val_to_w256 rtv dv` by
    metis_tac[exprSimPropsTheory.val_in_memory_word_type] >>
  gvs[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def,
    loweringPostsTheory.vv_at_def, loweringPostsTheory.post_value_type_def,
    exprSimMemDefsTheory.vv_store_bound_def, ptr_vv_ok_def, ptr_mem_ok_def,
    ptr_buf_ok_def, ptr_covers_def, expr_type_def, lowered_value_type_def,
    contextTheory.mk_ptr_def, eval_operand_def,
    vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  rpt conj_tac >> rpt strip_tac >>
  fs[loweringPostsTheory.wb_frame_def] >| [
    disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >>
    ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
    conj_tac >- decide_tac >> first_assum ACCEPT_TAC,
    metis_tac[]
  ]
QED

Theorem extcall_return_full_default_value:
  !DF lo d explicit ctx PG func cenv cx env es ann is_static skip fname
   arg_types ret_type opts args dflt st0 sa sb s0 G0 tn0 sr result_op vv
   addr_op buf_op cap target has_default default_op default_ty default_opt
   returnData ee t G tn.
    ret_type <> NoneT /\ has_default /\ returnData = [] /\
    expr_body_pre cenv cx env
      (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
         args dflt) es /\
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
    MEM func ctx.ctx_functions /\ ~ctx_has_dalloca ctx /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr_op buf_op
      cap target has_default default_op default_ty default_opt returnData ee t /\
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
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
                 args dflt) op G' t') /\
         (!t'' p. vv = LocatedValue t'' p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
                 args dflt) p.ptr_operand G' t') /\
         ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn') \/
         (exit_result r /\ expr_exit res r)))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[comp_bind_def] >> pairarg_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ sr = (buf,ar)` >>
  drule return_default_path_intervals >> strip_tac >>
  fs[extcall_returned_def] >>
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
  pop_assum (qx_choose_then `H0` assume_tac) >>
  `stmt_state_rel H0 ctx func cenv cx ee t /\
   ghost_inv_at (DF H0) lo d cenv cx ee G tn t` by metis_tac[] >>
  `cs_extends sr ar /\ cs_extends ar sb` by
    (metis_tac[ci_mono_compile_alloc_buffer,
      ci_mono_compile_default_return_path, ci_mono_def, pairTheory.SND]) >>
  `sr.cs_next_id < sb.cs_next_id` by
    (`ar.cs_next_id = sr.cs_next_id + 1` by
       (qpat_assum `compile_alloc_buffer _ sr = _`
          (mp_tac o AP_TERM ``\p:buffer # compile_state. (SND p).cs_next_id``) >>
        simp[NoAsms, contextTheory.compile_alloc_buffer_def, emit_op_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, fresh_var_def,
          fresh_id_def, emit_def]) >>
     `ar.cs_next_id <= sb.cs_next_id` by
       metis_tac[ci_mono_compile_default_return_path, ci_mono_def, pairTheory.SND] >>
     decide_tac) >>
  `fn_has_code sr ar func /\ fn_has_code ar sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  drule_all return_default_intervals_code >> strip_tac >>
  `type_memory_bytes cenv ret_type = type_memory_size rtv` by
    metis_tac[extcall_return_memory_size] >>
  `type_memory_size rtv + 64 < dimword (:256)` by
    metis_tac[extcall_return_store_bound] >>
  `type_memory_bytes cenv ret_type < dimword (:256)` by decide_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sr ar) t = OK allocated` >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `LENGTH t.vs_returndata < dimword (:256)` by simp[] >>
  drule_all return_default_prefix_joint >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`] strip_assume_tac) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sr x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sr x)` by
    (fs[not_fresh_at_def] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `DRESTRICT (DRESTRICT AG _) _` >>
  qmatch_asmsub_abbrev_tac `tm = atn with t_var := _` >>
  `ar.cs_next_var <= ar.cs_next_var /\ ar.cs_next_var <= a1.cs_next_var` by
    (qspecl_then [`RETURNDATASIZE`, `[]`, `ar`] mp_tac ci_mono_emit_op >>
     simp[ci_mono_def, cs_extends_def]) >>
  `ds.cs_current_bb = dl /\ ds.cs_current_insts = [] /\
   ar.cs_next_var <= ds.cs_next_var` by
    (gvs[new_block_def, fresh_label_def, emit_inst_def, emit_op_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
      fresh_id_def, emit_def] >> decide_tac) >>
  `local_ptrs_reserved cenv sr` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `sr.cs_next_var <= ar.cs_next_var` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_def, pairTheory.SND] >>
  `sr.cs_next_var <= ds.cs_next_var /\ sa.cs_next_var <= ds.cs_next_var` by
    decide_tac >>
  `local_ptrs_reserved cenv ds` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sr` >> simp[]) >>
  `safe_operand ds default_op` by
    metis_tac[exprSafeOperandTheory.safe_operand_mono] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ds x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ds x)` by
    (conj_tac >> rpt strip_tac >>
     `not_fresh_at sr x` by metis_tac[] >>
     metis_tac[stmtFragPtrTheory.not_fresh_at_mono]) >>
  `AG = step_prov PG G (mk_inst sr.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv ret_type))]
      [STRING #"%" (toString sr.cs_next_var)]) allocated /\
   atn = step_taint (mk_inst sr.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv ret_type))]
      [STRING #"%" (toString sr.cs_next_var)]) t allocated tn` by
    simp[Abbr `AG`, Abbr `atn`] >>
  qpat_assum `t.vs_returndata = []` (fn th =>
    qpat_x_assum `u = _` (assume_tac o REWRITE_RULE [th])) >>
  drule_then (drule_then
    (drule_at_then (Pat `stmt_state_rel _ _ _ _ _ _ _`)
      (drule_at_then (Pat `_ = jump_to _ _`)
        (drule_at_then (Pat `_ = step_prov _ _ _ _`)
          (drule_at_then (Pat `_ = step_taint _ _ _ _`)
            (drule_at_then (Pat `_ = DRESTRICT _ _`)
              (drule_at (Pat `_ = _ with t_var := _`))))))))
    return_default_prefix_store_resources >>
  disch_then (qspec_then `ds` mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then strip_assume_tac >>
  `!op. safe_operand sr op ==> eval_operand op u = eval_operand op t /\
      op_taint tm op = op_taint tn op` by
    (Cases >> simp[safe_operand_def, eval_operand_def, op_taint_def] >>
     metis_tac[]) >>
  `eval_operand default_op u = SOME w /\ eval_operand addr_op u = SOME aw /\
   op_taint tm default_op = {} /\ op_taint tm addr_op = {}` by metis_tac[] >>
  `expr_val_rel cx default_ty dv default_op u` by
    (qpat_x_assum `expr_val_rel cx default_ty dv default_op t` mp_tac >>
     simp[loweringPostsTheory.expr_val_rel_def]) >>
  `~is_word_type default_ty ==> ptr_mem_ok cx default_ty dv default_op Gf tm u` by
    (strip_tac >>
     `ptr_mem_ok cx default_ty dv default_op G tn t` by metis_tac[] >>
     irule bop_ptr_mem_ok_frame >>
     qexistsl_tac [`G`, `t`, `tn`, `tv`] >>
     conj_tac >- (rpt strip_tac >>
       `not_fresh_at sr x` by metis_tac[safe_operand_def] >> metis_tac[]) >>
     conj_tac >- (qx_gen_tac `sw` >> strip_tac >>
       `sw = w` by metis_tac[optionTheory.SOME_11] >>
       qpat_x_assum `sw = w` SUBST_ALL_TAC >>
       conj_tac >- metis_tac[] >> rpt strip_tac >>
       `w2n w + val_footprint tv dv <= t.vs_alloca_next` by metis_tac[] >>
       `i < t.vs_alloca_next` by decide_tac >> metis_tac[]) >>
     rpt conj_tac >> metis_tac[]) >>
  `ghost_inv_at (DF H0) lo d cenv cx ee Gf tm u /\
   ptr_covers Gf tm (STRING #"%" (toString sr.cs_next_var)) u
      (type_memory_bytes cenv ret_type) /\
   ghost_kept_at lo cenv ee sr G tn t Gf tm` by metis_tac[] >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    metis_tac[ghost_inv_at_def] >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) ==>
     off + sz <= t.vs_alloca_next` by
    (rpt strip_tac >>
     `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by
       (qpat_assum `wb_frame cenv es ee sa s0 t`
          (mp_tac o CONJUNCT1 o CONJUNCT2 o
           REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
        disch_then (qspecl_then [`aid`, `(off,sz)`] mp_tac) >> simp[]) >>
     qpat_assum `stmt_state_rel H0 ctx func cenv cx ee t`
       (mp_tac o CONJUNCT2 o REWRITE_RULE [venomMemDefsTheory.alloca_inv_def] o
        CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [stmt_state_rel_def]) >>
     pure_rewrite_tac[venomMemDefsTheory.alloca_next_valid_def] >>
     disch_then (qspecl_then [`aid`, `off`, `sz`] mp_tac) >> simp[]) >>
  `!name b sz. local_region cenv es.scopes s0 name b sz ==>
     b + sz <= t.vs_alloca_next` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes t name b sz` by
       (irule exprSimPropsTheory.local_region_frame_fwd >>
        qexistsl_tac [`s0`, `sa`, `es.scopes`] >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        qpat_assum `wb_frame cenv es ee sa s0 t`
          (ACCEPT_TAC o CONJUNCT1 o
           REWRITE_RULE [loweringPostsTheory.wb_frame_def])) >>
     `local_ptrs_rel func cenv ee.scopes t` by
       (qpat_assum `stmt_state_rel H0 ctx func cenv cx ee t` mp_tac >>
        simp[NoAsms, stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]) >>
     qpat_assum `local_region cenv ee.scopes t name b sz` mp_tac >>
     simp[NoAsms, local_region_def] >> strip_tac >>
     drule_all allocaFootprintTheory.local_ptr_below_frontier >>
     strip_tac >> metis_tac[optionTheory.SOME_11]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tm` by
    (mp_tac (Q.INST
       [`lo` |-> `lo`, `cenv` |-> `cenv`, `es` |-> `es`, `sa` |-> `sa`,
        `Gi` |-> `G0`, `ti` |-> `tn0`, `s0` |-> `s0`,
        `G` |-> `G`, `tn` |-> `tn`, `H` |-> `Gf`, `tf` |-> `tm`]
       (SPEC_ALL (INST_TYPE [alpha |-> ``:num # num``]
         bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_kept_at))) >>
     impl_tac >-
       (conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >-
          (rpt strip_tac >>
           `not_fresh_at sr x` by
             metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >> metis_tac[]) >>
        conj_tac >-
          (rpt strip_tac >>
           `i < t.vs_alloca_next` by metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS] >>
           metis_tac[]) >>
        conj_tac >-
          (rpt strip_tac >>
           `i < t.vs_alloca_next` by metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS] >>
           metis_tac[]) >>
        rpt strip_tac >> `i < t.vs_alloca_next` by decide_tac >> metis_tac[]) >>
     simp[NoAsms]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee u` by
    (gen_tac >> strip_tac >>
     `stmt_state_rel H ctx func cenv cx ee t` by metis_tac[] >>
     `stmt_state_rel H ctx func cenv cx ee allocated` by
       (irule return_default_alloc_state >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qexistsl_tac [`sr`, `ar`, `buf`, `type_memory_bytes cenv ret_type`, `t`] >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     irule extcallReturnDefaultResourcesTheory.return_default_shell_state >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
     qexists_tac `ar` >>
     qexistsl_tac [`LENGTH a2.cs_current_insts`, `dl`, `ar.cs_next_var`, `a1.cs_next_var`, `0w`, `1w`] >>
     simp[venomStateTheory.update_var_def] >>
     irule local_ptrs_reserved_next_var >>
     qexists_tac `sr` >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_x_assum `compile_alloc_buffer _ sr = _` mp_tac >>
     mp_tac (Q.SPECL [`type_memory_bytes cenv ret_type`, `sr`]
       (REWRITE_RULE [ci_mono_def] ci_mono_compile_alloc_buffer)) >>
     simp[] >> metis_tac[pairTheory.SND]) >>
  Cases_on `is_word_type ret_type`
  >- suspend "word"
  >> suspend "memory"
QED
Resume extcall_return_full_default_value[word]:
  `type_memory_size rtv = 32 /\ type_memory_bytes cenv ret_type = 32` by
    metis_tac[stmtSimReturnTheory.word_type_sizes] >>
  `~is_bytestring_type ret_type` by
    (qpat_x_assum `is_word_type ret_type` mp_tac >>
     map_every qid_spec_tac [`ret_type`] >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases >> simp[is_word_type_def, is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     simp[is_word_type_def, is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     simp[is_word_type_def, is_bytestring_type_def]) >>
  `default_ty = ret_type` by metis_tac[] >>
  `tv = rtv` by metis_tac[optionTheory.SOME_11] >>
  `w = typed_val_to_w256 rtv dv` by
    (qpat_x_assum `expr_val_rel cx default_ty dv default_op u` mp_tac >>
     simp[loweringPostsTheory.expr_val_rel_def] >> metis_tac[]) >>
  `lookup_var (STRING #"%" (toString sr.cs_next_var)) u = SOME w''` by
    metis_tac[eval_operand_def] >>
  `ptr_covers Gf tm (STRING #"%" (toString sr.cs_next_var)) u 32 /\
   w2n w'' + 32 <= u.vs_alloca_next /\ ~u.vs_halted` by metis_tac[] >>
  qpat_assum `buf.buf_operand = Var (STRING #"%" _)` (fn th =>
    qpat_assum `compile_store_memory _ _ _ _ _ _ = _`
      (mp_tac o REWRITE_RULE [th])) >>
  disch_then assume_tac >>
  drule_then
    (drule_at_then (Pat `lookup_var _ _ = SOME _`)
      (drule_at_then (Pat `ptr_covers _ _ _ _ _`)
        (drule_at_then (Pat `eval_operand _ _ = SOME _`)
          (drule_at_then (Pat `evaluate_type _ ret_type = SOME _`)
            (drule_at_then (Pat `value_has_type rtv dv`)
              (drule_at_then (Pat `fn_has_code ds de func`) mp_tac))))))
    (INST_TYPE [alpha |-> ``:256``] return_default_word_store_joint) >>
  disch_then (qspecl_then [`lo`, `explicit`, `ctx`, `PG`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then strip_assume_tac >>
  qpat_x_assum `!H ce cx ee sa. _ ==> stmt_state_rel H ctx func ce cx ee u'`
    (mk_asm "word_state") >>
  `allocas_from lo u' /\ eval_operand addr_op u' = SOME aw /\
   op_taint tm' addr_op = {}` by metis_tac[allocas_from_def] >>
  `wb_frame cenv es ee sa s0 u` by metis_tac[] >>
  `not_local_ptr cenv ee.scopes (STRING #"%" (toString sr.cs_next_var))` by
    (irule exprSimOperandsTheory.fresh_not_local_ptr >>
     qexists_tac `sr` >> simp[not_fresh_at_def]) >>
  `abi_malformed_destination func cenv ee.scopes sr.cs_next_id (w2n w'') 32 u` by
    (simp[abiMalformedRecursiveInterfaceTheory.abi_malformed_destination_def] >>
     qexists_tac `mk_inst sr.cs_next_id ALLOCA
       [Lit (n2w (type_memory_bytes cenv ret_type))]
       [STRING #"%" (toString sr.cs_next_var)]` >>
     simp[venomInstTheory.mk_inst_def] >> metis_tac[]) >>
  drule_at_then (Pat `abi_malformed_destination _ _ _ _ _ _ _`)
    (drule_at_then (Pat `stmt_state_rel _ _ _ _ _ _ _`)
      (drule_at_then (Pat `wb_frame _ _ _ _ _ _`) mp_tac))
    return_default_destination_separation >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then strip_assume_tac >>
  drule_then
    (drule_at_then (Pat `emit_inst JMP _ _ _ = _`)
      (drule_at_then (Pat `eval_operand _ _ = SOME _`)
        (drule_at_then (Pat `op_taint _ _ = {}`)
          (drule_at_then (Pat `fn_has_code _ _ _`)
            (drule_at_then (Pat `allocas_from _ _`)
              (drule_at_then (Pat `~ctx_has_dalloca _`) mp_tac))))))
    return_default_suffix_path_joint >>
  disch_then (qspecl_then [`explicit`, `PG`, `Gf`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then strip_assume_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee u'` by
    (rpt strip_tac >>
     asm "word_state" irule >>
     rpt conj_tac >> metis_tac[regions_disjoint_def]) >>
  `wb_frame cenv es ee sa s0 u'` by
    (qpat_x_assum `!ce es ee sa s0. _ ==> wb_frame ce es ee sa s0 u'` irule >>
     rpt conj_tac >> metis_tac[regions_disjoint_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     ghost_inv_at (DF H) lo d cenv cx ee Gf tm' u'` by
    (rpt strip_tac >>
     qpat_x_assum `!D d ce cx ee sa. _ ==> ghost_inv_at D lo d ce cx ee Gf tm' u'` irule >>
     conj_tac >-
       (qpat_x_assum `!name b sz. local_region cenv ee.scopes u name b sz ==> regions_disjoint _ _ _ _` mp_tac >>
        simp[regions_disjoint_def]) >>
     conj_tac >-
       metis_tac[allocas_from_def] >>
     conj_tac >- (qexists_tac `sr` >> metis_tac[]) >>
     conj_tac >-
       (qpat_assum `stmt_state_rel H0 ctx func cenv cx ee u` mp_tac >>
        pure_rewrite_tac[stmt_state_rel_def,
          loweringStateRelDefsTheory.state_rel_def] >>
        strip_tac >> first_assum ACCEPT_TAC) >>
     metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (t,G,tn) [] (r,G1,tn1)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (t,G,tn) _ _`
       (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (u,Gf,tm) _ _`
       (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (u',Gf,tm') _ _`
       (qspec_then `D` mp_tac) >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,
       listTheory.APPEND_NIL]) >>
  Cases_on `skip` >- suspend "word_skip" >>
  `stmt_state_rel H0 ctx func cenv cx ee u'` by metis_tac[] >>
  `((n2w (LENGTH (lookup_account (w2w aw) u'.vs_accounts).code):bytes32) <> 0w
     <=> ext_call_has_code target ee.accounts)` by
    metis_tac[extCallCodeCheckTheory.extcall_precheck_code_word] >>
  qpat_x_assum `~F ==> ?s. _` mp_tac >>
  pure_rewrite_tac [NOT_CLAUSES, IMP_CLAUSES] >> strip_tac >>
  Cases_on `ext_call_has_code target ee.accounts`
  >- suspend "word_code" >>
  qexistsl_tac [`r`, `G1`, `tn1`] >>
  gen_tac >> disch_tac >> conj_tac >- metis_tac[] >>
  disj2_tac >>
  `r = Abort Revert_abort (revert_state (set_returndata [] u''))` by metis_tac[] >>
  simp[exit_result_def, exprSimDefsTheory.expr_exit_def]
QED
Resume extcall_return_full_default_value[word_skip]:
  rename1 `expr_body_pre cenv cx env
    (Call ann (ExtCall stat T (fname,arg_types,ret_type) opts) args dflt) es` >>
  `ann = ret_type` by metis_tac[extcall_return_type_bounds] >>
  `ee with gas_obs := [] = ee` by
    (simp[NoAsms, vyperStateTheory.evaluation_state_component_equality] >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `ann = ret_type` (fn th => rewrite_tac[th]) >>
  qpat_assum `ee with gas_obs := [] = ee` (fn th => rewrite_tac[th]) >>
  `r = OK (jump_to xl u') /\ G1 = Gf /\ tn1 = tm'` by metis_tac[] >>
  qexistsl_tac [`r`, `G1`, `tn1`] >>
  gen_tac >> disch_tac >> conj_tac >- metis_tac[] >>
  `!x. lookup_var x (jump_to xl u') = lookup_var x u` by
    (gen_tac >>
     qpat_assum `!op. eval_operand op u' = eval_operand op u`
       (qspec_then `Var x` mp_tac) >>
     simp[NoAsms, eval_operand_def, lookup_var_def, jump_to_def]) >>
  `!name b sz. local_region cenv ee.scopes (jump_to xl u') name b sz <=>
     local_region cenv ee.scopes u name b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >> metis_tac[]) >>
  `eval_operand buf.buf_operand (jump_to xl u') = SOME w''` by
    (qpat_assum `buf.buf_operand = Var (STRING #"%" _)`
       (fn th => rewrite_tac[th, eval_operand_def]) >> metis_tac[]) >>
  `ptr_covers Gf tm' (STRING #"%" (toString sr.cs_next_var))
     (jump_to xl u') 32` by
    (qpat_assum `ptr_covers Gf tm _ u 32` mp_tac >>
     qpat_assum `tm' = tm with t_mem := _` (fn th => rewrite_tac[th]) >>
     pure_rewrite_tac[ptr_covers_def] >>
     qpat_assum `!x. lookup_var x (jump_to xl u') = lookup_var x u`
       (fn th => simp[NoAsms, th, op_taint_def])) >>
  `stmt_state_rel H ctx func cenv cx ee (jump_to xl u')` by
    (pure_rewrite_tac[stmt_state_rel_jump_to] >> metis_tac[]) >>
  `wb_frame cenv es ee sa s0 (jump_to xl u')` by
    (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
     goal_assum (drule_at (Pat `wb_frame _ _ _ _ _ u'`)) >>
     qexists_tac `sa` >> simp[NoAsms, jump_to_def, lookup_var_def]) >>
  mp_tac (Q.INST
    [`ty` |-> `ret_type`, `skip` |-> `T`, `G` |-> `Gf`, `tn` |-> `tm'`,
     `z` |-> `jump_to xl u'`, `op` |-> `buf.buf_operand`,
     `dst` |-> `STRING #"%" (toString sr.cs_next_var)`, `dw` |-> `w''`,
     `aid` |-> `sr.cs_next_id`, `b` |-> `w2n (w'' : bytes32)`, `sz` |-> `32`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] extcall_default_value_posts))) >>
  impl_tac >- (rpt conj_tac
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- metis_tac[]
    >- first_assum ACCEPT_TAC
    >- metis_tac[]
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- metis_tac[]
    >- (simp[NoAsms, jump_to_def] >>
        qpat_assum `u'.vs_alloca_next = u.vs_alloca_next` SUBST1_TAC >>
        qpat_assum `type_memory_size rtv = 32` SUBST1_TAC >>
        qpat_assum `w2n w'' + 32 <= u.vs_alloca_next` mp_tac >> decide_tac)
    >- (simp[NoAsms, jump_to_def] >>
        qpat_assum `u'.vs_allocas = u.vs_allocas` SUBST1_TAC >>
        qpat_assum `FLOOKUP u.vs_allocas sr.cs_next_id = SOME _` mp_tac >>
        qpat_assum `type_memory_bytes cenv ret_type = 32`
          (fn th => simp[NoAsms, th]))
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- simp[NoAsms]
    >- decide_tac
    >- (rpt strip_tac >>
        `regions_disjoint (w2n w'') 32 lb lsz` by metis_tac[] >>
        qpat_assum `regions_disjoint (w2n w'') 32 lb lsz` mp_tac >>
        simp[NoAsms, regions_disjoint_def])
    >- (simp[NoAsms, jump_to_def] >> metis_tac[])) >>
  strip_tac >>
  qpat_assum `G1 = Gf` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `tn1 = tm'` (fn th => pure_rewrite_tac[th]) >>
  qexists_tac `jump_to xl u'` >>
  conj_tac >- metis_tac[] >>
  conj_tac >- suspend "word_skip_vv" >>
  conj_tac >- suspend "word_skip_bound" >>
  conj_tac >- suspend "word_skip_bb" >>
  conj_tac >- suspend "word_skip_idx" >>
  conj_tac >- suspend "word_skip_history" >>
  conj_tac >- suspend "word_skip_next" >>
  conj_tac >- suspend "word_skip_ghost" >>
  conj_tac >- suspend "word_skip_ptr" >>
  conj_tac >- suspend "word_skip_code_loc" >>
  conj_tac >- suspend "word_skip_buf" >>
  suspend "word_skip_kept"
QED
Resume extcall_return_full_default_value[word_skip_ghost]:
  pure_rewrite_tac[bodyFullSharedTheory.ghost_inv_at_jump] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at _ _ _ _ _ _ _ _ u'`
    (qspec_then `H` mp_tac) >> simp[]
QED
Resume extcall_return_full_default_value[word_skip_bb]:
  qpat_assum `new_block xl cj = _` mp_tac >>
  simp[NoAsms, new_block_def, comp_bind_def, comp_return_def, jump_to_def] >>
  strip_tac >> pop_assum (SUBST1_TAC o SYM) >> simp[NoAsms]
QED
Resume extcall_return_full_default_value[word_skip_idx]:
  qpat_assum `new_block xl cj = _` mp_tac >>
  simp[NoAsms, new_block_def, comp_bind_def, comp_return_def, jump_to_def] >>
  strip_tac >> pop_assum (SUBST1_TAC o SYM) >> simp[NoAsms]
QED
Resume extcall_return_full_default_value[word_skip_next]:
  pure_rewrite_tac[jump_to_def] >> simp[NoAsms] >>
  qpat_assum `u'.vs_alloca_next = u.vs_alloca_next` SUBST1_TAC >>
  irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `t.vs_alloca_next` >>
  conj_tac >> first_assum ACCEPT_TAC
QED
Resume extcall_return_full_default_value[word_skip_code_loc]:
  simp[NoAsms, contextTheory.vv_location_def, contextTheory.mk_ptr_def]
QED
Resume extcall_return_full_default_value[word_skip_vv]:
  first_assum ACCEPT_TAC
QED
Resume extcall_return_full_default_value[word_skip_bound]:
  pure_rewrite_tac[expr_type_def, lowered_value_type_def] >> first_assum ACCEPT_TAC
QED
Resume extcall_return_full_default_value[word_skip_history]:
  irule allocaHistoryTheory.alloca_history_jump >>
  simp[NoAsms, jump_to_def] >> qexists_tac `u` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `alloca_history func t /\ _ ==> alloca_history func u` irule >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume extcall_return_full_default_value[word_skip_ptr]:
  pure_rewrite_tac[loweringPostsTheory.post_value_type_def, expr_type_def] >>
  first_assum ACCEPT_TAC
QED
Resume extcall_return_full_default_value[word_skip_buf]:
  simp[NoAsms, contextTheory.mk_ptr_def] >> rpt strip_tac >> first_assum ACCEPT_TAC
QED
Resume extcall_return_full_default_value[word_skip_kept]:
  qpat_x_assum `!lo ce es sa G0 tn0 s0. _ ==> ghost_kept_at _ _ _ _ _ _ _ Gf tm'` irule >>
  first_assum ACCEPT_TAC
QED
Resume extcall_return_full_default_value[word_code]:
  rename1 `expr_body_pre cenv cx env
    (Call ann (ExtCall stat F (fname,arg_types,ret_type) opts) args dflt) es` >>
  `ann = ret_type` by metis_tac[extcall_return_type_bounds] >>
  `ee with gas_obs := [] = ee` by
    (simp[NoAsms, vyperStateTheory.evaluation_state_component_equality] >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `ann = ret_type` (fn th => rewrite_tac[th]) >>
  qpat_assum `ee with gas_obs := [] = ee` (fn th => rewrite_tac[th]) >>
  qpat_assum `ext_call_has_code target ee.accounts` (fn th => rewrite_tac[th]) >>
  `r = OK (jump_to xl u'')` by metis_tac[COND_CLAUSES] >>
  `ci_mono ds de` by
    metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `ds.cs_next_var <= de.cs_next_var` by
    (qpat_assum `ci_mono ds de` mp_tac >> simp[NoAsms, ci_mono_def]) >>
  mp_tac (Q.INST
    [`sa` |-> `ds`, `n` |-> `de.cs_next_var`,
     `u` |-> `jump_to xl u''`, `lbl` |-> `xl`, `s` |-> `u'`,
     `w` |-> `(n2w (LENGTH (lookup_account (w2w (aw:bytes32)) u'.vs_accounts).code):bytes32)`,
     `k` |-> `LENGTH de.cs_current_insts + 1`,
     `G` |-> `Gf`, `tn` |-> `tm'`, `G1` |-> `G1`, `tn1` |-> `tn1`,
     `ctx` |-> `ctx`, `func` |-> `func`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] return_default_suffix_joint_frame))) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    qpat_assum `u'' = _` (fn th => simp[NoAsms, th])) >>
  strip_tac >>
  qpat_x_assum `!H ce cx ee. _ ==> stmt_state_rel H ctx func ce cx ee _`
    (mk_asm "code_state") >>
  qpat_x_assum `!D lo d ce cx ee. _ ==> ghost_inv_at D lo d ce cx ee _ _ _`
    (mk_asm "code_ghost") >>
  qpat_x_assum `!ce es ee sa0 s0. _ ==> wb_frame ce es ee sa0 s0 (jump_to _ _)`
    (mk_asm "code_frame") >>
  qpat_x_assum `!lo ce es sa0 G0 tn0 s0. _ /\ _ ==> ghost_kept_at lo ce es sa0 G0 tn0 s0 _ _`
    (mk_asm "code_kept") >>
  `u''.vs_memory = u'.vs_memory /\ u''.vs_allocas = u'.vs_allocas /\
   u''.vs_alloca_next = u'.vs_alloca_next /\ tn1.t_mem = tm'.t_mem` by
    (qpat_assum `u'' = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `tn1 = _ with t_var := _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, update_var_def]) >>
  `!x. lookup_var x u' = lookup_var x u` by
    (gen_tac >>
     qpat_assum `!op. eval_operand op u' = eval_operand op u`
       (qspec_then `Var x` mp_tac) >> simp[NoAsms, eval_operand_def]) >>
  `ptr_covers Gf tm' (STRING #"%" (toString sr.cs_next_var)) u' 32` by
    (qpat_assum `ptr_covers Gf tm _ u 32` mp_tac >>
     qpat_assum `tm' = tm with t_mem := _` (fn th => rewrite_tac[th]) >>
     pure_rewrite_tac[ptr_covers_def] >>
     qpat_assum `!x. lookup_var x u' = lookup_var x u`
       (fn th => simp[NoAsms, th, op_taint_def])) >>
  `lookup_var (STRING #"%" (toString sr.cs_next_var)) (jump_to xl u'') =
       lookup_var (STRING #"%" (toString sr.cs_next_var)) u' /\
   FLOOKUP G1 (STRING #"%" (toString sr.cs_next_var)) =
       FLOOKUP Gf (STRING #"%" (toString sr.cs_next_var)) /\
   op_taint tn1 (Var (STRING #"%" (toString sr.cs_next_var))) =
       op_taint tm' (Var (STRING #"%" (toString sr.cs_next_var)))` by
    (qpat_assum `!x. not_fresh_at ds x ==> lookup_var x (jump_to _ _) = _ /\ _`
       (qspec_then `STRING #"%" (toString sr.cs_next_var)` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[NoAsms]) >>
  `ptr_covers G1 tn1 (STRING #"%" (toString sr.cs_next_var)) (jump_to xl u'') 32` by
    (qpat_assum `ptr_covers Gf tm' _ u' 32` mp_tac >>
     pure_rewrite_tac[ptr_covers_def] >>
     qpat_assum `lookup_var _ (jump_to xl u'') = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `FLOOKUP G1 _ = FLOOKUP Gf _` (fn th => rewrite_tac[th]) >>
     qpat_assum `op_taint tn1 _ = op_taint tm' _` (fn th => simp[NoAsms, th])) >>
  qexistsl_tac [`r`, `G1`, `tn1`] >> gen_tac >> disch_tac >>
  conj_tac >- metis_tac[] >>
  `stmt_state_rel H ctx func cenv cx ee (jump_to xl u'')` by
    (asm "code_state" irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u'`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `wb_frame cenv es ee sa s0 (jump_to xl u'')` by
    (asm "code_frame" irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 (jump_to xl u'')` by
    (asm "code_ghost" irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at _ _ _ _ _ _ _ _ u'`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tm'` by
    (qpat_x_assum `!lo ce es sa G0 tn0 s0. _ ==> ghost_kept_at _ _ _ _ _ _ _ Gf tm'` irule >>
     first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` by
    (asm "code_kept" irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand buf.buf_operand (jump_to xl u'') = SOME w''` by
    (qpat_assum `buf.buf_operand = Var (STRING #"%" _)`
       (fn th => rewrite_tac[th, eval_operand_def]) >>
     qpat_assum `lookup_var _ (jump_to xl u'') = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `!x. lookup_var x u' = lookup_var x u` (fn th => pure_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at ds x ==> lookup_var x (jump_to xl u'') = lookup_var x u` by
    (gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at ds x ==> lookup_var x (jump_to _ _) = _ /\ _`
       (qspec_then `x` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!x. lookup_var x u' = lookup_var x u`
       (fn th => simp[NoAsms, th])) >>
  `!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     not_fresh_at ds p` by
    (qpat_assum `local_ptrs_reserved cenv ds`
       (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [local_ptrs_reserved_def]) >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `!name b sz. local_region cenv ee.scopes (jump_to xl u'') name b sz <=>
     local_region cenv ee.scopes u name b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     map_every qx_gen_tac [`reserved_name`, `reserved_entry`, `reserved_ptr`, `reserved_len`] >>
     strip_tac >>
     `not_fresh_at ds reserved_ptr` by
       (qpat_assum `!name p sz. FLOOKUP cenv.ce_vars name = _ ==> not_fresh_at ds p`
          (qspecl_then [`reserved_name`, `reserved_ptr`, `reserved_len`] mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> simp[NoAsms]) >>
     qpat_assum `!x. not_fresh_at ds x ==> lookup_var x (jump_to xl u'') = lookup_var x u`
       (qspec_then `reserved_ptr` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[NoAsms]) >>
  mp_tac (Q.INST
    [`ty` |-> `ret_type`, `skip` |-> `F`, `G` |-> `G1`, `tn` |-> `tn1`,
     `z` |-> `jump_to xl u''`, `op` |-> `buf.buf_operand`,
     `dst` |-> `STRING #"%" (toString sr.cs_next_var)`, `dw` |-> `w''`,
     `aid` |-> `sr.cs_next_id`, `b` |-> `w2n (w'' : bytes32)`, `sz` |-> `32`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] extcall_default_value_posts))) >>
  impl_tac >- (rpt conj_tac
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- metis_tac[]
    >- first_assum ACCEPT_TAC
    >- metis_tac[]
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- metis_tac[]
    >- (simp[NoAsms, jump_to_def] >>
        qpat_assum `u''.vs_alloca_next = u'.vs_alloca_next` SUBST1_TAC >>
        qpat_assum `u'.vs_alloca_next = u.vs_alloca_next` SUBST1_TAC >>
        qpat_assum `type_memory_size rtv = 32` SUBST1_TAC >>
        qpat_assum `w2n w'' + 32 <= u.vs_alloca_next` mp_tac >> decide_tac)
    >- (simp[NoAsms, jump_to_def] >>
        qpat_assum `u''.vs_allocas = u'.vs_allocas` SUBST1_TAC >>
        qpat_assum `u'.vs_allocas = u.vs_allocas` SUBST1_TAC >>
        qpat_assum `FLOOKUP u.vs_allocas sr.cs_next_id = SOME _` mp_tac >>
        qpat_assum `type_memory_bytes cenv ret_type = 32`
          (fn th => simp[NoAsms, th]))
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- simp[NoAsms]
    >- decide_tac
    >- (rpt strip_tac >>
        `regions_disjoint (w2n w'') 32 lb lsz` by metis_tac[] >>
        qpat_assum `regions_disjoint (w2n w'') 32 lb lsz` mp_tac >>
        simp[NoAsms, regions_disjoint_def])
    >- (simp[NoAsms, jump_to_def] >>
        qpat_assum `tn1.t_mem = tm'.t_mem` (fn th => pure_rewrite_tac[th]) >>
        qpat_assum `u''.vs_memory = u'.vs_memory` (fn th => pure_rewrite_tac[th]) >>
        first_assum ACCEPT_TAC)) >>
  strip_tac >> qexists_tac `jump_to xl u''` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (pure_rewrite_tac[expr_type_def, lowered_value_type_def] >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `new_block xl cj = _` mp_tac >>
     simp[NoAsms, new_block_def, comp_bind_def, comp_return_def, jump_to_def] >>
     strip_tac >> pop_assum (SUBST1_TAC o SYM) >> simp[NoAsms]) >>
  conj_tac >-
    (qpat_assum `new_block xl cj = _` mp_tac >>
     simp[NoAsms, new_block_def, comp_bind_def, comp_return_def, jump_to_def] >>
     strip_tac >> pop_assum (SUBST1_TAC o SYM) >> simp[NoAsms]) >>
  conj_tac >-
    (irule allocaHistoryTheory.alloca_history_jump >>
     simp[NoAsms, jump_to_def] >> qexists_tac `u` >>
     conj_tac >-
       (qpat_assum `u''.vs_allocas = u'.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     qpat_assum `alloca_history func t /\ _ ==> alloca_history func u` irule >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (simp[NoAsms, jump_to_def] >>
     qpat_assum `u''.vs_alloca_next = u'.vs_alloca_next` SUBST1_TAC >>
     qpat_assum `u'.vs_alloca_next = u.vs_alloca_next` SUBST1_TAC >>
     irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `t.vs_alloca_next` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (pure_rewrite_tac[loweringPostsTheory.post_value_type_def, expr_type_def] >> first_assum ACCEPT_TAC) >>
  conj_tac >- simp[NoAsms, contextTheory.vv_location_def, contextTheory.mk_ptr_def] >>
  conj_tac >-
    (simp[NoAsms, contextTheory.mk_ptr_def] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED
Resume extcall_return_full_default_value[memory]:
  `~is_word_type default_ty` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `type_memory_bytes cenv default_ty = type_memory_size tv` by
    (Cases_on `default_ty = ret_type` >- metis_tac[optionTheory.SOME_11] >>
     `is_bytestring_type default_ty` by metis_tac[] >>
     qpat_assum `evaluate_type (get_tenv cx) default_ty = SOME tv` mp_tac >>
     qpat_assum `is_bytestring_type default_ty` mp_tac >>
     map_every qid_spec_tac [`tv`, `default_ty`] >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases >> simp[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     simp[is_bytestring_type_def] >>
     TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[is_bytestring_type_def]) >>
     simp[is_bytestring_type_def, vyperValueTheory.evaluate_type_def,
       type_memory_bytes_def, valueEncodingTheory.type_memory_size_def,
       vfmConstantsTheory.word_size_def] >>
     rpt strip_tac >> gvs[valueEncodingTheory.type_memory_size_def,
       vfmConstantsTheory.word_size_def, arithmeticTheory.MULT_COMM] ) >>
  `type_memory_size tv <> 0 ==>
    ?x. default_op = Var x /\ ptr_covers Gf tm x u (type_memory_size tv) /\
      w2n w + type_memory_size tv <= u.vs_alloca_next` by
    (strip_tac >>
     qpat_assum `!dv'. SOME dv = SOME dv' /\ _ ==> _`
       (qspec_then `dv` mp_tac) >>
     impl_tac >- simp[] >>
     disch_then (CONJUNCTS_THEN2 (K all_tac) mp_tac) >>
     impl_tac >- metis_tac[] >>
     disch_then (qx_choose_then `source` (qx_choose_then `source_base`
       (qx_choose_then `source_size` (qx_choose_then `source_w` strip_assume_tac)))) >>
     `not_fresh_at sr source` by metis_tac[safe_operand_def] >>
     `source_w = w` by metis_tac[optionTheory.SOME_11] >>
     qexists_tac `source` >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (pure_rewrite_tac[ptr_covers_def] >>
        conj_tac >- metis_tac[] >>
        qexistsl_tac [`w`, `source_base`, `source_size`] >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        metis_tac[eval_operand_def]) >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qpat_assum `buf.buf_operand = Var (STRING #"%" _)` (fn th =>
    qpat_assum `compile_store_memory _ _ _ _ _ _ = _`
      (mp_tac o REWRITE_RULE [th])) >> disch_then assume_tac >>
  `lookup_var (STRING #"%" (toString sr.cs_next_var)) u = SOME w''` by
    metis_tac[eval_operand_def] >>
  `op_taint tm (Var (STRING #"%" (toString sr.cs_next_var))) = {}` by
    (qpat_assum `ptr_covers Gf tm _ u _`
      (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [ptr_covers_def])) >>
  `!x. default_op = Var x ==> not_fresh_at ds x` by
    (qpat_assum `safe_operand ds default_op`
      (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [safe_operand_def])) >>
  mp_tac (Q.INST
    [`ce` |-> `cenv`, `src` |-> `default_op`,
     `dst` |-> `STRING #"%" (toString sr.cs_next_var)`,
     `rt` |-> `ret_type`, `sty` |-> `default_ty`, `a` |-> `ds`, `b` |-> `de`,
     `tv` |-> `rtv`, `stv` |-> `tv`, `v` |-> `dv`, `s` |-> `u`,
     `sw` |-> `w`, `dw` |-> `w''`, `G` |-> `Gf`, `tn` |-> `tm`]
    (SPEC_ALL return_default_memory_store_capacity_joint)) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    metis_tac[eval_operand_def]) >>
  strip_tac >>
  `u'.vs_allocas = u.vs_allocas /\
   u'.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `u' with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = u`
      mp_tac >> simp[NoAsms, venom_state_component_equality] >> metis_tac[]) >>
  `wb_frame cenv es ee sa s0 u` by metis_tac[] >>
  `not_local_ptr cenv ee.scopes (STRING #"%" (toString sr.cs_next_var))` by
    (irule exprSimOperandsTheory.fresh_not_local_ptr >>
     qexists_tac `sr` >> simp[not_fresh_at_def]) >>
  `abi_malformed_destination func cenv ee.scopes sr.cs_next_id (w2n w'')
     (type_memory_size rtv) u` by
    (simp[abiMalformedRecursiveInterfaceTheory.abi_malformed_destination_def] >>
     qexists_tac `mk_inst sr.cs_next_id ALLOCA
       [Lit (n2w (type_memory_bytes cenv ret_type))]
       [STRING #"%" (toString sr.cs_next_var)]` >>
     simp[venomInstTheory.mk_inst_def] >> metis_tac[]) >>
  drule_at_then (Pat `abi_malformed_destination _ _ _ _ _ _ _`)
    (drule_at_then (Pat `stmt_state_rel _ _ _ _ _ _ _`)
      (drule_at_then (Pat `wb_frame _ _ _ _ _ _`) mp_tac))
    return_default_destination_separation >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then strip_assume_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee u'` by
    (rpt strip_tac >>
     mp_tac (Q.INST
       [`s` |-> `u`, `u` |-> `u'`, `sa` |-> `ds`,
        `start` |-> `w2n (w'' : bytes32)`, `nb` |-> `type_memory_size rtv`]
       (SPEC_ALL (INST_TYPE [alpha |-> ``:256``]
         extcallReturnDefaultMemoryFrameTheory.return_default_memory_state_frame))) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       metis_tac[regions_disjoint_def]) >> simp[NoAsms]) >>
  `wb_frame cenv es ee sa s0 u'` by
    (mp_tac (Q.INST
       [`s` |-> `u`, `u` |-> `u'`, `start` |-> `w2n (w'' : bytes32)`,
        `nb` |-> `type_memory_size rtv`]
       (SPEC_ALL extcallReturnDefaultMemoryFrameTheory.return_default_memory_wb_frame)) >>
     impl_tac >-
       (conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >-
          (rpt strip_tac >> `not_fresh_at ds x` by
             metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >> metis_tac[]) >>
        conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >- metis_tac[regions_disjoint_def] >>
        conj_tac >- metis_tac[regions_disjoint_def] >>
        first_assum ACCEPT_TAC) >> simp[NoAsms]) >>
  `lo <= w2n w''` by
    (qpat_assum `allocas_from lo u` mp_tac >>
     pure_rewrite_tac[allocas_from_def] >> metis_tac[]) >>
  `local_ptrs_rel func cenv ee.scopes u` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx ee u` mp_tac >>
     simp[NoAsms, stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     ghost_inv_at (DF H) lo d cenv cx ee Gf' tm' u'` by
    (rpt strip_tac >>
     mp_tac (Q.INST
       [`s` |-> `u`, `u` |-> `u'`, `sa` |-> `ds`,
        `start` |-> `w2n (w'' : bytes32)`, `nb` |-> `type_memory_size rtv`,
        `G` |-> `Gf`, `G'` |-> `Gf'`, `tn` |-> `tm`, `tm` |-> `tm'`,
        `D` |-> `DF (H : (bool # bytes32 # type_value) list # num list)`]
       (SPEC_ALL (INST_TYPE [alpha |-> ``:256``]
         extcallReturnDefaultMemoryFrameTheory.return_default_memory_ghost_frame))) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       metis_tac[regions_disjoint_def]) >> simp[NoAsms]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf' tm'` by
    (mp_tac (Q.INST
       [`lo` |-> `lo`, `cenv` |-> `cenv`, `es` |-> `es`, `sa` |-> `sa`,
        `Gi` |-> `G0`, `ti` |-> `tn0`, `s0` |-> `s0`,
        `G` |-> `Gf`, `tn` |-> `tm`, `H` |-> `Gf'`, `tf` |-> `tm'`]
       (SPEC_ALL (INST_TYPE [alpha |-> ``:num # num``]
         bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_kept_at))) >>
     impl_tac >-
       (conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >-
          (rpt strip_tac >> `not_fresh_at ds x` by
             metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >> metis_tac[]) >>
        conj_tac >-
          (rpt strip_tac >>
           `FLOOKUP u.vs_allocas aid = SOME (off,sz)` by
             (qpat_assum `wb_frame cenv es ee sa s0 u`
               (mp_tac o CONJUNCT1 o CONJUNCT2 o
                REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
              disch_then (qspecl_then [`aid`, `(off,sz)`] mp_tac) >> simp[]) >>
           `regions_disjoint (w2n w'') (type_memory_size rtv) off sz` by metis_tac[] >>
           `i < w2n w'' \/ w2n w'' + type_memory_size rtv <= i` by
             (qpat_assum `regions_disjoint _ _ off sz` mp_tac >>
              simp[NoAsms, regions_disjoint_def] >> decide_tac) >> metis_tac[]) >>
        conj_tac >-
          (rpt strip_tac >>
           `regions_disjoint (w2n w'') (type_memory_size rtv) b sz` by metis_tac[] >>
           `i < w2n w'' \/ w2n w'' + type_memory_size rtv <= i` by
             (qpat_assum `regions_disjoint _ _ b sz` mp_tac >>
              simp[NoAsms, regions_disjoint_def] >> decide_tac) >> metis_tac[]) >>
        rpt strip_tac >> `i < w2n w''` by decide_tac >> metis_tac[]) >>
     simp[NoAsms]) >>
  `ptr_covers Gf' tm' (STRING #"%" (toString sr.cs_next_var)) u'
     (type_memory_size rtv)` by
    (qpat_assum `ptr_covers Gf tm _ u _` mp_tac >>
     pure_rewrite_tac[ptr_covers_def] >>
     `lookup_var (STRING #"%" (toString sr.cs_next_var)) u' =
        lookup_var (STRING #"%" (toString sr.cs_next_var)) u /\
      FLOOKUP Gf' (STRING #"%" (toString sr.cs_next_var)) =
        FLOOKUP Gf (STRING #"%" (toString sr.cs_next_var)) /\
      op_taint tm' (Var (STRING #"%" (toString sr.cs_next_var))) =
        op_taint tm (Var (STRING #"%" (toString sr.cs_next_var)))` by metis_tac[] >>
     qpat_assum `lookup_var _ u' = lookup_var _ u` (fn th => rewrite_tac[th]) >>
     qpat_assum `FLOOKUP Gf' _ = FLOOKUP Gf _` (fn th => rewrite_tac[th]) >>
     qpat_assum `op_taint tm' _ = op_taint tm _` (fn th => rewrite_tac[th]) >>
     qpat_assum `type_memory_bytes cenv ret_type = _` (fn th => simp[NoAsms, th])) >>
  `allocas_from lo u'` by
    (qpat_assum `allocas_from lo u` mp_tac >>
     qpat_assum `u'.vs_allocas = u.vs_allocas` (fn th => simp[NoAsms, allocas_from_def, th])) >>
  `eval_operand addr_op u' = SOME aw /\ op_taint tm' addr_op = {}` by
    (`safe_operand ds addr_op` by metis_tac[safe_operand_mono] >>
     qpat_assum `eval_operand addr_op u = SOME aw` mp_tac >>
     qpat_assum `op_taint tm addr_op = {}` mp_tac >>
     qpat_assum `safe_operand ds addr_op` mp_tac >>
     qpat_assum `!x. not_fresh_at ds x ==> lookup_var x u' = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `addr_op` >>
     simp[NoAsms, eval_operand_def, op_taint_def, safe_operand_def] >>
     metis_tac[optionTheory.SOME_11]) >>
  drule_then
    (drule_at_then (Pat `emit_inst JMP _ _ _ = _`)
      (drule_at_then (Pat `eval_operand _ _ = SOME _`)
        (drule_at_then (Pat `op_taint _ _ = {}`)
          (drule_at_then (Pat `fn_has_code _ _ _`)
            (drule_at_then (Pat `allocas_from _ _`)
              (drule_at_then (Pat `~ctx_has_dalloca _`) mp_tac))))))
    return_default_suffix_path_joint >>
  disch_then (qspecl_then [`explicit`, `PG`, `Gf'`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then strip_assume_tac >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (t,G,tn) [] (r,G1,tn1)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (t,G,tn) _ _` (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (u,Gf,tm) _ _` (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (u',Gf',tm') _ _` (qspec_then `D` mp_tac) >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, listTheory.APPEND_NIL]) >>
  Cases_on `skip` >- suspend "memory_skip" >>
  `stmt_state_rel H0 ctx func cenv cx ee u'` by metis_tac[] >>
  `((n2w (LENGTH (lookup_account (w2w aw) u'.vs_accounts).code):bytes32) <> 0w
     <=> ext_call_has_code target ee.accounts)` by
    metis_tac[extCallCodeCheckTheory.extcall_precheck_code_word] >>
  qpat_x_assum `~F ==> ?s. _` mp_tac >>
  pure_rewrite_tac [NOT_CLAUSES, IMP_CLAUSES] >> strip_tac >>
  Cases_on `ext_call_has_code target ee.accounts`
  >- suspend "memory_code" >>
  qexistsl_tac [`r`, `G1`, `tn1`] >>
  gen_tac >> disch_tac >> conj_tac >- metis_tac[] >>
  disj2_tac >>
  `r = Abort Revert_abort (revert_state (set_returndata [] u''))` by metis_tac[] >>
  simp[exit_result_def, exprSimDefsTheory.expr_exit_def]
QED
Resume extcall_return_full_default_value[memory_skip]:
  rename1 `expr_body_pre cenv cx env
    (Call ann (ExtCall stat T (fname,arg_types,ret_type) opts) args dflt) es` >>
  `ann = ret_type` by metis_tac[extcall_return_type_bounds] >>
  `ee with gas_obs := [] = ee` by
    (simp[NoAsms, vyperStateTheory.evaluation_state_component_equality] >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `ann = ret_type` (fn th => rewrite_tac[th]) >>
  qpat_assum `ee with gas_obs := [] = ee` (fn th => rewrite_tac[th]) >>
  `r = OK (jump_to xl u') /\ G1 = Gf' /\ tn1 = tm'` by metis_tac[] >>
  qexistsl_tac [`r`, `G1`, `tn1`] >>
  gen_tac >> disch_tac >> conj_tac >- metis_tac[] >>
  `!x. not_fresh_at ds x ==>
     lookup_var x (jump_to xl u') = lookup_var x u` by
    (rpt strip_tac >> simp[NoAsms, jump_to_def, lookup_var_def] >>
     qpat_assum `!x. not_fresh_at ds x ==> lookup_var x u' = _ /\ _`
       (qspec_then `x` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[NoAsms, lookup_var_def]) >>
  `!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     not_fresh_at ds p` by
    (qpat_assum `local_ptrs_reserved cenv ds`
       (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [local_ptrs_reserved_def]) >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `!name b sz. local_region cenv ee.scopes (jump_to xl u') name b sz <=>
     local_region cenv ee.scopes u name b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >> metis_tac[]) >>
  `eval_operand buf.buf_operand (jump_to xl u') = SOME w''` by
    (qpat_assum `buf.buf_operand = Var (STRING #"%" _)`
       (fn th => rewrite_tac[th, eval_operand_def]) >> metis_tac[]) >>
  `ptr_covers Gf' tm' (STRING #"%" (toString sr.cs_next_var))
     (jump_to xl u') (type_memory_size rtv)` by
    (qpat_assum `ptr_covers Gf' tm' _ u' _` mp_tac >>
     simp[NoAsms, ptr_covers_def, jump_to_def, lookup_var_def]) >>
  `stmt_state_rel H ctx func cenv cx ee (jump_to xl u')` by
    (pure_rewrite_tac[stmt_state_rel_jump_to] >> metis_tac[]) >>
  `wb_frame cenv es ee sa s0 (jump_to xl u')` by
    (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
     goal_assum (drule_at (Pat `wb_frame _ _ _ _ _ u'`)) >>
     qexists_tac `sa` >> simp[NoAsms, jump_to_def, lookup_var_def]) >>
  mp_tac (Q.INST
    [`ty` |-> `ret_type`, `skip` |-> `T`, `G` |-> `Gf'`, `tn` |-> `tm'`,
     `z` |-> `jump_to xl u'`, `op` |-> `buf.buf_operand`,
     `dst` |-> `STRING #"%" (toString sr.cs_next_var)`, `dw` |-> `w''`,
     `aid` |-> `sr.cs_next_id`, `b` |-> `w2n (w'' : bytes32)`, `sz` |-> `(type_memory_size rtv)`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] extcall_default_value_posts))) >>
  impl_tac >- (rpt conj_tac
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- metis_tac[]
    >- first_assum ACCEPT_TAC
    >- metis_tac[]
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- metis_tac[]
    >- (simp[NoAsms, jump_to_def] >>
        qpat_assum `u'.vs_alloca_next = u.vs_alloca_next` SUBST1_TAC >>
        qpat_assum `w2n w'' + type_memory_bytes cenv ret_type <= u.vs_alloca_next` mp_tac >>
        qpat_assum `type_memory_bytes cenv ret_type = type_memory_size rtv`
          (fn th => simp[NoAsms, th]))
    >- (simp[NoAsms, jump_to_def] >>
        qpat_assum `u'.vs_allocas = u.vs_allocas` SUBST1_TAC >>
        qpat_assum `FLOOKUP u.vs_allocas sr.cs_next_id = SOME _` mp_tac >>
        qpat_assum `type_memory_bytes cenv ret_type = (type_memory_size rtv)`
          (fn th => simp[NoAsms, th]))
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- simp[NoAsms]
    >- decide_tac
    >- (rpt strip_tac >>
        `regions_disjoint (w2n w'') (type_memory_size rtv) lb lsz` by metis_tac[] >>
        qpat_assum `regions_disjoint (w2n w'') (type_memory_size rtv) lb lsz` mp_tac >>
        simp[NoAsms, regions_disjoint_def])
    >- (simp[NoAsms, jump_to_def] >> metis_tac[])) >>
  strip_tac >>
  qpat_assum `G1 = Gf'` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `tn1 = tm'` (fn th => pure_rewrite_tac[th]) >>
  qexists_tac `jump_to xl u'` >>
  conj_tac >- metis_tac[] >>
  conj_tac >- suspend "memory_skip_vv" >>
  conj_tac >- suspend "memory_skip_bound" >>
  conj_tac >- suspend "memory_skip_bb" >>
  conj_tac >- suspend "memory_skip_idx" >>
  conj_tac >- suspend "memory_skip_history" >>
  conj_tac >- suspend "memory_skip_next" >>
  conj_tac >- suspend "memory_skip_ghost" >>
  conj_tac >- suspend "memory_skip_ptr" >>
  conj_tac >- suspend "memory_skip_code_loc" >>
  conj_tac >- suspend "memory_skip_buf" >>
  suspend "memory_skip_kept"
QED
Resume extcall_return_full_default_value[memory_skip_ghost]:
  pure_rewrite_tac[bodyFullSharedTheory.ghost_inv_at_jump] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at _ _ _ _ _ _ _ _ u'`
    (qspec_then `H` mp_tac) >> simp[]
QED
Resume extcall_return_full_default_value[memory_skip_bb]:
  qpat_assum `new_block xl cj = _` mp_tac >>
  simp[NoAsms, new_block_def, comp_bind_def, comp_return_def, jump_to_def] >>
  strip_tac >> pop_assum (SUBST1_TAC o SYM) >> simp[NoAsms]
QED
Resume extcall_return_full_default_value[memory_skip_idx]:
  qpat_assum `new_block xl cj = _` mp_tac >>
  simp[NoAsms, new_block_def, comp_bind_def, comp_return_def, jump_to_def] >>
  strip_tac >> pop_assum (SUBST1_TAC o SYM) >> simp[NoAsms]
QED
Resume extcall_return_full_default_value[memory_skip_next]:
  pure_rewrite_tac[jump_to_def] >> simp[NoAsms] >>
  qpat_assum `u'.vs_alloca_next = u.vs_alloca_next` SUBST1_TAC >>
  irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `t.vs_alloca_next` >>
  conj_tac >> first_assum ACCEPT_TAC
QED
Resume extcall_return_full_default_value[memory_skip_code_loc]:
  simp[NoAsms, contextTheory.vv_location_def, contextTheory.mk_ptr_def]
QED
Resume extcall_return_full_default_value[memory_skip_vv]:
  first_assum ACCEPT_TAC
QED
Resume extcall_return_full_default_value[memory_skip_bound]:
  pure_rewrite_tac[expr_type_def, lowered_value_type_def] >> first_assum ACCEPT_TAC
QED
Resume extcall_return_full_default_value[memory_skip_history]:
  irule allocaHistoryTheory.alloca_history_jump >>
  simp[NoAsms, jump_to_def] >> qexists_tac `u` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `alloca_history func t /\ _ ==> alloca_history func u` irule >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume extcall_return_full_default_value[memory_skip_ptr]:
  pure_rewrite_tac[loweringPostsTheory.post_value_type_def, expr_type_def] >>
  first_assum ACCEPT_TAC
QED
Resume extcall_return_full_default_value[memory_skip_buf]:
  simp[NoAsms, contextTheory.mk_ptr_def] >> rpt strip_tac >> first_assum ACCEPT_TAC
QED
Resume extcall_return_full_default_value[memory_skip_kept]:
  first_assum ACCEPT_TAC
QED
Resume extcall_return_full_default_value[memory_code]:
  rename1 `expr_body_pre cenv cx env
    (Call ann (ExtCall stat F (fname,arg_types,ret_type) opts) args dflt) es` >>
  `ann = ret_type` by metis_tac[extcall_return_type_bounds] >>
  `ee with gas_obs := [] = ee` by
    (simp[NoAsms, vyperStateTheory.evaluation_state_component_equality] >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `ann = ret_type` (fn th => rewrite_tac[th]) >>
  qpat_assum `ee with gas_obs := [] = ee` (fn th => rewrite_tac[th]) >>
  qpat_assum `ext_call_has_code target ee.accounts` (fn th => rewrite_tac[th]) >>
  `r = OK (jump_to xl u'')` by metis_tac[COND_CLAUSES] >>
  `ci_mono ds de` by
    metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `ds.cs_next_var <= de.cs_next_var` by
    (qpat_assum `ci_mono ds de` mp_tac >> simp[NoAsms, ci_mono_def]) >>
  mp_tac (Q.INST
    [`sa` |-> `ds`, `n` |-> `de.cs_next_var`,
     `u` |-> `jump_to xl u''`, `lbl` |-> `xl`, `s` |-> `u'`,
     `w` |-> `(n2w (LENGTH (lookup_account (w2w (aw:bytes32)) u'.vs_accounts).code):bytes32)`,
     `k` |-> `LENGTH de.cs_current_insts + 1`,
     `G` |-> `Gf'`, `tn` |-> `tm'`, `G1` |-> `G1`, `tn1` |-> `tn1`,
     `ctx` |-> `ctx`, `func` |-> `func`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] return_default_suffix_joint_frame))) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    qpat_assum `u'' = _` (fn th => simp[NoAsms, th])) >>
  strip_tac >>
  qpat_x_assum `!H ce cx ee. _ ==> stmt_state_rel H ctx func ce cx ee _`
    (mk_asm "code_state") >>
  qpat_x_assum `!D lo d ce cx ee. _ ==> ghost_inv_at D lo d ce cx ee _ _ _`
    (mk_asm "code_ghost") >>
  qpat_x_assum `!ce es ee sa0 s0. _ ==> wb_frame ce es ee sa0 s0 (jump_to _ _)`
    (mk_asm "code_frame") >>
  qpat_x_assum `!lo ce es sa0 G0 tn0 s0. _ /\ _ ==> ghost_kept_at lo ce es sa0 G0 tn0 s0 _ _`
    (mk_asm "code_kept") >>
  `u''.vs_memory = u'.vs_memory /\ u''.vs_allocas = u'.vs_allocas /\
   u''.vs_alloca_next = u'.vs_alloca_next /\ tn1.t_mem = tm'.t_mem` by
    (qpat_assum `u'' = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `tn1 = _ with t_var := _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, update_var_def]) >>
  `lookup_var (STRING #"%" (toString sr.cs_next_var)) (jump_to xl u'') =
       lookup_var (STRING #"%" (toString sr.cs_next_var)) u' /\
   FLOOKUP G1 (STRING #"%" (toString sr.cs_next_var)) =
       FLOOKUP Gf' (STRING #"%" (toString sr.cs_next_var)) /\
   op_taint tn1 (Var (STRING #"%" (toString sr.cs_next_var))) =
       op_taint tm' (Var (STRING #"%" (toString sr.cs_next_var)))` by
    (qpat_assum `!x. not_fresh_at ds x ==> lookup_var x (jump_to _ _) = _ /\ _`
       (qspec_then `STRING #"%" (toString sr.cs_next_var)` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[NoAsms]) >>
  `ptr_covers G1 tn1 (STRING #"%" (toString sr.cs_next_var)) (jump_to xl u'') (type_memory_size rtv)` by
    (qpat_assum `ptr_covers Gf' tm' _ u' (type_memory_size rtv)` mp_tac >>
     pure_rewrite_tac[ptr_covers_def] >>
     qpat_assum `lookup_var _ (jump_to xl u'') = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `FLOOKUP G1 _ = FLOOKUP Gf' _` (fn th => rewrite_tac[th]) >>
     qpat_assum `op_taint tn1 _ = op_taint tm' _` (fn th => simp[NoAsms, th])) >>
  qexistsl_tac [`r`, `G1`, `tn1`] >> gen_tac >> disch_tac >>
  conj_tac >- metis_tac[] >>
  `stmt_state_rel H ctx func cenv cx ee (jump_to xl u'')` by
    (asm "code_state" irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u'`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `wb_frame cenv es ee sa s0 (jump_to xl u'')` by
    (asm "code_frame" irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 (jump_to xl u'')` by
    (asm "code_ghost" irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at _ _ _ _ _ _ _ _ u'`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` by
    (asm "code_kept" irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand buf.buf_operand (jump_to xl u'') = SOME w''` by
    (qpat_assum `buf.buf_operand = Var (STRING #"%" _)`
       (fn th => rewrite_tac[th, eval_operand_def]) >>
     qpat_assum `lookup_var _ (jump_to xl u'') = _` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at ds x ==> lookup_var x (jump_to xl u'') = lookup_var x u` by
    (gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at ds x ==> lookup_var x (jump_to _ _) = _ /\ _`
       (qspec_then `x` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     strip_tac >> metis_tac[]) >>
  `!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     not_fresh_at ds p` by
    (qpat_assum `local_ptrs_reserved cenv ds`
       (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [local_ptrs_reserved_def]) >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `!name b sz. local_region cenv ee.scopes (jump_to xl u'') name b sz <=>
     local_region cenv ee.scopes u name b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     map_every qx_gen_tac [`reserved_name`, `reserved_entry`, `reserved_ptr`, `reserved_len`] >>
     strip_tac >>
     `not_fresh_at ds reserved_ptr` by
       (qpat_assum `!name p sz. FLOOKUP cenv.ce_vars name = _ ==> not_fresh_at ds p`
          (qspecl_then [`reserved_name`, `reserved_ptr`, `reserved_len`] mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> simp[NoAsms]) >>
     qpat_assum `!x. not_fresh_at ds x ==> lookup_var x (jump_to xl u'') = lookup_var x u`
       (qspec_then `reserved_ptr` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[NoAsms]) >>
  mp_tac (Q.INST
    [`ty` |-> `ret_type`, `skip` |-> `F`, `G` |-> `G1`, `tn` |-> `tn1`,
     `z` |-> `jump_to xl u''`, `op` |-> `buf.buf_operand`,
     `dst` |-> `STRING #"%" (toString sr.cs_next_var)`, `dw` |-> `w''`,
     `aid` |-> `sr.cs_next_id`, `b` |-> `w2n (w'' : bytes32)`, `sz` |-> `(type_memory_size rtv)`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] extcall_default_value_posts))) >>
  impl_tac >- (rpt conj_tac
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- metis_tac[]
    >- first_assum ACCEPT_TAC
    >- metis_tac[]
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- metis_tac[]
    >- (simp[NoAsms, jump_to_def] >>
        qpat_assum `u''.vs_alloca_next = u'.vs_alloca_next` SUBST1_TAC >>
        qpat_assum `u'.vs_alloca_next = u.vs_alloca_next` SUBST1_TAC >>
        qpat_assum `w2n w'' + type_memory_bytes cenv ret_type <= u.vs_alloca_next` mp_tac >>
        qpat_assum `type_memory_bytes cenv ret_type = type_memory_size rtv`
          (fn th => simp[NoAsms, th]))
    >- (simp[NoAsms, jump_to_def] >>
        qpat_assum `u''.vs_allocas = u'.vs_allocas` SUBST1_TAC >>
        qpat_assum `u'.vs_allocas = u.vs_allocas` SUBST1_TAC >>
        qpat_assum `FLOOKUP u.vs_allocas sr.cs_next_id = SOME _` mp_tac >>
        qpat_assum `type_memory_bytes cenv ret_type = (type_memory_size rtv)`
          (fn th => simp[NoAsms, th]))
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- simp[NoAsms]
    >- decide_tac
    >- (rpt strip_tac >>
        `regions_disjoint (w2n w'') (type_memory_size rtv) lb lsz` by metis_tac[] >>
        qpat_assum `regions_disjoint (w2n w'') (type_memory_size rtv) lb lsz` mp_tac >>
        simp[NoAsms, regions_disjoint_def])
    >- (simp[NoAsms, jump_to_def] >>
        qpat_assum `tn1.t_mem = tm'.t_mem` (fn th => pure_rewrite_tac[th]) >>
        qpat_assum `u''.vs_memory = u'.vs_memory` (fn th => pure_rewrite_tac[th]) >>
        first_assum ACCEPT_TAC)) >>
  strip_tac >> qexists_tac `jump_to xl u''` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (pure_rewrite_tac[expr_type_def, lowered_value_type_def] >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `new_block xl cj = _` mp_tac >>
     simp[NoAsms, new_block_def, comp_bind_def, comp_return_def, jump_to_def] >>
     strip_tac >> pop_assum (SUBST1_TAC o SYM) >> simp[NoAsms]) >>
  conj_tac >-
    (qpat_assum `new_block xl cj = _` mp_tac >>
     simp[NoAsms, new_block_def, comp_bind_def, comp_return_def, jump_to_def] >>
     strip_tac >> pop_assum (SUBST1_TAC o SYM) >> simp[NoAsms]) >>
  conj_tac >-
    (irule allocaHistoryTheory.alloca_history_jump >>
     simp[NoAsms, jump_to_def] >> qexists_tac `u` >>
     conj_tac >-
       (qpat_assum `u''.vs_allocas = u'.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     qpat_assum `alloca_history func t /\ _ ==> alloca_history func u` irule >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (simp[NoAsms, jump_to_def] >>
     qpat_assum `u''.vs_alloca_next = u'.vs_alloca_next` SUBST1_TAC >>
     qpat_assum `u'.vs_alloca_next = u.vs_alloca_next` SUBST1_TAC >>
     irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `t.vs_alloca_next` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (pure_rewrite_tac[loweringPostsTheory.post_value_type_def, expr_type_def] >> first_assum ACCEPT_TAC) >>
  conj_tac >- simp[NoAsms, contextTheory.vv_location_def, contextTheory.mk_ptr_def] >>
  conj_tac >-
    (simp[NoAsms, contextTheory.mk_ptr_def] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED
Finalise extcall_return_full_default_value
