(* The selected default of an external-call return, on the linked frame. *)
Theory bodyExtReturnDefaultMods
Ancestors
  bodyExtReturnLayoutMods bodyExtReturnAllocMods bodyExtReturnDefaultControlMods
  bodyExtReturnDefaultWordMods bodyExtReturnDefaultBytesMods
  bodyExtReturnDefaultFlatMods bodyExtReturnDefaultWidenedMods
  bodyExtReturnDefaultPostMods actualAllocExec bodyPtrBopRepresentationFrame
  bodyPtrBopHashFootprint annassignRelayoutPost exprBodyPreProps
  exprBodyPreTypingProps bodyExprPreFacts exprSimExtCallCase
  compileEnv exprLoweringProps fragExec exprSafeOperand venomState
  ptrDiscipline freshWrites fragGasOriginPtr words finite_map
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
Libs monadsyntax

Theorem extcall_return_default_mods:
  ret_type <> NoneT /\ has_default /\ returnData = [] /\
  expr_body_pre_mods mods cenv cx env
    (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt) es /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  cap = abi_size_bound cenv.ce_struct_fields
          (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type) /\
  (if ret_type = NoneT then comp_return (Lit 0w)
   else if has_default then
     comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
       (\r. compile_default_return_path cenv ret_type default_ty buf_op
          r.buf_operand default_op addr_op skip
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
      FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      aid < sr.cs_next_id) /\
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
      eval_operand buf_op t = SOME ro /\ b <= w2n ro /\ w2n ro + cap <= b + sz /\
      (!i. w2n ro <= i /\ i < w2n ro + MIN cap (LENGTH returnData) ==> i NOTIN tn.t_mem)) ==>
  ?res r G' tn'.
    (!tail.
      (case (if returnData = [] then default_opt else NONE) of
       SOME v => do accounts' <- get_accounts;
                    check (skip \/ ext_call_has_code target accounts')
                      "ExtCall target has no code";
                    return (Value v) od
     | NONE => do v <- lift_sum_runtime
                    (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
                  return (Value v) od) (ee with gas_obs := tail) =
        (res,ee with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (r,G',tn') /\
      ((?z tv. r = OK z /\ res = INL tv /\
        let e = Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts)
                      args dflt in
        vv_post_mods H ctx func cenv cx e es sa sb s0 (ee with gas_obs := []) tv vv z /\
        vv_store_bound cx (expr_type e) (lowered_value_type cenv e) (ee with gas_obs := []) tv vv z /\
        z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
        ghost_inv_at_mods (DF H) lo d cenv cx (ee with gas_obs := []) G' tn' z /\
        ptr_vv_ok cx (post_value_type cenv e) tv vv (ee with gas_obs := []) G' tn' z /\
        (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
          ?val. read_result cx tv (ee with gas_obs := []) = (INL val,ee with gas_obs := []) /\
                !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                       eval_operand (vv_operand vv) z = SOME w ==>
                  w2n w + type_memory_size rt <= lo /\
                  (!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
                    val_in_memory rt val (w2n w) mem)) /\
        (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type cenv e) ==>
          ptr_buf_ok cenv e op G' z) /\
        (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv e p.ptr_operand G' z) /\
        vv_own cenv cx (post_value_type cenv e) sa sb (ee with gas_obs := []) tv vv z /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn') \/
       (exit_result r /\ expr_exit res r)))
Proof
  strip_tac >>
  qpat_x_assum `cap = abi_size_bound _ _` kall_tac >>
  gvs[] >>
  drule_all_then strip_assume_tac extcall_return_layout_mods >>
  qpat_assum `extcall_returned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[extcall_returned_def]) >>
  Cases_on `default_opt` >- fs[extcall_default_ready_def] >>
  rename1 `extcall_default_ready cx ret_type T default_op default_ty (SOME dv) t` >>
  qpat_x_assum `extcall_default_ready _ _ _ _ _ _ _` mp_tac >>
  simp[extcall_default_ready_def] >> strip_tac >>
  qexists_tac `if skip \/ ext_call_has_code target ee.accounts then INL (Value dv)
    else INR (Error (RuntimeError "ExtCall target has no code"))` >>
  simp[vyperStateTheory.get_accounts_def, vyperStateTheory.bind_def,
    vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
    vyperStateTheory.check_def, vyperStateTheory.assert_def, COND_RAND, COND_RATOR] >>
  Cases_on `?H. valid_horizon cx st0 H ee.storage_trace`
  >- suspend "entry" >>
  qexistsl_tac [`OK t`,`G`,`tn`] >> rpt strip_tac >> metis_tac[]
QED

Resume extcall_return_default_mods[entry]:
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `h0` assume_tac) >>
  qpat_x_assum `let rt = _ in _` kall_tac >>
  `type_memory_bytes cenv ret_type < dimword (:256)` by decide_tac >>
  Cases_on `compile_alloc_buffer (type_memory_bytes cenv ret_type) sr` >>
  rename1 `compile_alloc_buffer _ sr = (buf,ar)` >>
  fs[comp_bind_def] >>
  `ci_mono sr ar` by
    (qpat_assum `compile_alloc_buffer _ sr = (buf,ar)` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[ci_mono_compile_alloc_buffer,pairTheory.SND]) >>
  `ci_mono ar sb` by
    (qpat_assum `compile_default_return_path _ _ _ _ _ _ _ _ _ _ _ ar = (_,sb)` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[ci_mono_compile_default_return_path,pairTheory.SND]) >>
  `cs_extends sr ar /\ cs_extends ar sb` by fs[ci_mono_def] >>
  `fn_has_code sr ar func /\ fn_has_code ar sb func` by
    (conj_tac >> irule fn_has_code_mid >> simp[] >>
     qexistsl_tac [`sb`,`sr`] >> simp[cs_extends_refl]) >>
  `?H. valid_horizon cx st0 H ee.storage_trace` suffices_by
    (disch_tac >> drule_all extcall_return_alloc_cut_mods >>
     disch_then (qspecl_then [`explicit`,`PG`]
       (qx_choosel_then [`q`,`dw`,`a`,`J`,`tm`] strip_assume_tac)) >>
     suspend "control_entry") >>
  qexists_tac `h0` >> simp[]
QED

Resume extcall_return_default_mods[control_entry]:
  `sa.cs_next_id <= sr.cs_next_id /\ sr.cs_next_var <= ar.cs_next_var` by fs[ci_mono_def] >>
  `sa.cs_next_var <= ar.cs_next_var` by decide_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at ar x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv ar` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sr` >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ar x` by metis_tac[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ar x` by metis_tac[] >>
  `safe_operand ar default_op /\ safe_operand ar addr_op` by
    (conj_tac >> irule safe_operand_mono >> qexists_tac `sr` >> simp[]) >>
  `!op. safe_operand sr op ==>
      eval_operand op a = eval_operand op t /\ op_taint tm op = op_taint tn op` by
    (Cases_on `op` >> simp[safe_operand_def,eval_operand_def,op_taint_def] >>
     strip_tac >> qpat_assum `!x. not_fresh_at sr x ==> lookup_var x a = _ /\ _`
       (drule_then strip_assume_tac) >> fs[op_taint_def]) >>
  `eval_operand default_op a = SOME w /\ op_taint tm default_op = {} /\
   eval_operand addr_op a = SOME aw /\ op_taint tm addr_op = {}` by
    (qpat_assum `!op. safe_operand sr op ==> _`
       (qspecl_then [`default_op`] mp_tac) >>
     qpat_assum `!op. safe_operand sr op ==> _`
       (qspecl_then [`addr_op`] mp_tac) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ a /\ _`
    (qspec_then `h0` (drule_then strip_assume_tac)) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp a)` by
    (qpat_assum `stmt_state_rel h0 _ _ _ _ _ a` (mp_tac o MATCH_MP
       bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >> simp[]) >>
  `lo <= a.vs_alloca_next` by decide_tac >>
  qpat_assum `buf.buf_operand = Var q` (fn th =>
    qpat_x_assum `compile_default_return_path _ _ _ _ _ _ _ _ _ _ _ ar = _`
      (assume_tac o REWRITE_RULE[th])) >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`bs` |-> `[]`, `has_default` |-> `T`]
    extcall_default_entry_mods)) >>
  FAIL_TAC "control entry application"
QED

Finalise extcall_return_default_mods
