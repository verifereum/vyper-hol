(* Request prefixes of rounds starting just after the snapshot length. *)
Theory s1PrefixForArraySnapshotLoop
Ancestors
  s1PrefixForArrayRound s1PrefixForRounds s1PrefixCompose
  vyperStorageTrace vyperInterpreter

Theorem for_array_snapshot_loop_prefix:
  for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond_label,bod,incr,exit,idx,invalid,valid,done_var,next_var)
    (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
    (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
  body_const_cells_agree [(NONE,tops)] cx env em /\
  body_inv tops ctx c cx /\ shadow_body_inv tops ctx shadow_ctx /\ expr_body_pre c cx env e es0 /\
  ce_locals_declared c env /\ locals_alloc_ok c env /\
  supported_stmt tops bindings (For id fty (Array e) n loop_body) /\
  type_stmt env ret_ty (For id fty (Array e) n loop_body) = SOME env' /\
  stmt_exprs_ok c (For id fty (Array e) n loop_body) /\
  for_nonslot_code_frame [(NONE,tops)] c cx env ctx func id e loop_body loc rv vv av em tL /\
  stmt_loop_calls_ok [(NONE,tops)] (For id fty (Array e) n loop_body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id fty (Array e) n loop_body) ==> occurs_abi_decode_target target tops) /\
  call_evaluation_safe cx (int_calls_stmt (For id fty (Array e) n loop_body)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ c ret_ty /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved c sa0 /\ (!H. dead_lo_ok H (DF H) lo c cx) /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  return_buf_frame d c sa0 s0 /\ ret_pc_ok c sa0 s0 /\
  (!fn inst t. frag_reachable ctx func tL fn inst t ==> dalloca_fmp_headroom inst t) /\
  evaluate_type (get_tenv cx) fty = SOME dtv /\ body_for_full_ok cx dtv id loop_body vs /\
  body_for_prefix_ok cx dtv id loop_body vs /\
  gas_admissible (eval_for cx dtv id loop_body vs) (stmt_res_ok lctx) em /\
  storage_trace_domain cx st0 em.storage_trace /\
  return_buf_sep d c em tL /\
  vs = MAP Value xs /\
  (?obs. !tail. eval_expr cx e (es0 with gas_obs := obs ++ tail) =
                 (INL rv,em with gas_obs := tail)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV stv bd) /\
  value_has_type (ArrayTV stv bd) (ArrayV av) /\
  (!name path. rv = PlaceR (MemoryPlace name path) ==>
     runtime_place_typed cx em (MemoryPlace name path) (ArrayTV stv bd)) /\
  (!name path. rv = PlaceR (MemoryPlace name path) ==>
     ?ent. lookup_scopes name em.scopes = SOME ent /\
       evaluate_subscripts ent.type ent.value path = INL (ArrayV av)) /\
  read_result cx rv em = (INL (ArrayV av),em) /\
  extract_elements (ArrayTV stv bd) (ArrayV av) = SOME xs /\
  (loc = LocMemory \/ loc = LocCode) /\
  (loc = LocMemory ==> rv = Value (ArrayV av) \/ ?name path. rv = PlaceR (MemoryPlace name path)) /\
  eval_operand len_op tL = SOME (n2w (LENGTH vs)) /\ op_taint tnL len_op = {} /\
  op_prov GL len_op = NONE /\ ~tL.vs_halted /\ tL.vs_current_bb = saL.cs_current_bb /\
  tL.vs_inst_idx = LENGTH saL.cs_current_insts /\
  alloca_history func tL /\ (ctx_has_dalloca ctx ==> allocas_below_fmp tL) /\ allocas_from lo tL /\
  s0.vs_alloca_next <= tL.vs_alloca_next /\ alloca_frame c es0 sa0 s0 c em tL /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP tL.vs_allocas aid = SOME b) /\
  (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x tL = SOME w) /\
  ghost_kept_at lo c es0 sa0 G0 tn0 s0 GL tnL /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
    stmt_state_rel H ctx func c cx em tL /\ storage_well_formed_on cx em (FST H) /\
    ghost_inv_at (DF H) lo d c cx em GL tnL tL) /\
  vv_post (storage_trace_horizon em.storage_trace) ctx func c cx e es0 sa0 sbExpr s0 em rv vv tL /\
  vv_store_bound cx (post_value_type c e) (lowered_value_type c e) em rv vv tL /\
  ptr_vv_ok cx (post_value_type c e) rv vv em GL tnL tL /\
  (!v. rv = Value v /\ ~is_word_type (post_value_type c e) /\
    ~is_bytestring_type (post_value_type c e) ==>
    vv_own c cx (post_value_type c e) sa0 sbExpr em rv vv tL /\
    (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
  (c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (post_value_type c e) = SOME rt /\
      eval_operand (vv_operand vv) tL = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tnL.t_mem tL.vs_memory mem ==>
        val_in_memory rt (ArrayV av) (w2n w) mem)) /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type c e) ==>
    ptr_buf_ok c e op GL tL) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok c e p.ptr_operand GL tL) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
    (eval_for cx dtv id loop_body vs) (em,tL,GL,tnL)
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `for_nonslot_layout _ _ _ _ _ _ _`
    (mp_then (Pos hd) (mp_tac o SPEC_ALL)
      (Q.INST [`u` |-> `tL`,`Gu` |-> `GL`,`tu` |-> `tnL`]
        (SPEC_ALL for_nonslot_array_round_prefix_contracts_at))) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`s`,`G`,`tn`,`Inv`,`Done`]
    (map_every assume_tac o CONJUNCTS)) >>
  irule gas_prefix_full_zero_prefix_guarded >>
  simp[NoAsms,cj 4 evaluate_storage_trace_frame] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G`,`s`,`tn`] >>
  conj_tac >-
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==>
        gas_origin_ptr_path _ (tL,GL,tnL) [] (OK s,G,tn) /\ _`
       (qspec_then `H` (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
  irule eval_for_rounds_prefix >>
  conj_tac >-
    (qexists_tac `\rs b. if b then return () else eval_for cx dtv id loop_body rs` >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Done`,`Inv`,
    `\H ex ee gt r.
       (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
       halt_exit H cx ee (INR ex) r /\
       (ctx_has_dalloca ctx ==> !t. (r = Halt t \/ ?ir. r = IntRet ir t) ==> allocas_below_fmp t)`,
    `stmt_res_ok lctx`,
    `\a. do v <- read_result cx a; push_scope_with_var id dtv v;
       finally (try (do eval_stmts cx loop_body; return F od) handle_loop_exception) pop_scope od`,
    `cx_tops cx`] >>
  BETA_TAC >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >> conj_tac >> first_assum (drule_all_then ACCEPT_TAC)) >>
  conj_tac >- simp[] >>
  conj_tac >-
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==>
        gas_origin_ptr_path _ (tL,GL,tnL) [] (OK s,G,tn) /\ _`
       (qspec_then `H` (drule_then (ACCEPT_TAC o CONJUNCT2)))) >>
  first_assum ACCEPT_TAC
QED
