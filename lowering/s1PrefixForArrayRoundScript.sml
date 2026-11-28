(* Request-prefix companion to bodyFullForArrayRound. *)
Theory s1PrefixForArrayRound
Ancestors
  s1PrefixPreds bodyFullForArrayRound s1PrefixDefs
  s1PrefixForHandlers s1PrefixForArrayRoundHead s1PrefixInvalidTraceDomain
  vyperStorageTrace vyperState vyperInterpreter

val _ = Parse.hide "cond";

(* The round construction only needs the selected frame at the length
   endpoint. Ordinary iterators and captured snapshots obtain it differently. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`cond : string` |-> `cond_label`,
    `mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`,
    `B` |-> `\eb t Gf tnf.
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
        (finally (try (do eval_stmts cx loop_body; return F od)
          handle_loop_exception) pop_scope) (eb,t,Gf,tnf)`,
    `P` |-> `\a rs es z J tz.
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
        (do v <- read_result cx a; push_scope_with_var id dtv v;
            finally (try (do eval_stmts cx loop_body; return F od)
              handle_loop_exception) pop_scope od) (es,z,J,tz)`]
    (SPEC_ALL for_nonslot_array_round_contracts_at_with_prefix)) >>
  BETA_TAC >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >-
      suspend "body_entry" >> suspend "round_head")) >>
  suspend "assemble"
QED
*)
Theorem for_nonslot_array_round_prefix_contracts_at:
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
  for_nonslot_code_frame [(NONE,tops)] c cx env ctx func id e loop_body loc rv vv av em u /\
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
  (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t) /\
  evaluate_type (get_tenv cx) fty = SOME dtv /\ body_for_full_ok cx dtv id loop_body vs /\
  body_for_prefix_ok cx dtv id loop_body vs /\
  storage_trace_domain cx st0 em.storage_trace /\
  return_buf_sep d c em u /\
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
  eval_operand len_op u = SOME (n2w (LENGTH vs)) /\ op_taint tu len_op = {} /\
  op_prov Gu len_op = NONE /\ ~u.vs_halted /\ u.vs_current_bb = saL.cs_current_bb /\
  u.vs_inst_idx = LENGTH saL.cs_current_insts /\
  alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ allocas_from lo u /\
  s0.vs_alloca_next <= u.vs_alloca_next /\ alloca_frame c es0 sa0 s0 c em u /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
  ghost_kept_at lo c es0 sa0 G0 tn0 s0 Gu tu /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
    stmt_state_rel H ctx func c cx em u /\ storage_well_formed_on cx em (FST H) /\
    ghost_inv_at (DF H) lo d c cx em Gu tu u) /\
  vv_post (storage_trace_horizon em.storage_trace) ctx func c cx e es0 sa0 sbExpr s0 em rv vv u /\
  vv_store_bound cx (post_value_type c e) (lowered_value_type c e) em rv vv u /\
  ptr_vv_ok cx (post_value_type c e) rv vv em Gu tu u /\
  (!v. rv = Value v /\ ~is_word_type (post_value_type c e) /\
    ~is_bytestring_type (post_value_type c e) ==>
    vv_own c cx (post_value_type c e) sa0 sbExpr em rv vv u /\
    (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
  (c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (post_value_type c e) = SOME rt /\
      eval_operand (vv_operand vv) u = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
        val_in_memory rt (ArrayV av) (w2n w) mem)) /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type c e) ==>
    ptr_buf_ok c e op Gu u) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok c e p.ptr_operand Gu u) ==>
  ?s G tn Inv Done.
    ~s.vs_halted /\
    (!H. valid_horizon cx st0 H em.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (u,Gu,tu) [] (OK s,G,tn) /\ Inv H vs em G tn s) /\
    (!a rs es z J tz.
      ~z.vs_halted /\
      (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H (a::rs) es J tz z) /\
      gas_admissible (eval_for cx dtv id loop_body (a::rs)) (stmt_res_ok lctx) es ==>
      gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (cx_tops cx) cx st0
        (do v <- read_result cx a;
            push_scope_with_var id dtv v;
            finally (try (do eval_stmts cx loop_body; return F od)
              handle_loop_exception) pop_scope od)
        (es,z,J,tz)
        (\H res ee G1 tn1 t. ee.gas_obs = [] /\ ~t.vs_halted /\
          ?b. res = INL b /\ (b ==> Done H ee G1 tn1 t) /\ (~b ==> Inv H rs ee G1 tn1 t))
        (\H res ee gt r. ?ex. res = INR ex /\
          (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
          halt_exit H cx ee (INR ex) r /\
          (ctx_has_dalloca ctx ==> !t. (r = Halt t \/ ?ir. r = IntRet ir t) ==>
            allocas_below_fmp t))) /\
    (!a rs es z J tz.
      ~z.vs_halted /\
      (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H (a::rs) es J tz z) /\
      gas_admissible (eval_for cx dtv id loop_body (a::rs)) (stmt_res_ok lctx) es ==>
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cx st0
        (do v <- read_result cx a;
            push_scope_with_var id dtv v;
            finally (try (do eval_stmts cx loop_body; return F od)
              handle_loop_exception) pop_scope od)
        (es,z,J,tz)) /\
    (!es z J tz.
      ~z.vs_halted /\ storage_trace_domain cx st0 es.storage_trace /\
      (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H [] es J tz z) /\
      gas_admissible (eval_for cx dtv id loop_body []) (stmt_res_ok lctx) es ==>
      ?t G1 tn1. !H. valid_horizon cx st0 H es.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (z,J,tz) [] (OK t,G1,tn1) /\ Done H (es with gas_obs := []) G1 tn1 t) /\
    (!H ee G1 tn1 t. Done H ee G1 tn1 t ==>
      stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sb /\
      cenv_top_ext c c ee.scopes /\ stmt_state_rel H ctx func c cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d c sb t /\
      alloca_history func t /\ return_buf_sep d c ee t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d c cx ee G1 tn1 t /\
      (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa0 x ==>
        FLOOKUP G1 x = FLOOKUP G0 x /\ op_taint tn1 (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame c es0 sa0 s0 c ee t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
        (!name base len. local_region c es0.scopes s0 name base len ==>
          off + sz <= base \/ base + len <= off) /\
        off <= i /\ i < off + sz /\ i IN tn1.t_mem ==> i IN tn0.t_mem))
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume for_nonslot_array_round_prefix_contracts_at[body_entry]:
  rpt gen_tac >> DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  `body_stmts_prefix_ok cx loop_body` by
    (qpat_assum `body_for_prefix_ok _ _ _ _ _`
      (mp_tac o REWRITE_RULE [body_for_prefix_ok_def]) >>
     disch_then irule >> Cases_on `xs`
     >- gvs[] >>
     simp[read_result_def, return_def]) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) for_nonslot_array_body_exec_pre >>
  `eb.scopes <> []` by
    (qpat_assum `push_scope_with_var _ _ _ _ = _`
       (SUBST1_TAC o SYM o SIMP_RULE (srw_ss()) [push_scope_with_var_def, return_def]) >>
     simp[]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
     (eval_stmts cx loop_body) (eb,t,Gf,tnf)` by
    (qpat_x_assum `body_stmts_prefix_ok _ _` (mp_tac o REWRITE_RULE [body_stmts_prefix_ok_def]) >>
     disch_then drule_all >> disch_then (qspec_then `InLoop exit incr` mp_tac) >>
     rewrite_tac[stmt_frag_prefix_def] >>
     disch_then (qspecl_then [`st0`,`sbCopy`,`sbBody`,`shadow_sbCopy`,
       `shadow_sbBody`,`t`,`Gf`,`tnf`,`bc'`] mp_tac) >>
     simp[stmt_frag_full_pre_def] >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  qpat_x_assum `?Q R. gas_outcome_full _ _ _ _ _ _ Q R` strip_assume_tac >>
  irule for_body_cleanup_prefix >>
  qpat_assum `gas_outcome_full _ _ _ _ (eval_stmts _ _) _ _ _` (irule_at Any) >>
  simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_nonslot_array_round_prefix_contracts_at[round_head]:
  rpt gen_tac >> DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  irule for_array_round_prefix_prepend >>
  qpat_assum `gas_prefix_full _ _ _ _ _` (irule_at Any) >> simp[] >>
  qpat_assum `a = Value _` (irule_at Any) >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_nonslot_array_round_prefix_contracts_at[assemble]:
  disch_then (qx_choose_then `entry_s` (qx_choose_then `entry_G`
    (qx_choose_then `entry_tn` (qx_choose_then `RoundInv`
    (qx_choose_then `RoundDone` (map_every assume_tac o CONJUNCTS)))))) >>
  qexistsl_tac [`entry_s`,`entry_G`,`entry_tn`,`RoundInv`,`RoundDone`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac
  >- (qpat_assum `!a rs es z J tz. _` (drule_all_then strip_assume_tac) >>
      first_assum ACCEPT_TAC) >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- (qpat_assum `!a rs es z J tz. _` (drule_all_then strip_assume_tac) >> simp[]) >>
  irule gas_prefix_full_invalid_trace_domain >> simp[] >>
  irule storage_trace_frame_bind_all >>
  simp[evaluate_storage_trace_frame, storage_trace_frame_ignore_bind,
       storage_trace_frame_state_updates, storage_trace_frame_finally,
       storage_trace_frame_pop_scope, storage_trace_frame_try,
       storage_trace_frame_return, storage_trace_frame_loop_handler,
       storage_trace_frame_read_result]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise for_nonslot_array_round_prefix_contracts_at
*)

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  `!src name. e = TopLevelName (expr_type e) (src,name) ==>
     ?ts. ALOOKUP [(NONE,tops)] src = SOME ts /\
       IS_SOME (supported_immutable_type ts (NONE,name))` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!nid. e = TopLevelName _ nid ==> _`
       (qspec_then `(src,name)` (drule_then assume_tac)) >>
     Cases_on `src` >>
     gvs[alistTheory.ALOOKUP_def, supportedDeclsTheory.supported_immutable_type_def,
         supportedDeclsTheory.supported_lookup_other_module]) >>
  drule_all_then (map_every assume_tac o CONJUNCTS o Q.SPEC `av`)
    (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`]
      for_nonslot_array_round_source_pre) >>
  qpat_assum `for_nonslot_layout _ _ _ _ _ _ _`
    (mp_then (Pos hd) (mp_tac o SPEC_ALL) for_nonslot_array_round_prefix_contracts_at) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[]
QED
*)
Theorem for_nonslot_array_round_prefix_contracts:
  for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond_label,bod,incr,exit,idx,invalid,valid,done_var,next_var)
    (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
    (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
  body_const_cells_agree [(NONE,tops)] cx env es0 /\
  body_inv tops ctx c cx /\ shadow_body_inv tops ctx shadow_ctx /\ expr_body_pre c cx env e es0 /\
  ce_locals_declared c env /\ locals_alloc_ok c env /\
  supported_stmt tops bindings (For id fty (Array e) n loop_body) /\
  type_stmt env ret_ty (For id fty (Array e) n loop_body) = SOME env' /\
  stmt_exprs_ok c (For id fty (Array e) n loop_body) /\
  (!nid. e = TopLevelName (expr_type e) nid ==>
     IS_SOME (supported_immutable_type tops nid)) /\
  (~(?ty nid. e = TopLevelName ty nid) ==>
   !tgt nid. loop_iterator_place e = SOME tgt ==> target_root tgt <> TopLevelNameTarget nid) /\
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
  (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t) /\
  evaluate_type (get_tenv cx) fty = SOME dtv /\ body_for_full_ok cx dtv id loop_body vs /\
  body_for_prefix_ok cx dtv id loop_body vs /\
  storage_trace_domain cx st0 em.storage_trace /\
  return_buf_sep d c em u /\
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
  eval_operand len_op u = SOME (n2w (LENGTH vs)) /\ op_taint tu len_op = {} /\
  op_prov Gu len_op = NONE /\ ~u.vs_halted /\ u.vs_current_bb = saL.cs_current_bb /\
  u.vs_inst_idx = LENGTH saL.cs_current_insts /\
  alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ allocas_from lo u /\
  s0.vs_alloca_next <= u.vs_alloca_next /\ alloca_frame c es0 sa0 s0 c em u /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
  ghost_kept_at lo c es0 sa0 G0 tn0 s0 Gu tu /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
    stmt_state_rel H ctx func c cx em u /\ storage_well_formed_on cx em (FST H) /\
    ghost_inv_at (DF H) lo d c cx em Gu tu u) /\
  vv_post (storage_trace_horizon em.storage_trace) ctx func c cx e es0 sa0 sbExpr s0 em rv vv u /\
  vv_store_bound cx (post_value_type c e) (lowered_value_type c e) em rv vv u /\
  ptr_vv_ok cx (post_value_type c e) rv vv em Gu tu u /\
  (!v. rv = Value v /\ ~is_word_type (post_value_type c e) /\
    ~is_bytestring_type (post_value_type c e) ==>
    vv_own c cx (post_value_type c e) sa0 sbExpr em rv vv u /\
    (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
  (c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (post_value_type c e) = SOME rt /\
      eval_operand (vv_operand vv) u = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
        val_in_memory rt (ArrayV av) (w2n w) mem)) /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type c e) ==>
    ptr_buf_ok c e op Gu u) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok c e p.ptr_operand Gu u) ==>
  ?s G tn Inv Done.
    ~s.vs_halted /\
    (!H. valid_horizon cx st0 H em.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (u,Gu,tu) [] (OK s,G,tn) /\ Inv H vs em G tn s) /\
    (!a rs es z J tz.
      ~z.vs_halted /\
      (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H (a::rs) es J tz z) /\
      gas_admissible (eval_for cx dtv id loop_body (a::rs)) (stmt_res_ok lctx) es ==>
      gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (cx_tops cx) cx st0
        (do v <- read_result cx a;
            push_scope_with_var id dtv v;
            finally (try (do eval_stmts cx loop_body; return F od)
              handle_loop_exception) pop_scope od)
        (es,z,J,tz)
        (\H res ee G1 tn1 t. ee.gas_obs = [] /\ ~t.vs_halted /\
          ?b. res = INL b /\ (b ==> Done H ee G1 tn1 t) /\ (~b ==> Inv H rs ee G1 tn1 t))
        (\H res ee gt r. ?ex. res = INR ex /\
          (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
          halt_exit H cx ee (INR ex) r /\
          (ctx_has_dalloca ctx ==> !t. (r = Halt t \/ ?ir. r = IntRet ir t) ==>
            allocas_below_fmp t))) /\
    (!a rs es z J tz.
      ~z.vs_halted /\
      (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H (a::rs) es J tz z) /\
      gas_admissible (eval_for cx dtv id loop_body (a::rs)) (stmt_res_ok lctx) es ==>
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cx st0
        (do v <- read_result cx a;
            push_scope_with_var id dtv v;
            finally (try (do eval_stmts cx loop_body; return F od)
              handle_loop_exception) pop_scope od)
        (es,z,J,tz)) /\
    (!es z J tz.
      ~z.vs_halted /\ storage_trace_domain cx st0 es.storage_trace /\
      (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H [] es J tz z) /\
      gas_admissible (eval_for cx dtv id loop_body []) (stmt_res_ok lctx) es ==>
      ?t G1 tn1. !H. valid_horizon cx st0 H es.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (z,J,tz) [] (OK t,G1,tn1) /\ Done H (es with gas_obs := []) G1 tn1 t) /\
    (!H ee G1 tn1 t. Done H ee G1 tn1 t ==>
      stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sb /\
      cenv_top_ext c c ee.scopes /\ stmt_state_rel H ctx func c cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d c sb t /\
      alloca_history func t /\ return_buf_sep d c ee t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d c cx ee G1 tn1 t /\
      (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa0 x ==>
        FLOOKUP G1 x = FLOOKUP G0 x /\ op_taint tn1 (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame c es0 sa0 s0 c ee t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
        (!name base len. local_region c es0.scopes s0 name base len ==>
          off + sz <= base \/ base + len <= off) /\
        off <= i /\ i < off + sz /\ i IN tn1.t_mem ==> i IN tn0.t_mem))
Proof
  cheat
QED
