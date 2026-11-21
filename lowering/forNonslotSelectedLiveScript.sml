(* Loop packets which preserve the selected array, not its containing root. *)
Theory forNonslotSelectedLive
Ancestors
  bodyFullPreds bodyPtrDefs exprSimMemDefs loweringPosts stmtSimDefs
  allocaHistory whitelistForIterImmSource vyperBareGlobalName
  vyperTypeInvariants vyperTypeValues vyperValueOperation valueEncodingDefs
  fragExec fragExecMem vyperInterpreter vyperState
Libs
  monadsyntax

Theorem for_nonslot_read_immutable_path:
  read_result cx (PlaceR (ImmutablePlace src name path)) es = (INL v,es) <=>
  ?tv root. lookup_immutable cx es src name = SOME (tv,root) /\
            evaluate_subscripts tv root path = INL v
Proof
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  simp[read_result_def, read_place_def, get_immutables_def,
       get_address_immutables_def, lookup_immutable_def,
       bind_def, lift_option_type_def, lift_sum_def, return_def, raise_def] >>
  rename1 `ALOOKUP es.immutables cx.txn.target = SOME imms` >>
  Cases_on `FLOOKUP (get_source_immutables src imms) name` >>
  simp[AllCaseEqs(), return_def, raise_def] >>
  rename1 `FLOOKUP (get_source_immutables src imms) name = SOME tvroot` >>
  PairCases_on `tvroot` >>
  Cases_on `evaluate_subscripts tvroot0 tvroot1 path` >> simp[return_def,raise_def]
QED

Theorem for_nonslot_bare_immutable_lookup:
  expr_sim_inv c cx env es /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT et bd) /\
  ~cx_const_name cx (src,name) /\
  read_result cx (PlaceR (ImmutablePlace src name [])) es = (INL (ArrayV av),es) ==>
  ?tv. evaluate_type (get_tenv cx) (ArrayT et bd) = SOME tv /\
       lookup_immutable cx es src name = SOME (tv,ArrayV av)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac immutable_array_source_ready >>
  qpat_x_assum `src = c.ce_module` kall_tac >>
  `lookup_immutable cx es src name = SOME (atv,ArrayV av')` by
    simp[lookup_immutable_def] >>
  qpat_assum `read_result _ (PlaceR _) _ = _`
    (mp_tac o REWRITE_RULE [for_nonslot_read_immutable_path]) >>
  simp[evaluate_subscripts_def]
QED

(* es has the outer scopes. The machine environment and state view (cc,ee)
   are (c,es) at the condition and increment, and (bc,eb) at body entry.
   Neither the cursor nor a claim about future execution is part of live. *)
Definition for_nonslot_selected_live_def:
  for_nonslot_selected_live (D, lo, d, ctx, func, cx, c, id, env, loop_body)
    (es0, sa0, s0, G0, tn0)
    (e, sbExpr, saL, loc, vv, bd, stv, vs, rv, av, xs, em, u, Gu, tu)
    (len_op, idx, bw) (xd, dw, capacity, aidItem)
    (H, k, rs, es, cc, ee, G, tn, s) <=>
    k <= LENGTH vs /\ rs = DROP k vs /\
    LENGTH vs <= bound_length bd /\ bound_length bd < dimword (:256) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV stv bd) /\
    vs = MAP Value xs /\
    read_result cx rv em = (INL (ArrayV av),em) /\
    value_has_type (ArrayTV stv bd) (ArrayV av) /\
    extract_elements (ArrayTV stv bd) (ArrayV av) = SOME xs /\
    (!name path. rv = PlaceR (MemoryPlace name path) ==>
       runtime_place_typed cx em (MemoryPlace name path) (ArrayTV stv bd)) /\
    (!name path. rv = PlaceR (MemoryPlace name path) ==>
       ?entry. lookup_scopes name em.scopes = SOME entry /\
         evaluate_subscripts entry.type entry.value path = INL (ArrayV av)) /\
    (loc = LocMemory \/ loc = LocCode) /\
    (loc = LocMemory ==> rv = Value (ArrayV av) \/
       ?name path. rv = PlaceR (MemoryPlace name path)) /\
    vv_post H ctx func c cx e es0 sa0 sbExpr s0 em rv vv u /\
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
      ptr_buf_ok c e p.ptr_operand Gu u) /\
    (loc = LocMemory ==> !name path. rv = PlaceR (MemoryPlace name path) ==>
      OPTION_MAP (\entry. (entry.type,evaluate_subscripts entry.type entry.value path))
        (lookup_scopes name es.scopes) =
      OPTION_MAP (\entry. (entry.type,evaluate_subscripts entry.type entry.value path))
        (lookup_scopes name em.scopes)) /\
    (loc = LocCode ==>
      immutable_holds c cx (post_value_type c e) (Value (ArrayV av)) bw es s) /\
    (loc = LocCode ==> !src name path.
      rv = PlaceR (ImmutablePlace src name path) ==>
      ?tv root. lookup_immutable cx es src name = SOME (tv,root) /\
                evaluate_subscripts tv root path = INL (ArrayV av)) /\
    eval_operand (vv_operand vv) u = SOME bw /\
    eval_operand (vv_operand vv) s = SOME bw /\
    op_prov G (vv_operand vv) = op_prov Gu (vv_operand vv) /\
    op_taint tn (vv_operand vv) = {} /\
    eval_operand len_op s = SOME (n2w (LENGTH vs)) /\
    op_prov G len_op = NONE /\ op_taint tn len_op = {} /\
    lookup_var idx s = SOME (n2w k) /\ FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
    expr_sim_inv c cx env es /\ ce_locals_declared c env /\ locals_alloc_ok c env /\
    lookup_scopes id es.scopes = NONE /\
    (k <> 0 ==> body_stmts_full_ok cx loop_body) /\
    cenv_top_ext c cc ee.scopes /\
    stmt_state_rel H ctx func cc cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at D lo d cc cx ee G tn s /\
    return_buf_frame d cc sa0 s /\ ret_pc_ok cc sa0 s /\ ~s.vs_halted /\
    alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    (!fn inst t. frag_reachable ctx func s fn inst t ==> dalloca_no_wrap inst t) /\
    (* Original anchor, at entry to the whole For fragment. *)
    alloca_frame c es0 sa0 s0 cc ee s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
    (!x. not_fresh_at sa0 x ==>
      FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < sa0.cs_next_id /\
      (!name b len. local_region c es0.scopes s0 name b len ==>
        off + sz <= b \/ b + len <= off) /\
      off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem) /\
    (* Capture anchor, with the expression age for captured array bytes.
       The length operand is already reserved at saL, not necessarily at sbExpr. *)
    alloca_frame c em sbExpr u cc ee s /\
    (!aid r. FLOOKUP u.vs_allocas aid = SOME r ==> FLOOKUP s.vs_allocas aid = SOME r) /\
    (!x w. not_fresh_at saL x /\ lookup_var x u = SOME w ==> lookup_var x s = SOME w) /\
    (!name path root sz w. rv = PlaceR (MemoryPlace name path) /\
      FLOOKUP c.ce_vars name = SOME (PtrVar (Var root) sz) /\
      lookup_var root u = SOME w ==> lookup_var root s = SOME w) /\
    (!aid b len i. FLOOKUP u.vs_allocas aid = SOME (b,len) /\
      aid < sbExpr.cs_next_id /\
      (!name lb lsz. local_region c em.scopes u name lb lsz ==>
        b + len <= lb \/ lb + lsz <= b) /\
      b <= i /\ i < b + len /\ i IN tn.t_mem ==> i IN tu.t_mem) /\
    (* Item is a younger, separate allocation, not an old capture row. *)
    sa0.cs_next_id <= aidItem /\ sbExpr.cs_next_id <= aidItem /\
    w2n dw + capacity < dimword (:256) /\
    w2n dw + capacity <= s.vs_alloca_next /\
    FLOOKUP s.vs_allocas aidItem = SOME (w2n dw,capacity) /\
    lookup_var xd s = SOME dw /\ ptr_covers G tn xd s capacity /\
    (!name b len. local_region c es.scopes s name b len ==>
      w2n dw + capacity <= b \/ b + len <= w2n dw)
End

Definition for_nonslot_selected_body_entry_def:
  for_nonslot_selected_body_entry (D, lo, d, ctx, func, cx, c, id, env, loop_body)
    original captured operands (xd, dw, capacity, aidItem)
    (bc, benv, sbCopy, dtv, v) (H, k, rs, es, eb, G, tn, t) <=>
    for_nonslot_selected_live (D, lo, d, ctx, func, cx, c, id, env, loop_body)
      original captured operands (xd, dw, capacity, aidItem)
      (H, k, rs, es, bc, eb, G, tn, t) /\
    push_scope_with_var id dtv v es = (INL (),eb) /\
    TL eb.scopes = es.scopes /\ capacity = type_memory_size dtv /\
    value_has_type dtv v /\ val_wf dtv v /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    expr_sim_inv bc cx benv eb /\ ce_locals_declared bc benv /\ locals_alloc_ok bc benv /\
    body_stmts_full_ok cx loop_body /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var xd) capacity) /\
    return_buf_frame d bc sbCopy t /\ ret_pc_ok bc sbCopy t /\
    t.vs_current_bb = sbCopy.cs_current_bb /\ t.vs_inst_idx = LENGTH sbCopy.cs_current_insts
End

Theorem for_nonslot_selected_live_bare_root:
  for_nonslot_selected_live (D,lo,d,ctx,func,cx,c,id,env,loop_body)
    (es0,sa0,s0,G0,tn0)
    (e,sbExpr,saL,loc,vv,bd,stv,vs,rv,av,xs,em,u,Gu,tu)
    (len_op,idx,bw) (xd,dw,capacity,aidItem) (H,k,rs,es,cc,ee,G,tn,s) /\
  loc = LocCode /\ rv = PlaceR (ImmutablePlace src name []) /\
  expr_sim_inv c cx env em /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT et bd') /\
  ~cx_const_name cx (src,name) ==>
  lookup_immutable cx es src name = lookup_immutable cx em src name
Proof
  strip_tac >>
  qpat_x_assum `for_nonslot_selected_live _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [for_nonslot_selected_live_def]) >>
  qpat_x_assum `rv = PlaceR _` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac for_nonslot_bare_immutable_lookup >>
  `read_result cx (PlaceR (ImmutablePlace src name [])) es = (INL (ArrayV av),es)` by
    (irule (iffRL for_nonslot_read_immutable_path) >>
     qpat_assum `loc = LocCode ==> !src name path. _`
       (drule_then (qspecl_then [`src`,`name`,`[]`] mp_tac)) >> simp[]) >>
  qpat_assum `read_result _ (PlaceR _) es = _`
    (mp_then Any mp_tac for_nonslot_bare_immutable_lookup) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ es`)) >> simp[]
QED
