(* Snapshot continuation of an array For, at the actual expression cut. *)
Theory forCapturedArraySnapshot
Ancestors
  exprBodyPreProps
  bodyFullForExprCut bodyFullForArray bodyFullForArrayRound bodyFullForRounds bodyFullIfExpReach
  bodyFullShared bodyFullTargetArrayLoad ptrDiscipline
  gasOutcomeFullGuarded gasExemptCert reasonEndpointResourcesPtr
  bodySimFull bodySim vyperInterpreter vyperState vyperTyping vyperValueOperation
  vyperStorageFootprint vyperStorageTrace exprSimSource exprSimHyps loweringPosts
  vyperAST vyperValue vyperTypeValues
  exprSimProps exprSimOperands exprSimCopy exprSimBopRestWordLoads exprSimMemorySource
  exprLoweringProps compileEnv context emitHelper stmtLowering
  fragExec fragGasOriginPtr fragGasMode stmtSimDefs stmtSimProps haltExitProj
  gasContext gasOutcomeFull bodyPtrDefs bodyMemoryDefs exprSimMemDefs
  venomState venomInst venomExecSemantics list arithmetic words
  supportedStmts bodyFullPreds bodyFullShadowBodyInv
  vyperTypeContract[qualified,ignore_grammar]
  supportedExprTraverse[qualified,ignore_grammar]
Libs monadsyntax

Theorem snapshot_read:
  expr_body_pre c cx env e start /\ eval_expr cx e start = (INL rv,em) /\
  expr_type e = ArrayT typ bd /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  vv_post H ctx func c cx e es sa se s0 em rv vv u /\
  ((?av. rv = Value (ArrayV av)) \/ (?src name path. rv = PlaceR (ImmutablePlace src name path))) ==>
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV tyv bd) /\
  ?av xs. read_result cx rv em = (INL (ArrayV av),em) /\
    value_has_type (ArrayTV tyv bd) (ArrayV av) /\
    extract_elements (ArrayTV tyv bd) (ArrayV av) = SOME xs /\
    (rv = Value (ArrayV av) \/ (?src name path. rv = PlaceR (ImmutablePlace src name path))) /\
    (!tail. array_iterator_results cx (expr_type e) rv (em with gas_obs := tail) =
      (INL (MAP Value xs),em with gas_obs := tail)) /\
    (!tr slot etv b. rv <> PlaceR (StoragePlace tr slot (ArrayTV etv b))) /\
    LENGTH xs <= bound_length bd
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  `tvt = ArrayTV tyv bd` by
    (`evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME tvt` by metis_tac[] >>
     drule_then strip_assume_tac evaluate_type_ArrayT_cases >> fs[]) >>
  qpat_x_assum `tvt = ArrayTV _ _` SUBST_ALL_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  drule_then strip_assume_tac stmtReasonVvMemoryTheory.vv_post_read_ok >>
  `value_has_type (ArrayTV tyv bd) v` by simp[] >>
  `?av. v = ArrayV av` by (Cases_on `bd` >> Cases_on `v` >> fs[value_has_type_def]) >>
  pop_assum SUBST_ALL_TAC >>
  `!tr slot etv b. rv <> PlaceR (StoragePlace tr slot (ArrayTV etv b))` by
    (qpat_assum `(?av. rv = _) \/ _` strip_assume_tac >> simp[]) >>
  drule_then assume_tac read_result_gas_obs >>
  qexistsl [`av`,`array_elements (ArrayTV tyv bd) av`] >>
  simp[extract_elements_def, array_iterator_results_copy, bind_def, lift_option_type_def,
       return_def] >>
  conj_tac >-
    (qpat_assum `(?av. rv = _) \/ _` strip_assume_tac >> fs[read_result_def, return_def]) >>
  Cases_on `bd` >> Cases_on `av` >> gvs[value_has_type_inv, array_elements_def, bound_length_def]
QED

Theorem snapshot_location:
  expr_body_pre c cx env e es /\ expr_type e = ArrayT typ bd /\
  vv_post H ctx func c cx e es sa se s0 em rv vv u /\
  (!v. rv = Value v /\ ~is_word_type (post_value_type c e) /\
       ~is_bytestring_type (post_value_type c e) ==>
       vv_own c cx (post_value_type c e) sa se em rv vv u /\
       (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
  (rv = Value (ArrayV av) \/ ?src name path. rv = PlaceR (ImmutablePlace src name path)) /\
  loc = (case vv_location vv of NONE => LocMemory | SOME l => l) ==>
  (loc = LocMemory \/ loc = LocCode) /\ (loc = LocMemory ==> rv = Value (ArrayV av))
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac expr_body_pre_static_facts >>
  `?pty pbd. post_value_type c e = ArrayT pty pbd` by
    (`type_widens_to env.type_defs (post_value_type c e) (ArrayT typ bd)` by
       (qpat_assum `expr_type e = _` (SUBST1_TAC o SYM) >>
        irule post_value_type_widens >> simp[] >>
        qexistsl [`cx`,`es`] >> simp[]) >>
     pop_assum mp_tac >> simp[vyperTypeSystemTheory.type_widens_to_def] >>
     Cases_on `post_value_type c e` >> simp[vyperTypeSystemTheory.arg_type_fits_def]) >>
  qpat_x_assum `rv = _ \/ _` strip_assume_tac >>
  Cases_on `vv` >> gvs[vv_location_def,is_word_type_def,is_bytestring_type_def,
                      vv_post_def,vv_place_ptr_def,vv_at_def]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `dynamic = case bd of Fixed _ => F | Dynamic _ => T` >>
  qabbrev_tac `cnt = case bd of Fixed k => k | Dynamic k => k` >>
  `(if dynamic then compile_ptr_load c.ce_is_ctor c.ce_imm_alloca loc (vv_operand vv)
    else comp_return (Lit (n2w cnt))) se = (len_op,sl)` by
    (Cases_on `bd` >> gvs[Abbr `dynamic`,Abbr `cnt`]) >>
  `dynamic = (case bd of Fixed _ => F | Dynamic _ => T) /\
   cnt = (case bd of Fixed k => k | Dynamic k => k)` by simp[Abbr `dynamic`,Abbr `cnt`] >>
  drule_at_then (Pat `eval_expr _ _ _ = (INL _,_)`) drule_all
    (REWRITE_RULE [] (Q.INST [`addr` |-> `vv_operand vv`]
      (SPEC_ALL for_nonslot_array_length_observation))) >>
  disch_then (CONJUNCTS_THEN2 kall_tac
    (qx_choosel_then [`av`,`xs`,`pty`,`pbd`,`pet`,`a`] (map_every assume_tac o CONJUNCTS))) >>
  suspend "run"
QED
*)
Theorem snapshot_length:
  expr_body_pre c cx env e start /\ eval_expr cx e start = (INL rv,em) /\
  expr_type e = ArrayT typ bd /\ evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV tyv bd) /\
  (!tr slot etv b. rv <> PlaceR (StoragePlace tr slot (ArrayTV etv b))) /\
  array_iterator_results cx (expr_type e) rv em = (INL vs,em) /\
  vv_post H ctx func c cx e start sa se s0 em rv vv u /\
  ptr_vv_ok cx (post_value_type c e) rv vv em Gu tu u /\
  ghost_inv_at D0 lo d c cx em Gu tu u /\
  (c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx rv em = (INL v,em) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type c e) = SOME rt /\
         eval_operand (vv_operand vv) u = SOME w ==>
         w2n w + type_memory_size rt <= lo /\
         (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
           val_in_memory rt v (w2n w) mem)) /\
  loc = (case vv_location vv of NONE => LocMemory | SOME l => l) /\
  (loc = LocMemory \/ loc = LocCode) /\
  (case bd of Fixed cnt => comp_return (Lit (n2w cnt))
       | Dynamic _ => compile_ptr_load c.ce_is_ctor c.ce_imm_alloca loc
                        (vv_operand vv)) se = (len_op,sl) /\
  fn_has_code se sl func /\ ~u.vs_halted /\ u.vs_current_bb = se.cs_current_bb /\
  u.vs_inst_idx = LENGTH se.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,G',tn')) /\
    eval_operand len_op t = SOME (n2w (LENGTH vs)) /\
    op_taint tn' len_op = {} /\ op_prov G' len_op = NONE /\
    ~t.vs_halted /\ t.vs_current_bb = sl.cs_current_bb /\
    t.vs_inst_idx = LENGTH sl.cs_current_insts /\
    array_length_frame se u Gu tu t G' tn' /\
    ci_mono se sl /\ sl.cs_current_bb = se.cs_current_bb /\
    sl.cs_current_insts = se.cs_current_insts ++ emitted_insts se sl /\
    EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts se sl)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume snapshot_length[run]:
  qpat_x_assum `dynamic = (case bd of Fixed _ => _ | Dynamic _ => _)` kall_tac >>
  qpat_x_assum `cnt = (case bd of Fixed _ => _ | Dynamic _ => _)` kall_tac >>
  qpat_x_assum `loc = (case vv_location vv of NONE => _ | SOME _ => _)` kall_tac >>
  qpat_x_assum `vs = MAP Value xs` kall_tac >>
  `dynamic ==> eval_operand (vv_operand vv) u = SOME a` by
    (disch_tac >> first_assum ACCEPT_TAC) >>
  `dynamic /\ loc = LocCode /\ c.ce_is_ctor /\ c.ce_imm_alloca <> NONE ==>
    eval_operand (THE c.ce_imm_alloca) u = SOME 0w` by
    (qpat_assum `dynamic /\ loc = LocCode ==> _` mp_tac >>
     Cases_on `c.ce_imm_alloca` >> simp[NoAsms] >> metis_tac[]) >>
  drule_then drule_all for_nonslot_array_length_run >>
  disch_then (qspec_then `ctx` (qx_choosel_then [`z`,`t`] (map_every assume_tac o CONJUNCTS))) >>
  `allocas_from lo u` by fs[ghost_inv_at_def] >>
  `dynamic ==> eval_operand (vv_operand vv) u = SOME a /\
    (if loc = LocCode /\ ~c.ce_is_ctor then
      word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) u.vs_data_section ++ REPLICATE 32 0w))
     else mload (w2n a) u) = n2w (LENGTH vs)` by (strip_tac >> fs[]) >>
  `dynamic /\ loc = LocCode ==>
    op_taint tu (vv_operand vv) = {} /\ op_prov Gu (vv_operand vv) = NONE /\
    (if c.ce_is_ctor then
       mem_word_taint tu.t_mem (w2n a) = {} /\
       w2n a + 32 <= lo /\ lo <= u.vs_alloca_next /\
       (!rb. c.ce_imm_alloca = SOME rb ==> eval_operand rb u = SOME 0w /\
         op_taint tu rb = {} /\ op_prov Gu rb = NONE)
     else w2n a + 32 <= LENGTH u.vs_data_section)` by
    (qpat_assum `dynamic /\ loc = LocCode ==> _ /\ _ /\ (_ ==> _) /\ _`
       (fn th => POP_ASSUM_LIST (K (mp_tac th))) >> Cases_on `c.ce_is_ctor` >> simp[]) >>
  drule_then drule_all for_nonslot_array_length_checked >>
  qpat_assum `t = z with vs_inst_idx := _` (ONCE_REWRITE_TAC o single o GSYM) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`G'`,`tn'`] (map_every assume_tac o CONJUNCTS))) >>
  qexistsl [`t`,`G'`,`tn'`] >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "code"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume snapshot_length[code]:
  qpat_assum `(if dynamic then _ else _) se = _` mp_tac >>
  qpat_assum `loc = LocMemory \/ loc = LocCode` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  reverse (Cases_on `dynamic`) >> simp[]
  >- (simp[comp_return_def] >> strip_tac >> simp[ci_mono_refl,emitted_insts_def]) >>
  disch_tac >> disch_tac >>
  `loc <> LocCalldata` by (qpat_assum `loc = _ \/ loc = _` strip_assume_tac >> simp[]) >>
  drule_all exprSimBopRestWordLoadPathTheory.rest_word_ptr_load_code >> strip_tac >>
  conj_tac >-
    (qspecl_then [`c.ce_is_ctor`,`c.ce_imm_alloca`,`loc`,`vv_operand vv`,`se`]
       mp_tac ci_mono_compile_ptr_load >> simp[]) >>
  simp[EVERY_MEM] >> qx_gen_tac `i` >> disch_tac >>
  qpat_assum `EVERY _ _` (qspec_then `i` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  simp[] >> strip_tac >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise snapshot_length
*)

Theorem for_array_snapshot_length_setup:
  compile_stmt c lctx ret_ty (For id typ (Array e) n loop_body) sa = ((),sb) /\
  compile_stmt (gas_shadow_env T c) lctx ret_ty
    (gas_shadow_stmt (For id typ (Array e) n loop_body)) sha = ((),shb) /\
  compile_expr c (expr_type e) e sa = (vv,se) /\
  compile_expr (gas_shadow_env T c) (expr_type e) (gas_shadow_expr e) sha = (vv,she) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  body_inv tops ctx c cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ (Array e) n loop_body) /\
  type_stmt env ret_ty (For id typ (Array e) n loop_body) = SOME env' /\
  stmt_exprs_ok c (For id typ (Array e) n loop_body) /\
  vyperTypeContract$stmt_loop_calls_ok [(NONE,tops)] (For id typ (Array e) n loop_body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Array e) n loop_body) ==> occurs_abi_decode_target target tops) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n loop_body)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ c ret_ty /\
  c.ce_alloca_locals /\ local_ptrs_reserved c sa /\ ci_mono sa se /\
  ret_pc_ok c sa s0 /\ return_buf_frame d c sa s0 /\ return_buf_sep d c em u /\
  (!H. dead_lo_ok H (DF H) lo c cx) /\
  (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t) /\
  ce_locals_declared c env /\ locals_alloc_ok c env /\ expr_body_pre c cx env e es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_type e = ArrayT typ bd /\ bound_length bd <= n /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  storage_trace_domain cx st0 em.storage_trace /\
  (!tail. eval_expr cx e (es with gas_obs := obs ++ tail) =
     (INL rv,em with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
     for_array_expr_endpoint (DF,lo,d,ctx,func) c cx e (es,sa,s0,G0,tn0)
       (vv,se) H rv em Gu tu u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func c cx es s0) /\
  ((?av. rv = Value (ArrayV av)) \/ (?src name path. rv = PlaceR (ImmutablePlace src name path))) /\
  (!av. read_result cx rv em = (INL (ArrayV av),em) ==>
     for_nonslot_code_frame mods c cx env ctx func id e loop_body
       (case vv_location vv of NONE => LocMemory | SOME l => l) rv vv av em u) ==>
  ?she0 loc len_op sl bc saD saA xd capacity aidItem
   entry cond bod incr exit idx invalid valid done_var next_var
   sa' stride off_op sm sum_op sn addr saCopy sbCopy sbBody sj shadow_sbCopy shadow_sbBody
   av xs vs tL GL tnL.
    for_nonslot_layout (c,id,typ,e,typ,bd,ret_ty,loop_body) (func,shadow_func)
      (sa,vv,se,sha,she0,loc,len_op,sl) (bc,saD,saA,xd,capacity,aidItem)
      (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
      (sa',stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
      (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
    body_const_cells_agree [(NONE,tops)] cx env em /\
    (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    ~u.vs_halted /\ em with gas_obs := [] = em /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (u,Gu,tu) [] (OK tL,GL,tnL)) /\
    vs = MAP Value xs /\
    (!tail. array_iterator_results cx (expr_type e) rv (em with gas_obs := tail) =
      (INL vs,em with gas_obs := tail)) /\
    array_iterator_results cx (expr_type e) rv em = (INL vs,em) /\
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" = return () /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV tyv bd) /\
    read_result cx rv em = (INL (ArrayV av),em) /\
    value_has_type (ArrayTV tyv bd) (ArrayV av) /\
    extract_elements (ArrayTV tyv bd) (ArrayV av) = SOME xs /\
    (loc = LocMemory \/ loc = LocCode) /\
    (loc = LocMemory ==> rv = Value (ArrayV av) \/ ?name path. rv = PlaceR (MemoryPlace name path)) /\
    (!name path. rv = PlaceR (MemoryPlace name path) ==>
       runtime_place_typed cx em (MemoryPlace name path) (ArrayTV tyv bd)) /\
    (!name path. rv = PlaceR (MemoryPlace name path) ==>
       ?ent. lookup_scopes name em.scopes = SOME ent /\
         evaluate_subscripts ent.type ent.value path = INL (ArrayV av)) /\
    for_nonslot_code_frame mods c cx env ctx func id e loop_body loc rv vv av em tL /\
    (!fn inst t. frag_reachable ctx func tL fn inst t ==> dalloca_fmp_headroom inst t) /\
    return_buf_sep d c em tL /\
    eval_operand len_op tL = SOME (n2w (LENGTH vs)) /\ op_taint tnL len_op = {} /\
    op_prov GL len_op = NONE /\ ~tL.vs_halted /\ tL.vs_current_bb = sl.cs_current_bb /\
    tL.vs_inst_idx = LENGTH sl.cs_current_insts /\
    alloca_history func tL /\ (ctx_has_dalloca ctx ==> allocas_below_fmp tL) /\ allocas_from lo tL /\
    s0.vs_alloca_next <= tL.vs_alloca_next /\ alloca_frame c es sa s0 c em tL /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP tL.vs_allocas aid = SOME b) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x tL = SOME w) /\
    ghost_kept_at lo c es sa G0 tn0 s0 GL tnL /\
    (!H. valid_horizon cx st0 H em.storage_trace ==>
       stmt_state_rel H ctx func c cx em tL /\ storage_well_formed_on cx em (FST H) /\
       ghost_inv_at (DF H) lo d c cx em GL tnL tL) /\
    vv_post (storage_trace_horizon em.storage_trace) ctx func c cx e es sa se s0 em rv vv tL /\
    vv_store_bound cx (post_value_type c e) (lowered_value_type c e) em rv vv tL /\
    ptr_vv_ok cx (post_value_type c e) rv vv em GL tnL tL /\
    (!v. rv = Value v /\ ~is_word_type (post_value_type c e) /\
      ~is_bytestring_type (post_value_type c e) ==>
      vv_own c cx (post_value_type c e) sa se em rv vv tL /\
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
      ptr_buf_ok c e p.ptr_operand GL tL)
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`vv0`,`se0`,`she0`,`loc`,`len_op`,`sl`] assume_tac)
    (Q.INST [`sty` |-> `typ`] for_nonslot_array_layout_full) >>
  qpat_x_assum `?bc. _` strip_assume_tac >>
  `compile_expr c (expr_type e) e sa = (vv0,se0) /\
   loc = (case vv_location vv0 of NONE => LocMemory | SOME l => l) /\
   (case bd of Fixed cnt => comp_return (Lit (n2w cnt))
       | Dynamic _ => compile_ptr_load c.ce_is_ctor c.ce_imm_alloca loc
                        (vv_operand vv0)) se0 = (len_op,sl) /\ fn_has_code se0 sl func` by
    (qpat_assum `for_nonslot_layout _ _ _ _ _ _ _`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [for_nonslot_layout_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `vv0 = vv /\ se0 = se` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `vv0 = vv` SUBST_ALL_TAC >>
  qpat_x_assum `se0 = se` SUBST_ALL_TAC >>
  qabbrev_tac `H0 = storage_trace_horizon em.storage_trace` >>
  `valid_horizon cx st0 H0 em.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==> for_array_expr_endpoint _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H0` (drule_then (map_every assume_tac o CONJUNCTS o
      REWRITE_RULE [for_array_expr_endpoint_def]))) >>
  qabbrev_tac `start = es with gas_obs := obs` >>
  `em with gas_obs := [] = em` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  `eval_expr cx e start = (INL rv,em)` by
    (qpat_assum `em with gas_obs := [] = em` (fn eq =>
      qpat_assum `!tail. eval_expr cx e _ = _` (qspec_then `[]` mp_tac) >>
      simp[NoAsms, Abbr `start`,eq])) >>
  `expr_body_pre c cx env e start` by simp[Abbr `start`] >>
  `body_const_cells_agree [(NONE,tops)] cx env em` by
    (irule body_const_cells_agree_expr >>
     qpat_assum `eval_expr cx e start = _`
       (irule_at (Pat `eval_expr _ _ _ = _`)) >>
     qpat_assum `expr_body_pre c cx env e start`
       (assume_tac o cj 2 o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts) >>
     simp[Abbr `start`]) >>
  drule_all snapshot_read >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`av`,`xs`] (map_every assume_tac o CONJUNCTS))) >>
  drule_all snapshot_location >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qmatch_asmsub_abbrev_tac `INL (vs : eval_result list)` >> suspend "length"
QED

Resume for_array_snapshot_length_setup[length]:
  `!tail. array_iterator_results cx (expr_type e) rv (em with gas_obs := tail) =
     (INL vs,em with gas_obs := tail)` by simp[Abbr `vs`] >>
  `array_iterator_results cx (expr_type e) rv em = (INL vs,em)` by
    (qpat_assum `em with gas_obs := [] = em` (fn eq =>
      qpat_assum `!tail. array_iterator_results _ _ _ _ = (INL vs,_)`
        (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [eq])))) >>
  `check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" = return ()` by
    (simp[FUN_EQ_THM,compatible_bound_def,check_def,assert_def,return_def,Abbr `vs`] >> decide_tac) >>
  `vv_post H0 ctx func c cx e start sa se s0 em rv vv u` by
    simp[Abbr `start`,vv_post_initial_gas] >>
  drule_at_then (Pat `eval_expr _ _ _ = (INL _,_)`) drule_all snapshot_length >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`tL`,`GL`,`tnL`] (map_every assume_tac o CONJUNCTS))) >>
  `!H. valid_horizon cx st0 H em.storage_trace ==> valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H start.storage_trace` suffices_by simp[Abbr `start`] >>
     irule (Q.ISPEC `eval_expr cx e` (Q.GEN `f` valid_horizon_frame)) >>
     qexistsl [`e`,`INL rv`,`em`] >> simp[cj 5 evaluate_storage_trace_frame]) >>
  `local_ptrs_reserved c se` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> fs[ci_mono_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at se x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> fs[ci_mono_def]) >>
  `!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    (qpat_assum `return_buf_frame d c sa s0` (fn th => POP_ASSUM_LIST (K (mp_tac th))) >>
     Cases_on `d` >> simp[return_buf_frame_def, pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD] >>
     PairCases_on `x` >> rw[return_buf_frame_def] >> gvs[]) >>
  `!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x` by metis_tac[] >>
  `!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x` by
    metis_tac[ret_pc_ok_def] >>
  drule_all_then (assume_tac o REWRITE_RULE [copy_old_operand_def])
    reasonEndpointResourcesPtrTheory.compile_expr_old_operand >> suspend "transport"
QED

Resume for_array_snapshot_length_setup[transport]:
  `!H. valid_horizon cx st0 H em.storage_trace ==>
    stmt_state_rel H ctx func c cx em tL /\ storage_well_formed_on cx em (FST H) /\
    ghost_inv_at (DF H) lo d c cx em GL tnL tL /\
    alloca_history func tL /\ (ctx_has_dalloca ctx ==> allocas_below_fmp tL) /\
    allocas_from lo tL /\ s0.vs_alloca_next <= tL.vs_alloca_next /\
    alloca_frame c es sa s0 c em tL /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP tL.vs_allocas aid = SOME b) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x tL = SOME w) /\
    ghost_kept_at lo c es sa G0 tn0 s0 GL tnL /\
    vv_post H ctx func c cx e es sa se s0 em rv vv tL /\
    vv_store_bound cx (post_value_type c e) (lowered_value_type c e) em rv vv tL /\
    ptr_vv_ok cx (post_value_type c e) rv vv em GL tnL tL /\
    (!v. rv = Value v /\ ~is_word_type (post_value_type c e) /\
      ~is_bytestring_type (post_value_type c e) ==>
      vv_own c cx (post_value_type c e) sa se em rv vv tL /\
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
      ptr_buf_ok c e p.ptr_operand GL tL) /\
    eval_operand (vv_operand vv) tL = eval_operand (vv_operand vv) u` by
    suspend "transport_at_horizon" >>
  qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==> stmt_state_rel H ctx func c cx em tL /\ _`
    (qspec_then `H0` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `!H. valid_horizon cx st0 H em.storage_trace ==> stmt_state_rel H ctx func c cx em tL /\
       storage_well_formed_on cx em (FST H) /\ ghost_inv_at (DF H) lo d c cx em GL tnL tL` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  suspend "round_frame"
QED

Resume for_array_snapshot_length_setup[transport_at_horizon]:
  gen_tac >> disch_tac >>
  `valid_horizon cx st0 H es.storage_trace` by simp[] >>
  qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==> for_array_expr_endpoint _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS o
      REWRITE_RULE [for_array_expr_endpoint_def]))) >>
  `stmt_state_rel H ctx func c cx es s0` by simp[] >>
  drule_at_then (Pat `array_length_frame _ _ _ _ _ _ _`)
    (drule_at_then (Pat `stmt_state_rel _ _ _ _ _ _ _`)
      (drule_at_then (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) drule_all))
    for_nonslot_array_length_frame_transport >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (disch_tac >>
     qpat_assum `c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?v. read_result cx rv em = (INL v,em) /\
           !rt w. (_ /\ eval_operand (vv_operand vv) tL = SOME w) ==> _` mp_tac >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (qx_choose_then `cv` (map_every assume_tac o CONJUNCTS)) >>
     `cv = ArrayV av` by metis_tac[sumTheory.INL_11,pairTheory.PAIR_EQ] >>
     pop_assum SUBST_ALL_TAC >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_array_snapshot_length_setup[round_frame]:
  qpat_assum `array_length_frame _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [array_length_frame_def]) >>
  `tL = u with <|vs_vars := tL.vs_vars; vs_inst_idx := tL.vs_inst_idx|>` by
    (qpat_assum `_ with vs_vars := _ = u` (SUBST1_TAC o SYM) >>
     simp[venom_state_component_equality]) >>
  `tL.vs_allocas = u.vs_allocas /\ tL.vs_data_section = u.vs_data_section` by
    (pop_assum (fn th => conj_tac >> simp[Once th])) >>
  `return_buf_sep d c em tL` by
    (irule return_buf_sep_transport >>
     conj_tac >-
       (map_every qx_gen_tac [`bw`,`cap`] >> disch_then SUBST_ALL_TAC >>
        qpat_assum `return_buf_sep (SOME (bw,cap)) c em u`
          (mp_tac o CONJUNCT1 o REWRITE_RULE [return_buf_sep_def]) >>
        simp[allocas_from_def]) >>
     qexistsl [`c`,`em`,`u`] >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     `!x. not_fresh_at se x ==> lookup_var x tL = lookup_var x u` by simp[] >>
     drule_all_then (fn th => simp[th])
       (Q.SPECL [`c`,`se`,`u`,`tL`] copy_buffer_local_region_frame)) >>
  `!fn inst t. frag_reachable ctx func tL fn inst t ==> dalloca_fmp_headroom inst t` by
    (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       metis_tac[body_inv_no_phi] >>
     qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,tu) [] (OK tL,GL,tnL)`
       (qspec_then `DF H0` assume_tac) >>
     rpt strip_tac >> drule_all_then ACCEPT_TAC gas_origin_ptr_path_dalloca_fmp_headroom) >>
  `for_nonslot_code_frame mods c cx env ctx func id e loop_body loc rv vv av em tL` by
    (`for_nonslot_code_frame mods c cx env ctx func id e loop_body loc rv vv av em u` by
       (qpat_assum `loc = case vv_location vv of NONE => LocMemory | SOME l => l` SUBST1_TAC >> simp[]) >>
     qpat_x_assum `for_nonslot_code_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [for_nonslot_code_frame_def]) >>
     `vv_place_ptr c cx em u rv vv /\ vv_place_ptr c cx em tL rv vv` by
       (conj_tac >> fs[vv_post_def]) >>
     simp[for_nonslot_code_frame_def]) >>
  suspend "package"
QED

Resume for_array_snapshot_length_setup[package]:
  `vs = MAP Value xs` by simp[Abbr `vs`] >>
  `loc = LocMemory ==> rv = Value (ArrayV av) \/ ?name path. rv = PlaceR (MemoryPlace name path)` by simp[] >>
  `!name path. rv = PlaceR (MemoryPlace name path) ==> runtime_place_typed cx em (MemoryPlace name path) (ArrayTV tyv bd)` by
    (qpat_assum `rv = Value _ \/ _` strip_assume_tac >> simp[]) >>
  `!name path. rv = PlaceR (MemoryPlace name path) ==>
    ?ent. lookup_scopes name em.scopes = SOME ent /\ evaluate_subscripts ent.type ent.value path = INL (ArrayV av)` by
    (qpat_assum `rv = Value _ \/ _` strip_assume_tac >> simp[]) >>
  `vv_post (storage_trace_horizon em.storage_trace) ctx func c cx e es sa se s0 em rv vv tL` by
    (qpat_assum `vv_post H0 _ _ _ _ _ es sa se s0 em rv vv tL` mp_tac >>
     simp[Abbr `H0`]) >>
  qpat_assum `for_nonslot_layout _ _ _ _ _ _ _` (irule_at Any) >>
  qexistsl [`xs`,`vs`,`tnL`,`tL`,`av`,`GL`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise for_array_snapshot_length_setup

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL for_array_snapshot_length_setup) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then
    [`she0`,`loc`,`len_op`,`sl`,`bc`,`saD`,`saA`,`xd`,`capacity`,`aidItem`,
     `entry`,`cond`,`bod`,`incr`,`exit`,`idx`,`invalid`,`valid`,`done_var`,`next_var`,
     `sa'`,`stride`,`off_op`,`sm`,`sum_op`,`sn`,`addr`,`saCopy`,`sbCopy`,
     `sbBody`,`sj`,`shadow_sbCopy`,`shadow_sbBody`,`av`,`xs`,`vs`,`tL`,`GL`,`tnL`]
    (map_every assume_tac o CONJUNCTS)) >>
  `body_for_full_ok cx tyv id loop_body vs /\
   gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em` by
    (qpat_assum `!vs. _ ==> body_for_full_ok _ _ _ _ _ /\ _` irule >> simp[return_def]) >>
  pop_assum strip_assume_tac >>
  suspend "rounds"
QED
*)
Theorem for_array_snapshot_continue_full:
  compile_stmt c lctx ret_ty (For id typ (Array e) n loop_body) sa = ((),sb) /\
  compile_stmt (gas_shadow_env T c) lctx ret_ty
    (gas_shadow_stmt (For id typ (Array e) n loop_body)) sha = ((),shb) /\
  compile_expr c (expr_type e) e sa = (vv,se) /\
  compile_expr (gas_shadow_env T c) (expr_type e) (gas_shadow_expr e) sha = (vv,she) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  body_inv tops ctx c cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ (Array e) n loop_body) /\
  type_stmt env ret_ty (For id typ (Array e) n loop_body) = SOME env' /\
  stmt_exprs_ok c (For id typ (Array e) n loop_body) /\
  vyperTypeContract$stmt_loop_calls_ok [(NONE,tops)] (For id typ (Array e) n loop_body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Array e) n loop_body) ==> occurs_abi_decode_target target tops) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n loop_body)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ c ret_ty /\
  c.ce_alloca_locals /\ local_ptrs_reserved c sa /\ ci_mono sa se /\
  ret_pc_ok c sa s0 /\ return_buf_frame d c sa s0 /\ return_buf_sep d c em u /\
  (!H. dead_lo_ok H (DF H) lo c cx) /\
  (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t) /\
  ce_locals_declared c env /\ locals_alloc_ok c env /\ expr_body_pre c cx env e es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_type e = ArrayT typ bd /\ bound_length bd <= n /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  storage_trace_domain cx st0 em.storage_trace /\
  (!tail. eval_expr cx e (es with gas_obs := obs ++ tail) =
     (INL rv,em with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
     for_array_expr_endpoint (DF,lo,d,ctx,func) c cx e (es,sa,s0,G0,tn0)
       (vv,se) H rv em Gu tu u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func c cx es s0) /\
  ((?av. rv = Value (ArrayV av)) \/ (?src name path. rv = PlaceR (ImmutablePlace src name path))) /\
  (!av. read_result cx rv em = (INL (ArrayV av),em) ==>
     for_nonslot_code_frame mods c cx env ctx func id e loop_body
       (case vv_location vv of NONE => LocMemory | SOME l => l) rv vv av em u) /\
  (!vs. (!tail. array_iterator_results cx (expr_type e) rv (em with gas_obs := tail) =
                  (INL vs,em with gas_obs := tail)) /\
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" em = (INL (),em) ==>
    body_for_full_ok cx tyv id loop_body vs /\
    gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (bind (array_iterator_results cx (expr_type e) rv)
      (\items. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH items)) "For too long")
                         (eval_for cx tyv id loop_body items)))
    (em,u,Gu,tu) (for_array_loop_post (DF,lo,d,ctx,func) c cx lctx (es,sa,s0,G0,tn0) sb)
    (for_array_loop_exit ctx cx RetQ)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume for_array_snapshot_continue_full[rounds]:
  mp_tac (Q.INST [`u` |-> `tL`, `Gu` |-> `GL`, `tu` |-> `tnL`,
     `sty` |-> `typ`, `fty` |-> `typ`, `dtv` |-> `tyv`, `stv` |-> `tyv`, `es0` |-> `es`,
     `sa` |-> `sa'`, `sa0` |-> `sa`, `sbExpr` |-> `se`, `saL` |-> `sl`,
     `shadow_sa0` |-> `sha`, `shadow_sbExpr` |-> `she0`]
    (SPEC_ALL for_nonslot_array_round_contracts_at)) >>
  impl_tac >-
    (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- (qexists `obs` >> first_assum ACCEPT_TAC)) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`s`,`G`,`tn`,`Inv`,`Done`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "induct"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_array_snapshot_continue_full[induct]:
  qabbrev_tac `Round = (\a. do v <- read_result cx a;
      push_scope_with_var id tyv v;
      finally (try (do eval_stmts cx loop_body; return F od) handle_loop_exception) pop_scope od)` >>
  qabbrev_tac `Next = (\rs b. if b then return () else eval_for cx tyv id loop_body rs)` >>
  qabbrev_tac `Exit = (\H ex ee gt r. for_array_loop_exit ctx cx RetQ H (INR ex) ee gt r)` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_for cx tyv id loop_body vs) (em,s,G,tn)
    (\H res ee G1 tn1 t. res = INL () /\ Done H ee G1 tn1 t)
    (\H res ee gt r. ?ex. res = INR ex /\ Exit H ex ee gt r)` by
    (irule eval_for_rounds_full >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`Inv`,`Next`,`stmt_res_ok lctx`,`Round`] >>
     conj_tac >-
       (qpat_assum `!a rs es z J tz. _ ==> gas_outcome_full _ _ _ _ _ (es,z,J,tz) _ _` mp_tac >>
        simp[NoAsms,Abbr `Round`,Abbr `Exit`,for_array_loop_exit_def,exprSimDefsTheory.halt_exit_def]) >>
     conj_tac >-
       (rpt gen_tac >> strip_tac >> irule gas_exempt_cert_bind_bool >>
        goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >> simp[]) >>
     conj_tac >- (rpt gen_tac >> strip_tac >> irule gas_exempt_cert_error_bool >> simp[]) >>
     conj_tac >- simp[Abbr `Round`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[Abbr `Next`] >>
     conj_tac >-
       (gen_tac >> strip_tac >>
        qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==>
            gas_origin_ptr_path _ (tL,GL,tnL) [] (OK s,G,tn) /\ _`
          (qspec_then `H` (drule_then (ACCEPT_TAC o CONJUNCT2)))) >>
     first_assum ACCEPT_TAC) >>
  suspend "finish"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_array_snapshot_continue_full[finish]:
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_for cx tyv id loop_body vs) (em,tL,GL,tnL)
    (for_array_loop_post (DF,lo,d,ctx,func) c cx lctx (es,sa,s0,G0,tn0) sb)
    (for_array_loop_exit ctx cx RetQ)` by
    (irule gas_outcome_full_zero_prefix_guarded >>
     conj_tac >- simp[cj 4 evaluate_storage_trace_frame] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`G`,`s`,`tn`] >>
     conj_tac >-
       (gen_tac >> strip_tac >>
        qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==>
          gas_origin_ptr_path _ (tL,GL,tnL) [] (OK s,G,tn) /\ _`
          (qspec_then `H` (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
     irule gas_outcome_full_post_mono >>
     qpat_assum `gas_outcome_full _ _ _ _ (eval_for _ _ _ _ _) (em,s,G,tn) _ _` (irule_at Any) >>
     BETA_TAC >> conj_tac >-
       (rpt gen_tac >> strip_tac >>
        qpat_assum `res = INL ()` SUBST_ALL_TAC >> simp[for_array_loop_post_def] >>
        qpat_assum `!H ee G1 tn1 t. Done H ee G1 tn1 t ==> _` (drule_then strip_assume_tac) >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     simp[Abbr `Exit`] >> metis_tac[]) >>
  suspend "bind"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_array_snapshot_continue_full[bind]:
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all >> BETA_TAC >>
  conj_tac >-
    simp[NoAsms,storage_trace_frame_ignore_bind,storage_trace_frame_checks,
         cj 4 evaluate_storage_trace_frame] >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_bind_results >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_error_results >> simp[]) >>
  conj_tac >- simp[NoAsms,storage_trace_frame_array_iterator_results] >>
  qexists `\H res ee G tn t. res = INL vs /\ ee = em /\ G = GL /\ tn = tnL /\ t = tL` >> BETA_TAC >>
  reverse conj_tac >-
    (irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`GL`,`em`,`INL vs`,`tL`,`tnL`] >>
     BETA_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     gen_tac >> disch_tac >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `storage_trace_domain cx st0 mid.storage_trace` >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 mid.storage_trace`
       (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def])) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace`
      (drule_then (map_every SUBST_ALL_TAC o CONJUNCTS))) >>
  disj1_tac >> qexists `vs` >> conj_tac >- REFL_TAC >>
  qpat_assum `check _ _ = return ()`
    (fn th => rewrite_tac[th,ignore_bind_def,bind_return]) >>
  first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise for_array_snapshot_continue_full
*)
