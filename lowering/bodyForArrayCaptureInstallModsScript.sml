(* Join the reached Array replay to its single installed condition header. *)
Theory bodyForArrayCaptureInstallMods
Ancestors
  bodyForArraySelectionMods bodyForArrayCaptureReplayMods
  bodyForArraySlotPacketMods bodyForArrayImmutablePacketMods
  bodyForArrayMemoryPacketMods bodyForArrayPacketInstallMods
  bodyForArrayInstallBackingMods bodyForArrayHeldInstallRouteMods
  bodyForArrayOwnedInstallRouteMods bodyForArrayLengthLinkedTransportMods
  bodyForArrayExprRunMods bodyFullForFacts bodyFullIfExpReach
  bodyForRangeHeaderMods typedMemoryCopy exprBodyPreProps exprBodyPreTypingProps
  exprBodyPreCallSafetyProps vyperTypeEvalStoragePreservation vyperPlaceTyping
  bodySim allocLimits vyperTypeSystem vyperTypeInvariants
  exprLoweringProps emitHelperProps context compileEnv
  stmtLoweringMono loweringPosts bodyMemoryDefs bodyFullShadowBodyInv
  bodyForArrayLengthPacketMods exprSimCopy venomExecSemantics bodyFullPostsMods
  abiArgsCompilerImage exprSafeOperandBuiltins exprSafeOperand exprLowering
  stmtSimDefs targetPlaceSim loweringStateRelDefs freshWrites
  bodyFullForArrayRound vyperAST vyperValue vyperStorageFootprint vyperStorageTrace
  vyperState words finite_map arithmetic
  bodyForArrayMemoryBaseOperandMods bodyForArrayMemoryLengthFrameMods
  bodyForArrayCaptureHeldSnapshotMods bodyForArrayCaptureOwnedSnapshotMods
  bodyForArrayHeaderMods bodyForArraySelectedPacketMods
  bodyForArrayMemoryPacketOriginMods bodyForArrayHeaderInstallMods
  vyperInterpreter bodyForArrayOriginMods bodyForArrayEntryMods fragGasOriginPtrLoop
  bodyInvSplit moduleVariableKeyProps exprSimHypsDefs supportedNameRoot
  immutableRegionTypingProps vyperBareGlobalName bodyForArrayHeldDirectSelectionMods
Libs monadsyntax

Theorem capture_install_name_fresh[local]:
  expr_sim_inv_mods mods c cx env em /\ id NOTIN FDOM env.var_types ==>
  lookup_scopes id em.scopes = NONE
Proof
  strip_tac >> drule expr_sim_inv_mods_env >>
  simp[env_consistent_def,env_scopes_consistent_def] >> strip_tac >>
  Cases_on `lookup_scopes id em.scopes` >> simp[] >>
  qpat_assum `!nm ent. lookup_scopes nm em.scopes = SOME ent ==> _`
    (drule_then mp_tac) >> simp[FLOOKUP_DEF]
QED

Theorem capture_install_capacity[local]:
  capacity = type_memory_bytes c typ /\ stmt_exprs_ok c (For id typ (Array e) n loop_body) ==>
  capacity < dimword (:256)
Proof
  simp[stmt_exprs_ok_def,Once alloc_limits_stmt_def,dimword_def] >> decide_tac
QED

Theorem capture_place_nonlabel[local]:
  compile_expr c (expr_type e) e sa = (vv,sb) /\
  loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget nid ==>
  !lbl. vv_operand vv <> Label lbl
Proof
  Cases_on `e` >>
  simp[vyperTypeContractTheory.loop_iterator_place_def, target_root_def] >>
  simp[Once compile_expr_def, compile_expr_body_def, expr_type_def] >>
  rpt strip_tac >> gvs[target_root_def]
  >- (Cases_on `FLOOKUP c.ce_module_vars nid` >> gvs[]
      >- (pairarg_tac >> gvs[vv_operand_def]) >>
      rename1 `SOME binder` >> Cases_on `binder` >>
      gvs[vv_operand_def,mk_ptr_def] >> pairarg_tac >> gvs[vv_operand_def])
  >- (drule compile_subscript_not_label >> simp[]) >>
  drule compile_attribute_safe_operand >> simp[safe_operand_def]
QED

Theorem capture_return_buf_at_start[local]:
  return_buf_frame d c sb r /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  return_buf_frame d c sa r
Proof
  Cases_on `d` >- simp[return_buf_frame_def] >>
  rename1 `return_buf_frame (SOME rb)` >> PairCases_on `rb` >>
  simp[return_buf_frame_def] >> metis_tac[]
QED

Theorem capture_reserved[local]:
  compile_expr c (expr_type e) e sa = (vv,sb) /\ local_ptrs_reserved c sa ==>
  sa.cs_next_var <= sb.cs_next_var /\ local_ptrs_reserved c sb
Proof
  strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qspecl_then [`c`,`expr_type e`,`e`,`sa`] mp_tac (cj 1 ci_mono_compile_expr_sa) >>
     simp[ci_mono_def]) >>
  fs[local_ptrs_reserved_def] >> metis_tac[not_fresh_at_mono]
QED

Theorem for_array_capture_install_mods:
  contract_inv mods exps ctx c cx /\ MEM func ctx.ctx_functions /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved c sa0 /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!h. dead_lo_ok_mods h (DF h) lo c cx) /\
  type_stmt env ret_ty (For id typ (Array e) n loop_body) = SOME env' /\
  stmt_exprs_ok c (For id typ (Array e) n loop_body) /\
  expr_body_pre_mods mods c cx env e es /\
  for_nonslot_layout (c,id,typ,e,typ,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
    addr_cut body_cut /\
  (!tail. eval_expr cx e (es with gas_obs := prefix ++ tail) =
         (INL raw,em with gas_obs := tail)) /\
  storage_trace_domain cx st0 em.storage_trace /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
       for_array_expr_landed_mods (DF,lo,d,ctx,func) mods cx c env e vv sbExpr
          (es,sa0,s0,G0,tn0) H raw em Gr traw r) ==>
  ~r.vs_halted /\ ?vs t G tn.
    compatible_bound (Dynamic n) (LENGTH vs) /\
    (!tail. array_iterator_results cx (expr_type e) raw (em with gas_obs := tail) =
         (INL vs,em with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H em.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (r,Gr,traw) [] (OK t,G,tn) /\
      for_array_entry_mods mods (DF,lo,d,ctx,func,shadow_func) cx env st0
        (es,sa0,s0,G0,tn0)
        ((c,id,typ,e,typ,bd,ret_ty,loop_body),
         (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
         (bc,saD,saA,xd,capacity,aidItem),
         (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
         addr_cut,body_cut) H vs (em with gas_obs := []) G tn t)
Proof
  PairCases_on `addr_cut` >> PairCases_on `body_cut` >> strip_tac >>
  qhdtm_assum `for_nonslot_layout`
    (strip_assume_tac o REWRITE_RULE [for_nonslot_layout_def]) >>
  drule_then strip_assume_tac type_stmt_for_projection >>
  `bound_length bd = n` by
    (drule_then strip_assume_tac type_stmt_for_array_bound >> gvs[bound_length_def]) >>
  qabbrev_tac `h0 = storage_trace_horizon em.storage_trace` >>
  `valid_horizon cx st0 h0 em.storage_trace` by fs[storage_trace_domain_def,Abbr `h0`] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> for_array_expr_landed_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [for_array_expr_landed_mods_def])) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  drule_all_then strip_assume_tac for_array_capture_replay_mods >>
  `em with gas_obs := [] = em` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e (es with gas_obs := prefix) = (INL raw,em)` by simp[] >>
  `bound_length bd <= n` by simp[] >>
  `lookup_scopes id em.scopes = NONE` by (drule_all_then ACCEPT_TAC capture_install_name_fresh) >>
  `capacity < dimword (:256)` by (drule_all_then ACCEPT_TAC capture_install_capacity) >>
  `!bb. MEM bb func.fn_blocks ==> venomExecSemantics$phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> metis_tac[body_inv_no_phi_mods]) >>
  `copy_old_operand saL (vv_operand vv)` by simp[copy_old_operand_def] >>
  drule_all_then (qx_choose_then `et` (map_every assume_tac o CONJUNCTS))
    for_array_reached_selection_mods >>
  `bound_length bd < dimword (:256)` by
    (irule typed_copy_array_count_bound >> qexistsl_tac [`typ`,`get_tenv cx`,`ArrayTV et bd`] >>
     qpat_assum `post_value_type c e = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `?vs bw capture u Gu tu. for_array_length_packet_mods mods (DF,lo,d,ctx,func,shadow_func)
      (explicit,PG) cx env st0 (es,sa0,s0,G0,tn0)
      ((c,id,typ,e,typ,bd,ret_ty,loop_body),
       (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
       (bc,saD,saA,xd,capacity,aidItem),
       (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
       (addr_cut0,addr_cut1,addr_cut2,addr_cut3,addr_cut4,addr_cut5,addr_cut6,addr_cut7,addr_cut8),
       (body_cut0,body_cut1,body_cut2,body_cut3,body_cut4))
      raw n (r,Gr,traw) (em,u,Gu,tu,bw,capture,vs) /\ (!lbl. vv_operand vv <> Label lbl)`
  suffices_by suspend "install" >>
  qpat_x_assum `(?tr slot p tgt src name tops. _) \/ _`
    (DISJ_CASES_THEN2 strip_assume_tac (DISJ_CASES_THEN2 strip_assume_tac assume_tac))
  >- suspend "slot"
  >- suspend "immutable"
  >> suspend "memory"
QED

Resume for_array_capture_install_mods[install]:
  strip_tac >>
  drule_all_then strip_assume_tac for_array_packet_install_mods >>
  qhdtm_x_assum `for_array_length_packet_mods`
    (strip_assume_tac o REWRITE_RULE [for_array_length_packet_mods_def]) >>
  qexistsl_tac [`vs`,`t`,`G`,`tn`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_array_capture_install_mods[slot]:
  rename1 `raw = PlaceR (StoragePlace tr slot (ArrayTV et bd))` >>
  `!lbl. vv_operand vv <> Label lbl` by
    (gen_tac >> metis_tac[capture_place_nonlabel]) >>
  `return_buf_frame d c sa0 r` by (drule_all_then ACCEPT_TAC capture_return_buf_at_start) >>
  `!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x` by
    fs[ret_pc_ok_def] >>
  qpat_x_assum `raw = PlaceR (StoragePlace _ _ _)` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H em.storage_trace ==>
      storage_well_formed_on cx es (FST H) /\
      vv_post_mods H ctx func c cx e es sa0 sbExpr s0 em
        (PlaceR (StoragePlace tr slot (ArrayTV et bd))) vv r /\
      ghost_inv_at_mods (DF H) lo d c cx em Gr traw r` by
    (gen_tac >> strip_tac >>
     qpat_assum `!K. valid_horizon _ _ K _ ==> for_array_expr_landed_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H` (drule_then (strip_assume_tac o REWRITE_RULE [for_array_expr_landed_mods_def]))) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `?vs u Gu tu off root path delta.
     for_array_length_packet_mods mods (DF,lo,d,ctx,func,shadow_func)
       (explicit,PG) cx env st0 (es,sa0,s0,G0,tn0)
       ((c,id,typ,e,typ,bd,ret_ty,loop_body),
        (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
        (bc,saD,saA,xd,capacity,aidItem),
        (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
        (addr_cut0,addr_cut1,addr_cut2,addr_cut3,addr_cut4,addr_cut5,addr_cut6,addr_cut7,addr_cut8),
        (body_cut0,body_cut1,body_cut2,body_cut3,body_cut4))
       (PlaceR (StoragePlace tr slot (ArrayTV et bd))) n (r,Gr,traw)
       (em,u,Gu,tu,slot,ForArraySlot tr off root path delta,vs)` by
    (irule for_array_slot_packet_mods >>
     rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE
                      (qexists `prefix` >> first_assum ACCEPT_TAC))) >>
     first_assum ACCEPT_TAC) >>
  qexistsl_tac [`vs`,`slot`,`ForArraySlot tr off root path delta`,`u`,`Gu`,`tu`] >>
  conj_tac >> first_assum ACCEPT_TAC
QED
Resume for_array_capture_install_mods[immutable]:
  rename1 `raw = PlaceR (ImmutablePlace src name path)` >>
  `target_root tgt = TopLevelNameTarget (src,name)` by
    (qpat_assum `place_access tgt _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[place_access_root,pairTheory.FST]) >>
  `!lbl. vv_operand vv <> Label lbl` by
    (gen_tac >> metis_tac[capture_place_nonlabel]) >>
  `local_ptrs_reserved c sbExpr` by (drule_all_then strip_assume_tac capture_reserved) >>
  `loc = LocCode` by fs[vv_location_def] >>
  `post_value_type c e = expr_type e` by simp[] >>
  qpat_x_assum `raw = PlaceR (ImmutablePlace _ _ _)` SUBST_ALL_TAC >>
  qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >>
  drule_all for_array_immutable_packet_mods >>
  qpat_assum `!lbl. vv_operand vv <> Label lbl` (fn th => simp[NoAsms,th]) >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[for_array_length_packet_mods_def] >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`vs`,`n2w (delta + off)`,
    `ForArrayImmutable src name path off itv delta av`,`u`,`Gu`,`tu`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume for_array_capture_install_mods[memory]:
  Q.SUBGOAL_THEN `(?v. raw = Value v) \/ (?name path. raw = PlaceR (MemoryPlace name path))`
    assume_tac
  >- (qpat_x_assum `(?name path p tgt attrs tail. raw = PlaceR (MemoryPlace name path) /\ _) \/ _`
        strip_assume_tac >> simp[] >> metis_tac[]) >>
  Q.SUBGOAL_THEN `vv_location vv = NONE \/ vv_location vv = SOME LocMemory` assume_tac
  >- (qpat_x_assum `(?name path p tgt attrs tail. raw = PlaceR (MemoryPlace name path) /\ _) \/ _`
        strip_assume_tac >> simp[vv_location_def]) >>
  `loc = LocMemory` by
    (qpat_assum `loc = _` SUBST1_TAC >> qpat_x_assum `vv_location vv = NONE \/ _` strip_assume_tac >> simp[]) >>
  `!lbl. vv_operand vv <> Label lbl` by
    (drule_all_then ACCEPT_TAC for_array_memory_base_nonlabel_mods) >>
  `sa0.cs_next_var <= sbExpr.cs_next_var /\ local_ptrs_reserved c sbExpr` by
    (drule_all_then ACCEPT_TAC capture_reserved) >>
  `(case bd of Fixed k => comp_return (Lit (n2w k))
     | Dynamic _ => compile_ptr_load c.ce_is_ctor c.ce_imm_alloca LocMemory (vv_operand vv))
    sbExpr = (len_op,saL)` by
    (qpat_assum `loc = LocMemory` (fn eq =>
       qpat_assum `(case bd of Fixed _ => _ | Dynamic _ => _) sbExpr = (len_op,saL)`
         (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp r)` by
    fs[for_array_outer_frame_mods_def,range_outer_frame_mods_def] >>
  `expr_body_pre_mods mods c cx env e (es with gas_obs := prefix)` by simp[] >>
  `vv_post_mods h0 ctx func c cx e (es with gas_obs := prefix) sa0 sbExpr s0 em raw vv r` by
    (qpat_assum `vv_post_mods h0 _ _ _ _ _ es _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms,vv_post_mods_def,locals_kept_def,popped_kept_def] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[] >>
  CONV_TAC (QUANT_CONV (QUANT_CONV
    (SWAP_EXISTS_CONV THENC QUANT_CONV
      (SWAP_EXISTS_CONV THENC QUANT_CONV SWAP_EXISTS_CONV)))) >>
  irule (INST_TYPE [alpha |-> ``:256``] for_array_memory_packet_mods) >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE (qexists `typ` >> first_assum ACCEPT_TAC))) >>
  qexistsl [`h0`,`es with gas_obs := prefix`,`sa0`,`sbExpr`,`saL`] >>
  reverse conj_tac
  >- (conj_tac
      >- (gen_tac >> strip_tac >>
          qpat_assum `!v. raw = Value v /\ _ ==> _ /\ _` (drule_all_then strip_assume_tac) >>
          first_assum ACCEPT_TAC) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`etR`,`av`,`vs`,`pe`,`pb`,`pet`,`a`,`z`,`Gz`,`tz`] >>
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  `pe = typ /\ pb = bd` by
    (qpat_x_assum `post_value_type c e = ArrayT pe pb` mp_tac >> simp[EQ_SYM_EQ]) >>
  `evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME (ArrayTV etR bd)` by
    (qpat_assum `expr_type e = ArrayT typ bd` (fn eq =>
       qpat_assum `evaluate_type _ (expr_type e) = _` (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  `pet = etR` by
    (qpat_assum `post_value_type c e = ArrayT typ bd` (fn eq =>
       qpat_assum `evaluate_type _ (post_value_type c e) = SOME (ArrayTV pet pb)`
         (mp_tac o REWRITE_RULE [eq])) >> simp[EQ_SYM_EQ]) >>
  `ptr_mem_ok cx (ArrayT typ bd) (ArrayV av) (vv_operand vv) Gz tz z` by
    (qpat_assum `post_value_type c e = ArrayT typ bd` (fn eq =>
       qpat_assum `ptr_mem_ok _ (post_value_type c e) _ _ _ _ _` (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  `(0 < type_memory_size (ArrayTV etR bd) ==>
      w2n a + type_memory_size (ArrayTV etR bd) <= z.vs_alloca_next)` by
    (disch_tac >> qpat_assum `pet = etR` (fn et_eq =>
       qpat_assum `pb = bd` (fn bd_eq =>
         qpat_assum `0 < type_memory_size _ ==> _ /\ _`
           (drule_then (ACCEPT_TAC o CONJUNCT1) o REWRITE_RULE [et_eq,bd_eq])))) >>
  `LENGTH vs <= bound_length bd` by
    (qpat_assum `bound_length bd = n` (fn th => pure_rewrite_tac [th]) >>
     qpat_assum `compatible_bound (Dynamic n) _`
       (ACCEPT_TAC o REWRITE_RULE [compatible_bound_def])) >>
  drule_all_then strip_assume_tac for_array_memory_length_frame_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "owned_route" >> suspend "held_route"
QED

Resume for_array_capture_install_mods[owned_route]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  `vv_own c cx (ArrayT typ bd) sa0 sbExpr em (Value (ArrayV av)) vv r` by
    (qpat_x_assum `!v. raw = Value v /\ _ ==> _ /\ _`
       (qspec_then `ArrayV av` mp_tac) >>
     asm_simp_tac std_ss [is_word_type_def,is_bytestring_type_def] >> simp[]) >>
  drule_all_then MATCH_ACCEPT_TAC for_array_capture_owned_snapshot_mods
QED

Resume for_array_capture_install_mods[held_route]:
  map_every qx_gen_tac [`name`,`path`] >> strip_tac >> rpt gen_tac >> strip_tac >>
  reverse (qpat_x_assum `(?nm pth p tgt attrs tail. raw = PlaceR (MemoryPlace nm pth) /\ _) \/ _`
    (DISJ_CASES_THEN2 strip_assume_tac
      (qx_choose_then `owned_value` (map_every assume_tac o CONJUNCTS))))
  >- (qpat_assum `raw = PlaceR (MemoryPlace _ _)` (fn eq =>
        qpat_assum `raw = Value _` (mp_tac o PURE_ONCE_REWRITE_RULE [eq])) >> simp[NoAsms]) >>
  qpat_x_assum `raw = PlaceR (MemoryPlace _ _)` SUBST_ALL_TAC >>
  qpat_x_assum `PlaceR (MemoryPlace _ _) = PlaceR (MemoryPlace _ _)`
    (map_every SUBST_ALL_TAC o CONJUNCTS o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (REWRITE_RULE [vv_operand_def]) >>
  pure_rewrite_tac[vv_operand_def] >>
  drule_all_then MATCH_ACCEPT_TAC for_array_capture_held_snapshot_mods
QED

Finalise for_array_capture_install_mods

val _ = Parse.hide "body";

Theorem capture_reached_callback_mods[local]:
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  (!tenv s tyv t s1 vs t1 s2 u t2.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tyv,t) /\
     eval_iterator cx (Array e) s1 = (INL vs,t1) /\
     check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s2 = (INL u,t2) ==>
     body_for_full_ok_mods mods exps cx tyv id body vs) /\
  eval_expr cx e start = (INL raw,em) /\
  array_iterator_results cx (expr_type e) raw em = (INL vs,em) /\
  compatible_bound (Dynamic n) (LENGTH vs) ==>
  body_for_full_ok_mods mods exps cx tyv id body vs
Proof
  strip_tac >>
  `eval_iterator cx (Array e) start = (INL vs,em)` by
    simp[Once evaluate_def,bind_def] >>
  first_x_assum irule >>
  simp[lift_option_type_def,return_def,check_def,assert_def] >>
  goal_assum (drule_at Any)
QED

(* Installation does not change the source state. Static and current
   selection therefore supply the observation conjuncts at the same root. *)
Theorem capture_observation_at_entry_mods[local]:
  for_array_selector_static_mods c cx (e,sty,bd,saL)
    ((em,u,Gu,tu,dw,bw,capture),sel,w) /\
  for_array_selected_origin_mods c cx lo (sty,bd,loc) sbExpr op vs
    ((em,u,Gu,tu,dw,bw,capture),sel,w) /\
  for_array_entry_route_mods c cx lo (sty,bd,loc) (em,sbExpr,u,Gu,tu)
    (op,bw) vs capture H vs em G tn t ==>
  for_array_observation_mods c cx lo (sty,bd,loc) (em,sbExpr,u,Gu,tu)
    (op,bw) vs ((em,u,Gu,tu,dw,bw,capture),sel) H vs em G tn t
Proof
  strip_tac >> simp[for_array_observation_mods_def] >>
  Cases_on `capture` >> Cases_on `w` >>
  gvs[for_array_selector_static_mods_def,for_array_selected_origin_mods_def,
      for_array_origin_mods_def] >>
  rpt (goal_assum (drule_at Any) >> simp[])
QED

(* At the length endpoint itself, the physical route provides the origin
   geometry. The immutable prefix is supplied by the source selection. *)
Theorem capture_origin_at_length_mods[local]:
  for_array_selector_static_mods c cx (e,sty,bd,saL)
    ((em,u,Gu,tu,dw,bw,capture),sel,w) /\
  (case capture of
     ForArraySlot _ _ _ _ _ => sel = NONE
   | ForArrayOwned av => sel = SOME av
   | ForArrayHeld _ _ av => sel = SOME av
   | ForArrayImmutable _ _ _ _ _ _ _ => T) /\
  for_array_entry_route_mods c cx lo (sty,bd,loc) (em,sbExpr,u,Gu,tu)
    (op,bw) vs capture H vs em Gu tu u ==>
  for_array_selected_origin_mods c cx lo (sty,bd,loc) sbExpr op vs
    ((em,u,Gu,tu,dw,bw,capture),sel,w)
Proof
  strip_tac >>
  Cases_on `capture` >>
  gvs[for_array_selected_origin_mods_def,for_array_origin_mods_def,
      for_array_entry_route_mods_def,for_array_memory_backing_mods_def] >>
  rpt strip_tac >>
  TRY (first_assum (drule_then strip_assume_tac) >> goal_assum (drule_at Any) >> simp[] >> NO_TAC) >>
  Cases_on `w` >> gvs[for_array_selector_static_mods_def] >>
  rpt (goal_assum (drule_at Any) >> simp[])
QED

Theorem capture_install_selected_packet_mods[local]:
  for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var) addr_cut body_cut /\
  fn_inst_ids_distinct func /\ capacity < dimword (:256) /\
  bound_length bd < dimword (:256) /\
  storage_trace_domain cx st0 em.storage_trace /\ em.gas_obs = [] /\
  body_const_cells_agree_mods mods cx env em /\
  expr_sim_inv_mods mods c cx env em /\ lookup_scopes id em.scopes = NONE /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  copy_old_operand saL (vv_operand vv) /\ (!lbl. vv_operand vv <> Label lbl) /\
  for_array_length_packet_mods mods (DF,lo,d,ctx,func,shadow_func) (explicit,PG) cx env st0
    (es,sa0,s0,G0,tn0)
    ((c,id,fty,e,sty,bd,ret_ty,loop_body),
     (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
     (bc,saD,saA,xd,capacity,aidItem),
     (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),addr_cut,body_cut)
    raw n (r,Gr,traw) (em,u,Gu,tu,bw,capture,vs) /\
  body_for_full_ok_mods mods exps cx tyv id loop_body vs /\
  (!dw:256 word. for_array_selector_static_mods c cx (e,sty,bd,saL)
           ((em,u,Gu,tu,dw,bw,capture),sel,w) /\
        for_array_selector_current_mods cx ((em,u,Gu,tu,dw,bw,capture),sel,w) em) /\
  (case capture of
     ForArraySlot _ _ _ _ _ => sel = NONE
   | ForArrayOwned av => sel = SOME av
   | ForArrayHeld _ _ av => sel = SOME av
   | ForArrayImmutable _ _ _ _ _ _ _ => T) ==>
  ?t G tn. !H. valid_horizon cx st0 H em.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (r,Gr,traw) [] (OK t,G,tn) /\
    for_array_selected_entry_mods mods exps cx env st0 tyv id loop_body
      (DF,lo,d,ctx,func,shadow_func) (es,sa0,s0,G0,tn0)
      ((c,id,fty,e,sty,bd,ret_ty,loop_body),
       (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
       (bc,saD,saA,xd,capacity,aidItem),
       (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),addr_cut,body_cut)
      H vs (em with gas_obs := []) G tn t
Proof
  PairCases_on `addr_cut` >> PairCases_on `body_cut` >> strip_tac >>
  qhdtm_x_assum `for_array_length_packet_mods`
    (strip_assume_tac o REWRITE_RULE [for_array_length_packet_mods_def]) >>
  `!H. valid_horizon cx st0 H em.storage_trace ==>
       stmt_state_rel H ctx func c cx em u /\ immutable_frame_mods func c cx em u /\
       storage_well_formed_on cx em (FST H) /\ ghost_inv_at_mods (DF H) lo d c cx em Gu tu u` by
    (gen_tac >> strip_tac >>
     qpat_assum `!K. valid_horizon _ _ K _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `RouteX = for_array_entry_route_mods c cx lo (sty,bd,loc)
      (em,sbExpr,u,Gu,tu) (vv_operand vv,bw) vs capture` >>
  drule_all_then (qspecl_then [`explicit`,`RouteX`,`PG`]
    (qx_choosel_then [`dw`,`G`,`tn`,`t`] strip_assume_tac))
    for_array_header_install_mods >>
  qpat_assum `!dw. for_array_selector_static_mods _ _ _ ((_,_,_,_,dw,_,_),_,_) /\ _`
    (qspec_then `dw` strip_assume_tac) >>
  qabbrev_tac `h0 = storage_trace_horizon em.storage_trace` >>
  `valid_horizon cx st0 h0 em.storage_trace` by fs[storage_trace_domain_def,Abbr `h0`] >>
  `for_array_entry_route_mods c cx lo (sty,bd,loc) (em,sbExpr,u,Gu,tu)
     (vv_operand vv,bw) vs capture h0 vs em Gu tu u` by
     (`RouteX h0 vs em Gu tu u` suffices_by simp[Abbr `RouteX`] >>
      first_assum irule >> simp[for_array_install_frame_mods_def]) >>
  drule_all_then assume_tac capture_origin_at_length_mods >>
  `em with gas_obs := [] = em` by simp[evaluation_state_component_equality] >>
  qexistsl_tac [`t`,`G`,`tn`] >> pure_asm_rewrite_tac [] >> gen_tac >> strip_tac >>
  conj_tac
  >- (irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gu`,`u`,`tu`] >>
      conj_tac >-
        (qpat_assum `!K. valid_horizon _ _ K _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
           (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
      qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `DF H` ACCEPT_TAC)) >>
  simp[for_array_selected_entry_mods_def] >>
  qexists_tac `((em,u,Gu,tu,dw,bw,capture),sel,w)` >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qx_gen_tac `hor` >> strip_tac >>
  `RouteX hor vs em G tn t` by
    (first_assum irule >> simp[]) >>
  qpat_assum `!K. valid_horizon _ _ K _ /\ RouteX K _ _ _ _ _ ==> _`
    (drule_all_then assume_tac) >>
  `for_array_observation_mods c cx lo (sty,bd,loc) (em,sbExpr,u,Gu,tu) (vv_operand vv,bw)
    vs ((em,u,Gu,tu,dw,bw,capture),sel) hor vs em G tn t` by
    (irule capture_observation_at_entry_mods >>
     conj_tac >- (qexistsl [`e`,`saL`,`w`] >> simp[]) >>
     qpat_assum `RouteX hor _ _ _ _ _` mp_tac >> simp[Abbr `RouteX`]) >>
  qhdtm_x_assum `for_array_header_mods` mp_tac >>
  pure_rewrite_tac[for_array_selected_header_route_mods,for_array_header_mods_def] >>
  strip_tac >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem capture_immutable_root_bound_mods[local]:
  contract_inv mods exps ctx c cx /\ expr_sim_inv_mods mods c cx env em /\
  FLOOKUP c.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  lookup_immutable cx em src name = SOME (rt,root) ==>
  off + type_memory_size rt < dimword (:256)
Proof
  strip_tac >>
  drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
    contract_inv_immutable_section_layout >>
  qpat_assum `!src name off. FLOOKUP _ _ = _ <=> _`
    (qspecl_then [`src`,`name`,`off`] (drule_then strip_assume_tac o iffLR)) >>
  qhdtm_assum `immutable_region_mods`
    (strip_assume_tac o REWRITE_RULE [immutable_region_mods_def]) >>
  `MEM (VariableDecl vis Immutable name ty slot) tops` by simp[] >>
  drule_then assume_tac contract_inv_unqualified_variable_keys >>
  `~cx_const_name_mods mods (src,name)` by
    (`ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))`
       by metis_tac[] >>
     `?v t sl. supported_variable_decl tops (NONE,name) = SOME (v,Immutable,t,sl)` by
       metis_tac[supported_variable_decl_distinct_mem] >>
     qpat_x_assum `tops = _` kall_tac >>
     simp[cx_const_name_mods_def] >>
     drule_then (qspec_then `name` mp_tac) distinct_module_consts_env_names_constant >> simp[]) >>
  drule_all_then strip_assume_tac immutableRegionTypingPropsTheory.immutable_region_mods_type >>
  rename1 `FLOOKUP env.bare_globals (src,name) = SOME root_ty` >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `evaluate_type (get_tenv cx) root_ty = SOME rt` by
    (qpat_assum `lookup_immutable _ _ _ _ = _` mp_tac >>
     simp[NoAsms,lookup_immutable_def,AllCaseEqs()] >>
     disch_then (qx_choose_then `imms` strip_assume_tac) >>
     qhdtm_assum `env_consistent`
       (strip_assume_tac o REWRITE_RULE [env_consistent_def,env_immutables_consistent_def]) >>
     qpat_assum `!src id ty tv v. _`
       (qspecl_then [`src`,`name`,`root_ty`,`rt`,`root`] mp_tac) >> simp[]) >>
  qhdtm_x_assum `expr_sim_inv_mods`
    (strip_assume_tac o REWRITE_RULE [exprSimHypsDefsTheory.expr_sim_inv_mods_def]) >>
  qpat_assum `!src id ty. _ /\ (~cx_const_name_mods _ _ \/ _) ==> _`
    (qspecl_then [`src`,`name`,`root_ty`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (mp_tac o CONJUNCT2) >>
  qpat_assum `FLOOKUP c.ce_module_vars (src,name) = SOME (ImmutableLoc off)`
    (fn eq => simp[NoAsms,eq]) >>
  disch_then (qspec_then `rt` mp_tac) >> simp[]
QED

Theorem for_array_capture_install_from_direct_mods[local]:
  contract_inv mods exps ctx c cx /\ MEM func ctx.ctx_functions /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved c sa0 /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!h. dead_lo_ok_mods h (DF h) lo c cx) /\
  type_stmt env ret_ty (For id typ (Array e) n loop_body) = SOME env' /\
  stmt_exprs_ok c (For id typ (Array e) n loop_body) /\
  expr_body_pre_mods mods c cx env e es /\
  for_nonslot_layout (c,id,typ,e,typ,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
    addr_cut body_cut /\
  (!tail. eval_expr cx e (es with gas_obs := prefix ++ tail) =
         (INL raw,em with gas_obs := tail)) /\
  storage_trace_domain cx st0 em.storage_trace /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
       for_array_expr_landed_mods (DF,lo,d,ctx,func) mods cx c env e vv sbExpr
          (es,sa0,s0,G0,tn0) H raw em Gr traw r) /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  (!tenv s tyv t s1 vs t1 s2 u t2.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tyv,t) /\
     eval_iterator cx (Array e) s1 = (INL vs,t1) /\
     check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s2 = (INL u,t2) ==>
     body_for_full_ok_mods mods exps cx tyv id loop_body vs) /\
  (!name path. raw = PlaceR (MemoryPlace name path) ==>
     ?ent v. lookup_scopes name em.scopes = SOME ent /\
             evaluate_subscripts ent.type ent.value path = INL v) ==>
  ~r.vs_halted /\ ?vs t G tn.
    compatible_bound (Dynamic n) (LENGTH vs) /\
    (!tail. array_iterator_results cx (expr_type e) raw (em with gas_obs := tail) =
         (INL vs,em with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H em.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (r,Gr,traw) [] (OK t,G,tn) /\
      for_array_selected_entry_mods mods exps cx env st0 tyv id loop_body
        (DF,lo,d,ctx,func,shadow_func) (es,sa0,s0,G0,tn0)
        ((c,id,typ,e,typ,bd,ret_ty,loop_body),
         (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
         (bc,saD,saA,xd,capacity,aidItem),
         (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
         addr_cut,body_cut) H vs (em with gas_obs := []) G tn t)
Proof
  PairCases_on `addr_cut` >> PairCases_on `body_cut` >> strip_tac >>
  qhdtm_assum `for_nonslot_layout`
    (strip_assume_tac o REWRITE_RULE [for_nonslot_layout_def]) >>
  drule_then strip_assume_tac type_stmt_for_projection >>
  `bound_length bd = n` by
    (drule_then strip_assume_tac type_stmt_for_array_bound >> gvs[bound_length_def]) >>
  qabbrev_tac `h0 = storage_trace_horizon em.storage_trace` >>
  `valid_horizon cx st0 h0 em.storage_trace` by fs[storage_trace_domain_def,Abbr `h0`] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> for_array_expr_landed_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [for_array_expr_landed_mods_def])) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  drule_all_then strip_assume_tac for_array_capture_replay_mods >>
  `em with gas_obs := [] = em` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e (es with gas_obs := prefix) = (INL raw,em)` by simp[] >>
  `bound_length bd <= n` by simp[] >>
  `lookup_scopes id em.scopes = NONE` by (drule_all_then ACCEPT_TAC capture_install_name_fresh) >>
  `capacity < dimword (:256)` by (drule_all_then ACCEPT_TAC capture_install_capacity) >>
  `!bb. MEM bb func.fn_blocks ==> venomExecSemantics$phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> metis_tac[body_inv_no_phi_mods]) >>
  `copy_old_operand saL (vv_operand vv)` by simp[copy_old_operand_def] >>
  drule_all_then (qx_choose_then `et` (map_every assume_tac o CONJUNCTS))
    for_array_reached_selection_mods >>
  `bound_length bd < dimword (:256)` by
    (irule typed_copy_array_count_bound >> qexistsl_tac [`typ`,`get_tenv cx`,`ArrayTV et bd`] >>
     qpat_assum `post_value_type c e = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `Selected = \(ee,u,Gu:string |-> num # num,tu:taint,bw:256 word,capture,vs:eval_result list).
    ?sel w. (!dw:256 word. for_array_selector_static_mods c cx (e,typ,bd,saL)
           ((ee,u,Gu,tu,dw,bw,capture),sel,w) /\
        for_array_selector_current_mods cx ((ee,u,Gu,tu,dw,bw,capture),sel,w) ee) /\
    (case capture of
       ForArraySlot _ _ _ _ _ => sel = NONE
     | ForArrayOwned av => sel = SOME av
     | ForArrayHeld _ _ av => sel = SOME av
     | ForArrayImmutable _ _ _ _ _ _ _ => T)` >>
  `?vs bw capture u Gu tu. for_array_length_packet_mods mods (DF,lo,d,ctx,func,shadow_func)
      (explicit,PG) cx env st0 (es,sa0,s0,G0,tn0)
      ((c,id,typ,e,typ,bd,ret_ty,loop_body),
       (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
       (bc,saD,saA,xd,capacity,aidItem),
       (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
       (addr_cut0,addr_cut1,addr_cut2,addr_cut3,addr_cut4,addr_cut5,addr_cut6,addr_cut7,addr_cut8),
       (body_cut0,body_cut1,body_cut2,body_cut3,body_cut4))
      raw n (r,Gr,traw) (em,u,Gu,tu,bw,capture,vs) /\
      (!lbl. vv_operand vv <> Label lbl) /\ Selected (em,u,Gu,tu,bw,capture,vs)`
  suffices_by suspend "install" >>
  qpat_x_assum `(?tr slot p tgt src name tops. _) \/ _`
    (DISJ_CASES_THEN2 strip_assume_tac (DISJ_CASES_THEN2 strip_assume_tac assume_tac))
  >- suspend "slot"
  >- suspend "immutable"
  >> suspend "memory"
QED

Resume for_array_capture_install_from_direct_mods[install]:
  strip_tac >>
  qpat_x_assum `Selected _` mp_tac >>
  simp[NoAsms,Abbr `Selected`] >> strip_tac >>
  qhdtm_assum `for_array_length_packet_mods`
    (strip_assume_tac o REWRITE_RULE [for_array_length_packet_mods_def]) >>
  `array_iterator_results cx (expr_type e) raw em = (INL vs,em)` by
    (qpat_assum `em with gas_obs := [] = em` (fn eq =>
       qpat_assum `!tail. array_iterator_results _ _ _ (_ with gas_obs := tail) = _`
         (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [eq])))) >>
  `body_for_full_ok_mods mods exps cx tyv id loop_body vs` by
    (irule capture_reached_callback_mods >>
     qexistsl [`e`,`em`,`n`,`raw`,`es with gas_obs := prefix`,`typ`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_at_then (Pat `for_array_length_packet_mods _ _ _ _ _ _ _ _ _ _ _ _`)
    (drule_all_then (qx_choosel_then [`out`,`Gout`,`tout`] assume_tac))
    capture_install_selected_packet_mods >>
  qexistsl [`vs`,`out`,`Gout`,`tout`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_array_capture_install_from_direct_mods[slot]:
  rename1 `raw = PlaceR (StoragePlace tr slot (ArrayTV et bd))` >>
  `!lbl. vv_operand vv <> Label lbl` by
    (gen_tac >> metis_tac[capture_place_nonlabel]) >>
  `return_buf_frame d c sa0 r` by (drule_all_then ACCEPT_TAC capture_return_buf_at_start) >>
  `!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x` by
    fs[ret_pc_ok_def] >>
  qpat_x_assum `raw = PlaceR (StoragePlace _ _ _)` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H em.storage_trace ==>
      storage_well_formed_on cx es (FST H) /\
      vv_post_mods H ctx func c cx e es sa0 sbExpr s0 em
        (PlaceR (StoragePlace tr slot (ArrayTV et bd))) vv r /\
      ghost_inv_at_mods (DF H) lo d c cx em Gr traw r` by
    (gen_tac >> strip_tac >>
     qpat_assum `!K. valid_horizon _ _ K _ ==> for_array_expr_landed_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H` (drule_then (strip_assume_tac o REWRITE_RULE [for_array_expr_landed_mods_def]))) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  Q.SUBGOAL_THEN
    `?vs u Gu tu off root path delta.
       for_array_length_packet_mods mods (DF,lo,d,ctx,func,shadow_func)
         (explicit,PG) cx env st0 (es,sa0,s0,G0,tn0)
         ((c,id,typ,e,typ,bd,ret_ty,loop_body),
          (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
          (bc,saD,saA,xd,capacity,aidItem),
          (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
          (addr_cut0,addr_cut1,addr_cut2,addr_cut3,addr_cut4,addr_cut5,addr_cut6,addr_cut7,addr_cut8),
          (body_cut0,body_cut1,body_cut2,body_cut3,body_cut4))
         (PlaceR (StoragePlace tr slot (ArrayTV et bd))) n (r,Gr,traw)
         (em,u,Gu,tu,slot,ForArraySlot tr off root path delta,vs)`
    (qx_choosel_then [`xs`,`z`,`Gz`,`tz`,`off`,`root`,`path`,`delta`] assume_tac)
  >- (irule for_array_slot_packet_mods >>
      rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE
                       (qexists `prefix` >> first_assum ACCEPT_TAC))) >>
      first_assum ACCEPT_TAC) >>
  qexistsl [`xs`,`slot`,`ForArraySlot tr off root path delta`,`z`,`Gz`,`tz`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[Abbr `Selected`] >>
  qexists `ArraySelectorPlain` >>
  simp[for_array_selector_static_mods_def,for_array_selector_current_mods_def]
QED
Resume for_array_capture_install_from_direct_mods[immutable]:
  rename1 `raw = PlaceR (ImmutablePlace src name path)` >>
  rename1 `lookup_immutable cx em src name = SOME (rt,root)` >>
  rename1 `FLOOKUP c.ce_module_vars (src,name) = SOME (ImmutableLoc off)` >>
  rename1 `evaluate_subscripts rt root (MAP AttrSubscript attrs) = INL (ArrayV pav)` >>
  rename1 `evaluate_subscripts rt root path = INL (ArrayV av)` >>
  rename1 `loop_iterator_place e = SOME tgt` >>
  rename1 `path = MAP AttrSubscript attrs ++ tail` >>
  `off + type_memory_size rt < dimword (:256)` by
    (irule capture_immutable_root_bound_mods >>
     qexistsl [`c`,`ctx`,`cx`,`em`,`env`,`exps`,`mods`,`name`,`root`,`src`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!lbl. vv_operand vv <> Label lbl` by
    (gen_tac >> irule capture_place_nonlabel >>
     qexistsl [`c`,`e`,`(src,name)`,`sa0`,`sbExpr`,`tgt`] >>
     conj_tac >-
       (qpat_assum `place_access tgt [] = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[place_access_root,pairTheory.FST]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `expr_body_pre_mods mods c cx env e (es with gas_obs := prefix)` by simp[] >>
  `local_ptrs_reserved c sbExpr` by (drule_all_then strip_assume_tac capture_reserved) >>
  `loc = LocCode` by fs[vv_location_def] >>
  `post_value_type c e = expr_type e` by simp[] >>
  qpat_x_assum `raw = PlaceR (ImmutablePlace _ _ _)` SUBST_ALL_TAC >>
  qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >>
  Q.SUBGOAL_THEN
    `?xs z Gz tz offP rtP deltaP avP.
       for_array_length_packet_mods mods (DF,lo,d,ctx,func,shadow_func)
         (explicit,PG) cx env st0 (es,sa0,s0,G0,tn0)
         ((c,id,typ,e,typ,bd,ret_ty,loop_body),
          (vv,sbExpr,shadow_sa0,shadow_sbExpr,LocCode,len_op,saL),
          (bc,saD,saA,xd,capacity,aidItem),
          (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
          (addr_cut0,addr_cut1,addr_cut2,addr_cut3,addr_cut4,addr_cut5,addr_cut6,addr_cut7,addr_cut8),
          (body_cut0,body_cut1,body_cut2,body_cut3,body_cut4))
         (PlaceR (ImmutablePlace src name path)) n (r,Gr,traw)
         (em,z,Gz,tz,n2w (offP+deltaP),ForArrayImmutable src name path offP rtP deltaP avP,xs)`
    (qx_choosel_then [`xs`,`z`,`Gz`,`tz`,`offP`,`rtP`,`deltaP`,`avP`] assume_tac)
  >- (irule for_array_immutable_packet_mods >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >- (qexists `exps` >> first_assum ACCEPT_TAC) >>
      qexists `prefix` >> conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `cap = ForArrayImmutable src name path offP rtP deltaP avP` >>
  qabbrev_tac `bw = n2w (offP + deltaP):256 word` >>
  `for_array_entry_route_mods c cx lo (typ,bd,LocCode) (em,sbExpr,z,Gz,tz)
     (vv_operand vv,bw) xs cap h0 xs em Gz tz z` by
    (unabbrev_all_tac >>
     qhdtm_assum `for_array_length_packet_mods`
      (strip_assume_tac o REWRITE_RULE [for_array_length_packet_mods_def]) >>
     first_assum irule >> simp[for_array_install_frame_mods_def]) >>
  `offP = off /\ rtP = rt /\ avP = av` by
    (qhdtm_assum `for_array_entry_route_mods` mp_tac >>
     simp[NoAsms,for_array_entry_route_mods_def,Abbr `cap`] >>
     strip_tac >>
     conj_tac >-
       (qpat_assum `FLOOKUP c.ce_module_vars (src,name) = SOME (ImmutableLoc offP)` mp_tac >>
        qpat_assum `FLOOKUP c.ce_module_vars (src,name) = SOME (ImmutableLoc off)`
          (fn eq => simp[NoAsms,eq])) >>
     qpat_assum `lookup_immutable cx em src name = SOME (rtP,_)` mp_tac >>
     qpat_assum `lookup_immutable cx em src name = SOME (rt,root)`
       (fn eq => simp[NoAsms,eq]) >>
     strip_tac >>
     qpat_assum `evaluate_subscripts rt root path = INL (ArrayV av)` mp_tac >>
     qpat_assum `rt = rtP` SUBST_ALL_TAC >>
     qpat_assum `root = _` SUBST_ALL_TAC >> simp[]) >>
  qexistsl [`xs`,`bw`,`cap`,`z`,`Gz`,`tz`] >>
  conj_tac >- simp[Abbr `cap`,Abbr `bw`] >>
  simp[Abbr `Selected`,Abbr `cap`] >>
  qexistsl [`SOME pav`,`ArraySelectorImmutable tgt attrs tail pav`] >>
  qpat_assum `path = MAP AttrSubscript attrs ++ tail`
    (fn eq => qpat_assum `evaluate_subscripts rt root path = INL (ArrayV av)`
      (assume_tac o PURE_REWRITE_RULE [eq])) >>
  simp[for_array_selector_static_mods_def,for_array_selector_current_mods_def]
QED
Resume for_array_capture_install_from_direct_mods[memory]:
  Q.SUBGOAL_THEN `(?v. raw = Value v) \/ (?name path. raw = PlaceR (MemoryPlace name path))`
    assume_tac
  >- (qpat_assum `(?name path p tgt attrs tail. raw = PlaceR (MemoryPlace name path) /\ _) \/ _`
       strip_assume_tac >> simp[] >> metis_tac[]) >>
  Q.SUBGOAL_THEN `vv_location vv = NONE \/ vv_location vv = SOME LocMemory` assume_tac
  >- (qpat_assum `(?name path p tgt attrs tail. raw = PlaceR (MemoryPlace name path) /\ _) \/ _`
       strip_assume_tac >> simp[vv_location_def]) >>
  `loc = LocMemory` by
    (qpat_assum `loc = _` SUBST1_TAC >>
     qpat_x_assum `vv_location vv = NONE \/ _` strip_assume_tac >> simp[]) >>
  `!lbl. vv_operand vv <> Label lbl` by
    (drule_all_then ACCEPT_TAC for_array_memory_base_nonlabel_mods) >>
  `sa0.cs_next_var <= sbExpr.cs_next_var /\ local_ptrs_reserved c sbExpr` by
    (drule_all_then ACCEPT_TAC capture_reserved) >>
  `(case bd of Fixed k => comp_return (Lit (n2w k))
     | Dynamic _ => compile_ptr_load c.ce_is_ctor c.ce_imm_alloca LocMemory (vv_operand vv))
    sbExpr = (len_op,saL)` by
    (qpat_assum `loc = LocMemory` (fn eq =>
       qpat_assum `(case bd of Fixed _ => _ | Dynamic _ => _) sbExpr = (len_op,saL)`
         (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp r)` by
    fs[for_array_outer_frame_mods_def,range_outer_frame_mods_def] >>
  `expr_body_pre_mods mods c cx env e (es with gas_obs := prefix)` by simp[] >>
  `vv_post_mods h0 ctx func c cx e (es with gas_obs := prefix) sa0 sbExpr s0 em raw vv r` by
    (qpat_assum `vv_post_mods h0 _ _ _ _ _ es _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms,vv_post_mods_def,locals_kept_def,popped_kept_def] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[] >>
  CONV_TAC (QUANT_CONV (QUANT_CONV
    (SWAP_EXISTS_CONV THENC QUANT_CONV
      (SWAP_EXISTS_CONV THENC QUANT_CONV SWAP_EXISTS_CONV)))) >>
  irule (INST_TYPE [alpha |-> ``:256``] for_array_memory_packet_extra_mods) >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE (qexists `typ` >> first_assum ACCEPT_TAC))) >>
  qexistsl [`h0`,`es with gas_obs := prefix`,`sa0`,`sbExpr`,`saL`] >>
  reverse conj_tac
  >- (conj_tac
      >- (gen_tac >> strip_tac >>
          qpat_assum `!v. raw = Value v /\ _ ==> _ /\ _` (drule_all_then strip_assume_tac) >>
          first_assum ACCEPT_TAC) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`etR`,`arr`,`xs`,`pe`,`pb`,`pet`,`a`,`z`,`Gz`,`tz`] >>
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  `pe = typ /\ pb = bd` by
    (qpat_x_assum `post_value_type c e = ArrayT pe pb` mp_tac >> simp[EQ_SYM_EQ]) >>
  `evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME (ArrayTV etR bd)` by
    (qpat_assum `expr_type e = ArrayT typ bd` (fn eq =>
       qpat_assum `evaluate_type _ (expr_type e) = _` (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  `pet = etR` by
    (qpat_assum `post_value_type c e = ArrayT typ bd` (fn eq =>
       qpat_assum `evaluate_type _ (post_value_type c e) = SOME (ArrayTV pet pb)`
         (mp_tac o REWRITE_RULE [eq])) >> simp[EQ_SYM_EQ]) >>
  `ptr_mem_ok cx (ArrayT typ bd) (ArrayV arr) (vv_operand vv) Gz tz z` by
    (qpat_assum `post_value_type c e = ArrayT typ bd` (fn eq =>
       qpat_assum `ptr_mem_ok _ (post_value_type c e) _ _ _ _ _` (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  `(0 < type_memory_size (ArrayTV etR bd) ==>
      w2n a + type_memory_size (ArrayTV etR bd) <= z.vs_alloca_next)` by
    (disch_tac >> qpat_assum `pet = etR` (fn et_eq =>
       qpat_assum `pb = bd` (fn bd_eq =>
         qpat_assum `0 < type_memory_size _ ==> _ /\ _`
           (drule_then (ACCEPT_TAC o CONJUNCT1) o REWRITE_RULE [et_eq,bd_eq])))) >>
  `LENGTH xs <= bound_length bd` by
    (qpat_assum `bound_length bd = n` (fn th => pure_rewrite_tac [th]) >>
     qpat_assum `compatible_bound (Dynamic n) _`
       (ACCEPT_TAC o REWRITE_RULE [compatible_bound_def])) >>
  drule_all_then strip_assume_tac for_array_memory_length_frame_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "owned_selected" >> suspend "held_selected"
QED

Resume for_array_capture_install_from_direct_mods[owned_selected]:
  strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `vv_own c cx (ArrayT typ bd) sa0 sbExpr em (Value (ArrayV arr)) vv r` by
        (qpat_x_assum `!v. raw = Value v /\ _ ==> _ /\ _`
           (qspec_then `ArrayV arr` mp_tac) >>
         asm_simp_tac std_ss [is_word_type_def,is_bytestring_type_def] >> simp[]) >>
      drule_all_then MATCH_ACCEPT_TAC for_array_capture_owned_snapshot_mods) >>
  simp[Abbr `Selected`] >> qexists `ArraySelectorPlain` >>
  simp[for_array_selector_static_mods_def,for_array_selector_current_mods_def]
QED

Resume for_array_capture_install_from_direct_mods[held_selected]:
  map_every qx_gen_tac [`name`,`path`] >> strip_tac >>
  reverse (qpat_x_assum `(?nm pth p tgt attrs tail. raw = PlaceR (MemoryPlace nm pth) /\ _) \/ _`
    (DISJ_CASES_THEN2
      (qx_choosel_then [`nm`,`pth`,`p`,`tgt`,`attrs`,`tail`] (map_every assume_tac o CONJUNCTS))
      (qx_choose_then `owned_value` (map_every assume_tac o CONJUNCTS))))
  >- (qpat_assum `raw = PlaceR (MemoryPlace _ _)` (fn eq =>
        qpat_assum `raw = Value _` (mp_tac o PURE_ONCE_REWRITE_RULE [eq])) >> simp[NoAsms]) >>
  qpat_x_assum `raw = PlaceR (MemoryPlace name path)` SUBST_ALL_TAC >>
  qpat_x_assum `PlaceR (MemoryPlace _ _) = PlaceR (MemoryPlace _ _)`
    (map_every SUBST_ALL_TAC o CONJUNCTS o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (REWRITE_RULE [vv_operand_def]) >>
  pure_rewrite_tac[vv_operand_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all_then MATCH_ACCEPT_TAC for_array_capture_held_snapshot_mods) >>
  `evaluate_type (get_tenv cx) typ = SOME etR` by
    (qpat_assum `evaluate_type (get_tenv cx) (ArrayT typ bd) = _` mp_tac >>
     simp[NoAsms,evaluate_type_def,AllCaseEqs()]) >>
  `runtime_place_typed cx em (MemoryPlace nm pth) (ArrayTV etR bd)` by
    (qpat_assum `expr_body_pre_mods mods c cx env e (es with gas_obs := prefix)`
       (strip_assume_tac o MATCH_MP expr_body_pre_mods_runtime_typing) >>
     qpat_assum `expr_body_pre_mods mods c cx env e (es with gas_obs := prefix)`
       (assume_tac o MATCH_MP expr_body_pre_mods_call_evaluation_safe) >>
     drule_all_then strip_assume_tac eval_expr_success_storage_facts >>
     `env.type_defs = get_tenv cx` by
       fs[vyperTypeExprSoundnessTheory.runtime_consistent_def,env_consistent_def,
          env_context_consistent_def] >>
     qpat_x_assum `eval_result_typed _ _ _` mp_tac >> simp[eval_result_typed_def]) >>
  drule_all_then (qx_choosel_then [`entry0`,`q`,`sz`,`rw`,`delta`] strip_assume_tac)
    for_array_held_length_root_mods >>
  qpat_assum `!name path. PlaceR (MemoryPlace nm pth) = _ ==> _`
    (qspecl_then [`nm`,`pth`] mp_tac) >>
  simp[NoAsms] >>
  disch_then (qx_choosel_then [`entry1`,`v`] strip_assume_tac) >>
  `entry1 = entry0` by
    (qpat_assum `lookup_scopes nm em.scopes = SOME entry1` mp_tac >>
     qpat_assum `lookup_scopes nm em.scopes = SOME entry0`
       (fn eq => simp[NoAsms,eq])) >>
  pop_assum SUBST_ALL_TAC >>
  `evaluate_subscripts entry0.type entry0.value pth = INL (ArrayV arr)` by
    (qpat_assum `read_result cx (PlaceR (MemoryPlace nm pth)) em = _` mp_tac >>
     qpat_assum `lookup_scopes nm em.scopes = SOME entry0`
       (fn lookup => qpat_assum
         `evaluate_subscripts entry0.type entry0.value pth = INL v`
         (fn selected =>
           simp[NoAsms,read_result_def,read_place_def,read_memory_path_def,
                get_scopes_def,lookup,selected,bind_def,lift_option_type_def,
                lift_sum_def,return_def]))) >>
  `not_fresh_at saL q` by
    (qpat_assum `local_ptrs_reserved c saL` mp_tac >>
     simp[NoAsms,local_ptrs_reserved_def] >>
     qpat_assum `FLOOKUP c.ce_vars nm = SOME (PtrVar (Var q) sz)` mp_tac >>
     metis_tac[]) >>
  simp[Abbr `Selected`] >>
  qexists `ArraySelectorHeld tgt attrs tail entry0 etR q sz rw delta` >>
  simp[for_array_selector_static_mods_def,for_array_selector_current_mods_def] >>
  qpat_assum `pth = MAP AttrSubscript attrs ++ tail` (SUBST1_TAC o SYM) >>
  simp[] >>
  qpat_assum `a = rw + n2w delta` (SUBST1_TAC o SYM) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  CONV_TAC (BINOP_CONV (REWR_CONV arithmeticTheory.ADD_COMM)) >>
  first_assum ACCEPT_TAC
QED

Finalise for_array_capture_install_from_direct_mods[local]

Theorem for_array_origin_capture_install_mods:
  contract_inv mods exps ctx c cx /\ MEM func ctx.ctx_functions /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved c sa0 /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!h. dead_lo_ok_mods h (DF h) lo c cx) /\
  type_stmt env ret_ty (For id typ (Array e) n loop_body) = SOME env' /\
  stmt_exprs_ok c (For id typ (Array e) n loop_body) /\
  expr_body_pre_mods mods c cx env e es /\
  for_nonslot_layout (c,id,typ,e,typ,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
    addr_cut body_cut /\
  (!tail. eval_expr cx e (es with gas_obs := prefix ++ tail) =
         (INL raw,em with gas_obs := tail)) /\
  storage_trace_domain cx st0 em.storage_trace /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
       for_array_expr_landed_mods (DF,lo,d,ctx,func) mods cx c env e vv sbExpr
          (es,sa0,s0,G0,tn0) H raw em Gr traw r) /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  (!tenv s tyv' t s1 vs1 t1 s2 u t2.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tyv',t) /\
     eval_iterator cx (Array e) s1 = (INL vs1,t1) /\
     check (compatible_bound (Dynamic n) (LENGTH vs1)) "For too long" s2 = (INL u,t2) ==>
     body_for_full_ok_mods mods exps cx tyv' id loop_body vs1) ==>
  ~r.vs_halted /\ ?vs t G tn.
    compatible_bound (Dynamic n) (LENGTH vs) /\
    (!tail. array_iterator_results cx (expr_type e) raw (em with gas_obs := tail) =
         (INL vs,em with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H em.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (r,Gr,traw) [] (OK t,G,tn) /\
      for_array_selected_entry_mods mods exps cx env st0 tyv id loop_body
        (DF,lo,d,ctx,func,shadow_func) (es,sa0,s0,G0,tn0)
        ((c,id,typ,e,typ,bd,ret_ty,loop_body),
         (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
         (bc,saD,saA,xd,capacity,aidItem),
         (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
         addr_cut,body_cut) H vs (em with gas_obs := []) G tn t)
Proof
  strip_tac >>
  drule_then strip_assume_tac type_stmt_for_projection >>
  `well_typed_expr env e /\ expr_writes_ok (\_. F) e` by
    fs[well_typed_iterator_def] >>
  `!name path. raw = PlaceR (MemoryPlace name path) ==>
     ?ent v. lookup_scopes name em.scopes = SOME ent /\
             evaluate_subscripts ent.type ent.value path = INL v` by
    (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
     qspecl_then [`e`,`cx`,`env`,`es with gas_obs := prefix`,
                  `name`,`path`,`em with gas_obs := []`] mp_tac
       held_eval_direct_selection_mods >>
     qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
     fs[]) >>
  irule for_array_capture_install_from_direct_mods >>
  PURE_ASM_REWRITE_TAC [FORALL_SIMP,AND_CLAUSES] >>
  conj_tac >- (qexists_tac `prefix` >> first_assum ACCEPT_TAC) >>
  simp[]
QED
