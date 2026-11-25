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
  bodyForArrayHeaderMods
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
