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
  qpat_x_assum `(?tr slot p tgt src name tops. _) \/ _` strip_assume_tac
  >- suspend "slot"
  >- suspend "immutable"
  >- suspend "held"
  >> suspend "owned"
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
  drule_all for_array_slot_packet_mods >>
  qpat_assum `!lbl. vv_operand vv <> Label lbl` (fn th => simp[NoAsms,th]) >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[for_array_length_packet_mods_def] >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`vs`,`slot`,`ForArraySlot tr off root path delta`,`u`,`Gu`,`tu`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
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
Resume for_array_capture_install_mods[held]:
  cheat
QED
Resume for_array_capture_install_mods[owned]:
  cheat
QED

Finalise for_array_capture_install_mods
