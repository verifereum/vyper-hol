(* Capture a qualified immutable once, then use the install frame to
   retain either its constructor-memory window or its runtime data bytes. *)
Theory bodyForArrayImmutablePacketMods
Ancestors
  bodyForArrayLengthPacketMods bodyForArrayImmutableLengthMods
  bodyForArrayEntryMods bodyForArrayHeaderInstallMods bodyForArrayHeaderMods
  bodyForArrayLengthLinkedTransportMods stmtLoweringMono
  bodyForRangeHeaderMods
  bodyForArrayExprRunMods bodyFullHashKeccakFixed
  forNestedArrayCapture stateFrame exprSimCopy exprSimProps
  exprBodyPreTypingProps vyperTypeEvalStoragePreservation
  vyperPlaceTyping vyperBareGlobalName vyperContext vyperArray
  vyperTyping vyperValueOperation vyperAST exprBodyPreCallSafetyProps
  vyperTypeExprSoundness vyperTypeInvariants vyperState
  valueEncoding exprLoweringProps emitHelperProps context compileEnv
  bodyFullPostsMods bodyFullPredsMods bodyFullShadowBodyInv
  loweringPosts stmtSimProps loweringStateRelDefs bodyPtrDefs ptrDiscipline
  fragGasOriginPtr vyperStorageTrace vyperStorageFootprint
  venomState venomInst finite_map words list arithmetic
Libs
  monadsyntax

Theorem immutable_capture_install_route[local]:
  evaluate_type (get_tenv cx) sty = SOME et /\
  eval_operand op u = SOME bw /\ op_prov Gu op = NONE /\
  copy_old_operand saL op /\
  ALOOKUP c.ce_modules src = SOME tops /\
  FLOOKUP c.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  bw = n2w (off + delta) /\ mem_path_offset itv path = SOME (delta,ArrayTV et bd) /\
  lookup_immutable cx em src name = SOME (itv,iv) /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  vs = MAP Value (array_elements (ArrayTV et bd) av) /\
  w2n bw + type_memory_size (ArrayTV et bd) < dimword (:256) /\
  lo <= u.vs_alloca_next /\
  (if c.ce_is_ctor then w2n bw + type_memory_size (ArrayTV et bd) <= lo /\
     (!mem taint. (!i. i < lo ==> mem_bytes_at i 1 mem = mem_bytes_at i 1 u.vs_memory) /\
        (!i. i < lo /\ i IN taint ==> i IN tu.t_mem) ==>
        !m. mem_agree_outside taint mem m ==>
            val_in_memory (ArrayTV et bd) (ArrayV av) (w2n bw) m)
   else w2n bw + type_memory_size (ArrayTV et bd) <= LENGTH u.vs_data_section /\
     val_in_memory (ArrayTV et bd) (ArrayV av) (w2n bw) u.vs_data_section) /\
  for_array_install_frame_mods saL u Gu tu G tn t ==>
  for_array_entry_route_mods c cx lo (sty,bd,LocCode) (em,sbExpr,u,Gu,tu)
    (op,bw) vs (ForArrayImmutable src name path off itv delta av) h vs em G tn t
Proof
  strip_tac >>
  `op_prov G op = op_prov Gu op` by
    (Cases_on `op` >> gvs[copy_old_operand_def,for_array_install_frame_mods_def,op_prov_def]) >>
  qpat_x_assum `bw = _` SUBST_ALL_TAC >>
  simp[for_array_entry_route_mods_def] >>
  fs[for_array_install_frame_mods_def] >>
  Cases_on `c.ce_is_ctor` >> fs[] >>
  `!i. i < lo /\ i IN tn.t_mem ==> i IN tu.t_mem` by
    (rpt strip_tac >> `i < u.vs_alloca_next` by decide_tac >>
     qpat_assum `!i. i < u.vs_alloca_next ==> _` (drule_then mp_tac) >> simp[]) >>
  qpat_assum `!mem taint. _ ==> _`
    (qspecl_then [`u.vs_memory`,`tn.t_mem`] mp_tac) >> simp[]
QED

Theorem immutable_capture_bounds[local]:
  immutable_holds_mods c cx (ArrayT sty bd) raw bw em r /\
  evaluate_type (get_tenv cx) (ArrayT sty bd) = SOME (ArrayTV et bd) ==>
  w2n bw + type_memory_size (ArrayTV et bd) < dimword (:256)
Proof
  simp[immutable_holds_mods_def,immutable_holds_def,sub_layout_def] >>
  strip_tac >>
  `off + k < dimword (:256)` by decide_tac >>
  gvs[w2n_n2w] >> decide_tac
QED

Theorem immutable_capture_count[local]:
  value_has_type (ArrayTV et bd) (ArrayV av) ==>
  LENGTH (array_elements (ArrayTV et bd) av) <= bound_length bd
Proof
  Cases_on `bd` >> Cases_on `av` >>
  simp[value_has_type_def,array_elements_length_sarray,array_elements_length_dyn,
       array_length_def,bound_length_def]
QED

Theorem immutable_capture_path_type[local]:
  expr_body_pre_mods mods c cx env e start /\
  expr_type e = ArrayT sty bd /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et bd) /\
  eval_expr cx e start = (INL (PlaceR (ImmutablePlace src name path)),em) /\
  lookup_immutable cx em src name = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (delta,tv) ==>
  tv = ArrayTV et bd
Proof
  strip_tac >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  drule_all_then strip_assume_tac eval_expr_success_storage_facts >>
  `env.type_defs = get_tenv cx` by
    fs[runtime_consistent_def,env_consistent_def,env_context_consistent_def] >>
  `subscripts_type itv path = SOME (ArrayTV et bd)` by
    (Cases_on `ALOOKUP em.immutables cx.txn.target` >>
     gvs[eval_result_typed_def,runtime_place_typed_immutable,
         lookup_immutable_def,get_immutables_def,get_address_immutables_def,
         bind_def,lift_option_type_def,return_def,raise_def]) >>
  drule mem_path_offset_sound >> simp[]
QED

Theorem immutable_length_code[local]:
  (case bd of Fixed k => comp_return (Lit (n2w k))
    | Dynamic _ => compile_ptr_load ctor imm LocCode op) sbExpr = (len_op,saL) ==>
  saL.cs_current_bb = sbExpr.cs_current_bb /\
  saL.cs_current_insts = sbExpr.cs_current_insts ++ emitted_insts sbExpr saL /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sbExpr saL)
Proof
  Cases_on `bd` >> simp[]
  >- simp[comp_return_def,emitted_insts_def] >>
  strip_tac >>
  `same_blocks sbExpr saL` by (drule_then ACCEPT_TAC compile_ptr_load_same_blocks) >>
  fs[same_blocks_def,compile_ptr_load_def,compile_imm_load_word_def] >>
  Cases_on `ctor` >> gvs[]
  >- (Cases_on `imm` >> gvs[comp_bind_def]
      >- (drule emitted_insts_emit_op >> simp[mk_inst_def]) >>
      Cases_on `emit_op ADD [op;x] sbExpr` >> gvs[] >>
      qpat_assum `emit_op ADD _ _ = _` (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
      qpat_assum `emit_op ILOAD _ _ = _` (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
      `saL.cs_current_insts = sbExpr.cs_current_insts ++
         (emitted_insts sbExpr r ++ emitted_insts r saL)` by simp[APPEND_ASSOC] >>
      `emitted_insts sbExpr saL = emitted_insts sbExpr r ++ emitted_insts r saL` by
         (CONV_TAC (LHS_CONV (REWR_CONV emitted_insts_def)) >>
          qpat_assum `saL.cs_current_insts = sbExpr.cs_current_insts ++ (_ ++ _)`
            (pure_once_rewrite_tac o single) >> simp[rich_listTheory.DROP_LENGTH_APPEND]) >>
      simp[mk_inst_def,APPEND_ASSOC])
  >> drule emitted_insts_emit_op >> simp[mk_inst_def]
QED

Theorem immutable_capture_initial_gas[local]:
  vv_post_mods h ctx func c cx e (es with gas_obs := prefix) sa sb s0 em raw vv r <=>
  vv_post_mods h ctx func c cx e es sa sb s0 em raw vv r
Proof
  simp[vv_post_mods_def,locals_kept_def,pure_frame_def,popped_kept_def]
QED

(* Transport the original statement frame over the selected length slice. *)
Theorem for_array_immutable_packet_mods:
  expr_body_pre_mods mods c cx env e (es0 with gas_obs := prefix) /\
  contract_inv mods exps ctx c cx /\
  expr_type e = ArrayT sty bd /\ post_value_type c e = expr_type e /\
  bound_length bd <= n /\
  eval_expr cx e (es0 with gas_obs := prefix) = (INL (PlaceR (ImmutablePlace src name path)),em) /\
  storage_trace_domain cx st0 em.storage_trace /\
  (!h. valid_horizon cx st0 h em.storage_trace ==>
    for_array_expr_landed_mods (DF,lo,d,ctx,func) mods cx c env e vv sbExpr
      (es0,sa0,s0,G0,tn0) h (PlaceR (ImmutablePlace src name path)) em Gr traw r) /\
  (!h. dead_lo_ok_mods h (DF h) lo c cx) /\
  local_ptrs_reserved c sbExpr /\ copy_old_operand saL (vv_operand vv) /\
  (case bd of Fixed k => comp_return (Lit (n2w k))
    | Dynamic _ => compile_ptr_load c.ce_is_ctor c.ce_imm_alloca LocCode (vv_operand vv))
      sbExpr = (len_op,saL) /\ fn_has_code sbExpr saL func /\
  compile_expr c (expr_type e) e sa0 = (vv,sbExpr) /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!bb. MEM bb func.fn_blocks ==> venomExecSemantics$phi_prefix_length bb.bb_instructions = 0) ==>
  ?vs u Gu tu off itv delta av.
    for_array_length_packet_mods mods (DF,lo,d,ctx,func,shadow_func)
      (explicit,PG) cx env st0 (es0,sa0,s0,G0,tn0)
      ((c,id,fty,e,sty,bd,ret_ty,loop_body),
       (vv,sbExpr,shadow_sa0,shadow_sbExpr,LocCode,len_op,saL),item,blocks,addr_cut,body_cut)
      (PlaceR (ImmutablePlace src name path)) n (r,Gr,traw)
      (em,u,Gu,tu,n2w (off+delta),ForArrayImmutable src name path off itv delta av,vs)
Proof
  strip_tac >>
  qabbrev_tac `h0 = storage_trace_horizon em.storage_trace` >>
  `valid_horizon cx st0 h0 em.storage_trace` by fs[storage_trace_domain_def,Abbr `h0`] >>
  qpat_assum `!h. valid_horizon _ _ _ _ ==> for_array_expr_landed_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [for_array_expr_landed_mods_def])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp r` by
    fs[for_array_outer_frame_mods_def,bodyForRangeHeaderModsTheory.range_outer_frame_mods_def] >>
  `dead_lo_ok_mods h0 (DF h0) lo c cx` by simp[] >>
  `vv_post_mods h0 ctx func c cx e (es0 with gas_obs := prefix) sa0 sbExpr s0 em
      (PlaceR (ImmutablePlace src name path)) vv r` by
    (pure_rewrite_tac [immutable_capture_initial_gas] >> first_assum ACCEPT_TAC) >>
  drule_all for_array_immutable_length_ready_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  suspend "qualified"
QED

Resume for_array_immutable_packet_mods[qualified]:
  `tv = ArrayTV et bd` by (drule_all_then ACCEPT_TAC immutable_capture_path_type) >>
  qpat_x_assum `tv = ArrayTV et bd` SUBST_ALL_TAC >>
  `evaluate_subscripts itv iv path = INL (ArrayV av)` by gvs[read_result_immutable_place] >>
  `LENGTH vs <= bound_length bd` by simp[immutable_capture_count] >>
  `eval_operand p.ptr_operand r = SOME (n2w (off + delta))` by
    (`t.vs_labels = r.vs_labels` by fs[state_frame_def] >>
     `copy_old_operand sbExpr p.ptr_operand` by fs[vv_operand_def] >>
     Cases_on `p.ptr_operand` >> gvs[copy_old_operand_def,eval_operand_def] >>
     qpat_assum `!x. not_fresh_at sbExpr x ==> _` (drule_then strip_assume_tac) >> fs[]) >>
  `w2n (n2w (off + delta):bytes32) + type_memory_size (ArrayTV et bd) < dimword (:256)` by
    (irule immutable_capture_bounds >>
     qexistsl [`c`,`cx`,`em`,`r`,`PlaceR (ImmutablePlace src name path)`,`sty`] >>
     gvs[vv_post_mods_def,vv_holds_mods_def]) >>
  suspend "transport"
QED

Resume for_array_immutable_packet_mods[transport]:
  drule_then strip_assume_tac immutable_length_code >>
  `t = r with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>` by
    (qpat_assum `state_frame t = _`
       (mp_tac o PURE_REWRITE_RULE [state_frame_eq_reconstruct] o SYM) >>
     simp[NoAsms]) >>
  `sa0.cs_next_var <= sbExpr.cs_next_var` by
    (qspecl_then [`c`,`expr_type e`,`e`,`sa0`] mp_tac (cj 1 ci_mono_compile_expr_sa) >>
     simp[ci_mono_def]) >>
  `!h. valid_horizon cx st0 h em.storage_trace ==>
       ret_pc_ok c sa0 t /\ return_buf_frame d c sa0 t /\ return_buf_sep d c em t /\
       stmt_state_rel h ctx func c cx em t /\ immutable_frame_mods func c cx em t /\
       storage_well_formed_on cx em (FST h) /\ ghost_inv_at_mods (DF h) lo d c cx em G' tn' t /\
       for_array_outer_frame_mods ctx func c sa0 es0 s0 G0 tn0 em G' tn' t /\
       (!fn inst q. frag_reachable ctx func t fn inst q ==> dalloca_fmp_headroom inst q)` by
    (qx_gen_tac `h` >> strip_tac >>
     qpat_assum `!h. valid_horizon _ _ _ _ ==> for_array_expr_landed_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `h` (drule_then (strip_assume_tac o REWRITE_RULE [for_array_expr_landed_mods_def]))) >>
     qpat_assum `vv_post_mods h _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     qpat_assum `!D'. gas_origin_ptr_path _ _ _ _` (qspec_then `DF h` assume_tac) >>
     irule for_array_length_linked_transport_mods >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE all_tac) >>
     qexistsl [`Gr`,`PG`,`emitted_insts sbExpr saL`,`explicit`,`r`,`saL`,`sbExpr`,`traw`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!h. valid_horizon _ _ _ _ ==> ret_pc_ok _ _ _ /\ _`
    (qspec_then `h0` (drule_then strip_assume_tac)) >>
  `eval_operand (vv_operand vv) t = SOME (n2w (off + delta)) /\
   op_taint tn' (vv_operand vv) = {}` by simp[vv_operand_def] >>
  qexistsl [`vs`,`t`,`G'`,`tn'`,`off`,`itv`,`delta`,`av`] >>
  pure_rewrite_tac[for_array_length_packet_mods_def] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE all_tac)
  >- (qx_gen_tac `h` >> strip_tac >>
      qpat_assum `!h. valid_horizon _ _ _ _ ==> ret_pc_ok _ _ _ /\ _`
        (qspec_then `h` (drule_then strip_assume_tac)) >>
      qpat_assum `!D'. gas_origin_ptr_path _ _ _ _` (qspec_then `DF h` assume_tac) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> irule immutable_capture_install_route >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE REFL_TAC ORELSE all_tac)
  >- (qexists_tac `tops` >> first_assum ACCEPT_TAC)
  >- simp[vv_operand_def]
  >- (qexists_tac `iv` >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (qexists_tac `et` >> rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE all_tac) >>
      Cases_on `c.ce_is_ctor` >>
      qpat_x_assum `if c.ce_is_ctor then _ else _` mp_tac >>
      ((qpat_assum `c.ce_is_ctor` (fn th => pure_rewrite_tac[th,COND_CLAUSES])) ORELSE
       (qpat_assum `~c.ce_is_ctor` (fn th => pure_rewrite_tac[th,COND_CLAUSES]))) >>
      strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `saL` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise for_array_immutable_packet_mods
