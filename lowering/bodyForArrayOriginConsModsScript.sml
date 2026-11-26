(* Run the actual landed copy and preserve the fixed selection after pop. *)
Theory bodyForArrayOriginConsMods
Ancestors
  bodyForArraySelectedPacketMods bodyForArrayLayoutItemCutMods
  bodyForArrayBodyLandingMods bodyForArrayLandedSlotMods bodyForArrayLandedSnapshotMods
  bodyForArraySlotOwnedRestoreMods bodyForArrayHeldRestoreMods bodyForArrayImmutableRestoreMods
  bodyAssignNameLinkedSetup bodyFullForFacts bodyInvSplit bodyLoopCalls
  bodyFullForArrayRound bodyForArrayHeaderMods bodyForArrayOriginMods bodyForArrayEntryMods
  bodyArrayMemorySourcePathsMods gasOutcomeFullPostPathMods
  vyperTypeContract vyperTypeSystem vyperStorageTrace vyperStorageFootprint
  stmtSimProps loweringPosts loweringShapeDefs compileEnv ptrDiscipline finite_map
  exprBodyPreProps logArgumentTypeEval vyperTypeEvalCaseProofs vyperValue
Libs
  monadsyntax

val _ = Parse.hide "body";

(* Freshness suffices to retype the iterator in the body environment. *)
Theorem iterator_typing_extend_local[local]:
  (!env e. well_typed_expr env e ==>
    !id ty. id NOTIN FDOM env.var_types ==> well_typed_expr (extend_local env id ty F) e) /\
  (!env e vt. type_place_expr env e = SOME vt ==>
    !id ty. id NOTIN FDOM env.var_types ==> type_place_expr (extend_local env id ty F) e = SOME vt) /\
  (!env target vt. type_place_target env target = SOME vt ==>
    !id ty. id NOTIN FDOM env.var_types ==> type_place_target (extend_local env id ty F) target = SOME vt) /\
  (!env es. well_typed_exprs env es ==>
    !id ty. id NOTIN FDOM env.var_types ==> well_typed_exprs (extend_local env id ty F) es) /\
  (!env opt. well_typed_opt env opt ==>
    !id ty. id NOTIN FDOM env.var_types ==> well_typed_opt (extend_local env id ty F) opt) /\
  (!env es. well_typed_named_exprs env es ==>
    !id ty. id NOTIN FDOM env.var_types ==> well_typed_named_exprs (extend_local env id ty F) es)
Proof
  ho_match_mp_tac well_typed_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  simp[NoAsms,well_typed_expr_def,extend_local_def] >> rpt strip_tac >>
  gvs[well_typed_expr_def,extend_local_def,FLOOKUP_UPDATE,AllCaseEqs()] >>
  fs[FLOOKUP_DEF]
  >- (strip_tac >> gvs[])
  >- (disj1_tac >> irule subscript_base_type_exact_transfer >>
      qexists_tac `env` >> simp[]) >>
  `id' <> id` by (strip_tac >> gvs[]) >> simp[]
QED

Theorem for_array_origin_cons_mods:
  contract_inv mods exps ctx c cx /\ module_body_inv mods src tops c cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings (For id fty (Array e) n body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id fty (Array e) n body) ==>
      EXISTS (occurs_abi_decode_target target o SND) mods) /\
  ce_locals_declared c env /\ locals_alloc_ok c env /\
  type_stmt env ret_ty (For id fty (Array e) n body) = SOME env' /\
  stmt_exprs_ok c (For id fty (Array e) n body) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root c env)
    (For id fty (Array e) n body) /\
  (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
      (vyperSubscriptOverlap$accesses_stmt (For id fty (Array e) n body)) /\
      IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
      IS_SOME (FLOOKUP c.ce_module_vars key)) /\
  call_evaluation_safe cx (int_calls_stmt (For id fty (Array e) n body)) /\
  stmt_loop_calls_ok mods (For id fty (Array e) n body) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ c ret_ty /\
  evaluate_type (get_tenv cx) fty = SOME tyv /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_inst_ids_distinct func /\
  (!H. dead_lo_ok_mods H (DF H) lo c cx) /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  local_ptrs_reserved c sa0 /\ ~block_is_terminated sbCopy /\
  (is_slot_addressed loc ==>
    ?tgt nid. loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget nid) /\
  for_array_selected_origin_mods c cx lo (sty,bd,loc) sbExpr (vv_operand vv) vs P /\
  for_array_selector_static_mods c cx (e,sty,bd,saL) P /\
  body_for_full_ok_mods mods exps cx tyv id body vs /\
  ~s.vs_halted /\ storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    for_array_selected_header_mods mods exps (DF,lo,d,ctx,func,shadow_func) cx env st0
      (es0,sa0,s0,G0,tn0)
      ((c,id,fty,e,sty,bd,ret_ty,body),
       (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
       (bc,saD,saA,xd,capacity,aidItem),
       (entry,cond,bod,incr,exit,idx,invalid,valid,dv,next_var),
       (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy),
       (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody)) P H vs (a::rs) es G tn s) /\
  gas_admissible (eval_for cx tyv id body (a::rs)) (stmt_res_ok lctx) es ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) mods cx st0
    (do v <- read_result cx a;
        push_scope_with_var id tyv v;
        finally (try (do eval_stmts cx body; return F od)
                     handle_loop_exception) pop_scope od) (es,s,G,tn)
    (\H res ee G1 tn1 t. ee.gas_obs = [] /\ ~t.vs_halted /\ ?b. res = INL b /\
      (b ==> for_array_done_mods DF lo d ctx func c cx lctx sa0 sb es0 s0 G0 tn0 H ee G1 tn1 t) /\
      (~b ==> for_array_selected_header_mods mods exps (DF,lo,d,ctx,func,shadow_func)
        cx env st0 (es0,sa0,s0,G0,tn0)
        ((c,id,fty,e,sty,bd,ret_ty,body),
         (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
         (bc,saD,saA,xd,capacity,aidItem),
         (entry,cond,bod,incr,exit,idx,invalid,valid,dv,next_var),
         (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy),
         (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody)) P H vs rs ee G1 tn1 t))
    (\H res ee gt r. ?ex. res = INR ex /\
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
      halt_exit H cx ee (INR ex : unit + exception) r /\
      (ctx_has_dalloca ctx ==> !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z))
Proof
  PairCases_on `P` >>
  rename1 `for_array_selector_static_mods _ _ _ ((em,u,Gu,tu,dw,bw,capture),sel,w) /\ _` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!H. _ ==> for_array_selected_header_mods mods exps _ cx env st0 _ _ _ H vs _ es G tn s`
    (assume_tac o REWRITE_RULE [for_array_selected_header_route_mods]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> for_nonslot_layout _ _ _ _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  drule_then (qx_choosel_then [`inst`,`bc_out`] strip_assume_tac)
    for_array_layout_item_cut_mods >>
  `type_memory_size tyv <= capacity` by
    (qhdtm_assum `for_nonslot_layout`
       (strip_assume_tac o REWRITE_RULE [for_nonslot_layout_def]) >>
     qhdtm_assum `for_array_header_mods`
       (strip_assume_tac o REWRITE_RULE [for_array_header_mods_def]) >>
     drule_all_then assume_tac assign_name_memory_bytes_mods >> simp[]) >>
  qpat_x_assum `inst.inst_id = capacity_id` (SUBST_ALL_TAC o SYM) >>
  qabbrev_tac `Route = \H rs ee G1 tn1 t.
    for_array_observation_mods c cx lo (sty,bd,loc)
      (em,sbExpr,u,Gu,tu) (vv_operand vv,bw) vs
      ((em,u,Gu,tu,dw,bw,capture),sel) H rs ee G1 tn1 t /\
    for_array_selector_current_mods cx ((em,u,Gu,tu,dw,bw,capture),sel,w) ee` >>
  qabbrev_tac `Qold = \H (res:bool + exception) ee G1 tn1 t. ee.gas_obs = [] /\ ~t.vs_halted /\
    ?b. res = INL b /\
      (b ==> for_array_done_mods DF lo d ctx func c cx lctx sa0 sb es0 s0 G0 tn0 H ee G1 tn1 t) /\
      (~b ==> for_array_header_mods mods DF lo d ctx func c cx env id st0
        (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu) (xd,dw,capacity,inst.inst_id)
        vs (vv_operand vv,bw,len_op,idx) cond Route H rs ee G1 tn1 t /\
        body_stmts_full_ok_mods mods exps cx body)` >>
  irule gas_outcome_full_mods_post_path >> qexists_tac `Qold` >>
  conj_tac >-
    (simp[Abbr `Qold`, Abbr `Route`, for_array_selected_header_route_mods] >>
     rpt strip_tac >> qexists_tac `b` >> simp[]) >>
  simp[Abbr `Qold`] >>
  qhdtm_assum `for_nonslot_layout`
    (mp_then (Pat `for_nonslot_layout _ _ _ _ _ _ _`) irule
      for_array_cons_from_item_landed_mods) >>
  asm_rewrite_tac[] >>
  conj_tac >- suspend "copy" >>
  conj_tac >-
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> for_nonslot_layout _ _ _ _ _ _ _ /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >> first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "restore" >>
  conj_tac >- simp[] >>
  qexistsl [`bindings`,`env'`,`n`,`src`,`tops`] >> asm_rewrite_tac[]
QED

Resume for_array_origin_cons_mods[copy]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `Abbrev (Route = _)`
    (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (assume_tac o SIMP_RULE (srw_ss()) [for_array_observation_mods_def]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    for_array_header_mods mods DF lo d ctx func c cx env id st0
      (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu) (xd,dw,capacity,inst.inst_id)
      vs (vv_operand vv,bw,len_op,idx) bod (\_ _ _ _ _ _. T) H (a::rs) es Gh th sh /\
    for_array_entry_route_mods c cx lo (sty,bd,loc) (em,sbExpr,u,Gu,tu)
      (vv_operand vv,bw) vs capture H (a::rs) es G tn s` by
    (gen_tac >> disch_tac >>
     qpat_x_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _` drule >> simp[]) >>
  qpat_x_assum `a = EL k vs` kall_tac >>
  qpat_x_assum `rs = DROP (SUC k) vs` kall_tac >>
  qpat_x_assum `sh = jump_to _ _` kall_tac >>
  qpat_x_assum `Gh = DRESTRICT _ _` kall_tac >>
  qpat_x_assum `th = tn with t_var := _` kall_tac >>
  Cases_on `?tr off root path delta. capture = ForArraySlot tr off root path delta`
  >- (qpat_x_assum `?tr off root path delta. capture = _`
        (qx_choosel_then [`tr`,`off`,`root`,`path`,`delta`] SUBST_ALL_TAC) >>
      `loc = slot_loc tr` by
        (qhdtm_assum `for_array_selected_origin_mods`
           (mp_tac o REWRITE_RULE [for_array_selected_origin_mods_def,for_array_origin_mods_def]) >>
         simp[] >> strip_tac >> first_assum ACCEPT_TAC) >>
      `is_slot_addressed loc` by (Cases_on `tr` >> simp[slot_loc_def,is_slot_addressed_def]) >>
      qpat_x_assum `is_slot_addressed _ ==> _` (drule_then strip_assume_tac) >>
      qpat_x_assum `loc = slot_loc tr` SUBST_ALL_TAC >>
      qhdtm_assum `for_nonslot_layout`
        (mp_then (Pat `for_nonslot_layout _ _ _ _ _ _ _`) irule for_array_landed_slot_item_mods) >>
      asm_rewrite_tac[] >>
      conj_tac >- (qexistsl [`nid`,`tgt`] >> asm_rewrite_tac[]) >>
      qexistsl [`G`,`Gu`,`bw`,`delta`,`env`,`env'`,`mods`,`n`,`off`,`path`,`root`,`rs`,`s`,`tn`,`tr`,`vs`] >>
      asm_rewrite_tac[]) >>
  qhdtm_assum `for_nonslot_layout`
    (mp_then (Pat `for_nonslot_layout _ _ _ _ _ _ _`) irule for_array_landed_snapshot_item_mods) >>
  asm_rewrite_tac[] >>
  `well_typed_iterator env fty (Array e)` by
    (drule_then strip_assume_tac type_stmt_for_projection >> first_assum ACCEPT_TAC) >>
  qexistsl [`G`,`Gu`,`bw`,`capture`,`env`,`exps`,`mods`,`rs`,`s`,`tn`,`vs`] >>
  asm_rewrite_tac[] >> simp[] >>
  qpat_assum `~(?tr off root path delta. capture = _)` mp_tac >> simp[]
QED

Resume for_array_origin_cons_mods[restore]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `Abbrev (Route = _)`
    (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `for_array_header_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ es G tn s`
    (strip_assume_tac o BETA_RULE o MATCH_MP for_array_header_route_mods) >>
  `!k0. valid_horizon cx st0 k0 es.storage_trace ==>
    for_array_entry_route_mods c cx lo (sty,bd,loc) (em,sbExpr,u,Gu,tu)
      (vv_operand vv,bw) vs capture k0 (a::rs) es G tn s` by
    (qx_gen_tac `k0` >> disch_tac >>
     qpat_x_assum `!k0. valid_horizon _ _ k0 _ ==> for_nonslot_layout _ _ _ _ _ _ _ /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     qpat_assum `for_array_header_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k0 _ es G tn s`
       (strip_assume_tac o BETA_RULE o MATCH_MP for_array_header_route_mods) >>
     qpat_x_assum `for_array_observation_mods _ _ _ _ _ _ _ _ k0 _ _ _ _ _`
       (mp_tac o REWRITE_RULE [for_array_observation_mods_def]) >> simp[]) >>
  Cases_on `capture` >> Cases_on `w` >>
  qhdtm_x_assum `for_array_selector_static_mods`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [for_array_selector_static_mods_def]) >>
  qhdtm_x_assum `for_array_selected_origin_mods`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [for_array_selected_origin_mods_def,for_array_origin_mods_def])
  >- (qpat_x_assum `loc = slot_loc _` SUBST_ALL_TAC >>
      qpat_x_assum `sel = NONE` SUBST_ALL_TAC >>
      simp[NoAsms,for_array_observation_mods_def,for_array_selector_current_mods_def] >>
      irule for_array_slot_restore_mods >>
      rpt (first_assum (irule_at Any)) >>
      qexistsl [`tn`,`s`,`a`,`G`] >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (qpat_x_assum `loc = LocMemory` SUBST_ALL_TAC >>
      qpat_x_assum `sel = SOME _` SUBST_ALL_TAC >>
      simp[NoAsms,for_array_observation_mods_def,for_array_selector_current_mods_def] >>
      irule for_array_owned_restore_mods >>
      rpt (first_assum (irule_at Any)) >>
      qexistsl [`tn`,`s`,`a`,`G`] >>
      rpt conj_tac >- first_assum ACCEPT_TAC
      >- (qpat_assum `evaluate_type _ sty = SOME _` (fn th => simp[th])) >>
      first_assum ACCEPT_TAC)
  >- (rename1 `for_array_selector_current_mods cx
        ((_,_,_,_,_,_,ForArrayHeld name path av),sel,
         ArraySelectorHeld p attrs tail saved tv0 q sz rw delta) es` >>
      qpat_x_assum `loc = LocMemory` SUBST_ALL_TAC >>
      qpat_x_assum `sel = SOME av` SUBST_ALL_TAC >>
      qpat_x_assum `path = MAP AttrSubscript attrs ++ tail` SUBST_ALL_TAC >>
      qhdtm_x_assum `for_array_selector_current_mods`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [for_array_selector_current_mods_def]) >>
      drule_then strip_assume_tac type_stmt_for_projection >>
      `well_typed_expr (extend_local env id fty F) e` by
        (irule (cj 1 iterator_typing_extend_local) >> fs[well_typed_iterator_def]) >>
      `expr_type e = ArrayT sty bd` by
        (qhdtm_assum `for_nonslot_layout`
          (strip_assume_tac o REWRITE_RULE [for_nonslot_layout_def]) >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `IS_SOME (type_stmts _ _ _)`
        (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
      rename1 `lookup_scopes name es.scopes = SOME ent` >>
      `mem_path_offset ent.type (MAP AttrSubscript attrs ++ tail) = SOME (delta,ArrayTV tv0 bd)` by
        (qpat_assum `ent.type = saved.type` (fn th => simp[th])) >>
      qabbrev_tac `ee = fin with scopes := TL fin.scopes` >>
      simp[NoAsms,for_array_selector_current_mods_def] >>
      `for_array_observation_mods c cx lo (sty,bd,LocMemory)
         (em,sbExpr,u,Gu,tu) (vv_operand vv,bw) vs
         ((em,u,Gu,tu,dw,bw,ForArrayHeld name (MAP AttrSubscript attrs ++ tail) av),SOME av)
         H rs ee G1 tn1 f /\
       lookup_var q f = SOME rw /\ ptr_covers G1 tn1 q f sz /\
       (?entry. lookup_scopes name ee.scopes = SOME entry /\ entry.type = ent.type /\
         mem_path_offset entry.type (MAP AttrSubscript attrs ++ tail) = SOME (delta,ArrayTV tv0 bd) /\
         evaluate_subscripts entry.type entry.value (MAP AttrSubscript attrs ++ tail) = INL (ArrayV av))`
        suffices_by
          (strip_tac >> conj_tac >- first_assum ACCEPT_TAC >>
           rename1 `lookup_scopes name ee.scopes = SOME now` >>
           qexists_tac `now` >> simp[]) >>
      irule for_array_held_restore_mods >>
      qhdtm_assum `for_array_observation_mods` (irule_at Any) >>
      rpt (first_assum (irule_at Any)) >> simp[Abbr `ee`]) >>
  rename1 `for_array_selector_current_mods cx
    ((_,_,_,_,_,_,ForArrayImmutable src0 name path off itv delta av),sel,
     ArraySelectorImmutable ip iattrs itail icap) es` >>
  qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >>
  qpat_x_assum `sel = SOME icap` SUBST_ALL_TAC >>
  drule_then strip_assume_tac type_stmt_for_projection >>
  `ALOOKUP cx.sources cx.txn.target = SOME mods` by
    (qhdtm_assum `contract_inv` (mp_tac o REWRITE_RULE [contract_inv_def]) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `?tv. evaluate_type (get_tenv cx) (ArrayT sty bd) = SOME (ArrayTV tv bd)` by
    (`well_typed_expr env e` by fs[well_typed_iterator_def] >>
     qhdtm_assum `for_nonslot_layout`
       (strip_assume_tac o REWRITE_RULE [for_nonslot_layout_def]) >>
     qpat_assum `for_array_header_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ es G tn s`
       (strip_assume_tac o REWRITE_RULE [for_array_header_mods_def]) >>
     drule_then assume_tac expr_sim_inv_mods_env >>
     drule_then assume_tac env_consistent_type_defs_get_tenv >>
     drule_all checked_expr_type_well_formed >>
     simp[well_formed_type_def, evaluate_type_def]) >>
  `for_array_entry_route_mods c cx lo (sty,bd,LocCode) (em,sbExpr,u,Gu,tu)
    (vv_operand vv,bw) vs (ForArrayImmutable src0 name path off itv delta av)
    (storage_trace_horizon es.storage_trace) (a::rs) es G tn s` by
    (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `ee = fin with scopes := TL fin.scopes` >>
  qpat_assum `for_array_header_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ee G1 tn1 f`
    (strip_assume_tac o REWRITE_RULE [for_array_header_mods_def]) >>
  qhdtm_x_assum `for_array_selector_current_mods`
    (qx_choose_then `current_root` strip_assume_tac o
     SIMP_RULE (srw_ss()) [for_array_selector_current_mods_def]) >>
  simp[NoAsms,for_array_observation_mods_def,for_array_selector_current_mods_def] >>
  `for_array_entry_route_mods c cx lo (sty,bd,LocCode) (em,sbExpr,u,Gu,tu)
    (vv_operand vv,bw) vs (ForArrayImmutable src0 name path off itv delta av) H rs ee G1 tn1 f /\
   (?now. lookup_immutable cx ee src0 name = SOME (itv,now) /\
          evaluate_subscripts itv now (MAP AttrSubscript iattrs) = INL (ArrayV icap) /\
          evaluate_subscripts itv now path = INL (ArrayV av))`
    suffices_by
      (strip_tac >> rpt conj_tac >- first_assum ACCEPT_TAC
       >- (rename1 `lookup_immutable cx ee src0 name = SOME (itv,new_root)` >>
           qexistsl [`iattrs`,`itail`,`new_root`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
       rename1 `lookup_immutable cx ee src0 name = SOME (itv,new_root)` >>
       qexists_tac `new_root` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. dead_lo_ok_mods H (DF H) lo c cx` (qspec_then `H` assume_tac) >>
  irule for_array_immutable_restore_mods >>
  qhdtm_assum `for_array_entry_route_mods` (irule_at Any) >>
  qpat_assum `lookup_immutable cx es src0 name = SOME (itv,current_root)` (irule_at Any) >>
  rpt (first_assum (irule_at Any)) >> simp[Abbr `ee`]
QED

Finalise for_array_origin_cons_mods
