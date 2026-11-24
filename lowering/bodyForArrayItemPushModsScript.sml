(* Interpret the copied Array item as a local without another target step. *)
Theory bodyForArrayItemPushMods
Ancestors
  bodyForArrayHeaderMods bodyForRangeHeaderMods
  bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit
  bodyMemoryDefs bodyPtrDefs bodySimFull stmtFragPtr stmtSimDeclCompose
  stmtSimProps stmtSimDefs stateRelProj exprLoweringProps loweringStateRelDefs
  memoryValueEncoding compileEnv vyperStorageFootprint vyperState
  venomMemDefs ptrDiscipline finite_map

Theorem array_item_region_module[local]:
  local_region (c with ce_module := src) scopes z n a l <=> local_region c scopes z n a l
Proof
  simp[local_region_def]
QED

Theorem array_item_scope_lookups[local]:
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var xd) cap) /\
  (!n. n <> id ==> FLOOKUP bc.ce_vars n = FLOOKUP c.ce_vars n) /\
  ep.scopes = (FEMPTY |+ (id,ent))::es.scopes /\ lookup_var xd z = SOME dw ==>
  (!n. n <> id ==> lookup_scopes n ep.scopes = lookup_scopes n es.scopes) /\
  (!src n b sz. local_region (bc with ce_module := src) ep.scopes z n b sz <=>
      if n = id then b = w2n dw /\ sz = cap else local_region c es.scopes z n b sz)
Proof
  strip_tac >> conj_tac
  >- simp[lookup_scopes_def, FLOOKUP_UPDATE] >>
  rpt gen_tac >> Cases_on `n = id` >>
  simp[local_region_def, lookup_scopes_def, FLOOKUP_UPDATE]
QED

Theorem array_item_local_ptrs[local]:
  local_ptrs_rel func c es.scopes z /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var xd) cap) /\
  (!n. n <> id ==> FLOOKUP bc.ce_vars n = FLOOKUP c.ce_vars n) /\
  ep.scopes = (FEMPTY |+ (id,ent))::es.scopes /\ lookup_var xd z = SOME dw /\
  local_backed func xd z (w2n dw) cap /\ w2n dw + cap <= z.vs_alloca_next /\
  type_memory_size ent.type <= cap /\ val_wf ent.type ent.value /\
  memory_value_rel ent.type ent.value (w2n dw) z.vs_memory /\
  (!n b sz. local_region c es.scopes z n b sz ==> regions_disjoint (w2n dw) cap b sz) ==>
  local_ptrs_rel func bc ep.scopes z
Proof
  strip_tac >> drule_all_then strip_assume_tac array_item_scope_lookups >>
  `!n b sz. local_region bc ep.scopes z n b sz <=>
      if n = id then b = w2n dw /\ sz = cap else local_region c es.scopes z n b sz` by
    (rpt gen_tac >> Cases_on `n = id` >>
     simp[local_region_def, lookup_scopes_def, FLOOKUP_UPDATE]) >>
  qhdtm_x_assum `local_ptrs_rel` (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
  rw[local_ptrs_rel_def]
  >- (Cases_on `name = id` >- (gvs[lookup_scopes_def, FLOOKUP_UPDATE] >> qexists_tac `dw` >> simp[]) >>
      fs[lookup_scopes_def, FLOOKUP_UPDATE] >>
      qpat_assum `!n. n <> id ==> FLOOKUP bc.ce_vars n = _` (drule_then (fs o single)) >>
      first_assum (drule_all_then ACCEPT_TAC)) >>
  Cases_on `n1 = id` >> Cases_on `n2 = id` >> gvs[]
  >- first_assum (drule_then ACCEPT_TAC)
  >- (qpat_assum `!n b sz. local_region _ _ _ n b sz ==> regions_disjoint (w2n dw) cap b sz`
        (drule_then mp_tac) >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  first_assum (drule_all_then ACCEPT_TAC)
QED

(* Both declaration-time and initialized-immutable separation already protect
   this row, before its address becomes visible through the new scope. *)
Theorem array_item_immutable_sep[local]:
  immutable_alloca_sep func c cx es z /\
  bc.ce_module_vars = c.ce_module_vars /\ bc.ce_module_var_type = c.ce_module_var_type /\
  bc.ce_module = c.ce_module /\ bc.ce_is_ctor = c.ce_is_ctor /\
  ep.immutables = es.immutables /\
  FLOOKUP z.vs_allocas inst.inst_id = SOME (b,sz) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  (!n a l. local_region bc ep.scopes z n a l ==>
            (a = b /\ l = sz) \/ local_region c es.scopes z n a l) ==>
  immutable_alloca_sep func bc cx ep z
Proof
  simp[immutable_alloca_sep_def, immutable_decl_sep_alt] >> strip_tac >>
  conj_tac >> rpt strip_tac >>
  first_assum (drule_all_then strip_assume_tac) >>
  first_assum (drule_then strip_assume_tac) >> gvs[] >> metis_tac[]
QED

Theorem array_item_stmt_scope[local]:
  stmt_state_rel H ctx func c cx es z /\
  local_ptrs_rel func bc ep.scopes z /\ immutable_alloca_sep func bc cx ep z /\
  bc.ce_module_vars = c.ce_module_vars /\ bc.ce_module_var_type = c.ce_module_var_type /\
  bc.ce_module = c.ce_module /\ bc.ce_is_ctor = c.ce_is_ctor /\ bc.ce_imm_alloca = c.ce_imm_alloca /\
  ep = es with <|scopes := scopes; gas_obs := []|> ==>
  stmt_state_rel H ctx func bc cx ep z
Proof
  strip_tac >>
  qpat_x_assum `ep = _` SUBST_ALL_TAC >>
  qhdtm_x_assum `stmt_state_rel` mp_tac >>
  simp[stmt_state_rel_def, state_rel_def, immutable_base_zero_def,
       storage_vars_rel_def, transient_vars_rel_def, immutables_rel_def,
       logs_rel_def, log_entry_equiv_def, loweringStateRelDefsTheory.storage_rel_def,
       transient_rel_def, accounts_rel_def] >>
  strip_tac >> rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  qpat_assum `LIST_REL (log_entry_equiv c _) _ _` mp_tac >>
  simp[FUN_EQ_THM, ETA_AX, log_entry_equiv_def] >>
  `log_entry_equiv bc cx.txn.target = log_entry_equiv c cx.txn.target` by
    simp[FUN_EQ_THM, log_entry_equiv_def] >> simp[]
QED

Theorem array_item_linked_immutables[local]:
  immutable_frame_mods func c cx es z /\
  bc.ce_modules = c.ce_modules /\ bc.ce_module_vars = c.ce_module_vars /\
  bc.ce_module_var_type = c.ce_module_var_type /\ bc.ce_is_ctor = c.ce_is_ctor /\
  ep.immutables = es.immutables /\
  FLOOKUP z.vs_allocas inst.inst_id = SOME (b,sz) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  (!src n a l. local_region (bc with ce_module := src) ep.scopes z n a l ==>
            (a = b /\ l = sz) \/ local_region c es.scopes z n a l) ==>
  immutable_frame_mods func bc cx ep z
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def, immutables_rel_def,
       immutable_alloca_sep_mods_def] >> strip_tac >> conj_tac
  >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!src tops. _ ==> immutable_alloca_sep _ _ _ _ _`
    (drule_then assume_tac) >>
  irule array_item_immutable_sep >>
  goal_assum (drule_at (Pat `immutable_alloca_sep _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP z.vs_allocas _.inst_id = _`)) >>
  simp[] >> rpt strip_tac >>
  first_assum (drule_then strip_assume_tac)
  >- simp[] >>
  disj2_tac >>
  qpat_assum `local_region c es.scopes z n a l`
    (mp_tac o REWRITE_RULE [local_region_def]) >> simp[local_region_def]
QED

Theorem array_item_pushed_ghost[local]:
  ghost_inv_at_mods D lo d c cx es G tn z /\
  bc.ce_return_buf = c.ce_return_buf /\ bc.ce_return_pc = c.ce_return_pc /\
  bc.ce_imm_alloca = c.ce_imm_alloca /\ imm_section_dead_mods bc = imm_section_dead_mods c /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var xd) cap) /\
  (!n. n <> id ==> FLOOKUP bc.ce_vars n = FLOOKUP c.ce_vars n) /\
  ep.scopes = (FEMPTY |+ (id,ent))::es.scopes /\ lookup_var xd z = SOME dw /\
  ptr_covers G tn xd z cap /\
  (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
         val_in_memory ent.type ent.value (w2n dw) mem) ==>
  ghost_inv_at_mods D lo d bc cx ep G tn z
Proof
  strip_tac >>
  `return_buf_ptr d bc G tn z <=> return_buf_ptr d c G tn z` by
    (Cases_on `d` >- simp[return_buf_ptr_def] >> PairCases_on `x` >> simp[return_buf_ptr_def]) >>
  qhdtm_x_assum `ghost_inv_at_mods` mp_tac >> simp[ghost_inv_at_mods_def] >>
  strip_tac >> rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  rpt gen_tac >> Cases_on `name = id` >> simp[lookup_scopes_def, FLOOKUP_UPDATE]
  >- (strip_tac >> gvs[]) >>
  strip_tac >> first_assum (drule_all_then ACCEPT_TAC)
QED

Theorem array_item_pushed_return_sep[local]:
  return_buf_sep d c es z /\ FLOOKUP z.vs_allocas aid = SOME (b,sz) /\
  (!n a l. local_region bc ep.scopes z n a l ==>
            (a = b /\ l = sz) \/ local_region c es.scopes z n a l) ==>
  return_buf_sep d bc ep z
Proof
  Cases_on `d` >- simp[return_buf_sep_def] >> PairCases_on `x` >>
  simp[return_buf_sep_def] >> strip_tac >> simp[] >> rpt strip_tac >>
  qpat_assum `!n a l. local_region bc _ _ _ _ _ ==> _` (drule_then strip_assume_tac)
  >- (gvs[] >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
      disj1_tac >>
      qhdtm_assum `allocas_from` (drule_then ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  first_assum (drule_then ACCEPT_TAC)
QED

Theorem array_item_lift_anchor[local]:
  alloca_frame c anchor start before c es z /\
  (!aid row. FLOOKUP before.vs_allocas aid = SOME row ==>
             FLOOKUP z.vs_allocas aid = SOME row) /\
  allocas_non_overlapping z /\ FLOOKUP z.vs_allocas itemAid = SOME (b,cap) /\
  start.cs_next_id <= itemAid /\
  (!n a l. local_region bc ep.scopes z n a l ==>
           (a = b /\ l = cap) \/ local_region c es.scopes z n a l) ==>
  alloca_frame c anchor start before bc ep z
Proof
  simp[alloca_frame_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `!aid off sz. _ ==> mem_bytes_at _ _ _ = _ /\ _`
    (drule_all_then strip_assume_tac) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!n a l. local_region bc _ _ _ _ _ ==> _` (drule_then strip_assume_tac)
  >- (gvs[] >> `aid <> itemAid` by decide_tac >>
      qhdtm_assum `allocas_non_overlapping`
        (mp_tac o REWRITE_RULE [allocas_non_overlapping_def]) >>
      disch_then (qspecl_then [`aid`,`itemAid`,`off`,`sz`,`b`,`cap`] mp_tac) >>
      simp[GSYM arithmeticTheory.ADD_ASSOC]) >>
  first_assum (drule_then ACCEPT_TAC)
QED

Theorem for_array_item_push_frame_mods:
  declare_local c id typ saLen = (bc,saD) /\ c.ce_alloca_locals /\
  (!l. FLOOKUP c.ce_vars id = SOME l ==> ?p sz. l = PtrVar p sz) /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var xd) cap) /\
  lookup_scopes id es.scopes = NONE /\ type_memory_size tyv <= cap /\
  value_has_type tyv v /\ val_wf tyv v /\
  ep = es with <|scopes := (FEMPTY |+ (id,<|assignable := F; type := tyv;
                                          value := v; popped := []|>))::es.scopes;
                 gas_obs := []|> /\
  (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
         val_in_memory tyv v (w2n dw) mem) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [xd] /\
  for_array_item_mods c sa saExpr (xd,dw,cap,inst.inst_id) es G tn z /\
  for_array_outer_frame_mods ctx func c sa es0 s0 G0 tn0 es G tn z /\
  for_array_capture_frame_mods c (em,saExpr,saLen,u,tu) es tn z /\
  sa.cs_next_var <= sbCopy.cs_next_var /\
  ret_pc_ok c sa z /\ return_buf_frame d c sa z /\ return_buf_sep d c es z /\
  stmt_state_rel H ctx func c cx es z /\ immutable_frame_mods func c cx es z /\
  storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods D lo d c cx es G tn z ==>
  cenv_top_ext c bc ep.scopes /\
  stmt_state_rel H ctx func bc cx ep z /\ immutable_frame_mods func bc cx ep z /\
  storage_well_formed_on cx ep (FST H) /\ ghost_inv_at_mods D lo d bc cx ep G tn z /\
  ret_pc_ok bc sbCopy z /\ return_buf_frame d bc sbCopy z /\ return_buf_sep d bc ep z /\
  alloca_frame c es0 sa s0 bc ep z /\ alloca_frame c em saExpr u bc ep z
Proof
  strip_tac >> drule_all_then strip_assume_tac declare_local_ptr >>
  qpat_x_assum `FLOOKUP bc.ce_vars id = SOME (PtrVar (Var (STRING #"%" _)) _)` kall_tac >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `allocas_non_overlapping z` by fs[alloca_inv_def] >>
  simp[NoAsms] >>
  qhdtm_x_assum `for_array_item_mods` (strip_assume_tac o REWRITE_RULE [for_array_item_mods_def]) >>
  qabbrev_tac `ent = <|assignable := F; type := tyv; value := v; popped := []|>` >>
  `ep.scopes = (FEMPTY |+ (id,ent))::es.scopes /\ ep.immutables = es.immutables` by simp[] >>
  drule_all_then strip_assume_tac array_item_scope_lookups >>
  `!src n a l. local_region (bc with ce_module := src) ep.scopes z n a l ==>
            (a = w2n dw /\ l = cap) \/ local_region c es.scopes z n a l` by
    (rpt gen_tac >> Cases_on `n = id` >> simp[]) >>
  `!n a l. local_region bc ep.scopes z n a l ==>
            (a = w2n dw /\ l = cap) \/ local_region c es.scopes z n a l` by
    (qpat_assum `!src n a l. local_region _ _ _ _ _ _ ==> _`
       (mp_tac o REWRITE_RULE [array_item_region_module]) >> simp[]) >>
  qpat_assum `bc with <|ce_vars := _; ce_var_type := _; ce_dynarray_capacity := _|> = c`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [compile_env_component_equality]) >>
  suspend "local"
QED

Resume for_array_item_push_frame_mods[local]:
  `local_backed func xd z (w2n dw) cap` by
    (simp[local_backed_def] >> disj1_tac >> qexists_tac `inst` >> simp[]) >>
  `memory_value_rel tyv v (w2n dw) z.vs_memory` by
    (irule val_in_memory_memory_value_rel >> simp[mem_agree_outside_def]) >>
  `local_ptrs_rel func bc ep.scopes z` by
    (irule array_item_local_ptrs >> goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP bc.ce_vars id = _`)) >>
     goal_assum (drule_at (Pat `ep.scopes = _`)) >>
     goal_assum (drule_at (Pat `lookup_var xd z = _`)) >>
     simp[Abbr `ent`, loweringStateRelDefsTheory.regions_disjoint_def] >>
     rpt strip_tac >>
     qpat_assum `!nm b sz. local_region c es.scopes z nm b sz ==> _`
       (drule_then mp_tac) >> simp[]) >>
  conj_tac >-
    (qpat_assum `ep.scopes = _` (rewrite_tac o single) >>
     irule cenv_top_ext_declare_local >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`id`,`saLen`,`saD`,`typ`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "stmt" >>
  conj_tac >- suspend "immutable" >>
  conj_tac >- (irule (iffRL storage_well_formed_on_backends) >> qexists_tac `es` >> simp[]) >>
  conj_tac >- suspend "ghost" >>
  suspend "return_and_frames"
QED

Resume for_array_item_push_frame_mods[stmt]:
  `immutable_alloca_sep func bc cx ep z` by
    (irule array_item_immutable_sep >>
     goal_assum (drule_at (Pat `FLOOKUP z.vs_allocas _.inst_id = _`)) >>
     qexists_tac `c` >> qexists_tac `es` >>
     fs[stmt_state_rel_def]) >>
  irule array_item_stmt_scope >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`c`,`es`,`(FEMPTY |+ (id,ent))::es.scopes`] >> simp[]
QED

Resume for_array_item_push_frame_mods[immutable]:
  irule array_item_linked_immutables >>
  goal_assum (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP z.vs_allocas _.inst_id = _`)) >> simp[]
QED

Resume for_array_item_push_frame_mods[ghost]:
  irule array_item_pushed_ghost >>
  goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP bc.ce_vars id = _`)) >>
  goal_assum (drule_at (Pat `ep.scopes = _`)) >>
  goal_assum (drule_at (Pat `lookup_var xd z = _`)) >>
  simp[Abbr `ent`, FUN_EQ_THM, imm_section_dead_mods_def]
QED

Resume for_array_item_push_frame_mods[return_and_frames]:
  conj_tac >- (irule ret_pc_ok_frame >> goal_assum (drule_at (Pat `ret_pc_ok _ _ _`)) >> simp[]) >>
  conj_tac >- (irule return_buf_frame_frame >> goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >> simp[]) >>
  conj_tac >- (irule array_item_pushed_return_sep >>
    goal_assum (drule_at (Pat `return_buf_sep _ _ _ _`)) >>
    qexistsl_tac [`inst.inst_id`,`w2n dw`,`cap`] >> simp[]) >>
  fs[for_array_outer_frame_mods_def, range_outer_frame_mods_def,
     for_array_capture_frame_mods_def] >>
  conj_tac >> irule array_item_lift_anchor >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`w2n dw`,`cap`,`es`,`inst.inst_id`] >>
  simp[]
QED

Finalise for_array_item_push_frame_mods
