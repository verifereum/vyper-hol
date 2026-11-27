(* The read-only length slice carries the linked expression frame to its
   actual instruction cursor; the original statement frame stays anchored. *)
Theory bodyForArrayLengthLinkedTransportMods
Ancestors
  bodyForArrayHeaderMods bodyForRangeHeaderMods bodyForRangeScalarFrameMods
  bodyPtrSignedConvertSourceFrame bodyBinopFragMemory stmtReasonLitFragMemory
  bodyFullIfExpReach bodyFullShadowBodyInv bodyFullPostsMods bodyMemoryDefs
  exprSimCopy fragGasOriginPtr allocaHistory freshWrites loweringPosts
  bodySimFull ptrDiscipline
  stmtSimDefs stmtSimProps compileEnv venomState venomExecSemantics
  unitTransformDefs contextRawReachable loweringStateRelDefs rich_list finite_map

Theorem array_length_history[local]:
  fn_has_code se saL func /\ saL.cs_current_bb = se.cs_current_bb /\
  saL.cs_current_insts = se.cs_current_insts ++ code /\
  EVERY (\i. i.inst_opcode <> ALLOCA) code /\
  r.vs_current_bb = se.cs_current_bb /\ u.vs_current_bb = r.vs_current_bb /\
  r.vs_inst_idx = LENGTH se.cs_current_insts /\
  u.vs_inst_idx = LENGTH saL.cs_current_insts /\
  u.vs_allocas = r.vs_allocas /\ alloca_history func r ==>
  alloca_history func u
Proof
  strip_tac >>
  drule_all_then strip_assume_tac fn_has_code_code >>
  qpat_x_assum `isPREFIX code _`
    (qx_choose_then `rest` assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  `u with vs_inst_idx := r.vs_inst_idx + LENGTH code = u` by
    simp[venom_state_component_equality] >>
  pop_assum (SUBST1_TAC o SYM) >>
  irule alloca_history_no_alloca_slice >>
  simp[] >> qexistsl_tac [`bb`,`rest`] >> simp[]
QED

Theorem array_length_return[local]:
  return_buf_frame d c se r /\ return_buf_sep d c em r /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!x. not_fresh_at se x ==> lookup_var x u = lookup_var x r) /\
  (!nm b sz. local_region c em.scopes u nm b sz <=> local_region c em.scopes r nm b sz) /\
  u.vs_allocas = r.vs_allocas /\ u.vs_alloca_next = r.vs_alloca_next ==>
  return_buf_frame d c sa0 u /\ return_buf_sep d c em u
Proof
  Cases_on `d` >- simp[return_buf_frame_def,return_buf_sep_def] >>
  rename1 `return_buf_frame (SOME rb)` >> PairCases_on `rb` >>
  strip_tac >> conj_tac
  >- (qpat_x_assum `return_buf_frame _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [return_buf_frame_def]) >>
      simp[return_buf_frame_def] >> goal_assum (drule_at Any) >> simp[]) >>
  fs[return_buf_sep_def,allocas_from_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem for_array_length_linked_transport_mods:
  fn_has_code se saL func /\ saL.cs_current_bb = se.cs_current_bb /\
  saL.cs_current_insts = se.cs_current_insts ++ code /\
  EVERY (\i. i.inst_opcode <> ALLOCA) code /\
  r.vs_current_bb = se.cs_current_bb /\ r.vs_inst_idx = LENGTH se.cs_current_insts /\
  u.vs_inst_idx = LENGTH saL.cs_current_insts /\
  u = r with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!x. not_fresh_at se x ==> lookup_var x u = lookup_var x r /\
       FLOOKUP Gu x = FLOOKUP Gr x /\ op_taint tu (Var x) = op_taint tr (Var x)) /\
  tu.t_mem = tr.t_mem /\ tu.t_stor = tr.t_stor /\ tu.t_trans = tr.t_trans /\ tu.t_imm = tr.t_imm /\
  local_ptrs_reserved c se /\ sa0.cs_next_var <= se.cs_next_var /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  ret_pc_ok c sa0 r /\ return_buf_frame d c se r /\ return_buf_sep d c em r /\
  stmt_state_rel H ctx func c cx em r /\ immutable_frame_mods func c cx em r /\
  storage_well_formed_on cx em (FST H) /\ ghost_inv_at_mods D lo d c cx em Gr tr r /\
  for_array_outer_frame_mods ctx func c sa0 es0 s0 G0 tn0 em Gr tr r /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (r,Gr,tr) [] (OK u,Gu,tu) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst q. frag_reachable ctx func r fn inst q ==> dalloca_fmp_headroom inst q) ==>
  ret_pc_ok c sa0 u /\ return_buf_frame d c sa0 u /\ return_buf_sep d c em u /\
  stmt_state_rel H ctx func c cx em u /\ immutable_frame_mods func c cx em u /\
  storage_well_formed_on cx em (FST H) /\ ghost_inv_at_mods D lo d c cx em Gu tu u /\
  for_array_outer_frame_mods ctx func c sa0 es0 s0 G0 tn0 em Gu tu u /\
  (!fn inst q. frag_reachable ctx func u fn inst q ==> dalloca_fmp_headroom inst q)
Proof
  strip_tac >>
  `u.vs_memory = r.vs_memory /\ u.vs_allocas = r.vs_allocas /\
   u.vs_alloca_next = r.vs_alloca_next /\ u.vs_data_section = r.vs_data_section /\
   u.vs_call_ctx = r.vs_call_ctx /\ u.vs_accounts = r.vs_accounts /\
   u.vs_transient = r.vs_transient /\ u.vs_immutables = r.vs_immutables /\
   u.vs_initial_fmp = r.vs_initial_fmp /\ u.vs_fmp = r.vs_fmp /\
   u.vs_current_bb = r.vs_current_bb` by
    (rpt conj_tac >> qpat_assum `u = _` (fn th => simp[Once th])) >>
  `!x. not_fresh_at sa0 x ==> not_fresh_at se x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa0` >> simp[]) >>
  `!x. not_fresh_at sa0 x ==> lookup_var x u = lookup_var x r /\
       FLOOKUP Gu x = FLOOKUP Gr x /\ op_taint tu (Var x) = op_taint tr (Var x)` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `!nm b sz. local_region c em.scopes u nm b sz <=> local_region c em.scopes r nm b sz` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists_tac `se` >> simp[]) >>
  `alloca_history func r` by fs[for_array_outer_frame_mods_def,range_outer_frame_mods_def] >>
  `alloca_history func u` by
    (irule array_length_history >> qexistsl_tac [`code`,`r`,`saL`,`se`] >> fs[]) >>
  `ret_pc_ok c sa0 u` by fs[ret_pc_ok_def] >>
  `return_buf_frame d c sa0 u /\ return_buf_sep d c em u` by
    (irule array_length_return >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`r`,`se`] >> simp[]) >>
  `stmt_state_rel H ctx func c cx em u` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl_tac [`r`,`se`] >> simp[]) >>
  `immutable_frame_mods func c cx em u` by
    (irule immutable_frame_mods_exterior_frame >> qexistsl_tac [`em`,`r`,`se`] >> simp[]) >>
  `ghost_inv_at_mods D lo d c cx em Gu tu u` by
    (irule ghost_inv_at_mods_exterior_frame >> qexistsl_tac [`Gr`,`em`,`r`,`se`,`tr`] >>
     simp[] >> fs[ret_pc_ok_def] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (fs[for_array_outer_frame_mods_def,range_outer_frame_mods_def,
         alloca_frame_def,allocas_below_fmp_def] >>
      rpt conj_tac >-
        (strip_tac >> qpat_assum `ctx_has_dalloca ctx ==> _` drule >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  drule gas_origin_ptr_path_dalloca_fmp_headroom >>
  disch_then (mk_asm "headroom") >> rpt gen_tac >> strip_tac >>
  asm "headroom" irule >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `fn` >> first_assum ACCEPT_TAC
QED
