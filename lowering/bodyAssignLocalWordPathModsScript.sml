(* Clean MSTORE at a reached word subplace of an existing local. *)
Theory bodyAssignLocalWordPathMods
Ancestors
  bodyLocalCopyWritesMods augAssignFullPathWriteRobust wordLoadStorePtr
  placeMemoryStateRebuild exprSimPopNestedLocalPost bodyMemoryDefs
  vyperScopePreservation vyperPlaceFrames vyperLookup vyperState
  bodyFullShadowBodyInv stmtSimDeclStore loweringStateRelDefs localPtrsProps
  stateRelProj exprLoweringProps loweringSlice bodyPtrDefs typedMemoryCopy
  stmtSimDefs bodySimFull bodyFullShared bodyFullAbiEncodeStore
  augAssignFullMstoreSafety instMemFrontier loweringShapeRules memSafeRun
  fragExec fragGasOriginPtr emitHelperProps bodyFullUnwrapRun bodyFullHashKeccakFixed
  venomInst venomExecSemantics vyperStorageFootprint exprOpenPrimitives list
  valueEncodingProofs valueEncodingProps memoryValueEncoding ptrDiscipline exprSimProps
  venomState finite_map pred_set words

Theorem assign_local_word_robust[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  lookup_var p s = SOME b /\
  mem_path_offset entry.type path = SOME (off,ptv) /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  value_has_type entry.type entry.value /\ value_has_type ptv v /\
  store_lays_out etv ptv v /\ off + 32 <= cap /\
  write_place cx (MemoryPlace id path) v es = (INL (),ee) ==>
  !name e q sz. lookup_scopes name ee.scopes = SOME e /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) sz) ==>
    ptr_covers G tn q s sz /\
    !w mem. lookup_var q s = SOME w /\
      mem_agree_outside (tn.t_mem DIFF {j | w2n b + off <= j /\ j < w2n b + off + 32})
        (mstore (w2n b + off) (typed_val_to_w256 etv v) s).vs_memory mem ==>
      val_in_memory e.type e.value (w2n w) mem
Proof
  strip_tac >> drule write_memory_place_entry_update >> strip_tac >> gvs[] >>
  gvs[replace_memory_entry_def, AllCaseEqs()] >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  rpt gen_tac >> strip_tac >> Cases_on `name = id`
  >- (gvs[] >> conj_tac >- metis_tac[] >>
      rpt strip_tac >> gvs[] >> irule augassign_path_word_store_robust >>
      goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
      goal_assum (drule_at (Pat `assign_subscripts _ _ _ _ = _`)) >>
      qexistsl_tac [`old`, `s`, `tn.t_mem`, `typed_val_to_w256 etv v`] >>
      fs[store_lays_out_def] >> metis_tac[val_footprint_le]) >>
  `lookup_scopes name es.scopes = SOME e` by metis_tac[] >>
  conj_tac >- metis_tac[] >> rpt gen_tac >> strip_tac >>
  `local_region cenv es.scopes s id (w2n b) cap /\
   local_region cenv es.scopes s name (w2n w) sz` by simp[local_region_def] >>
  `regions_disjoint (w2n b) cap (w2n w) sz` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >> metis_tac[]) >>
  `w2n w + sz <= w2n b + off \/ w2n b + off + 32 <= w2n w` by
    (fs[regions_disjoint_def] >> decide_tac) >>
  irule mstore_local_robust >>
  goal_assum (drule_at (Pat `mem_agree_outside _ _ _`)) >>
  qexistsl_tac [`cenv`, `func`, `name`, `q`, `es.scopes`, `sz`, `tn.t_mem`] >>
  pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >>
  (conj_tac >- (rpt strip_tac >> metis_tac[])) >>
  rpt conj_tac >> FIRST [REFL_TAC, first_assum ACCEPT_TAC, decide_tac]
QED

Theorem assign_local_word_install[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  lookup_var p s = SOME b /\ mem_path_offset entry.type path = SOME (off,ptv) /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  value_has_type ptv v /\ store_lays_out etv ptv v /\ off + 32 <= cap /\
  write_place cx (MemoryPlace id path) v es = (INL (),ee) ==>
  stmt_state_rel H ctx func cenv cx ee
    (mstore (w2n b + off) (typed_val_to_w256 etv v) s with vs_inst_idx := pc)
Proof
  strip_tac >> simp[stmt_state_rel_inst_idx] >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `local_region cenv es.scopes s id (w2n b) cap` by simp[local_region_def] >>
  qabbrev_tac `t = mstore (w2n b + off) (typed_val_to_w256 etv v) s` >>
  `type_memory_size ptv = 32 /\ val_in_memory ptv v (w2n b + off) t.vs_memory` by
    fs[store_lays_out_def, Abbr `t`] >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   (!x. lookup_var x t = lookup_var x s)` by
    simp[Abbr `t`, mstore_def, lookup_var_def] >>
  `local_ptrs_rel func cenv ee.scopes t` by
    (irule memory_place_write_local_ptrs >>
     goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
     goal_assum (drule_at (Pat `lookup_var _ s = SOME b`)) >>
     qexists_tac `cap` >> simp[] >>
     rpt strip_tac >> simp[Abbr `t`] >>
     irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by metis_tac[write_place_scopes_dom] >>
  drule write_memory_place_frame >> strip_tac >> gvs[] >>
  irule pop_path_stmt_state_rel >> simp[] >>
  goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
  qexistsl_tac [`off`, `sa`, `typed_val_to_w256 etv v`] >>
  simp[Abbr `t`, mstore_def, venom_state_component_equality]
QED

Theorem assign_local_word_linked_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  u = (mstore a w s with vs_inst_idx := pc) /\
  tf = (tn with t_mem := tn.t_mem DIFF {q | a <= q /\ q < a + 32}) /\
  lo <= a /\
  (!name e q sz. lookup_scopes name ee.scopes = SOME e /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) sz) ==>
    ptr_covers G tn q s sz /\
    !p mem. lookup_var q s = SOME p /\ mem_agree_outside tf.t_mem u.vs_memory mem ==>
      val_in_memory e.type e.value (w2n p) mem) ==>
  ghost_inv_at_mods D lo d cenv cx ee G tf u
Proof
  strip_tac >> gvs[] >>
  `mem_bytes_at 0 lo (mstore a w s).vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  simp[ghost_inv_at_mods_def] >> conj_tac
  >- (rpt strip_tac >> first_assum (drule_all_then strip_assume_tac) >>
      gvs[ptr_covers_def, op_taint_def, lookup_var_def, mstore_def]) >>
  conj_tac
  >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
      PairCases_on `x` >>
      gvs[return_buf_ptr_def, ptr_covers_def, op_taint_def, lookup_var_def, mstore_def]) >>
  gvs[op_taint_def, stor_taint_ok_at_def, allocas_from_def, mstore_def, IN_DIFF] >>
  metis_tac[]
QED

Theorem assign_local_word_mstore_path[local]:
  emit_void MSTORE [Var q;op] sa = ((),sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var q s = SOME a /\ eval_operand op s = SOME w /\
  ptr_covers G tn q s 32 /\ op_taint tn op = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ w2n a + 32 <= s.vs_alloca_next ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (mstore (w2n a) w s with vs_inst_idx := LENGTH sb.cs_current_insts), G,
     tn with t_mem := tn.t_mem DIFF {j | w2n a <= j /\ j < w2n a + 32})
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MSTORE [Var q;op] []]` by gvs[emit_void_eq] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst sa.cs_next_id MSTORE [Var q;op] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `s.vs_inst_idx + 1 = LENGTH sb.cs_current_insts` by simp[] >>
  `step_taint (mk_inst sa.cs_next_id MSTORE [Var q;op] []) s
     (mstore (w2n a) w s) tn =
     (tn with t_mem := tn.t_mem DIFF {j | w2n a <= j /\ j < w2n a + 32})` by
    (irule (cj 2 augassign_mstore_clean_transition) >> simp[eval_operand_def]) >>
  qpat_x_assum `step_taint _ _ _ _ = _` (once_rewrite_tac o single o SYM) >>
  qpat_x_assum `_ + 1 = LENGTH sb.cs_current_insts`
    (once_rewrite_tac o single o SYM) >>
  REWRITE_TAC[GSYM arithmeticTheory.ADD1] >>
  irule abi_encode_mstore_origin_path >> simp[] >>
  conj_tac >- metis_tac[] >> simp[below_frontier_MSTORE, eval_operand_def]
QED

Theorem assign_local_word_mstore_history[local]:
  emit_void MSTORE [Var q;op] sa = ((),sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var q s = SOME a /\ eval_operand op s = SOME w ==>
  alloca_history func (mstore (w2n a) w s with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id MSTORE [Var q;op] []]` by gvs[emit_void_eq] >>
  `step_inst_base (mk_inst sa.cs_next_id MSTORE [Var q;op] []) s = OK (mstore (w2n a) w s)` by
    (irule step_MSTORE >> simp[eval_operand_def]) >>
  `run_inst_seq [mk_inst sa.cs_next_id MSTORE [Var q;op] []] s = OK (mstore (w2n a) w s)` by
    simp[run_inst_seq_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) [mk_inst sa.cs_next_id MSTORE [Var q;op] []]` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all emitted_alloca_history >> simp[]
QED

(* Both the whole-word NameTarget (off = 0) and a selected word subplace
   use this last store. The old path must be readable: a successful
   write_place alone can also be the source semantics' no-op case. *)
Theorem assign_local_word_write_mods:
  emit_void MSTORE [Var q;op] sa = ((),sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ local_ptrs_reserved cenv sa /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\ lookup_var p s = SOME b /\
  mem_path_offset entry.type path = SOME (off,ptv) /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  value_has_type ptv v /\ store_lays_out etv ptv v /\ off + 32 <= cap /\
  lookup_var q s = SOME a /\ w2n a = w2n b + off /\ lo <= w2n a /\
  eval_operand op s = SOME (typed_val_to_w256 etv v) /\
  ptr_covers G tn q s 32 /\ op_taint tn op = {} /\
  write_place cx (MemoryPlace id path) v es = (INL (),ee) /\
  stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
  ghost_inv_at_mods D lo d cenv cx es G tn s /\ return_buf_frame d cenv sa s /\
  return_buf_sep d cenv es s /\ alloca_frame c0 es0 sa0 s0 cenv es s /\
  u = (mstore (w2n a) (typed_val_to_w256 etv v) s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  tf = (tn with t_mem := tn.t_mem DIFF {j | w2n a <= j /\ j < w2n a + 32}) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G,tf) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  stmt_state_rel H ctx func cenv cx ee u /\ immutable_frame_mods func cenv cx ee u /\
  ghost_inv_at_mods D lo d cenv cx ee G tf u /\ return_buf_frame d cenv sb u /\
  return_buf_sep d cenv ee u /\ alloca_frame c0 es0 sa0 s0 cenv ee u /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  (!x. lookup_var x u = lookup_var x s) /\
  (!x. op_taint tf (Var x) = op_taint tn (Var x)) /\ tf.t_mem SUBSET tn.t_mem /\
  ~block_is_terminated sb /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (fn_inst_ids_distinct func /\ alloca_history func s ==> alloca_history func u) /\
  (storage_well_formed_on cx es (FST H) ==> storage_well_formed_on cx ee (FST H))
Proof
  strip_tac >>
  `local_region cenv es.scopes s id (w2n b) cap` by simp[local_region_def] >>
  `w2n a + 32 <= s.vs_alloca_next` by
    (drule_all body_local_region_frontier >> decide_tac) >>
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by metis_tac[write_place_scopes_dom] >>
  `ee.immutables = es.immutables` by metis_tac[write_memory_place_immutables] >>
  conj_tac >-
    (qpat_assum `u = _` (once_rewrite_tac o single) >>
     qpat_assum `tf = _` (once_rewrite_tac o single) >>
     irule assign_local_word_mstore_path >> metis_tac[]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\ sb.cs_next_var = sa.cs_next_var` by
    gvs[emit_void_eq] >>
  `!x. lookup_var x u = lookup_var x s` by simp[mstore_def, lookup_var_def] >>
  `typed_copy_state_frame sa (w2n a) 32 s u` by simp[typed_copy_mstore_state_frame] >>
  `~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts` by simp[mstore_def] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `u = _` (once_rewrite_tac o single) >>
     qpat_assum `w2n a = _` (once_rewrite_tac o single) >>
     drule_all assign_local_word_install >> simp[]) >>
  conj_tac >- (irule local_copy_immutable_frame_mods >>
    goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
    goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >> simp[] >> decide_tac) >>
  conj_tac >-
    (irule assign_local_word_linked_ghost >>
     goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `u = _`)) >> simp[] >>
     drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
     mp_tac assign_local_word_robust >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  conj_tac >- (irule return_buf_frame_frame >>
    goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >> simp[mstore_def]) >>
  conj_tac >-
    (irule return_buf_sep_locals_kept >> conj_tac
     >- (rpt gen_tac >> disch_tac >>
         gvs[return_buf_sep_def, allocas_from_def, mstore_def] >>
         first_assum ACCEPT_TAC) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >> metis_tac[]) >>
  conj_tac >-
    (irule alloca_frame_region_write >>
     goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >> simp[] >>
     rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `~block_is_terminated sb` by (drule emit_void_terminated >> simp[is_terminator_def]) >>
  `fn_inst_ids_distinct func /\ alloca_history func s ==> alloca_history func u` by
    (strip_tac >> drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
     qpat_assum `u = _` (once_rewrite_tac o single) >>
     drule_all assign_local_word_mstore_history >> simp[]) >>
  `storage_well_formed_on cx es (FST H) ==> storage_well_formed_on cx ee (FST H)` by
    (drule write_memory_place_storage >> simp[storage_well_formed_on_def]) >>
  `allocas_below_fmp u <=> allocas_below_fmp s` by
    simp[allocas_below_fmp_def, mstore_def] >>
  simp[op_taint_def, mstore_def, SUBSET_DEF, IN_DIFF]
QED
