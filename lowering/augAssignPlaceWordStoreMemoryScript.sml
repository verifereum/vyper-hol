(* Counted one-word writes for computed place destinations. *)
Theory augAssignPlaceWordStoreMemory
Ancestors
  placeStore bodyDeclMemoryCounted bodyDeclMemoryCore allocaFootprint
  instMemFrontier fragGasMode venomExecSemantics venomInst venomState
  emitHelperProps exprSimProps exprLoweringProps memSafeRun loweringPosts

Theorem place_store_emit_run_mem[local]:
  (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient) /\
  emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                       | _ => MSTORE) [dst; op] sa = ((),sb) /\
  eval_operand dst s = SOME w /\ eval_operand op s = SOME wd /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (loc = LocMemory \/ ~s.vs_call_ctx.cc_static) /\
  (loc = LocMemory ==> w2n w + 32 <= s.vs_alloca_next) /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  u = (case loc of LocStorage => sstore w wd s
                | LocTransient => tstore w wd s
                | _ => mstore (w2n w) wd s) ==>
  gas_marked_path T ctx func s 0
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  (!x. lookup_var x u = lookup_var x s) /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id
     (case loc of LocStorage => SSTORE | LocTransient => TSTORE | _ => MSTORE)
     [dst; op] []) s = OK u` by
    (gvs[] >> simp[step_inst_base_opcode_eqs, mk_inst_def,
                    exec_write2_def]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK u` by
    (gvs[] >> simp[run_inst_seq_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule emit_void_mem_ok >> disch_then irule >>
     gvs[] >> simp[below_frontier_MSTORE, below_frontier_no_ranges,
                   inst_dload_in_section_other, mk_inst_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (gvs[] >> simp[mk_inst_def, is_terminator_def]) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by simp[] >>
  drule_all body_decl_cursor_path >> strip_tac >>
  `alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s`, `sa`] >> gvs[] >> simp[mk_inst_def, is_terminator_def]) >>
  simp[gas_marked_path_def] >>
  gvs[] >> simp[mstore_def, sstore_def, tstore_def, lookup_var_def]
QED

(* A step that keeps the memory and the registers handed out before sp
   keeps an alloca frame, re-read at scopes with the same names. *)
Theorem alloca_frame_memory_kept:
  !H c0 e0 sa0 s0 c ee t ctx func cx sp ee1 u.
  alloca_frame c0 e0 sa0 s0 c ee t /\ stmt_state_rel H ctx func c cx ee t /\
  local_ptrs_reserved c sp /\ MAP FDOM ee1.scopes = MAP FDOM ee.scopes /\
  (!x w. not_fresh_at sp x /\ lookup_var x t = SOME w ==>
         lookup_var x u = SOME w) /\
  u.vs_memory = t.vs_memory ==>
  alloca_frame c0 e0 sa0 s0 c ee1 u
Proof
  rpt gen_tac >> rewrite_tac[stmtSimDefsTheory.alloca_frame_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas _ = _ /\ _ ==> _`
    (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  conj_tac >- fs[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!n b sz'. local_region c ee.scopes t _ _ _ ==> _` irule >>
  metis_tac[stmtSimDefsTheory.local_region_kept]
QED

(* The one-word store keeps an alloca frame: a storage or transient store
   leaves memory alone, and a local store writes inside the local. *)
Theorem place_store_word_alloca_frame[local]:
  alloca_frame c0 e0 sa0 s0 cenv ee s /\
  stmt_state_rel H ctx func cenv cx ee s /\ local_ptrs_reserved cenv sa /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
  is_word_type dty /\ evaluate_type (get_tenv cx) dty = SOME dtv /\
  (!id path entry t0.
     p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
     cenv.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  write_place cx p v ee = (INL (), ff) ==>
  alloca_frame c0 e0 sa0 s0 cenv ff
    ((case loc of LocStorage => sstore w wd s
                | LocTransient => tstore w wd s
                | _ => mstore (w2n w) wd s) with vs_inst_idx := ix)
Proof
  strip_tac >>
  `MAP FDOM ff.scopes = MAP FDOM ee.scopes` by
    metis_tac[vyperScopePreservationTheory.write_place_scopes_dom] >>
  Cases_on `p` >> gvs[place_ptr_rel_def]
  >- (rename1 `StoragePlace tr slot tv` >> Cases_on `tr` >> gvs[slot_loc_def] >>
      irule alloca_frame_memory_kept >>
      simp[sstore_def, tstore_def, lookup_var_def] >> metis_tac[]) >>
  rename1 `MemoryPlace id path` >>
  drule placeMemoryStateRebuildTheory.write_memory_place_entry_update >>
  strip_tac >>
  drule mem_path_offset_sound >> strip_tac >>
  `local_region cenv ee.scopes s id (w2n b) sz` by
    (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
  `local_ptrs_rel func cenv ee.scopes s` by
    fs[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_def, alloca_room_next_lt] >>
  `type_memory_size entry.type <= sz /\ w2n b + sz <= s.vs_alloca_next` by
    (fs[loweringStateRelDefsTheory.local_ptrs_rel_def] >>
     qpat_x_assum `!name ent p sz. _` drule >>
     disch_then drule >> strip_tac >> gvs[]) >>
  `evaluate_type (get_tenv cx) t0 = SOME entry.type` by metis_tac[] >>
  drule_all word_tv_memory_size >> strip_tac >>
  gvs[] >>
  `w2n b + k < dimword (:256)` by decide_tac >>
  `w2n (b + n2w k) = w2n b + k` by
    (rewrite_tac[wordsTheory.word_add_def] >> simp[]) >>
  irule stmtSimDefsTheory.alloca_frame_region_write >>
  goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
  simp[] >>
  conj_tac >- simp[lookup_var_def, mstore_def] >>
  rpt strip_tac >> simp[] >>
  irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> decide_tac
QED

(* The stored state satisfies the relation at every horizon that observes the
   place: the proof does not look at the horizon, so one witness serves all. *)
Theorem place_store_word_state_any[local]:
  place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
  is_word_type dty /\ expr_sim_inv cenv cx env ee /\
  storage_place_observed H p /\
  (!id path entry t0.
     p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
     cenv.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
  stmt_state_rel H ctx func cenv cx ee s /\
  write_place cx p v ee = (INL (), ff) ==>
  stmt_state_rel H ctx func cenv cx ff
    (case loc of LocStorage => sstore w (typed_val_to_w256 dtv v) s
               | LocTransient => tstore w (typed_val_to_w256 dtv v) s
               | _ => mstore (w2n w) (typed_val_to_w256 dtv v) s)
Proof
  strip_tac >> Cases_on `p`
  >- (gvs[place_ptr_rel_def, slot_loc_def] >>
      drule_all place_store_word_backend_state >> Cases_on `b` >> gvs[])
  >- (rename1 `MemoryPlace id path` >>
      `loc = LocMemory` by fs[place_ptr_rel_def] >>
      gvs[] >> irule place_store_word_memory_state >>
      qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
      qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `evaluate_type _ dty = _` (irule_at Any) >> simp[])
  >> gvs[place_ptr_rel_def, slot_loc_def] >>
  drule_all place_store_word_backend_state >> Cases_on `b` >> gvs[]
QED

Theorem place_store_word_run_mem:
  emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                       | _ => MSTORE) [dst_op; op] sa = ((), sb) /\
  eval_operand dst_op s = SOME w /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
  (!x. dst_op = Var x ==> not_fresh_at sa x) /\
  is_word_type dty /\ expr_val_rel cx dty v op s /\
  expr_sim_inv cenv cx env ee /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  local_ptrs_reserved cenv sa /\
  (!id path entry t0.
     p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
     cenv.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
  stmt_state_rel H ctx func cenv cx ee s /\
  write_place cx p v ee = (INL (), ff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s /\
  (loc = LocMemory ==> w2n w + 32 <= s.vs_alloca_next) ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      (!H'. storage_place_observed H' p /\
            stmt_state_rel H' ctx func cenv cx ee s ==>
            stmt_state_rel H' ctx func cenv cx ff t) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s.vs_alloca_next = t.vs_alloca_next /\
      (!c0 e0 sa0 sx. alloca_frame c0 e0 sa0 sx cenv ee s ==>
                      alloca_frame c0 e0 sa0 sx cenv ff t)
Proof
  strip_tac >>
  `eval_operand op s = SOME (typed_val_to_w256 dtv v)` by
    (fs[expr_val_rel_def] >> metis_tac[]) >>
  qabbrev_tac `u = (case loc of LocStorage => sstore w (typed_val_to_w256 dtv v) s
                  | LocTransient => tstore w (typed_val_to_w256 dtv v) s
                  | _ => mstore (w2n w) (typed_val_to_w256 dtv v) s)` >>
  `!H'. storage_place_observed H' p /\
        stmt_state_rel H' ctx func cenv cx ee s ==>
        stmt_state_rel H' ctx func cenv cx ff u` by
    (gen_tac >> strip_tac >> simp[Abbr `u`] >>
     mp_tac (Q.INST [`H` |-> `H'`] place_store_word_state_any) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  drule_all place_store_write_location >> strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  `gas_marked_path T ctx func s 0
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   (!x. lookup_var x u = lookup_var x s) /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb` by
    (irule place_store_emit_run_mem >> simp[] >>
     qexistsl_tac [`dst_op`, `loc`, `op`, `sa`] >>
     simp[Abbr `u`]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[stmt_state_rel_inst_idx, lookup_var_def] >>
  rpt strip_tac >> drule_all place_store_word_alloca_frame >> simp[Abbr `u`]
QED
