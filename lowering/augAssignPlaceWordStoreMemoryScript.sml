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
    (gvs[] >> rewrite_tac[step_inst_base_def, mk_inst_def] >>
     simp[exec_write2_def]) >>
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

Theorem place_store_word_run_mem:
  emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                       | _ => MSTORE) [dst_op; op] sa = ((), sb) /\
  eval_operand dst_op s = SOME w /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
  (!x. dst_op = Var x ==> not_fresh_at sa x) /\
  is_word_type dty /\ expr_val_rel cx dty v op s /\
  expr_sim_inv cenv cx env ee /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
  (!id path entry t0.
     p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
     cenv.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
  stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p v ee = (INL (), ff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s /\
  (loc = LocMemory ==> w2n w + 32 <= s.vs_alloca_next) ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx ff t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s.vs_alloca_next = t.vs_alloca_next
Proof
  strip_tac >>
  `eval_operand op s = SOME (typed_val_to_w256 dtv v)` by
    (fs[expr_val_rel_def] >> metis_tac[]) >>
  qabbrev_tac `u = (case loc of LocStorage => sstore w (typed_val_to_w256 dtv v) s
                  | LocTransient => tstore w (typed_val_to_w256 dtv v) s
                  | _ => mstore (w2n w) (typed_val_to_w256 dtv v) s)` >>
  `stmt_state_rel ctx func cenv cx ff u` by
    (Cases_on `p`
     >- (gvs[place_ptr_rel_def, Abbr `u`, slot_loc_def] >>
         drule_all place_store_word_backend_state >> Cases_on `b` >> gvs[])
     >- (rename1 `MemoryPlace id path` >>
         `loc = LocMemory` by fs[place_ptr_rel_def] >>
         gvs[Abbr `u`] >> irule place_store_word_memory_state >>
         qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
         qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
         qpat_assum `evaluate_type _ dty = _` (irule_at Any) >> simp[])
     >> gvs[place_ptr_rel_def, Abbr `u`, slot_loc_def] >>
     drule_all place_store_word_backend_state >> Cases_on `b` >> gvs[]) >>
  drule_all place_store_write_location >> strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def, compileEnvTheory.state_rel_def] >>
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
  fs[stmt_state_rel_inst_idx, lookup_var_def]
QED
