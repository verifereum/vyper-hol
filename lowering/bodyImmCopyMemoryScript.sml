(* Memory certificates for immutable For element preparation. *)
Theory bodyImmCopyMemory
Ancestors
  whitelistForIterImmCopy bodyImmutableCopyMemory exprSimMemUnwrap
  exprSimBopRestWordLoadSafety exprSimCopy valueEncodingProps
  stmtLowering context emitHelper compileEnv exprLoweringProps
  immutableCopyExecution words arithmetic exprSimStorageCopy
  allocaHistory bodyMemoryDefs venomState

Theorem immutable_iter_slot_copy[local]:
  0 < type_memory_size tv ==>
  compile_iter_elem_copy ce src dst (type_memory_size tv) LocCode F ty ty =
  compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca
    src dst (type_slot_size tv) 0
Proof
  simp[type_memory_size_slots] >> strip_tac >>
  Cases_on `type_slot_size tv <= 1`
  >- (`type_slot_size tv = 1` by decide_tac >>
      simp[immutable_iter_small_copy, compile_imm_copy_to_memory_compute,
           compile_lit_byte_offset_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def, FUN_EQ_THM] >>
      gen_tac >> pairarg_tac >> simp[] >>
      simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def,
           comp_return_def]) >>
  simp[immutable_iter_large_copy, ADD_DIV_ADD_DIV]
QED

Theorem immutable_iter_copy_mem_ok:
  compile_iter_elem_copy cenv src dst bytes LocCode F ty ty sa = ((),sb) /\
  bytes = type_memory_size tv /\ 0 < bytes /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel ctx func cenv cx es s /\
  immutable_holds cenv cx ty (Value v) a es s /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  w2n b + bytes <= s.vs_alloca_next /\
  w2n b + bytes < dimword (:256) /\
  (!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> gvs[] >>
  drule_all rest_word_immutable_region_bound >> strip_tac >>
  drule_all immutable_holds_bounds >> strip_tac >>
  gvs[immutable_iter_slot_copy] >>
  Cases_on `cenv.ce_is_ctor` >> gvs[]
  >- (irule body_ctor_copy_mem_ok >>
      goal_assum (drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)) >>
      simp[GSYM type_memory_size_slots]) >>
  irule body_immutable_copy_mem_ok >>
  goal_assum (drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)) >>
  simp[GSYM type_memory_size_slots]
QED

Theorem immutable_iter_copy_mem_run:
  compile_iter_elem_copy cenv src dst bytes LocCode F ty ty sa = ((),sb) /\
  bytes = type_memory_size tv /\ 0 < bytes /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel ctx func cenv cx es s /\
  immutable_holds cenv cx ty (Value v) a es s /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  w2n b + bytes <= s.vs_alloca_next /\
  w2n b + bytes < dimword (:256) /\
  (cenv.ce_is_ctor ==> regions_disjoint (w2n a) bytes (w2n b) bytes) /\
  (!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) /\
  alloca_history func s /\ return_buf_frame d cenv sa s ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  ?z. copy_runtime_frame sa s sb z /\
      val_wf tv v /\ val_in_memory tv v (w2n b) z.vs_memory /\
      val_footprint tv v <= bytes /\
      LENGTH s.vs_memory <= LENGTH z.vs_memory /\
      (!off len. off + len <= w2n b \/ w2n b + bytes <= off ==>
        mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
      (z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      z.vs_alloca_next = s.vs_alloca_next /\ z.vs_allocas = s.vs_allocas /\
      alloca_history func z /\ return_buf_frame d cenv sb z
Proof
  strip_tac >> conj_tac
  >- (drule_all immutable_iter_copy_mem_ok >> simp[]) >>
  drule_all immutable_iter_copy_typed_run_full >> strip_tac >>
  `copy_static z = copy_static s` by fs[copy_runtime_frame_def] >>
  drule copy_static_fields >> strip_tac >>
  `alloca_history func z` by
    (irule alloca_history_frame >> qexists_tac `s` >>
     gvs[venom_state_component_equality]) >>
  `return_buf_frame d cenv sb z` by
    (irule return_buf_frame_frame >> goal_assum (drule_at Any) >>
     fs[copy_runtime_frame_def]) >>
  qexists_tac `z` >> gvs[] >> metis_tac[]
QED
