(* Checked element copies for runtime immutable array iteration. *)
Theory bodyImmCopyPtr
Ancestors
  exprSimPtrTopLevelImmutableCopy exprSimPtrTopLevelImmutableRun exprSimPtrTopLevelImmutablePost
  whitelistForIterImmCopy forPtrWriteScope forPtrRangePrepare
  annAssignPtrStore exprSimPtrLiteralBuffer exprSimStorageCopy exprSimCopy immutableCopyExecution
  exprLoweringProps loweringStateRelDefs loweringPosts valueEncodingProps emitHelperProps
  context compileEnv bodyPtrDefs ptrDiscipline venomState venomInst
  finite_map words list arithmetic pred_set
Libs monadsyntax

Theorem immutable_iter_copy_words:
  0 < type_memory_size tv ==>
  compile_iter_elem_copy cenv src dst (type_memory_size tv) LocCode F ty ty =
  compile_imm_copy_to_memory cenv.ce_is_ctor cenv.ce_imm_alloca
    src dst (type_slot_size tv) 0
Proof
  simp[type_memory_size_slots] >> strip_tac >>
  Cases_on `32 * type_slot_size tv <= 32`
  >- (`type_slot_size tv = 1` by decide_tac >>
      simp[immutable_iter_small_copy] >>
      CONV_TAC (RAND_CONV (ONCE_DEPTH_CONV numLib.num_CONV)) >>
      simp[compile_imm_copy_to_memory_def, immutable_copy_one_def,
        compile_lit_byte_offset_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, FUN_EQ_THM] >> gen_tac >>
      pairarg_tac >> pairarg_tac >> gvs[] >> pairarg_tac >> simp[]) >>
  simp[immutable_iter_large_copy, arithmeticTheory.ADD_DIV_ADD_DIV]
QED

Theorem immutable_iter_copy_checked:
  compile_iter_elem_copy cenv src (Var p) bytes LocCode F ty ty sa = ((),sb) /\
  bytes = type_memory_size tv /\ 0 < bytes /\ ~cenv.ce_is_ctor /\
  copy_old_operand sa src /\ not_fresh_at sa p /\
  eval_operand src s = SOME a /\ lookup_var p s = SOME b /\
  op_taint tn src = {} /\ ptr_covers G tn p s cap /\ bytes <= cap /\
  w2n b + cap < dimword (:256) /\ ~ctx_has_dalloca ctx ==>
  ?t H tm.
    copy_runtime_frame sa s sb t /\
    (!k. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) H tm) /\
    ptr_covers H tm p t cap /\
    immutable_copy_ghost_frame sa s G tn sb t H tm 0 bytes b
Proof
  strip_tac >> gvs[] >>
  drule immutable_iter_copy_words >> strip_tac >> gvs[] >>
  drule toplevel_immutable_copy_frame >>
  simp[GSYM type_memory_size_slots] >>
  strip_tac >> first_x_assum drule_all >>
  disch_then (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) >>
  qexistsl [`t`,`H`,`tm`] >>
  gvs[type_memory_size_slots, immutable_copy_ghost_frame_def]
QED

Theorem immutable_iter_copy_ptr:
  compile_iter_elem_copy cenv src (Var p) bytes LocCode F ty ty sa = ((),sb) /\
  bytes = type_memory_size tv /\ 0 < bytes /\ ~cenv.ce_is_ctor /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  ghost_inv d cenv cx es G tn s /\
  es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME b /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n b,cap) /\
  bytes <= cap /\ w2n b + cap < dimword (:256) /\
  immutable_holds cenv cx ty (Value v) a es s /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\ op_taint tn src = {} /\
  ptr_covers G tn p s cap /\ local_ptrs_reserved cenv sa /\
  (!q sz. cenv.ce_return_buf = SOME (PtrVar (Var q) sz) \/
     cenv.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at sa q) /\
  ~ctx_has_dalloca ctx ==>
  ?t H tm.
    copy_runtime_frame sa s sb t /\
    (!k. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) H tm) /\
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
        (sc |+ (id, <|assignable := assign; type := tv; value := v; popped := []|>)) :: rest) t /\
    ghost_inv d cenv cx
      (es with scopes :=
        (sc |+ (id, <|assignable := assign; type := tv; value := v; popped := []|>)) :: rest) H tm t /\
    ptr_covers H tm p t cap /\
    val_wf tv v /\ val_in_memory tv v (w2n b) t.vs_memory /\
    val_footprint tv v <= bytes /\
    immutable_copy_ghost_frame sa s G tn sb t H tm 0 bytes b
Proof
  strip_tac >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  drule_all immutable_iter_copy_checked >>
  disch_then (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) >>
  `copy_old_operand sa (Var p) /\ eval_operand (Var p) s = SOME b` by
    simp[copy_old_operand_def, eval_operand_def] >>
  `w2n b + bytes < dimword (:256)` by decide_tac >>
  `cenv.ce_is_ctor ==> regions_disjoint (w2n a) bytes (w2n b) bytes` by simp[] >>
  `!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region` by simp[] >>
  drule_all immutable_iter_copy_typed_run_full >> strip_tac >>
  `z = t` by gvs[copy_runtime_frame_def] >> gvs[] >>
  `!q. q = p \/ ~not_local_ptr cenv es.scopes q ==> not_fresh_at sa q` by
    (fs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  `type_memory_size tv + w2n b < dimword (:256)` by decide_tac >>
  drule_at (Pat `stmt_state_rel _ _ _ _ _ _`) immutable_iter_copy_declare_rel >>
  gvs[] >> strip_tac >>
  `type_memory_size tv + w2n b < dimword (:256)` by decide_tac >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum (qspec_then `assign` strip_assume_tac) >>
  `z = t` by gvs[copy_runtime_frame_def] >> gvs[] >>
  qexistsl [`t`,`H`,`tm`] >> simp[] >>
  `ghost_inv d cenv cx es H tm t` by suspend "outer" >>
  irule annassign_ghost_scope_update_ptr >> simp[] >>
  rpt strip_tac >>
  `w = b` by gvs[copy_runtime_frame_def] >> gvs[] >>
  irule literal_clean_representation_robust >> simp[] >>
  qexistsl [`tm.t_mem`,`t.vs_memory`] >> simp[] >>
  rpt strip_tac >>
  gvs[immutable_copy_ghost_frame_def] >>
  simp[] >> decide_tac
QED

Resume immutable_iter_copy_ptr[outer]:
  qpat_assum `stmt_state_rel ctx func cenv cx es s`
    (mp_then Any mp_tac for_alloca_scalar_write_separation) >>
  simp[] >> strip_tac >>
  irule ghost_inv_after_separated_write >>
  qexistsl [`G`,`{q | not_fresh_at sa q}`,`s`,`tn`,
    `{i | w2n b <= i /\ i < w2n b + type_memory_size tv}`] >> simp[] >>
  gvs[immutable_copy_ghost_frame_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >-
    (rpt gen_tac >> disch_then strip_assume_tac >>
     conj_tac >- (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     first_x_assum drule_all >> strip_tac >> simp[] >>
     rpt strip_tac >> first_x_assum drule_all >> decide_tac) >>
  conj_tac >- (gvs[copy_runtime_frame_def]) >>
  `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient` by
    gvs[copy_runtime_frame_def, copy_static_def, venom_state_component_equality] >>
  simp[mem_agree_outside_def] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED
Finalise immutable_iter_copy_ptr
