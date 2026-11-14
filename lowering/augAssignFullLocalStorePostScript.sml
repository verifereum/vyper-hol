(* The full post of the explicit local AugAssign word store. *)
Theory augAssignFullLocalStorePost
Ancestors
  augAssignFullOperator augAssignFullSource augAssignFullRhs
  wordLoadStorePtr exprPtrUnwrapCopyEdges fragGasSeqPtr fragGasOriginPtr
  emitHelperProps codegenRel contextCodegenRel unitTransformDefs
  instMemFrontier memSafeRun venomExecSemantics venomInst venomState
  compileEnv stmtLowering exprLoweringProps fragExec list
  bodyFullMemoryFrames bodySimFull
  assignTuplePtrStoreWord stmtSimAugAssign stmtSimDeclStore
  stmtSimAssignStore stmtSimDefs bodyMemoryDefs bodyPtrDefs bodyBinopFragMemory
  allocaHistory stmtSimProps exprSimProps vyperStorageFootprint
  vyperLookup loweringStateRelDefs loweringPosts ptrDiscipline
  exprOpenPrimitives exprLowering finite_map pred_set

(* The compiled AugAssign output environment is needed in the ghost post. *)
Theorem augassign_local_store_output_ghost_full[local]:
  stmt_env cenv lctx ret_ty (AugAssign ty (NameTarget id) bop e) sa = (c,sf) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME aw /\ eval_operand op s = SOME (typed_val_to_w256 etv v) /\
  op_taint tn op = {} /\
  write_place cx (MemoryPlace id []) v es = (res,ee) /\
  (!m. res <> INR (Error (TypeError m))) /\
  (!entry. lookup_scopes id es.scopes = SOME entry ==> store_lays_out etv entry.type v) /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  lo <= w2n aw /\
  t = (mstore (w2n aw) (typed_val_to_w256 etv v) s with
    vs_inst_idx := LENGTH sf.cs_current_insts) /\
  Gf = step_prov PG G (mk_inst sc.cs_next_id MSTORE [Var p;op] [])
    (mstore (w2n aw) (typed_val_to_w256 etv v) s) /\
  tf = step_taint (mk_inst sc.cs_next_id MSTORE [Var p;op] []) s
    (mstore (w2n aw) (typed_val_to_w256 etv v) s) tn ==>
  ghost_inv_at D lo d c cx ee Gf tf t
Proof
  strip_tac >>
  `c = cenv` by metis_tac[augassign_local_code_parts] >>
  qpat_x_assum `c = cenv` SUBST_ALL_TAC >> gvs[] >>
  drule_all write_place_local >> strip_tac >> gvs[] >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `store_lays_out etv entry.type v` by simp[] >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `32 <= sz` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
     rewrite_tac[local_ptrs_rel_def] >> strip_tac >>
     first_x_assum (qspecl_then [`id`, `entry`, `p`, `sz`] mp_tac) >>
     simp[] >> strip_tac >> fs[store_lays_out_def]) >>
  `local_region cenv es.scopes s id (w2n aw) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `sc.cs_next_id`] strip_assume_tac) >>
  drule body_full_local_scope_ghost_post >> disch_then irule >>
  simp[lookup_var_def, op_taint_def] >>
  conj_tac >- fs[ghost_inv_at_def] >>
  conj_tac >- suspend "prefix" >>
  conj_tac >- (gvs[ghost_inv_at_def, allocas_from_def, mstore_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- suspend "storage_taint" >>
  conj_tac >- metis_tac[] >>
  qexistsl [`aw`, `32`] >> simp[lookup_var_def] >>
  conj_tac >- (rpt strip_tac >> irule store_lays_out_robust_ptr >> metis_tac[]) >>
  suspend "exterior"
QED
Resume augassign_local_store_output_ghost_full[prefix]:
  irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> simp[]
QED
Resume augassign_local_store_output_ghost_full[storage_taint]:
  `(step_taint (mk_inst sc.cs_next_id MSTORE [Var p;op] []) s
    (mstore (w2n aw) (typed_val_to_w256 etv v) s) tn).t_imm = tn.t_imm` by
    simp[step_taint_def, imm_taint_def, mk_inst_def] >>
  fs[ghost_inv_at_def, stor_taint_ok_at_def] >>
  simp[mstore_def]
QED
Resume augassign_local_store_output_ghost_full[exterior]:
  reverse conj_tac >- fs[lookup_var_def] >>
  rpt strip_tac >>
  irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> decide_tac
QED
Finalise augassign_local_store_output_ghost_full

Theorem augassign_local_store_post_full:
  stmt_env cenv lctx ret_ty (AugAssign ty (NameTarget id) bop e) sa = (cenv,sf) /\
  emit_void MSTORE [Var p;op] sc = ((),sf) /\ fn_has_code sc sf func /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ cs_extends sa sc /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME aw /\ eval_operand op s = SOME (typed_val_to_w256 etv v) /\
  op_taint tn op = {} /\
  write_place cx (MemoryPlace id []) v es = (res,ee) /\
  (!m. res <> INR (Error (TypeError m))) /\
  (!entry. lookup_scopes id es.scopes = SOME entry ==> store_lays_out etv entry.type v) /\
  stmt_state_rel H ctx func cenv cx es s /\
  storage_well_formed_on cx es (FST H) /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  stmt_state_rel H ctx func cenv cx es0 s0 /\
  alloca_frame cenv es0 sa s0 cenv es s /\
  MAP FDOM es.scopes = MAP FDOM es0.scopes /\ local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sc s /\ alloca_history func s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ lo <= w2n aw /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  t = (mstore (w2n aw) (typed_val_to_w256 etv v) s with
    vs_inst_idx := LENGTH sf.cs_current_insts) /\
  Gf = step_prov PG G (mk_inst sc.cs_next_id MSTORE [Var p;op] [])
    (mstore (w2n aw) (typed_val_to_w256 etv v) s) /\
  tf = step_taint (mk_inst sc.cs_next_id MSTORE [Var p;op] []) s
    (mstore (w2n aw) (typed_val_to_w256 etv v) s) tn ==>
  res = INL () /\
  ?cenv'. stmt_lands lctx sf res t /\ ~t.vs_halted /\
    (res = INL () ==> ~block_is_terminated sf /\ cenv' = cenv) /\
    cenv_top_ext cenv cenv' ee.scopes /\
    stmt_state_rel H ctx func cenv' cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d cenv' sf t /\ alloca_history func t /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at D lo d cenv' cx ee Gf tf t /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
      op_taint tf (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >>
  drule_all augassign_local_store_output_ghost_full >> strip_tac >>
  drule_all write_place_local >> strip_tac >> gvs[] >>
  `sf.cs_current_bb = sc.cs_current_bb /\
   sf.cs_current_insts = sc.cs_current_insts ++ [mk_inst sc.cs_next_id MSTORE [Var p;op] []] /\
   sf.cs_next_var = sc.cs_next_var` by
    (drule emitted_insts_emit_void >> drule emit_void_same_blocks >>
     simp[same_blocks_def]) >>
  `~block_is_terminated sf` by
    (drule emit_void_terminated >> simp[is_terminator_def]) >>
  `(mstore (w2n aw) (typed_val_to_w256 etv v) s).vs_halted = s.vs_halted /\
   (mstore (w2n aw) (typed_val_to_w256 etv v) s).vs_current_bb = s.vs_current_bb /\
   (mstore (w2n aw) (typed_val_to_w256 etv v) s).vs_alloca_next = s.vs_alloca_next /\
   (mstore (w2n aw) (typed_val_to_w256 etv v) s).vs_allocas = s.vs_allocas /\
   (mstore (w2n aw) (typed_val_to_w256 etv v) s).vs_vars = s.vs_vars` by
    simp[mstore_def] >>
  simp[stmt_lands_def, cenv_top_ext_refl, lookup_var_def, op_taint_def] >>
  rpt conj_tac
  >- suspend "state"
  >- suspend "storage"
  >- suspend "return_buffer"
  >- suspend "history"
  >- metis_tac[lookup_var_def] >>
  simp[step_prov_def, step_taint_def, mk_inst_def, set_prov_def, set_var_taint_def] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _`
    (qspec_then `x` mp_tac) >> simp[op_taint_def, DRESTRICT_UNIV]
QED

Resume augassign_local_store_post_full[state]:
  rewrite_tac[stmt_state_rel_inst_idx] >>
  irule stmt_state_rel_write_local_store >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  simp[] >> qexistsl [`p`, `sz`] >> simp[]
QED
Resume augassign_local_store_post_full[storage]:
  fs[storage_well_formed_on_def] >> rpt gen_tac >>
  qpat_x_assum `!b slot tv. _` (qspecl_then [`b`, `slot`, `tv`] mp_tac) >>
  Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]
QED
Resume augassign_local_store_post_full[return_buffer]:
  irule return_buf_frame_frame >>
  qexistsl [`cenv`, `s`, `sc`] >> simp[lookup_var_def]
QED
Resume augassign_local_store_post_full[history]:
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  simp[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  `DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst sc.cs_next_id MSTORE [Var p;op] []] ++ l` by
      (asm_rewrite_tac[] >>
       pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >> REFL_TAC) >>
  mp_tac alloca_history_no_alloca_slice >>
  disch_then (qspecl_then [`func`, `s`,
    `mstore (w2n aw) (typed_val_to_w256 etv v) s`, `bb`,
    `[mk_inst sc.cs_next_id MSTORE [Var p;op] []]`, `l`] mp_tac) >>
  simp[mk_inst_def]
QED
Finalise augassign_local_store_post_full
