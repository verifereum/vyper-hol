Theory bodyPtrIfExpStorageMaterialize
Ancestors bodyPtrIfExpStorageCaller bodyPtrIfExpStorageSource
  bodyPtrIfExpStorageCompiler bodyPtrIfExpStorageExit bodyPtrIfExpStorageSingle pred_set
  bodyPtrIfExpActiveCopyPost bodyPtrIfExpAllocSource exprSimStorageCopy
  loweringPosts compileEnv venomState finite_map valueEncodingProps
  valueEncodingTyping bodyPtrIfExpBytesInputs bodyPtrIfExpStorageInvariant slotCopyExecution
  copyExecution exprLoweringProps exprSimCopy loweringHalt

Theorem ifexp_ensure_memory_storage_loop:
  expr_body_pre ce cx env e es /\ eval_expr cx e es = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  stmt_state_rel ctx fn ce cx es s0 /\
  vv_post ctx fn ce cx e es sa sb s0 ee raw (LocatedValue tag pp) s /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue tag pp) ee G tn s /\
  (pp.ptr_location = LocStorage \/ pp.ptr_location = LocTransient) /\
  n = (type_memory_bytes ce (expr_type e)+31) DIV 32 /\ n <> 1 /\
  compile_ensure_in_memory pp.ptr_operand pp.ptr_location
    (type_memory_bytes ce (expr_type e)) n is_ctor imm sb = (dst,sd) /\
  fn_has_code sb sd fn /\
  ghost_inv rty ce cx ee G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_inst_ids_distinct fn /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  type_memory_bytes ce (expr_type e) < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  fresh_vars_wrt sb s ==>
  ?out d ty t G' tn'.
    dst = Var out /\ eval_operand dst t = SOME d /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t.vs_current_bb = sd.cs_current_bb /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==> val_in_memory ty v (w2n d) m) /\
    ptr_covers G' tn' out t (type_memory_bytes ce (expr_type e)) /\
    ghost_inv rty ce cx ee G' tn' t /\ ghost_kept ce es sa G0 tn0 s0 G' tn' /\
    (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
      off+sz <= w2n d \/ w2n d+type_memory_bytes ce (expr_type e) <= off) /\
    (!name pos len. local_region ce es.scopes s0 name pos len ==>
      pos+len <= w2n d \/ w2n d+type_memory_bytes ce (expr_type e) <= pos) /\
    (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!b len. b+len <= w2n d \/ w2n d+type_memory_bytes ce (expr_type e) <= b ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_transient = s.vs_transient /\ t.vs_data_section = s.vs_data_section /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (~is_word_type (expr_type e) ==> expr_post ctx fn ce cx e es sa sd s0 ee v dst t)
Proof
  strip_tac >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) ifexp_storage_arm_source >>
  simp[] >> disch_then drule_all >> strip_tac >>
  drule_at (Pat `compile_ensure_in_memory _ _ _ _ _ _ _ = _`)
    ifexp_ensure_memory_slot_loop_parts >> simp[] >> disch_then drule >> strip_tac >>
  `compile_alloc_buffer (32*n) sb = (buf,cs)` by simp[] >>
  `fn_has_code cs (slot_copy_final cs pp.ptr_operand buf.buf_operand n
    (if pp.ptr_location = LocStorage then SLOAD else TLOAD)) fn` by
    (qpat_x_assum `fn_has_code cs sd fn` mp_tac >> simp[]) >>
  `MEM (if pp.ptr_location = LocStorage then SLOAD else TLOAD) [SLOAD;TLOAD]` by simp[] >>
  `32*n < dimword (:256)` by simp[] >>
  `!j k. j<n /\ k IN (if (if pp.ptr_location = LocStorage then SLOAD else TLOAD)=SLOAD
    then key_taint tn.t_stor (p+n2w j) else key_taint tn.t_trans (p+n2w j)) ==>
    (j,k) IN {(j,k) | (p+n2w j,k) IN
      (if pp.ptr_location = LocStorage then tn.t_stor else tn.t_trans)}` by
    simp[ptrDisciplineTheory.key_taint_def] >>
  drule_all ifexp_copy_allocated_execution >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `contract_storage (u with vs_inst_idx := SUC s.vs_inst_idx) = contract_storage s /\
   contract_transient (u with vs_inst_idx := SUC s.vs_inst_idx) = contract_transient s` by
    (qpat_x_assum `contract_storage u = _` mp_tac >>
     qpat_x_assum `contract_transient u = _` mp_tac >>
     simp[venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def]) >>
  drule ifexp_copy_ptr_exit >> simp[] >>
  disch_then (qspecl_then [`v`, `tvt`, `get_storage cx ee (pp.ptr_location = LocTransient)`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  suspend "semantic"
QED

Resume ifexp_ensure_memory_storage_loop[semantic]:
  markerLib.RESUME_TAC >>
  drule_all ifexp_arm_annotation_typed >> strip_tac >>
  `val_wf tvt v /\ val_footprint tvt v <= 32*n` by
    (gvs[] >> metis_tac[value_has_type_val_wf, exprSimPropsTheory.val_footprint_le]) >>
  drule ifexp_copy_ptr_ordinary_frame >> strip_tac >>
  `!x. not_fresh_at cs x ==> lookup_var x t = lookup_var x u` by
    (rpt strip_tac >>
     qpat_x_assum `ifexp_copy_ptr_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ifexp_copy_ptr_inv_def, slot_copy_inv_def] >> strip_tac >>
     qpat_x_assum `!op. slot_copy_external cs op ==> _`
       (qspec_then `Var x` mp_tac) >>
     simp[ifexp_copy_not_fresh_external, eval_operand_def, lookup_var_def]) >>
  `eval_operand (Var out) u = SOME d` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     qpat_x_assum `!x. not_fresh_at cs x ==> lookup_var x t = lookup_var x u`
       (qspec_then `out` mp_tac) >> gvs[eval_operand_def, lookup_var_def]) >>
  `val_in_memory tvt v (w2n d) t.vs_memory` by
    (qpat_x_assum `!m. mem_agree_outside tn'.t_mem _ m ==> _`
      (qspec_then `t.vs_memory` mp_tac) >> simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  suspend "post"
QED

Resume ifexp_ensure_memory_storage_loop[post]:
  markerLib.RESUME_TAC >>
  `~is_word_type (expr_type e) ==> expr_post ctx fn ce cx e es sa sd s0 ee v dst t` by
    (strip_tac >> irule ifexp_allocated_copy_post >> simp[] >>
     qexistsl_tac [`buf`, `cs`, `out`, `raw`, `s`, `sb`, `32*n`, `u`, `LocatedValue tag pp`] >>
     gvs[copy_static_def, slot_copy_final_def] >>
     rule_assum_tac (SIMP_RULE (srw_ss()) []) >> simp[] >> first_assum ACCEPT_TAC) >>
  qexists_tac `d` >> qexists_tac `t` >> simp[] >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  simp[copyExecutionTheory.slot_copy_final_def] >>
  gvs[] >> rule_assum_tac (SIMP_RULE (srw_ss()) [slot_copy_final_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise ifexp_ensure_memory_storage_loop

(* Both compiler branches finish at the end of the current instruction list. *)
Theorem ifexp_ensure_memory_storage:
  expr_body_pre ce cx env e es /\ eval_expr cx e es = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  stmt_state_rel ctx fn ce cx es s0 /\
  vv_post ctx fn ce cx e es sa sb s0 ee raw (LocatedValue tag pp) s /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue tag pp) ee G tn s /\
  (pp.ptr_location = LocStorage \/ pp.ptr_location = LocTransient) /\
  n = (type_memory_bytes ce (expr_type e)+31) DIV 32 /\
  compile_ensure_in_memory pp.ptr_operand pp.ptr_location
    (type_memory_bytes ce (expr_type e)) n is_ctor imm sb = (dst,sd) /\
  fn_has_code sb sd fn /\
  ghost_inv rty ce cx ee G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_inst_ids_distinct fn /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  type_memory_bytes ce (expr_type e) < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  fresh_vars_wrt sb s ==>
  ?out d ty t G' tn'.
    dst = Var out /\ eval_operand dst t = SOME d /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t.vs_current_bb = sd.cs_current_bb /\
    t.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~t.vs_halted /\
    (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==> val_in_memory ty v (w2n d) m) /\
    ptr_covers G' tn' out t (type_memory_bytes ce (expr_type e)) /\
    ghost_inv rty ce cx ee G' tn' t /\ ghost_kept ce es sa G0 tn0 s0 G' tn' /\
    (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
      off+sz <= w2n d \/ w2n d+type_memory_bytes ce (expr_type e) <= off) /\
    (!name pos len. local_region ce es.scopes s0 name pos len ==>
      pos+len <= w2n d \/ w2n d+type_memory_bytes ce (expr_type e) <= pos) /\
    (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!b len. b+len <= w2n d \/ w2n d+type_memory_bytes ce (expr_type e) <= b ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_transient = s.vs_transient /\ t.vs_data_section = s.vs_data_section /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (~is_word_type (expr_type e) ==> expr_post ctx fn ce cx e es sa sd s0 ee v dst t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `n = 1`
  >- (qpat_x_assum `n = 1` SUBST_ALL_TAC >>
      irule ifexp_ensure_memory_storage_single >> simp[] >> metis_tac[]) >>
  `LENGTH sd.cs_current_insts = 0` by
    (drule_all ifexp_ensure_memory_slot_loop_parts >> strip_tac >>
     simp[copyExecutionTheory.slot_copy_final_def]) >>
  drule_all ifexp_ensure_memory_storage_loop >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[]
QED
