Theory bodyPtrIfExpOldStorageSingle
Ancestors bodyPtrIfExpStorageSingle bodyPtrIfExpOldOperandAllocation
  bodyPtrIfExpStorageAllocation
  bodyPtrIfExpSingleCopyPost bodyPtrIfExpStorageAllocationFrame
  bodyPtrIfExpStorageSource bodyPtrIfExpMaterializeSingle
  bodyPtrIfExpAllocSource bodyPtrIfExpBytesInputs
  context compileEnv emitHelper fragExec loweringHalt loweringPosts
  venomState finite_map valueEncodingProps valueEncodingTyping pred_set

(* The source operand is compiler-old; unrelated future registers may exist. *)
Theorem ifexp_old_ensure_memory_storage_single:
  expr_body_pre ce cx env e es /\ eval_expr cx e es = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  stmt_state_rel ctx fn ce cx es s0 /\
  vv_post ctx fn ce cx e es sa sb s0 ee raw (LocatedValue tag pp) s /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue tag pp) ee G tn s /\
  (pp.ptr_location = LocStorage \/ pp.ptr_location = LocTransient) /\
  (type_memory_bytes ce (expr_type e)+31) DIV 32 = 1 /\
  compile_ensure_in_memory pp.ptr_operand pp.ptr_location
    (type_memory_bytes ce (expr_type e)) 1 is_ctor imm sb = (dst,sd) /\
  fn_has_code sb sd fn /\
  ghost_inv rty ce cx ee G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_inst_ids_distinct fn /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  type_memory_bytes ce (expr_type e) < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  copy_old_operand sb pp.ptr_operand ==>
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
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) ifexp_storage_arm_source >>
  simp[] >> disch_then drule_all >> strip_tac >>
  drule_at (Pat `compile_ensure_in_memory _ _ _ _ _ _ _ = _`) ifexp_storage_single_code >>
  simp[] >> disch_then drule >> strip_tac >>
  `compile_alloc_buffer 32 sb = (buf,cs)` by simp[] >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) ifexp_old_source_allocation_start >>
  simp[wordsTheory.dimword_def] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_at (Pat `step_inst_base _ _ = _`)
    (SRULE [] (Q.INST [`n` |-> `1`] ifexp_copy_allocation_loop_bounds)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  suspend "execute"
QED

Resume ifexp_old_ensure_memory_storage_single[execute]:
  qmatch_asmsub_abbrev_tac `ptr_covers Gb tb out u 32` >>
  drule_at (Pat `step_inst_base _ _ = _`)
    (SRULE [] (Q.INST [`n` |-> `32`] alloca_step_contracts)) >>
  simp[wordsTheory.dimword_def] >> strip_tac >>
  `tb.t_stor = tn.t_stor /\ tb.t_trans = tn.t_trans` by
    simp[Abbr `tb`, decoderGhostFramePtrTheory.step_taint_nonmemory_frame, venomInstTheory.mk_inst_def] >>
  `not_fresh_at cs out` by
    (drule compile_alloc_buffer_parts >> simp[] >> metis_tac[]) >>
  `lookup_var out u = SOME d` by gvs[venomStateTheory.eval_operand_def] >>
  qabbrev_tac `r = u with vs_inst_idx := LENGTH cs.cs_current_insts` >>
  qabbrev_tac `opc = if pp.ptr_location = LocStorage then SLOAD else TLOAD` >>
  qabbrev_tac `w = lookup_storage p (if pp.ptr_location = LocStorage
    then contract_storage s else contract_transient s)` >>
  `MEM opc [SLOAD;TLOAD]` by
    (Cases_on `pp.ptr_location = LocStorage` >> simp[Abbr `opc`]) >>
  `step_inst_base (mk_inst cs.cs_next_id opc [pp.ptr_operand]
    [STRING #"%" (toString cs.cs_next_var)]) r =
    OK (update_var (STRING #"%" (toString cs.cs_next_var)) w r)` by
    (`eval_operand pp.ptr_operand r = SOME p` by simp[Abbr `r`] >>
     drule_at (Pat `eval_operand _ r = _`) ifexp_storage_load_step >>
     disch_then (qspecl_then [`STRING #"%" (toString cs.cs_next_var)`, `opc`, `cs.cs_next_id`] mp_tac) >>
     Cases_on `pp.ptr_location = LocStorage` >>
     simp[Abbr `r`, Abbr `opc`, Abbr `w`, venomStateTheory.sload_def,
       venomStateTheory.tload_def, venomStateTheory.contract_storage_def,
       venomStateTheory.contract_transient_def]) >>
  `(do loaded <- emit_op opc [pp.ptr_operand];
       emit_void MSTORE [Var out;loaded] od) cs = ((),sd)` by metis_tac[] >>
  `eval_operand pp.ptr_operand r = SOME p /\ lookup_var out r = SOME d /\
   ptr_covers Gb tb out r 32 /\ ~r.vs_halted /\
   r.vs_current_bb = cs.cs_current_bb /\ r.vs_inst_idx = LENGTH cs.cs_current_insts` by
    (fs[venomStateTheory.lookup_var_def] >> simp[Abbr `r`, venomStateTheory.lookup_var_def]) >>
  drule_at (Pat `step_inst_base _ r = _`) ifexp_materialize_single_path >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "frames"
QED

Resume ifexp_old_ensure_memory_storage_single[frames]:
  `out' <> out` by metis_tac[] >>
  drule_at (Pat `G2 = _`) ifexp_materialize_single_effect >>
  disch_then drule_all >> disch_then (qspec_then `LENGTH sd.cs_current_insts` strip_assume_tac) >>
  `!x. not_fresh_at sa x ==> x <> out'` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]) >>
  `ghost_inv rty ce cx ee Gb tb r` by simp[Abbr `r`] >>
  `eval_operand (Var out) s1 = SOME d` by
    (qpat_x_assum `s1 = _` SUBST1_TAC >>
     simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     metis_tac[venomStateTheory.lookup_var_def]) >>
  `!name entry b sz z. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var b) sz) /\ lookup_var b s1 = SOME z ==>
    val_wf entry.type entry.value /\
    (w2n z+type_memory_size entry.type <= w2n d \/ w2n d+32 <= w2n z)` by
    (rpt strip_tac >>
     `b <> out'` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     `lookup_var b r = SOME z` by
       (qpat_x_assum `lookup_var b s1 = _` mp_tac >>
        qpat_x_assum `s1 = _` SUBST1_TAC >>
        simp[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
     qpat_x_assum `!name entry v sz w. _` drule_all >> simp[]) >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!name p len. local_region ce es.scopes s0 name p len ==> off+sz <= p \/ p+len <= off) ==>
    off+sz <= w2n d \/ w2n d+32 <= off` by metis_tac[] >>
  `!name b len. local_region ce es.scopes s0 name b len ==>
    b+len <= w2n d \/ w2n d+32 <= b` by metis_tac[arithmeticTheory.ADD_COMM] >>
  drule_at (Pat `tn2 = _`) ifexp_materialize_single_frames >>
  disch_then drule_all >>
  disch_then (qspec_then `LENGTH sd.cs_current_insts` strip_assume_tac) >>
  suspend "content"
QED

Resume ifexp_old_ensure_memory_storage_single[content]:
  `u' = mstore (w2n d) (lookup_storage p
    (if pp.ptr_location = LocStorage then contract_storage s else contract_transient s)) s1` by
    simp[Abbr `w`] >>
  drule_at (Pat `u' = mstore _ (lookup_storage _ _) _`) ifexp_storage_single_robust >>
  disch_then (drule_at (Pat `decode_value _ _ _ = _`)) >> simp[] >>
  disch_then (qspecl_then [`if pp.ptr_location = LocStorage then tn.t_stor else tn.t_trans`,
    `tb.t_mem`] assume_tac) >>
  `!m. mem_agree_outside tn2.t_mem u'.vs_memory m ==> val_in_memory tvt v (w2n d) m` by
    (gen_tac >> disch_tac >> first_x_assum irule >>
     Cases_on `pp.ptr_location = LocStorage` >>
     simp[Abbr `opc`, arithmeticTheory.ADD_COMM] >>
     qpat_x_assum `mem_agree_outside tn2.t_mem _ m` mp_tac >>
     qpat_x_assum `tn2.t_mem = _` SUBST1_TAC >>
     qpat_x_assum `u' = mstore _ w s1` SUBST1_TAC >> simp[arithmeticTheory.ADD_COMM]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2
    (OK (u' with vs_inst_idx := LENGTH sd.cs_current_insts))` by
    (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] fragGasPathPtrTheory.gas_path_ptr_then)) >>
     qexistsl_tac [`Gb`, `r`, `tb`] >> conj_tac
     >- (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn _ _ Gb tb _` mp_tac >> simp[Abbr `r`]) >>
     first_assum ACCEPT_TAC) >>
  `eval_operand (Var out) (u' with vs_inst_idx := LENGTH sd.cs_current_insts) = SOME d` by
    (qpat_x_assum `lookup_var out u' = _` mp_tac >>
     simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]) >>
  `~u'.vs_halted` by
    simp[venomStateTheory.mstore_def, venomStateTheory.write_memory_with_expansion_def,
      venomStateTheory.update_var_def] >>
  suspend "ordinary"
QED

Resume ifexp_old_ensure_memory_storage_single[ordinary]:
  `local_ptrs_reserved ce sb` by metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx fn ce cx ee s` by fs[loweringPostsTheory.vv_post_def] >>
  `!x. not_fresh_at sb x ==> x <> out'` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `u' with vs_inst_idx := LENGTH sd.cs_current_insts =
   (mstore (w2n d) w (update_var out' w (u with vs_inst_idx := LENGTH cs.cs_current_insts)))
     with vs_inst_idx := LENGTH sd.cs_current_insts` by
    (qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
     simp[Abbr `r`, venomStateTheory.mstore_def, venomStateTheory.update_var_def]) >>
  drule_at (Pat `t = (mstore _ _ _) with vs_inst_idx := _`) ifexp_storage_single_allocation_frame >>
  disch_then drule_all >> strip_tac >>
  drule_all ifexp_arm_annotation_typed >> strip_tac >>
  `val_wf tvt v /\ val_footprint tvt v <= 32` by
    (metis_tac[value_has_type_val_wf, exprSimPropsTheory.val_footprint_le, optionTheory.SOME_11]) >>
  `val_in_memory tvt v (w2n d) u'.vs_memory` by
    (qpat_x_assum `!m. mem_agree_outside tn2.t_mem _ m ==> _`
       (qspec_then `u'.vs_memory` mp_tac) >> simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  `!x. not_fresh_at cs x ==> x <> out'` by
    (qpat_x_assum `out' = _` SUBST1_TAC >> simp[not_fresh_at_def]) >>
  `cs.cs_next_id <= sd.cs_next_id` by
    (qpat_x_assum `(do loaded <- emit_op _ _; _ od) cs = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
  suspend "package"
QED

Resume ifexp_old_ensure_memory_storage_single[package]:
  `~is_word_type (expr_type e) ==> expr_post ctx fn ce cx e es sa sd s0 ee v (Var out)
    (u' with vs_inst_idx := LENGTH sd.cs_current_insts)` by
    (strip_tac >>
     `val_in_memory tvt v (w2n d) (u' with vs_inst_idx := LENGTH sd.cs_current_insts).vs_memory` by
       (simp[NoAsms] >> first_assum ACCEPT_TAC) >>
     drule_at (Pat `t = (mstore _ _ _) with vs_inst_idx := _`) ifexp_single_allocated_copy_post >>
     disch_then drule_all >> simp[]) >>
  qexistsl_tac [`d`, `u' with vs_inst_idx := LENGTH sd.cs_current_insts`, `G2`, `tn2`] >>
  simp[NoAsms] >>
  conj_tac >- (pure_rewrite_tac[venomStateTheory.eval_operand_def] >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_x_assum `ptr_covers G2 tn2 out _ 32` mp_tac >> simp[NoAsms]) >>
  conj_tac >- (qpat_x_assum `ghost_inv rty ce cx ee G2 tn2 _` mp_tac >> simp[NoAsms]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!name pos len. local_region _ _ _ _ _ _ ==> _` drule_all >> decide_tac) >>
  rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
  rpt conj_tac >> asm_rewrite_tac [] >>
  qpat_x_assum `~is_word_type _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >> simp[]
QED

Finalise ifexp_old_ensure_memory_storage_single
