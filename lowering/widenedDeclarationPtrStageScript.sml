(* The declaration's retained RHS is staged at its physical layout before
   the fresh destination is initialized at its annotated layout. *)
Theory widenedDeclarationPtrStage
Ancestors widenedDeclarationPtrStore widenedAssignPtrContinuation
  assignBasePtrStaging abiBuiltinAllocation bodyDeclMemoryCore
  annAssignPtrMemoryStageFrame annAssignPtrBytestring exprSimProps exprSimBufferStore
  freshWrites fragGasPathPtr wordArgsPtr
  exprLoweringProps emitHelper emitHelperProps context compileEnv
  ptrDiscipline bodyPtrDefs loweringStateRelDefs localPtrsProps
  venomState venomInst venomExecSemantics venomMemDefs
  valueEncodingProps valueEncodingDefs typedMemoryCopy finite_map words ASCIInumbers

Theorem widened_declaration_staged_store_ptr:
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  ~is_word_type sty /\ ~is_word_type dty /\
  ~is_bytestring_type dty /\ dty <> sty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  type_memory_bytes ce sty = type_memory_size stv /\
  0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\
  val_wf stv v /\ val_wf dtv v /\
  compile_assign_value ce (Var p) LocMemory (Var src) F (SOME LocMemory)
    dty sty bytes sa = ((),sb) /\
  not_fresh_at sa p /\ not_fresh_at sa src /\
  lookup_var p s = SOME dw /\ lookup_var src s = SOME sw /\
  ptr_covers G tn p s cap /\ type_memory_size dtv <= cap /\
  ptr_covers G tn src s (type_memory_size stv) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory stv v (w2n sw) m) /\
  expr_val_at ce cx sty va vb es v (Var src) s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  stmt_state_rel ctx func ce cx es s /\ ghost_inv d ce cx es G tn s /\
  ghost_kept ce es fr G0 tn0 s0 G tn /\ local_ptrs_reserved ce sa /\
  (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  fr.cs_next_var <= sa.cs_next_var /\ fr.cs_next_id <= inst.inst_id /\
  inst.inst_id < sa.cs_next_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,cap) /\
  (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
    FLOOKUP s.vs_allocas aid = SOME ent) /\
  (!name b n. local_region ce es.scopes s0 name b n <=>
    local_region ce es.scopes s name b n) /\
  not_local_ptr ce es.scopes p /\
  es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) cap) ==>
  ?H tm t.
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    stmt_state_rel ctx func ce cx
      (es with scopes := (sc |+ (id,<|assignable := T; type := dtv;
        value := v; popped := []|>)) :: rest) t /\
    ghost_inv d ce cx
      (es with scopes := (sc |+ (id,<|assignable := T; type := dtv;
        value := v; popped := []|>)) :: rest) H tm t /\
    ghost_kept ce es fr G0 tn0 s0 H tm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all widened_assign_local_staged_code >> strip_tac >>
  drule body_scratch_alloc_operand >> strip_tac >>
  qmatch_asmsub_abbrev_tac `buf.buf_operand = Var fresh` >>
  `!x. not_fresh_at sa x ==> x <> fresh` by
    (simp[Abbr `fresh`, not_fresh_at_def] >> metis_tac[]) >>
  `not_local_ptr ce es.scopes fresh` by
    (simp[Abbr `fresh`] >> irule local_ptrs_reserved_fresh >>
     qexists_tac `sa` >> simp[]) >>
  `(!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> x <> fresh) /\
   (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> x <> fresh)` by
    metis_tac[] >>
  `src <> fresh /\ p <> fresh` by metis_tac[] >>
  `compile_copy_memory (Var fresh) (Var src) (type_memory_size stv) sm = ((),sn)` by
    metis_tac[] >>
  `compile_alloc_buffer (type_memory_size stv) sa = (buf,sm)` by metis_tac[] >>
  `sa.cs_next_id <= sa.cs_next_id /\ fr.cs_next_id <= sa.cs_next_id` by decide_tac >>
  `eval_operand (Var src) s = SOME sw /\ val_footprint stv v <= type_memory_size stv`
    by (simp[eval_operand_def] >> metis_tac[val_footprint_le]) >>
  `?t H th a.
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H th (OK t) /\
    stmt_state_rel ctx func ce cx es t /\ ghost_inv d ce cx es H th t /\
    ghost_kept ce es sa G tn s H th /\
    t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\ ~t.vs_halted /\
    lookup_var fresh t = SOME a /\ lookup_var p t = SOME dw /\
    ptr_covers H th fresh t (type_memory_size stv) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n a,type_memory_size stv) /\
    w2n a + type_memory_size stv < dimword (:256) /\
    (!m. mem_agree_outside th.t_mem t.vs_memory m ==>
      val_in_memory stv v (w2n a) m) /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
      FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!name b n. local_region ce es.scopes t name b n <=>
      local_region ce es.scopes s name b n) /\
    (!q. q <> Var fresh ==> eval_operand q t = eval_operand q s)` by
    (unabbrev_all_tac >>
     drule_all (Q.INST [`frame_sa` |-> `sa`]
       (SPEC_ALL assign_base_alloc_scratch_staging_ptr)) >>
     disch_then (qspecl_then [`PG`,`cx_dead cx`]
       (qx_choosel_then [`u`,`a`,`Gi`,`ti`,`t`,`H`,`th`] strip_assume_tac)) >>
     qexistsl_tac [`t`,`H`,`th`,`a`] >> simp[] >>
     metis_tac[eval_operand_def, operand_11]) >>
  `ptr_covers H th p t cap` by
    (irule annassign_ptr_covers_frame_ptr >>
     qexistsl_tac [`G`,`s`,`tn`] >> simp[] >> fs[ghost_kept_def] >> metis_tac[]) >>
  `ghost_kept ce es fr G0 tn0 s0 H th` by
    (irule wordArgsPtrTheory.ghost_kept_trans >>
     goal_assum (drule_at (Pat `ghost_kept _ _ fr _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `ghost_kept _ _ sa _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
    FLOOKUP t.vs_allocas aid = SOME ent` by metis_tac[] >>
  `!name b n. local_region ce es.scopes s0 name b n ==>
    local_region ce es.scopes t name b n` by metis_tac[] >>
  `FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n dw,cap)` by metis_tac[] >>
  `w2n dw + type_memory_size dtv <= w2n a \/
   w2n a + type_memory_size stv <= w2n dw` by
    (`allocas_non_overlapping t` by fs[stmt_state_rel_def, alloca_inv_def] >>
     fs[allocas_non_overlapping_def] >>
     first_x_assum (qspecl_then [`inst.inst_id`,`sa.cs_next_id`,
       `w2n dw`,`cap`,`w2n a`,`type_memory_size stv`] mp_tac) >>
     simp[] >> decide_tac) >>
  `sa.cs_next_var <= sn.cs_next_var` by
    (drule_all body_scratch_prefix_shape >> simp[]) >>
  `local_ptrs_reserved ce sn` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     simp[] >> fs[cs_extends_def] >> decide_tac) >>
  `fr.cs_next_var <= sn.cs_next_var` by
    (fs[cs_extends_def] >> decide_tac) >>
  `(!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sn x) /\
   (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sn x) /\
   not_fresh_at sn p /\ not_fresh_at sn fresh` by
    (drule_all body_scratch_prefix_shape >> strip_tac >>
     drule buffer_copy_memory_shape >> strip_tac >>
     gvs[compile_alloc_buffer_def, emit_op_def, fresh_var_def,
       fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, not_fresh_at_def, Abbr `fresh`, toString_inj] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `op_taint th (Var p) = {} /\ op_taint th (Var fresh) = {}` by fs[ptr_covers_def] >>
  mp_tac (Q.INST [`s` |-> `t`, `sa` |-> `sn`, `G` |-> `H`,
    `tn` |-> `th`, `src` |-> `Var fresh`, `sw` |-> `a`]
    (SPEC_ALL widened_declaration_store_ptr)) >>
  (impl_tac >- (simp[eval_operand_def] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`Hf`,`tf`,`u`] strip_assume_tac) >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Hf tf (OK u)` by
    (irule (SRULE [] (Q.INST [`n` |-> `0`,`m` |-> `0`] gas_path_ptr_then)) >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`Hf`,`tf`,`u`] >> simp[] >>
  rpt strip_tac >>
  `not_fresh_at sn x` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `x <> fresh` by metis_tac[] >>
  `lookup_var x t = lookup_var x s` by
    (qpat_x_assum `!q. q <> Var fresh ==> _` (qspec_then `Var x` mp_tac) >>
     simp[eval_operand_def]) >>
  qpat_x_assum `!x. not_fresh_at sn x ==> _` drule >>
  qpat_x_assum `ghost_kept ce es sa G tn s H th` mp_tac >>
  simp[ghost_kept_def] >> metis_tac[]
QED
