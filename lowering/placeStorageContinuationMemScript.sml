(* Strict widened aggregate storage continuation, conditional on its frame. *)
Theory placeStorageContinuationMem
Ancestors
  placeStorageNormalizationMem placeStorageNormalizedSuffixMem
  placeStorageNormalizationFrame
  exprSimHyps valueEncodingProps stmtLowering compileEnv exprLoweringProps
  fragExec exprSimDefs loweringPosts exprSimHypsDefs bodyMemoryDefs fragGasPathMem
  placeStore vyperTyping vyperValue stmtLoweringMono

Theorem place_storage_assign_value_mem_with_frame:
  (!ctx func ce cx es st sb s t inst b sz.
    stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce st /\
    typed_copy_effect ctx func st sb s t b sz /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    (!name lb len. local_region ce es.scopes s name lb len ==>
       b+sz <= lb \/ lb+len <= b) ==>
    stmt_state_rel ctx func ce cx es t) ==>
  !ce dst loc src dty src_loc sty sa sb a func ctx cx ee env s d w p v stv ff.
  (compile_assign_value ce dst loc src (is_word_type dty) src_loc dty sty
    (case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes ce et + 31) DIV 32, type_memory_bytes ce et)
     | _ => NONE) (type_memory_bytes ce dty) sa = ((),sb) /\
   (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient) /\
   fn_has_code a sa func /\ fn_has_code sa sb func /\
   fn_inst_ids_distinct func /\ local_ptrs_reserved ce a /\
   local_ptrs_reserved ce sa /\ ce.ce_target CapMcopy /\
   acyclic_struct_metadata ce.ce_struct_fields /\
   stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
   alloca_history func s /\ return_buf_frame d ce sa s /\
   eval_operand dst s = SOME w /\
   place_ptr_rel ce cx s (PlaceR p) w (SOME loc) (Type dty) /\
   (!x. dst = Var x ==> not_fresh_at sa x) /\
   (!x. src = Var x ==> not_fresh_at sa x) /\
   expr_val_rel cx sty v src s /\ expr_val_at ce cx sty a sa ee v src s /\
   expr_val_own ce cx sty a sa ee v src s /\
   evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
   type_widens_to (get_tenv cx) sty dty /\
   ~is_word_type sty /\ ~is_word_type dty /\
   ~is_bytestring_type sty /\ ~is_bytestring_type dty /\ sty <> dty /\
   storage_place_region cx p /\
   (!id path entry t0. p = MemoryPlace id path /\
      lookup_scopes id ee.scopes = SOME entry /\ ce.ce_var_type id = SOME t0 ==>
      evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
   write_place cx p v ee = (INL (),ff) /\
   ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
   s.vs_inst_idx = LENGTH sa.cs_current_insts /\
   (loc = LocStorage \/ loc = LocTransient) /\
   type_memory_bytes ce dty < dimword (:256)) ==>
  ?dtv t. evaluate_type (get_tenv cx) dty = SOME dtv /\
   gas_path_mem ctx func s 0 (OK t) /\ stmt_state_rel ctx func ce cx ff t /\
   alloca_history func t /\ return_buf_frame d ce sb t /\
   s.vs_alloca_next <= t.vs_alloca_next /\
   ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts /\ t.vs_labels = s.vs_labels /\
   (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
   (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
   LENGTH s.vs_memory <= LENGTH t.vs_memory /\
   (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
      aid < sa.cs_next_id /\
      (!name b len. local_region ce ee.scopes s name b len ==>
         off+sz <= b \/ b+len <= off) ==>
      mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s.vs_memory) /\
   (loc = LocMemory ==> val_in_memory dtv v (w2n w) t.vs_memory) /\
   (!off n. t.vs_alloca_next <= off ==>
      mem_bytes_at off n t.vs_memory = mem_bytes_at off n s.vs_memory)
Proof
  disch_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all place_storage_normalization_mem_mono >>
  disch_then (qx_choosel_then
    [`sn`,`nb`,`bw`,`dtv`,`q`,`tr`,`mid`,`name`,`subs`,`k`,`root`,`path`,`delta`,`writes`]
    (map_every assume_tac o CONJUNCTS)) >>
  `~q.vs_call_ctx.cc_static` by
    (drule_all place_store_write_location >> strip_tac >>
     fs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  `!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     type_memory_bytes ce ty = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `0 < type_memory_size dtv` by
    (drule_all externalNormalizePremisesTheory.normalize_return_value_layout >>
     strip_tac >> gvs[]) >>
  `!et cap. dty = ArrayT et (Dynamic cap) ==>
    ?etv. evaluate_type (get_tenv cx) et = SOME etv /\
      type_memory_bytes ce et = type_memory_size etv` by
    (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
     metis_tac[expr_sim_inv_memory_size]) >>
  qpat_x_assum `loc = if tr then LocTransient else LocStorage` SUBST_ALL_TAC >>
  `!x. nb = Var x \/ dst = Var x ==> not_fresh_at sn x` by metis_tac[] >>
  drule_at (Pat `compile_assign_value _ _ _ _ F _ _ _ _ _ _ = _`)
    normalized_storage_assign_value_mem >>
  disch_then drule_all >>
  disch_then (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)) >>
  suspend "frames"
QED

Resume place_storage_assign_value_mem_with_frame[frames]:
  `ci_mono sn sb /\ ci_mono sa sb` by
    metis_tac[cj 1 ci_mono_stmt_helpers, pairTheory.SND] >>
  `return_buf_frame d ce sb t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`q`,`sn`] >>
     simp[] >> fs[ci_mono_def] >> metis_tac[]) >>
  `gas_path_mem ctx func s 0 (OK t)` by
    metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sn x` by
    (rpt strip_tac >>
     irule exprOperandVarTheory.compiler_ci_mono_not_fresh >>
     qexists_tac `sa` >> simp[]) >>
  qexistsl_tac [`dtv`,`t`] >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  Cases_on `tr` >> simp[]
QED

Finalise place_storage_assign_value_mem_with_frame

Theorem place_storage_assign_value_mem:
  !ce dst loc src dty src_loc sty sa sb a func ctx cx ee env s d w p v stv ff.
  (compile_assign_value ce dst loc src (is_word_type dty) src_loc dty sty
    (case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes ce et + 31) DIV 32, type_memory_bytes ce et)
     | _ => NONE) (type_memory_bytes ce dty) sa = ((),sb) /\
   (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient) /\
   fn_has_code a sa func /\ fn_has_code sa sb func /\
   fn_inst_ids_distinct func /\ local_ptrs_reserved ce a /\
   local_ptrs_reserved ce sa /\ ce.ce_target CapMcopy /\
   acyclic_struct_metadata ce.ce_struct_fields /\
   stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
   alloca_history func s /\ return_buf_frame d ce sa s /\
   eval_operand dst s = SOME w /\
   place_ptr_rel ce cx s (PlaceR p) w (SOME loc) (Type dty) /\
   (!x. dst = Var x ==> not_fresh_at sa x) /\
   (!x. src = Var x ==> not_fresh_at sa x) /\
   expr_val_rel cx sty v src s /\ expr_val_at ce cx sty a sa ee v src s /\
   expr_val_own ce cx sty a sa ee v src s /\
   evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
   type_widens_to (get_tenv cx) sty dty /\
   ~is_word_type sty /\ ~is_word_type dty /\
   ~is_bytestring_type sty /\ ~is_bytestring_type dty /\ sty <> dty /\
   storage_place_region cx p /\
   (!id path entry t0. p = MemoryPlace id path /\
      lookup_scopes id ee.scopes = SOME entry /\ ce.ce_var_type id = SOME t0 ==>
      evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
   write_place cx p v ee = (INL (),ff) /\
   ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
   s.vs_inst_idx = LENGTH sa.cs_current_insts /\
   (loc = LocStorage \/ loc = LocTransient) /\
   type_memory_bytes ce dty < dimword (:256)) ==>
  ?dtv t. evaluate_type (get_tenv cx) dty = SOME dtv /\
   gas_path_mem ctx func s 0 (OK t) /\ stmt_state_rel ctx func ce cx ff t /\
   alloca_history func t /\ return_buf_frame d ce sb t /\
   s.vs_alloca_next <= t.vs_alloca_next /\
   ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts /\ t.vs_labels = s.vs_labels /\
   (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
   (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
   LENGTH s.vs_memory <= LENGTH t.vs_memory /\
   (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
      aid < sa.cs_next_id /\
      (!name b len. local_region ce ee.scopes s name b len ==>
         off+sz <= b \/ b+len <= off) ==>
      mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s.vs_memory) /\
   (loc = LocMemory ==> val_in_memory dtv v (w2n w) t.vs_memory) /\
   (!off n. t.vs_alloca_next <= off ==>
      mem_bytes_at off n t.vs_memory = mem_bytes_at off n s.vs_memory)
Proof
  match_mp_tac place_storage_assign_value_mem_with_frame >>
  ACCEPT_TAC typed_copy_buffer_state_rel
QED
