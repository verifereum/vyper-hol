(* A pending Log row retains its memory representation across topic writes. *)
Theory bodyLogSavedMemoryPtrFrameMods
Ancestors
  bodyPtrBopRepresentationFrame bodyFullLogArgs logValueFramePtr
  exprSimProps loweringPosts bodyPtrDefs valueEncodingProofs valueEncodingDefs
  context compileEnv venomState words arithmetic

Theorem log_saved_footprint_frame[local]:
  expr_val_at ce cx ty si ss ee v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w /\ wb_frame ce ee ee ss s u /\
  ghost_kept_at lo ce ee ss G tn s Gu tu ==>
  val_wf tv v /\
  mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
  (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tu.t_mem ==>
       i IN tn.t_mem)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  conj_asm1_tac
  >- (qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _`
        (qspec_then `tv` mp_tac o REWRITE_RULE [expr_val_at_def]) >> simp[]) >>
  reverse conj_tac
  >- (rpt strip_tac >> drule_all pure_argument_taint_kept >> simp[]) >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _`
    (qspec_then `tv` mp_tac o REWRITE_RULE [expr_val_at_def]) >>
  simp[] >> strip_tac >>
  gvs[]
  >- (`mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz u.vs_memory` by
        (sym_tac >> qpat_x_assum `wb_frame _ _ _ _ _ _` mp_tac >>
         simp[wb_frame_def] >> strip_tac >>
         qpat_assum `!aid b sz. _ ==> mem_bytes_at b sz _ = _`
           (qspecl_then [`aid`, `b`, `sz`] mp_tac) >> simp[] >>
         (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
      drule mem_bytes_at_agree_window >> simp[])
  >- (`mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz u.vs_memory` by
        (sym_tac >> qpat_x_assum `wb_frame _ _ _ _ _ _` mp_tac >>
         simp[wb_frame_def,locals_kept_def] >> strip_tac >>
         qpat_assum `!n b sz. _ ==> mem_bytes_at b sz _ = _`
           (qspecl_then [`n`, `b`, `sz`] mp_tac) >> simp[]) >>
      drule mem_bytes_at_agree_window >> simp[]) >>
  simp[mem_bytes_at_def]
QED

Theorem log_saved_memory_ptr_frame:
  (vv_location sv = NONE \/ vv_location sv = SOME LocMemory) /\
  (vv_location sv = SOME LocMemory ==> ~is_word_type ty) /\
  read_result cx raw ee = (INL v,ee) /\
  vv_at ce cx ty si ss ee raw sv s /\ ptr_vv_ok cx ty raw sv ee G tn s /\
  wb_frame ce ee ee ss s u /\ ghost_kept_at lo ce ee ss G tn s Gu tu /\
  eval_operand (vv_operand sv) u = eval_operand (vv_operand sv) s /\
  (!x. vv_operand sv = Var x ==> FLOOKUP Gu x = FLOOKUP G x) /\
  op_taint tu (vv_operand sv) = op_taint tn (vv_operand sv) ==>
  ptr_vv_ok cx ty raw sv ee Gu tu u
Proof
  Cases_on `sv` >> simp[vv_location_def,vv_operand_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  >- (gvs[ptr_vv_ok_def,vv_at_def] >>
      irule ptr_val_ok_footprint_frame >>
      goal_assum (drule_at (Pat `ptr_val_ok _ _ _ _ _ _ _`)) >> simp[] >>
      rpt gen_tac >> strip_tac >>
      drule_all log_saved_footprint_frame >> simp[]) >>
  drule_all vv_at_memory_val_at >> strip_tac >>
  gvs[ptr_vv_ok_def] >>
  Cases_on `evaluate_type (get_tenv cx) ty` >- simp[ptr_mem_ok_def] >>
  rename1 `evaluate_type _ _ = SOME tv` >>
  `val_wf tv v` by
    (qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _`
       (qspec_then `tv` mp_tac o REWRITE_RULE [expr_val_at_def]) >> simp[]) >>
  irule bop_ptr_mem_ok_frame >>
  goal_assum (drule_at (Pat `ptr_mem_ok _ _ _ _ _ _ _`)) >>
  qexists `tv` >> simp[] >>
  rpt gen_tac >> disch_tac >>
  drule_all log_saved_footprint_frame >> simp[]
QED
