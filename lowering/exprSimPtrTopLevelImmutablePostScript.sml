(* Clean immutable-copy buffers and retained ghost posts. *)
Theory exprSimPtrTopLevelImmutablePost
Ancestors exprSimPtrTopLevelImmutableRun exprSimPtrTopLevelImmutableCopy
  exprSimPtrTopLevelStorageAlloc
  exprSimPtrTopLevelStorageFrame exprSimPtrLiteralBuffer exprSimCopy
  bodyPtrDefs exprSimProps exprLoweringProps valueEncoding valueEncodingProps
  pred_set finite_map venomState words vyperAST vyperState exprLowering compileEnv

Theorem toplevel_immutable_full_copy_clean:
  immutable_copy_ghost_frame sa s G tn sb t H tm 0 nb w ==>
  (!i. w2n w <= i /\ i < w2n w+nb ==> i NOTIN tm.t_mem)
Proof
  simp[immutable_copy_ghost_frame_def] >> SET_TAC[]
QED

Theorem toplevel_immutable_alloc_copy_taint_subset:
  tn1.t_mem SUBSET tn.t_mem UNION {i | w2n w <= i /\ i < w2n w+nb} /\
  immutable_copy_ghost_frame sa s G1 tn1 sb t H tm 0 nb w ==>
  tm.t_mem SUBSET tn.t_mem
Proof
  simp[immutable_copy_ghost_frame_def] >> SET_TAC[]
QED

Theorem toplevel_immutable_clean_pointer_post:
  ~is_word_type ann /\ evaluate_type (get_tenv cx) ann = SOME tv /\
  lookup_var root t = SOME w /\ ptr_covers G tn root t nb /\
  val_wf tv v /\ val_in_memory tv v (w2n w) t.vs_memory /\
  val_store_size tv v <= nb /\ type_memory_bytes cenv ann <= nb /\
  (!i. w2n w <= i /\ i < w2n w+nb ==> i NOTIN tn.t_mem) ==>
  ptr_val_ok cx ann v (Var root) G tn t /\
  ptr_vv_ok cx ann (Value v) (StackValue ann (Var root)) es G tn t /\
  ptr_buf_ok cenv (TopLevelName ann nsid) (Var root) G t
Proof
  strip_tac >>
  `val_footprint tv v <= nb` by
    metis_tac[val_footprint_le_store_size, arithmeticTheory.LESS_EQ_TRANS] >>
  `!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem` by
    (rpt strip_tac >> irule literal_clean_representation_robust >> simp[] >>
     qexistsl_tac [`tn.t_mem`,`t.vs_memory`] >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  drule_all toplevel_storage_copy_pointer_post >>
  simp[ptr_vv_ok_def, read_result_def, vyperStateTheory.return_def]
QED

Theorem toplevel_immutable_alloc_copy_kept:
  (!x. not_fresh_at st x ==> not_fresh_at sa x /\
     FLOOKUP G1 x = FLOOKUP G x /\
     op_taint tn1 (Var x) = op_taint tn (Var x)) /\
  tn1.t_mem SUBSET tn.t_mem UNION {i | w2n w <= i /\ i < w2n w+nb} /\
  immutable_copy_ghost_frame sa s G1 tn1 sb t H tm 0 nb w ==>
  ghost_kept cenv es st G tn s0 H tm
Proof
  strip_tac >> irule literal_ghost_kept >> conj_tac
  >- (gvs[immutable_copy_ghost_frame_def] >> metis_tac[]) >>
  metis_tac[toplevel_immutable_alloc_copy_taint_subset]
QED
