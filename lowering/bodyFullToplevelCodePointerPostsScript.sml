(* Conditional ownership and size transport for the common immutable run. *)
Theory bodyFullToplevelCodePointerPosts
Ancestors
  exprPtrCleanBufferPost exprPtrUnwrapTypedSize exprSimMemDefs
  exprSimIfExpWidenedProvenance exprLowering loweringPosts bodyPtrDefs
  compileEnv context venomState arithmetic words

Theorem toplevel_code_runtime_pointer_posts:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm0) /\
  ~is_word_type (post_value_type cenv (TopLevelName ann nsid)) /\
  evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rty /\
  expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sb s0 ee v (Var root) z /\
  eval_operand (Var root) z = SOME w /\ ptr_covers G tn root z nb /\
  val_wf rty v /\ type_memory_size rty <= nb /\
  type_memory_bytes cenv (lowered_value_type cenv (TopLevelName ann nsid)) <= nb /\
  (!i. w2n w <= i /\ i < w2n w+nb ==> i NOTIN tn.t_mem) ==>
  ptr_val_ok cx (post_value_type cenv (TopLevelName ann nsid)) v (Var root) G tn z /\
  ptr_buf_ok cenv (TopLevelName ann nsid) (Var root) G z
Proof
  strip_tac >> irule clean_buffer_pointer_posts >>
  (conj_tac >- simp[]) >> reverse conj_tac
  >- (goal_assum (drule_at Any)) >>
  qexistsl [`nb`, `rty`, `w`] >> simp[]
QED

Theorem toplevel_code_runtime_size_posts:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm0) /\
  expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sb s0 ee v op z /\
  read_result cx raw ee = (INL v,ee) /\
  (!id path. raw <> PlaceR (MemoryPlace id path)) /\
  ~is_word_type (post_value_type cenv (TopLevelName ann nsid)) /\
  eval_operand op z = SOME w /\ w2n w+nb <= z.vs_alloca_next /\
  (!rt. evaluate_type (get_tenv cx) (expr_type (TopLevelName ann nsid)) = SOME rt ==>
     val_wf rt v /\ type_memory_bytes cenv (expr_type (TopLevelName ann nsid)) =
       type_memory_size rt /\ type_memory_bytes cenv (expr_type (TopLevelName ann nsid)) <= nb) /\
  (!rt. evaluate_type (get_tenv cx) (lowered_value_type cenv (TopLevelName ann nsid)) = SOME rt ==>
     type_memory_size rt <= nb) ==>
  expr_store_bound cx (expr_type (TopLevelName ann nsid)) v op z /\
  vv_at cenv cx (post_value_type cenv (TopLevelName ann nsid)) sa sb ee raw
    (LocatedValue (post_value_type cenv (TopLevelName ann nsid)) (mk_ptr op LocMemory)) z /\
  (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
     eval_operand op z = SOME w ==>
     type_memory_size rt = 0 \/ w2n w+type_memory_size rt <= z.vs_alloca_next)
Proof
  strip_tac >> conj_tac
  >- (rw[expr_store_bound_def] >>
      `val_store_size tv v <= nb` by
        (irule LESS_EQ_TRANS >> qexists `type_memory_bytes cenv (expr_type (TopLevelName ann nsid))` >>
         simp[] >> irule unwrap_typed_buffer_store_bound >> metis_tac[]) >>
      gvs[] >> decide_tac) >>
  conj_tac
  >- (irule vv_at_of_val_at_nonplace >>
      fs[expr_post_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >> res_tac >> decide_tac
QED
