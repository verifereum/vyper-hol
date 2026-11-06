(* Local postcondition countermodel, NOT a reachable call or target
   counterexample.  Capacity 160 covers both layouts; tainted byte 64 is
   invisible to the annotation but belongs to the declared second header. *)
Theory bodyPtrStructLitRepresentationProbe
Ancestors bodyPtrStructLitLayoutProbe bodyPtrDefs exprSimProps
  vyperValue valueEncoding loweringPosts ptrDiscipline venomState finite_map

Theorem structlit_probe_tuple_evaluations:
  !tenv.
    evaluate_type tenv
      (TupleT [BaseT (BytesT (Dynamic 33)); BaseT (BytesT (Dynamic 1))]) =
      SOME (TupleTV [BaseTV (BytesT (Dynamic 33)); BaseTV (BytesT (Dynamic 1))]) /\
    evaluate_type tenv
      (TupleT [BaseT (BytesT (Dynamic 1)); BaseT (BytesT (Dynamic 1))]) =
      SOME (TupleTV [BaseTV (BytesT (Dynamic 1)); BaseTV (BytesT (Dynamic 1))])
Proof
  gen_tac >> EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC
QED

Theorem structlit_probe_post_representation_gap:
  !cx s G tn x cenv e.
    type_memory_bytes cenv (lowered_value_type cenv e) = 128 /\
    eval_operand (Var x) s = SOME 0w /\ s.vs_memory = [] /\
    tn.t_mem = {64} /\ op_taint tn (Var x) = {} /\
    FLOOKUP G x = SOME (0,160) ==>
    ptr_val_ok cx
      (TupleT [BaseT (BytesT (Dynamic 33)); BaseT (BytesT (Dynamic 1))])
      (ArrayV (TupleV [BytesV []; BytesV []])) (Var x) G tn s /\
    ptr_buf_ok cenv e (Var x) G s /\
    (0 + type_memory_size
      (TupleTV [BaseTV (BytesT (Dynamic 1)); BaseTV (BytesT (Dynamic 1))]) <=
      0 + 160) /\
    ~(!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory
        (TupleTV [BaseTV (BytesT (Dynamic 1)); BaseTV (BytesT (Dynamic 1))])
        (ArrayV (TupleV [BytesV []; BytesV []])) 0 mem)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (simp[ptr_val_ok_def, ptr_mem_ok_def, structlit_probe_tuple_evaluations,
           structlit_probe_annotated_robust] >> EVAL_TAC >> simp[]) >>
  conj_tac >- simp[ptr_buf_ok_def] >>
  gvs[structlit_probe_header_offsets] >>
  metis_tac[structlit_probe_lowered_not_robust]
QED

(* The state/ghost side of the local witness is nonvacuous.  This does
   not assert body_inv or execution reachability. *)
Theorem structlit_probe_resources_exist:
  !s0 x. ?s G tn.
    eval_operand (Var x) s = SOME 0w /\ s.vs_memory = [] /\
    tn.t_mem = {64} /\ op_taint tn (Var x) = {} /\
    FLOOKUP G x = SOME (0,160)
Proof
  rpt gen_tac >>
  qexistsl_tac [`update_var x 0w (s0 with vs_memory := [])`,
    `FEMPTY |+ (x,(0,160))`, `entry_taint with t_mem := {64}`] >>
  simp[eval_operand_def, update_var_def, lookup_var_def,
       entry_taint_def, op_taint_def, FLOOKUP_UPDATE]
QED
