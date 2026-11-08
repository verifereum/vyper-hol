(* Struct compiler and named-field interpretation of the uniform tuple loop. *)
Theory bodyPtrStructLitUniformFieldsLoop
Ancestors bodyPtrStructLitUniformTupleLoop exprSimAggregateLayout
  placeMemoryTypedBase gasSummaryComposePtr vyperTypeABI list

Theorem structlit_uniform_fields_loop_outcome_ptr:
  !fields ce cx env off si out sb es tvs cells G0 tn0 s0.
  compile_struct_lit compile_expr ce sty fields (Var root) off si = (out,sb) /\
  EVERY (\(name,e). ALOOKUP (get_struct_fields ce.ce_struct_fields
    (case sty of StructT nsid => nsid_to_string nsid | _ => "")) name =
      SOME (expr_type e,type_memory_bytes ce (expr_type e))) fields /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type (MAP SND fields)) = SOME tvs /\
  expr_sim_inv ce cx env es /\
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es si G0 tn0 s0 cells off /\
  literal_prefix_ok cells tn0 s0 /\ stmt_state_rel ctx func ce cx ees sf /\
  off + type_memory_size_list tvs <= capacity /\
  fn_has_code si sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  body_inv tops ctx ce cx /\ body_exprs_ptr_ok cx (MAP SND fields) /\
  (!e st. MEM e (MAP SND fields) /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  (!e. MEM e (MAP SND fields) ==> post_value_type ce e = expr_type e) ==>
  out = Var root /\
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx (MAP SND fields)) (es,s0,G0,tn0)
    (\res ee H tm z. ?vs added. res = INL vs /\ expr_sim_inv ce cx env ee /\
      LIST_REL value_has_type tvs vs /\
      literal_loop_frame ctx func ce cx d root aid addr capacity
        ees fr sf Gf tnf ee sb H tm z (cells ++ added) (off + type_memory_size_list tvs) /\
      literal_prefix_ok (cells ++ added) tm z /\
      (!m. mem_agree_outside tm.t_mem z.vs_memory m ==>
        fields_in_memory (ZIP (MAP FST fields,vs)) (ZIP (MAP FST fields,tvs)) (addr+off) m))
    (\res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_struct_lit_as_tuple >> strip_tac >>
  `compile_make_tuple compile_expr ce (MAP SND fields) (Var root) off si = (out,sb)` by
    metis_tac[] >>
  drule_all structlit_uniform_tuple_loop_outcome_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >> simp[] >>
  `LENGTH (MAP FST fields) = LENGTH tvs` by (drule OPT_MMAP_LENGTH >> simp[]) >>
  drule gas_outcome_ptr_conseq >> disch_then irule >> simp[] >>
  rpt gen_tac >> strip_tac >> gvs[] >> qexists `added` >> simp[] >>
  rpt strip_tac >>
  `LENGTH (MAP FST fields) = LENGTH vs` by (simp[] >> metis_tac[LIST_REL_LENGTH]) >>
  gvs[typed_memory_fields_tuple_zip]
QED
