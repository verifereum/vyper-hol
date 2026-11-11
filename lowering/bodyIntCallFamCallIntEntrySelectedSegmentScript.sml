(* Compiler traces for a selected internal package, before packaging. *)
Theory bodyIntCallFamCallIntEntrySelectedSegment
Ancestors
  moduleLowering compileEnv vyperCompiler loweringShapeDefs loweringShapeProps

Theorem intcall_internal_bodies_append:
  !xs ys s.
    compile_internal_fn_bodies (xs ++ ys) s =
    comp_ignore_bind (compile_internal_fn_bodies xs)
      (compile_internal_fn_bodies ys) s
Proof
  Induct
  >- simp[compile_internal_fn_bodies_def, comp_ignore_bind_def,
          comp_bind_def, comp_return_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >>
  simp[compile_internal_fn_bodies_def, comp_ignore_bind_def, comp_bind_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem intcall_selected_internal_compilation:
  !pre post lbl ce params rb nr key tr view ctor imm body rt s t.
    compile_internal_fn_bodies
      (pre ++ (lbl,ce,params,rb,nr,key,tr,view,ctor,imm,body,rt)::post) s =
      ((),t) ==>
    ?a old b c.
      compile_internal_fn_bodies pre s = ((),a) /\
      new_block lbl a = (old,b) /\
      compile_internal_function ce params rb nr key tr view ctor imm body rt b =
        ((),c) /\
      compile_internal_fn_bodies post c = ((),t)
Proof
  rpt gen_tac >>
  simp[intcall_internal_bodies_append, compile_internal_fn_bodies_def,
       comp_ignore_bind_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any))
QED

Theorem intcall_internal_descriptors_append:
  !xs ys. internal_fn_descriptors (xs ++ ys) =
          internal_fn_descriptors xs ++ internal_fn_descriptors ys
Proof
  Induct >> simp[internal_fn_descriptors_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >>
  simp[internal_fn_descriptors_def]
QED

Theorem intcall_selected_segment_trace:
  !pre post lbl ce params rb nr key tr view ctor imm body rt s t.
    compile_internal_fn_bodies
      (pre ++ (lbl,ce,params,rb,nr,key,tr,view,ctor,imm,body,rt)::post) s =
      ((),t) /\ shape_state s /\
    EVERY internal_fn_shape_ok
      (pre ++ (lbl,ce,params,rb,nr,key,tr,view,ctor,imm,body,rt)::post) /\
    EVERY (\d. internal_label_ok (FST d))
      (internal_fn_descriptors
        (pre ++ (lbl,ce,params,rb,nr,key,tr,view,ctor,imm,body,rt)::post)) ==>
    ?a old b c before seg after.
      compile_internal_fn_bodies pre s = ((),a) /\
      new_block lbl a = (old,b) /\
      compile_internal_function ce params rb nr key tr view ctor imm body rt b =
        ((),c) /\
      compile_internal_fn_bodies post c = ((),t) /\
      all_blocks a = all_blocks s ++ FLAT before /\
      all_blocks c = all_blocks a ++ seg /\
      all_blocks t = all_blocks c ++ FLAT after /\
      LIST_REL internal_segment_ok (internal_fn_descriptors pre) before /\
      internal_segment_ok (lbl,rb,ce.ce_returns_count) seg /\
      LIST_REL internal_segment_ok (internal_fn_descriptors post) after /\
      cs_extends b c
Proof
  rpt gen_tac >> strip_tac >>
  drule intcall_selected_internal_compilation >> strip_tac >>
  gvs[listTheory.EVERY_APPEND, internal_fn_shape_ok_def,
      intcall_internal_descriptors_append, internal_fn_descriptors_def] >>
  drule_all compile_internal_fn_bodies_shape >> strip_tac >>
  drule_all shape_state_new_block >> strip_tac >>
  `b.cs_current_bb = lbl` by gvs[new_block_def] >>
  drule_all compile_internal_function_shape >>
  rewrite_tac[shape_step_def] >>
  disch_then drule >> simp[] >> strip_tac >>
  drule_all internal_segment_new_block >>
  disch_then (qspecl_then [`rb`, `ce.ce_returns_count`] strip_assume_tac) >>
  rename1 `LIST_REL internal_segment_ok (internal_fn_descriptors pre) before` >>
  qpat_assum `compile_internal_fn_bodies post c = _`
    (mp_then Any mp_tac compile_internal_fn_bodies_shape) >>
  simp[] >> strip_tac >>
  rename1 `LIST_REL internal_segment_ok (internal_fn_descriptors post) after` >>
  qexistsl_tac [`before`, `after`] >>
  gvs[shape_extends_def]
QED
