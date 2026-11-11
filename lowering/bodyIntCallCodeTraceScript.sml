(* Compilation intervals and descriptor-aligned segments for internal packages. *)
Theory bodyIntCallCodeTrace
Ancestors
  moduleLowering compileEnv fragExec loweringShapeProps loweringShapeDefs
  vyperCompiler venomExecProps list

Theorem compile_internal_fn_bodies_append:
  !xs ys st.
    compile_internal_fn_bodies (xs ++ ys) st =
    (comp_ignore_bind (compile_internal_fn_bodies xs)
                      (compile_internal_fn_bodies ys)) st
Proof
  Induct >> simp[compile_internal_fn_bodies_def, comp_ignore_bind_def,
                comp_bind_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_internal_fn_bodies_def, comp_ignore_bind_def,
       comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem compile_internal_fn_bodies_selected:
  !xs selected ys st r final.
    compile_internal_fn_bodies (xs ++ [selected] ++ ys) st = (r,final) ==>
    ?before after u v w.
      compile_internal_fn_bodies xs st = (u,before) /\
      compile_internal_fn_bodies [selected] before = (v,after) /\
      compile_internal_fn_bodies ys after = (w,final)
Proof
  simp[compile_internal_fn_bodies_append, comp_ignore_bind_def,
       comp_bind_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem compile_internal_fn_bodies_singleton:
  compile_internal_fn_bodies
    [(label,cenv,params,has_buf,nr,nkey,use_trans,is_view,is_ctor,imm_len,ss,ret)]
    st = (r,final) ==>
  ?old entry.
    new_block label st = (old,entry) /\
    compile_internal_function cenv params has_buf nr nkey use_trans is_view
      is_ctor imm_len ss ret entry = ((),final)
Proof
  simp[compile_internal_fn_bodies_def, comp_ignore_bind_def,
       comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem fn_has_code_block_suffix:
  final.cs_blocks = fresh ++ entry.cs_blocks /\
  func.fn_blocks = REVERSE fresh ++
    [<| bb_label := final.cs_current_bb;
        bb_instructions := final.cs_current_insts |>] /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) ==>
  fn_has_code entry final func
Proof
  strip_tac >> simp[fn_has_code_def, emitted_blocks_def] >> conj_tac
  >- (rpt strip_tac >> irule MEM_lookup_block >>
      simp[] >> gvs[TAKE_APPEND1]) >>
  qexists_tac `<| bb_label := final.cs_current_bb;
                 bb_instructions := final.cs_current_insts |>` >>
  simp[] >> irule MEM_lookup_block >> gvs[]
QED

Theorem fn_has_code_new_block_segment:
  new_block label before = (old,entry) /\
  cs_extends entry final /\
  all_blocks final = all_blocks before ++ func.fn_blocks /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) ==>
  fn_has_code entry final func
Proof
  strip_tac >> gvs[cs_extends_def] >>
  irule fn_has_code_block_suffix >> goal_assum (drule_at Any) >>
  gvs[new_block_def, all_blocks_def, APPEND_ASSOC]
QED

Theorem internal_fn_descriptors_append[simp]:
  !xs ys. internal_fn_descriptors (xs ++ ys) =
          internal_fn_descriptors xs ++ internal_fn_descriptors ys
Proof
  Induct >> simp[internal_fn_descriptors_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[internal_fn_descriptors_def]
QED

Theorem compile_internal_fn_bodies_selected_segments:
  compile_internal_fn_bodies (xs ++ [selected] ++ ys) st = (r,final) /\
  shape_state st /\ EVERY internal_fn_shape_ok (xs ++ [selected] ++ ys) /\
  EVERY (\d. internal_label_ok (FST d))
    (internal_fn_descriptors (xs ++ [selected] ++ ys)) ==>
  ?before after seg pre post.
    (?u. compile_internal_fn_bodies xs st = (u,before)) /\
    (?v. compile_internal_fn_bodies [selected] before = (v,after)) /\
    (?w. compile_internal_fn_bodies ys after = (w,final)) /\
    all_blocks before = all_blocks st ++ FLAT pre /\
    all_blocks after = all_blocks before ++ seg /\
    all_blocks final = all_blocks after ++ FLAT post /\
    LIST_REL internal_segment_ok (internal_fn_descriptors xs) pre /\
    LIST_REL internal_segment_ok (internal_fn_descriptors [selected]) [seg] /\
    LIST_REL internal_segment_ok (internal_fn_descriptors ys) post
Proof
  strip_tac >> drule compile_internal_fn_bodies_selected >> strip_tac >>
  fs[internal_fn_descriptors_def] >>
  qpat_assum `compile_internal_fn_bodies xs st = _`
    (mp_then Any mp_tac compile_internal_fn_bodies_shape) >>
  simp[internal_fn_descriptors_def] >> strip_tac >>
  qpat_assum `compile_internal_fn_bodies [selected] before = _`
    (mp_then Any mp_tac compile_internal_fn_bodies_shape) >>
  simp[internal_fn_descriptors_def] >> strip_tac >>
  qpat_assum `compile_internal_fn_bodies ys after = _`
    (mp_then Any mp_tac compile_internal_fn_bodies_shape) >>
  simp[internal_fn_descriptors_def] >> strip_tac >>
  PairCases_on `selected` >>
  gvs[internal_fn_descriptors_def, LIST_REL_CONS1] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED
