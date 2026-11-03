(* Exact compilation witnesses for selected internal functions. *)
Theory bodyIntCallCode
Ancestors
  intCallLookup intCallCallee fragExec loweringShapeProps list
  moduleLowering compileEnv stmtSim vyperCompiler venomInst bodyIntCallLabels
  bodyIntCallLabelFrame bodyIntCallContextLabels bodyIntCallMaterialLabels
  bodyIntCallBuiltinLabels bodyIntCallTypeBuiltinLabels bodyIntCallExprBodyLabels
  bodyIntCallSupportedExprLabels bodyIntCallStmtHelperLabels bodyIntCallStmtControlLabels
  bodyIntCallSupportedStmtLabels bodyIntCallFunctionLabels

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

Theorem compile_internal_function_body_states:
  compile_internal_function cenv params has_buf F nkey use_trans is_view
    F imm_len ss ret entry = ((),final) ==>
  ?cenv2 pc body_start body_env body_end.
    compile_internal_prologue cenv params has_buf ret entry =
      ((cenv2,pc),body_start) /\
    stmts_env
      (cenv2 with <| ce_imm_alloca := NONE; ce_alloca_locals := T |>) NoLoop
      (case ret of SOME t => t | NONE => BaseT BoolT) ss body_start =
      (body_env,body_end) /\
    (if block_is_terminated body_end then ((),body_end)
     else case ret of
       NONE => emit_inst RET [pc] [] body_end
     | SOME t => emit_inst INVALID [] [] body_end) = ((),final)
Proof
  Cases_on `compile_internal_prologue cenv params has_buf ret entry` >>
  rename1 `_ = (pr,body_start)` >> PairCases_on `pr` >>
  rename1 `_ = ((cenv2,pc),body_start)` >>
  drule_at Any compile_internal_function_prologue >> simp[] >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def, comp_get_def,
       compile_stmts_env] >>
  Cases_on `stmts_env
    (cenv2 with <| ce_imm_alloca := NONE; ce_alloca_locals := T |>) NoLoop
    (case ret of SOME t => t | NONE => BaseT BoolT) ss body_start` >>
  rename1 `_ = (body_env,body_end)` >>
  simp[] >> strip_tac >> gvs[] >>
  Cases_on `block_is_terminated body_end` >> gvs[] >>
  Cases_on `ret` >> gvs[comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[]
QED

Theorem compile_internal_fn_singleton_segment:
  compile_internal_fn_bodies
    [(label,cenv,params,has_buf,nr,nkey,use_trans,is_view,is_ctor,imm_len,ss,ret)]
    st = (r,final) /\
  shape_state st /\
  internal_fn_shape_ok
    (label,cenv,params,has_buf,nr,nkey,use_trans,is_view,is_ctor,imm_len,ss,ret) ==>
  ?seg.
    shape_state final /\
    all_blocks final = all_blocks st ++ seg /\
    internal_segment_ok (label,has_buf,cenv.ce_returns_count) seg
Proof
  strip_tac >> drule compile_internal_fn_bodies_shape >>
  simp[vyperCompilerTheory.internal_fn_descriptors_def] >> strip_tac >>
  gvs[LIST_REL_EL_EQN] >>
  Cases_on `segs` >> gvs[] >>
  rename1 `LENGTH tail = 0` >> Cases_on `tail` >> gvs[]
QED

Theorem lower_vyper_runtime_unit_static_integrity:
  lower_vyper_runtime_unit tops rpolicy = SOME unit ==>
  ctx_inst_ids_distinct unit.cu_context /\
  forced_alloc_inputs_check unit.cu_context
Proof
  simp[compileVyperTheory.lower_vyper_runtime_unit_def] >>
  pairarg_tac >> simp[AllCaseEqs()] >> strip_tac >>
  drule vyperCompilerTheory.run_lowering_static_integrity >> simp[]
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
  >- (rpt strip_tac >> irule venomExecPropsTheory.MEM_lookup_block >>
      simp[] >> gvs[TAKE_APPEND1]) >>
  qexists_tac `<| bb_label := final.cs_current_bb;
                 bb_instructions := final.cs_current_insts |>` >>
  simp[] >> irule venomExecPropsTheory.MEM_lookup_block >> gvs[]
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
  gvs[new_block_def, loweringShapeDefsTheory.all_blocks_def, APPEND_ASSOC]
QED

Theorem compile_internal_fn_bodies_selected_segments:
  compile_internal_fn_bodies (xs ++ [selected] ++ ys) st = (r,final) /\
  shape_state st /\ EVERY internal_fn_shape_ok (xs ++ [selected] ++ ys) ==>
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
  fs[] >>
  qpat_assum `compile_internal_fn_bodies xs st = _`
    (mp_then Any mp_tac compile_internal_fn_bodies_shape) >>
  simp[] >> strip_tac >>
  qpat_assum `compile_internal_fn_bodies [selected] before = _`
    (mp_then Any mp_tac compile_internal_fn_bodies_shape) >>
  simp[] >> strip_tac >>
  qpat_assum `compile_internal_fn_bodies ys after = _`
    (mp_then Any mp_tac compile_internal_fn_bodies_shape) >>
  simp[] >> strip_tac >>
  PairCases_on `selected` >>
  gvs[internal_fn_descriptors_def, LIST_REL_CONS1] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem run_lowering_partition_lookup:
  run_lowering selectors external_fns internal_fns fallback_fn rpolicy
    bucket_count fn_metadata_bytes dense_buckets entry_info "__entry" =
    SOME unit /\
  compile_generate_runtime selectors external_fns internal_fns fallback_fn
    Linear bucket_count fn_metadata_bytes dense_buckets entry_info
    (initial_compile_state "__entry") = ((),final) /\
  all_blocks final = entry ++ FLAT segs /\
  LIST_REL internal_segment_ok (internal_fn_descriptors internal_fns) segs /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors internal_fns)) /\
  EVERY (\d. ~compiler_label (FST d) /\
              ~MEM (FST d) (MAP (\bb. bb.bb_label) entry))
    (internal_fn_descriptors internal_fns) ==>
  !i. i < LENGTH segs ==>
    lookup_function (FST (EL i (internal_fn_descriptors internal_fns)))
      unit.cu_context.ctx_functions =
    SOME (mk_internal_function
      (FST (EL i (internal_fn_descriptors internal_fns))) (EL i segs)
      (FST (SND (EL i (internal_fn_descriptors internal_fns))))
      (SND (SND (EL i (internal_fn_descriptors internal_fns)))))
Proof
  strip_tac >>
  `package_internal_blocks (internal_fn_descriptors internal_fns)
     (entry ++ FLAT segs) =
   SOME (entry, MAP2 (\d seg. mk_internal_function (FST d) seg
                   (FST (SND d)) (SND (SND d)))
                   (internal_fn_descriptors internal_fns) segs)` by
    (irule package_internal_blocks_segments >> simp[]) >>
  `lowering_policy_ok rpolicy` by
    (qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rw[run_lowering_def]) >>
  `rpolicy.rpol_frontend_dispatch = Linear` by
    fs[lowering_policy_ok_def] >>
  drule LIST_REL_LENGTH >> strip_tac >> rpt strip_tac >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `all_blocks final = _`
    (assume_tac o REWRITE_RULE [loweringShapeDefsTheory.all_blocks_def]) >>
  gs[run_lowering_def, extract_context_with_internals_def] >>
  strip_tac >> gvs[lowering_context_ok_def, ctx_fn_names_def,
                  mk_venom_context_def] >>
  qmatch_goalsub_abbrev_tac `lookup_function _ fns = SOME f` >>
  `MEM f fns` by
    (simp[Abbr `fns`, Abbr `f`, MEM_EL] >> disj2_tac >>
     qexists_tac `i` >> simp[EL_MAP2]) >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) fns)` by simp[Abbr `fns`] >>
  drule_all lookup_function_distinct_mem >>
  simp[Abbr `f`, mk_internal_function_metadata]
QED

Theorem compile_generate_runtime_internal_start:
  compile_generate_runtime selectors external_fns internal_fns fallback_fn
    Linear bucket_count fn_metadata_bytes dense_buckets entry_info
    (initial_compile_state "__entry") = ((),final) /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) selectors /\
  EVERY external_fn_shape_ok external_fns /\ fallback_shape_ok fallback_fn ==>
  ?start.
    compile_internal_fn_bodies internal_fns start = ((),final) /\
    shape_state start /\ all_blocks start <> [] /\
    (HD (all_blocks start)).bb_label = "__entry" /\
    EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks start)))
Proof
  strip_tac >> drule_all runtime_entry_prefix_shape >> strip_tac >>
  qmatch_asmsub_abbrev_tac `shape_step F jump_label_ok (\st. T) prefix _` >>
  `compile_generate_runtime selectors external_fns internal_fns fallback_fn
     Linear bucket_count fn_metadata_bytes dense_buckets entry_info =
   comp_ignore_bind prefix
     (comp_bind (compile_internal_fn_bodies internal_fns) (\x. comp_return ()))`
    by simp[compile_generate_runtime_def, Abbr `prefix`,
            comp_ignore_bind_def, comp_bind_assoc] >>
  qpat_x_assum `compile_generate_runtime _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac [] >>
  Cases_on `prefix (initial_compile_state "__entry")` >>
  rename1 `prefix _ = (prefix_result,start)` >> Cases_on `prefix_result` >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `shape_step _ _ _ _ _` mp_tac >>
  simp[loweringShapeDefsTheory.shape_step_def] >> disch_then drule >>
  simp[shape_state_initial_compile_state] >> strip_tac >>
  drule runtime_entry_blocks_shape >> strip_tac >>
  qexists_tac `start` >> gvs[]
QED

Theorem internal_fn_descriptors_append:
  !xs ys. internal_fn_descriptors (xs ++ ys) =
          internal_fn_descriptors xs ++ internal_fn_descriptors ys
Proof
  Induct >> simp[internal_fn_descriptors_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[internal_fn_descriptors_def]
QED

Theorem compile_internal_fn_singleton_code:
  compile_internal_fn_bodies
    [(label,cenv,params,has_buf,nr,nkey,use_trans,is_view,is_ctor,imm_len,ss,ret)]
    before = (r,after) /\
  shape_state before /\
  internal_fn_shape_ok
    (label,cenv,params,has_buf,nr,nkey,use_trans,is_view,is_ctor,imm_len,ss,ret) /\
  all_blocks after = all_blocks before ++ func.fn_blocks /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) ==>
  ?old entry.
    new_block label before = (old,entry) /\
    compile_internal_function cenv params has_buf nr nkey use_trans is_view
      is_ctor imm_len ss ret entry = ((),after) /\
    fn_has_code entry after func
Proof
  strip_tac >> drule compile_internal_fn_bodies_singleton >> strip_tac >>
  drule_all shape_state_new_block >> strip_tac >>
  fs[internal_fn_shape_ok_def] >>
  drule_all compile_internal_function_shape >>
  rewrite_tac[loweringShapeDefsTheory.shape_step_def] >>
  disch_then drule >> simp[] >> strip_tac >>
  irule fn_has_code_new_block_segment >>
  gvs[loweringShapeDefsTheory.shape_extends_def] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem run_lowering_selected_partition_lookup:
  run_lowering selectors external_fns (xs ++ [selected] ++ ys) fallback_fn
    rpolicy bucket_count fn_metadata_bytes dense_buckets entry_info "__entry" =
    SOME unit /\
  compile_generate_runtime selectors external_fns (xs ++ [selected] ++ ys)
    fallback_fn Linear bucket_count fn_metadata_bytes dense_buckets entry_info
    (initial_compile_state "__entry") = ((),final) /\
  all_blocks final = entry ++ FLAT (pre ++ [seg] ++ post) /\
  LIST_REL internal_segment_ok (internal_fn_descriptors xs) pre /\
  LIST_REL internal_segment_ok (internal_fn_descriptors [selected]) [seg] /\
  LIST_REL internal_segment_ok (internal_fn_descriptors ys) post /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors (xs ++ [selected] ++ ys))) /\
  EVERY (\d. ~compiler_label (FST d) /\
              ~MEM (FST d) (MAP (\bb. bb.bb_label) entry))
    (internal_fn_descriptors (xs ++ [selected] ++ ys)) ==>
  lookup_function (FST (HD (internal_fn_descriptors [selected])))
    unit.cu_context.ctx_functions =
  SOME (mk_internal_function (FST (HD (internal_fn_descriptors [selected]))) seg
    (FST (SND (HD (internal_fn_descriptors [selected]))))
    (SND (SND (HD (internal_fn_descriptors [selected])))))
Proof
  strip_tac >>
  `LIST_REL internal_segment_ok
     (internal_fn_descriptors (xs ++ [selected] ++ ys))
     (pre ++ [seg] ++ post)` by
    simp[internal_fn_descriptors_append, LIST_REL_APPEND_suff] >>
  drule run_lowering_partition_lookup >>
  disch_then drule >>
  disch_then (qspecl_then [`pre ++ [seg] ++ post`, `entry`, `LENGTH pre`] mp_tac) >>
  simp[] >>
  imp_res_tac LIST_REL_LENGTH >>
  PairCases_on `selected` >>
  gvs[internal_fn_descriptors_append, internal_fn_descriptors_def,
      EL_APPEND_EQN]
QED

Theorem compiler_block_tail_clean_run:
  compiler_block_tail m /\ m entry = (r,final) /\
  m (entry with cs_blocks := []) = (v,clean) ==>
  r = v /\ final = clean with cs_blocks := clean.cs_blocks ++ entry.cs_blocks
Proof
  simp[compiler_block_tail_def] >> strip_tac >>
  first_x_assum (qspecl_then [`entry.cs_blocks`, `entry with cs_blocks := []`] mp_tac) >>
  simp[]
QED

Theorem compiler_block_tail_segment_distinct:
  compiler_block_tail m /\ m entry = (r,final) /\
  new_block label before = (old,entry) /\
  all_blocks final = all_blocks before ++ seg /\
  compile_state_ok (entry with cs_blocks := []) /\
  (!st v out. m st = (v,out) /\ compile_state_ok st ==> compile_state_ok out) ==>
  ALL_DISTINCT (MAP (\bb. bb.bb_label) seg)
Proof
  strip_tac >> Cases_on `m (entry with cs_blocks := [])` >>
  rename1 `_ = (v,clean)` >>
  `compile_state_ok clean` by metis_tac[] >>
  drule_all compiler_block_tail_clean_run >> strip_tac >>
  gvs[new_block_def, loweringShapeDefsTheory.all_blocks_def, APPEND_ASSOC] >>
  fs[compile_state_ok_def, ALL_DISTINCT_APPEND, MEM_MAP, MEM_REVERSE,
     MAP_REVERSE, ALL_DISTINCT_REVERSE]
QED

Theorem compile_runtime_internal_segment_distinct:
  supported_stmts tops bindings ss /\
  ~supported_stmts_expr_exists expr_internal_call_root ss /\
  ~compiler_label label /\
  compile_internal_fn_bodies
    [(label,ce,params,has_buf,F,nkey,transient,view,F,imm_len,ss,ret)]
    before = (r,final) /\
  all_blocks final = all_blocks before ++ seg ==>
  ALL_DISTINCT (MAP (\bb. bb.bb_label) seg)
Proof
  strip_tac >> drule compile_internal_fn_bodies_singleton >> strip_tac >>
  irule (INST_TYPE [alpha |-> ``:unit``] compiler_block_tail_segment_distinct) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  `compile_state_ok (entry with cs_blocks := [])` by
    metis_tac[new_block_clean_entry_ok] >> simp[] >> reverse conj_tac
  >- (irule compiler_block_tail_runtime_internal_function >> metis_tac[]) >>
  rpt strip_tac >> drule_all compile_runtime_internal_function_label_bounds >> simp[]
QED

Theorem compile_runtime_internal_singleton_code:
  supported_stmts tops bindings ss /\
  ~supported_stmts_expr_exists expr_internal_call_root ss /\
  ~compiler_label label /\ shape_state before /\
  internal_fn_shape_ok
    (label,ce,params,has_buf,F,nkey,transient,view,F,imm_len,ss,ret) /\
  compile_internal_fn_bodies
    [(label,ce,params,has_buf,F,nkey,transient,view,F,imm_len,ss,ret)]
    before = (r,final) /\
  all_blocks final = all_blocks before ++ func.fn_blocks ==>
  ?old entry cenv2 pc body_start body_env body_end.
    new_block label before = (old,entry) /\
    compile_internal_function ce params has_buf F nkey transient view F imm_len ss ret
      entry = ((),final) /\
    fn_has_code entry final func /\
    compile_internal_prologue ce params has_buf ret entry = ((cenv2,pc),body_start) /\
    stmts_env (cenv2 with <| ce_imm_alloca := NONE; ce_alloca_locals := T |>) NoLoop
      (case ret of SOME t => t | NONE => BaseT BoolT) ss body_start =
      (body_env,body_end) /\
    (if block_is_terminated body_end then ((),body_end)
     else case ret of NONE => emit_inst RET [pc] [] body_end
                    | SOME t => emit_inst INVALID [] [] body_end) = ((),final)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks)` by
    (irule compile_runtime_internal_segment_distinct >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  drule_all compile_internal_fn_singleton_code >> strip_tac >>
  drule compile_internal_function_body_states >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem run_lowering_selected_code_segment:
  run_lowering selectors external_fns (xs ++ [selected] ++ ys) fallback_fn rpolicy
    bucket_count fn_metadata_bytes dense_buckets entry_info "__entry" = SOME unit /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) selectors /\
  EVERY external_fn_shape_ok external_fns /\ fallback_shape_ok fallback_fn /\
  EVERY internal_fn_shape_ok (xs ++ [selected] ++ ys) /\
  EVERY (\d. internal_label_ok (FST d))
    (internal_fn_descriptors (xs ++ [selected] ++ ys)) ==>
  ?before after seg.
    shape_state before /\
    (?v. compile_internal_fn_bodies [selected] before = (v,after)) /\
    all_blocks after = all_blocks before ++ seg /\
    lookup_function (FST (HD (internal_fn_descriptors [selected])))
      unit.cu_context.ctx_functions =
    SOME (mk_internal_function (FST (HD (internal_fn_descriptors [selected]))) seg
      (FST (SND (HD (internal_fn_descriptors [selected]))))
      (SND (SND (HD (internal_fn_descriptors [selected])))))
Proof
  strip_tac >>
  Cases_on `compile_generate_runtime selectors external_fns (xs ++ [selected] ++ ys)
    fallback_fn Linear bucket_count fn_metadata_bytes dense_buckets entry_info
    (initial_compile_state "__entry")` >>
  rename1 `_ = (u,final)` >> Cases_on `u` >>
  drule_all compile_generate_runtime_internal_start >> strip_tac >>
  drule_all compile_internal_fn_bodies_selected_segments >> strip_tac >>
  `shape_state before` by
    (qpat_assum `compile_internal_fn_bodies xs start = _`
      (mp_then Any mp_tac compile_internal_fn_bodies_shape) >> fs[] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP FST (internal_fn_descriptors (xs ++ [selected] ++ ys)))` by
    metis_tac[run_lowering_descriptors_distinct] >>
  `EVERY (\d. ~compiler_label (FST d) /\
      ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks start)))
    (internal_fn_descriptors (xs ++ [selected] ++ ys))` by
    (rewrite_tac[EVERY_MEM] >> gen_tac >> disch_tac >>
     BETA_TAC >> irule internal_name_not_entry_label >> fs[EVERY_MEM]) >>
  `lookup_function (FST (HD (internal_fn_descriptors [selected])))
     unit.cu_context.ctx_functions =
   SOME (mk_internal_function (FST (HD (internal_fn_descriptors [selected]))) seg
     (FST (SND (HD (internal_fn_descriptors [selected]))))
     (SND (SND (HD (internal_fn_descriptors [selected])))))` by
    (irule run_lowering_selected_partition_lookup >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[FLAT_APPEND, APPEND_ASSOC] >> metis_tac[]) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem run_lowering_runtime_internal_code:
  selected = (label,ce,params,has_buf,F,nkey,transient,view,F,imm_len,ss,ret) /\
  run_lowering selectors external_fns (xs ++ [selected] ++ ys) fallback_fn rpolicy
    bucket_count fn_metadata_bytes dense_buckets entry_info "__entry" = SOME unit /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) selectors /\
  EVERY external_fn_shape_ok external_fns /\ fallback_shape_ok fallback_fn /\
  EVERY internal_fn_shape_ok (xs ++ [selected] ++ ys) /\
  EVERY (\d. internal_label_ok (FST d))
    (internal_fn_descriptors (xs ++ [selected] ++ ys)) /\
  supported_stmts tops bindings ss /\
  ~supported_stmts_expr_exists expr_internal_call_root ss ==>
  ?func before old entry final cenv2 pc body_start body_env body_end.
    lookup_function label unit.cu_context.ctx_functions = SOME func /\
    new_block label before = (old,entry) /\
    compile_internal_function ce params has_buf F nkey transient view F imm_len ss ret
      entry = ((),final) /\
    fn_has_code entry final func /\
    compile_internal_prologue ce params has_buf ret entry = ((cenv2,pc),body_start) /\
    stmts_env (cenv2 with <| ce_imm_alloca := NONE; ce_alloca_locals := T |>) NoLoop
      (case ret of SOME t => t | NONE => BaseT BoolT) ss body_start =
      (body_env,body_end) /\
    (if block_is_terminated body_end then ((),body_end)
     else case ret of NONE => emit_inst RET [pc] [] body_end
                    | SOME t => emit_inst INVALID [] [] body_end) = ((),final)
Proof
  strip_tac >> drule_all run_lowering_selected_code_segment >> strip_tac >>
  `internal_fn_shape_ok selected` by fs[] >>
  `internal_label_ok label` by
    gvs[internal_fn_descriptors_append, internal_fn_descriptors_def] >>
  `~compiler_label label` by
    (strip_tac >> drule compiler_label_prefix >> strip_tac >>
     gvs[internal_label_ok_def]) >>
  gvs[internal_fn_descriptors_def] >>
  qmatch_asmsub_abbrev_tac `lookup_function label _ = SOME func` >>
  `all_blocks after = all_blocks before ++ func.fn_blocks` by
    simp[Abbr `func`, mk_internal_function_def, mk_raw_function_def] >>
  drule_all compile_runtime_internal_singleton_code >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
