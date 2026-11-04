(* Exact compilation witnesses for selected internal functions. *)
Theory bodyIntCallCode
Ancestors
  intCallLookup intCallCallee fragExec loweringShapeProps list
  moduleLowering compileEnv stmtSim vyperCompiler venomInst bodyIntCallLabels
  bodyIntCallLabelFrame bodyIntCallContextLabels bodyIntCallMaterialLabels
  bodyIntCallBuiltinLabels bodyIntCallTypeBuiltinLabels bodyIntCallExprBodyLabels
  bodyIntCallSupportedExprLabels bodyIntCallStmtHelperLabels bodyIntCallStmtControlLabels
  bodyIntCallSupportedStmtLabels bodyIntCallFunctionLabels bodyIntCallPrefix
  bodyIntCallPrefixLabels abiDecoderAppend emitHelperProps pred_set loweringShapeDefs
  supportedProgram supportedDecls compileVyper

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

(* Extension alone retains the delimiter, independently of code shape or
   instruction certification.  The completed-history witness gives the exact
   suffix as well, so no block-tail hypothesis is needed at this boundary. *)
Theorem new_block_cs_extends_segment_head:
  new_block label before = (old,entry) /\
  cs_extends entry final ==>
  ?seg. all_blocks final = all_blocks before ++ seg /\
        seg <> [] /\ (HD seg).bb_label = label
Proof
  simp[new_block_def] >> strip_tac >> gvs[cs_extends_def] >>
  qexists_tac `REVERSE new ++
    [<| bb_label := final.cs_current_bb;
        bb_instructions := final.cs_current_insts |>]` >>
  conj_tac
  >- simp[loweringShapeDefsTheory.all_blocks_def, REVERSE_APPEND, APPEND_ASSOC] >>
  Cases_on `new` >> gvs[] >>
  qmatch_goalsub_abbrev_tac `HD (REVERSE t ++ [h;cur])` >>
  `REVERSE t ++ [h;cur] = REVERSE (cur::h::t)` by simp[] >>
  `HD (REVERSE (cur::h::t)) = LAST (cur::h::t)` by
    metis_tac[HD_REVERSE, NOT_CONS_NIL] >>
  `LAST (cur::h::t) = LAST (h::t)` by simp[LAST_CONS_cond] >>
  metis_tac[]
QED

Theorem runtime_fallback_segment_head:
  new_block label before = (old,entry) /\
  (case fb of
     NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
   | SOME (ce, pay, nr, key, trans, view, stmts, ret) =>
       compile_fallback_body ce pay nr key trans view stmts ret)
    entry = (r,final) ==>
  ?seg. all_blocks final = all_blocks before ++ seg /\
        seg <> [] /\ (HD seg).bb_label = label
Proof
  strip_tac >> irule new_block_cs_extends_segment_head >>
  goal_assum (drule_at Any) >>
  mp_tac compile_runtime_fallback_cs_appends >>
  rewrite_tac[cs_appends_def] >> disch_then drule >> simp[]
QED

Theorem compiler_block_tail_new_block_segment:
  compiler_block_tail m /\ m entry = (r,final) /\
  new_block label before = (old,entry) ==>
  ?seg. all_blocks final = all_blocks before ++ seg
Proof
  strip_tac >> Cases_on `m (entry with cs_blocks := [])` >>
  rename1 `_ = (v,clean)` >>
  drule_all compiler_block_tail_clean_run >> strip_tac >>
  qexists_tac `REVERSE clean.cs_blocks ++
    [<| bb_label := clean.cs_current_bb;
        bb_instructions := clean.cs_current_insts |>]` >>
  gvs[new_block_def, loweringShapeDefsTheory.all_blocks_def,
      REVERSE_APPEND, APPEND_ASSOC]
QED

Theorem compiler_block_tail_new_block_code:
  compiler_block_tail m /\ m entry = (r,final) /\
  new_block label before = (old,entry) /\
  all_blocks final = all_blocks before ++ func.fn_blocks /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) ==>
  fn_has_code entry final func
Proof
  strip_tac >> Cases_on `m (entry with cs_blocks := [])` >>
  rename1 `_ = (v,clean)` >>
  drule_all compiler_block_tail_clean_run >> strip_tac >>
  irule fn_has_code_block_suffix >> conj_tac >- simp[] >>
  qexists_tac `clean.cs_blocks` >>
  gvs[new_block_def, loweringShapeDefsTheory.all_blocks_def,
      REVERSE_APPEND, APPEND_ASSOC]
QED

Theorem compile_runtime_internal_singleton_segment_code:
  supported_stmts tops bindings ss /\
  ~supported_stmts_expr_exists expr_internal_call_root ss /\
  ~compiler_label label /\
  compile_internal_fn_bodies
    [(label,ce,params,has_buf,F,nkey,transient,view,F,imm_len,ss,ret)]
    before = (r,final) /\
  all_blocks final = all_blocks before ++ func.fn_blocks ==>
  ?old entry.
    new_block label before = (old,entry) /\
    compile_internal_function ce params has_buf F nkey transient view F imm_len ss ret
      entry = ((),final) /\
    fn_has_code entry final func
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks)` by
    (irule compile_runtime_internal_segment_distinct >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  drule compile_internal_fn_bodies_singleton >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  irule (INST_TYPE [alpha |-> ``:unit``] compiler_block_tail_new_block_code) >>
  conj_tac >- simp[] >> conj_tac
  >- (goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  goal_assum (drule_at Any) >>
  irule compiler_block_tail_runtime_internal_function >> metis_tac[]
QED

Theorem internal_label_not_compiler:
  internal_label_ok label ==> ~compiler_label label
Proof
  strip_tac >> strip_tac >> drule compiler_label_prefix >> strip_tac >>
  gvs[internal_label_ok_def, isPREFIX]
QED

(* The inductive boundary only excludes the pending descriptor names from
   the prefix; an already packaged segment is a valid prefix for the rest. *)
Theorem package_internal_blocks_label_segments:
  !descs segs prefix.
    LIST_REL (\d seg. seg <> [] /\ (HD seg).bb_label = FST d /\
               EVERY compiler_label (MAP (\bb. bb.bb_label) (TL seg))) descs segs /\
    ALL_DISTINCT (MAP FST descs) /\
    EVERY (\d. ~compiler_label (FST d) /\
               ~MEM (FST d) (MAP (\bb. bb.bb_label) prefix)) descs ==>
    package_internal_blocks descs (prefix ++ FLAT segs) =
      SOME (prefix, MAP2 (\d seg. mk_internal_function (FST d) seg
                        (FST (SND d)) (SND (SND d))) descs segs)
Proof
  Induct >- simp[package_internal_blocks_def] >>
  PairCases >> rw[LIST_REL_CONS1] >>
  rename1 `seg <> []` >>
  rename1 `LIST_REL _ descs ys` >>
  `?bb tl. seg = bb::tl` by (Cases_on `seg` >> gvs[]) >> gvs[] >>
  `split_blocks_at bb.bb_label (prefix ++ bb::(tl ++ FLAT ys)) =
     SOME (prefix, bb::(tl ++ FLAT ys))` by
    (irule split_blocks_at_append_delimiter >> gs[]) >>
  gs[package_internal_blocks_def] >>
  first_x_assum (qspecl_then [`ys`, `bb::tl`] mp_tac) >> impl_tac
  >- (gvs[EVERY_MEM, MEM_MAP, pairTheory.FORALL_PROD,
           pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  simp[]
QED

Theorem package_internal_blocks_internal_label_segments:
  LIST_REL (\d seg. seg <> [] /\ (HD seg).bb_label = FST d /\
             EVERY compiler_label (MAP (\bb. bb.bb_label) (TL seg))) descs segs /\
  ALL_DISTINCT (MAP FST descs) /\
  EVERY (\d. internal_label_ok (FST d)) descs /\
  EVERY (\bb. ~internal_label_ok bb.bb_label) prefix ==>
  package_internal_blocks descs (prefix ++ FLAT segs) =
    SOME (prefix, MAP2 (\d seg. mk_internal_function (FST d) seg
                      (FST (SND d)) (SND (SND d))) descs segs)
Proof
  strip_tac >> irule package_internal_blocks_label_segments >> simp[] >>
  gvs[EVERY_MEM, MEM_MAP] >> metis_tac[internal_label_not_compiler]
QED

Theorem run_lowering_label_partition_lookup:
  run_lowering selectors external_fns internal_fns fallback_fn rpolicy
    bucket_count fn_metadata_bytes dense_buckets entry_info "__entry" =
    SOME unit /\
  compile_generate_runtime selectors external_fns internal_fns fallback_fn
    Linear bucket_count fn_metadata_bytes dense_buckets entry_info
    (initial_compile_state "__entry") = ((),final) /\
  all_blocks final = prefix ++ FLAT segs /\
  LIST_REL (\d seg. seg <> [] /\ (HD seg).bb_label = FST d /\
             EVERY compiler_label (MAP (\bb. bb.bb_label) (TL seg)))
    (internal_fn_descriptors internal_fns) segs /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors internal_fns)) /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internal_fns) /\
  EVERY (\bb. ~internal_label_ok bb.bb_label) prefix ==>
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
     (prefix ++ FLAT segs) =
   SOME (prefix, MAP2 (\d seg. mk_internal_function (FST d) seg
                   (FST (SND d)) (SND (SND d)))
                   (internal_fn_descriptors internal_fns) segs)` by
    (irule package_internal_blocks_internal_label_segments >> simp[]) >>
  `lowering_policy_ok rpolicy` by
    (qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rw[run_lowering_def]) >>
  `rpolicy.rpol_frontend_dispatch = Linear` by fs[lowering_policy_ok_def] >>
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

Theorem compile_internal_param_decls_cs_appends:
  !params idx. cs_appends (compile_internal_param_decls params idx)
Proof
  Induct >> simp[compile_internal_param_decls_def, cs_appends_return] >>
  PairCases >> gen_tac >> rewrite_tac[compile_internal_param_decls_def] >>
  irule cs_appends_bind >> simp[cs_appends_emit_helpers] >> gen_tac >>
  irule cs_appends_bind >> simp[cs_appends_return]
QED

Theorem materialize_internal_params_cs_appends:
  !params ce. cs_appends (materialize_internal_params ce params)
Proof
  Induct >> simp[materialize_internal_params_def, cs_appends_return] >>
  PairCases >> gen_tac >> rewrite_tac[materialize_internal_params_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  irule cs_appends_bind >> simp[cs_appends_emit_helpers] >> gen_tac >>
  irule cs_appends_ignore_bind >> simp[cs_appends_emit_helpers]
QED

Theorem compile_runtime_internal_function_cs_appends:
  cs_appends
    (compile_internal_function ce params has_buf F nkey transient view F imm_len ss ret)
Proof
  rewrite_tac[compile_internal_function_def] >>
  simp[comp_ignore_bind_def, tuple_comp_return_bind] >>
  irule cs_appends_bind >> reverse conj_tac
  >- (Cases_on `has_buf` >> simp[cs_appends_return] >>
      irule cs_appends_bind >> simp[cs_appends_emit_helpers, cs_appends_return]) >>
  gen_tac >> BETA_TAC >> irule cs_appends_bind >>
  simp[compile_internal_param_decls_cs_appends] >> gen_tac >> BETA_TAC >>
  irule cs_appends_bind >> simp[cs_appends_emit_helpers] >> gen_tac >> BETA_TAC >>
  irule cs_appends_bind >> simp[materialize_internal_params_cs_appends] >>
  gen_tac >> BETA_TAC >> irule cs_appends_bind >> reverse conj_tac
  >- (Cases_on `ret` >> simp[cs_appends_return] >> IF_CASES_TAC >>
      simp[cs_appends_return] >> irule cs_appends_bind >>
      simp[cs_appends_abi_alloc_buffer, cs_appends_return]) >>
  gen_tac >> BETA_TAC >> irule cs_appends_bind >>
  simp[compile_stmts_cs_appends] >> rpt gen_tac >> BETA_TAC >>
  irule cs_appends_bind >> simp[cs_appends_get] >> gen_tac >> BETA_TAC >>
  irule cs_appends_bind >> simp[cs_appends_return] >>
  IF_CASES_TAC >> simp[cs_appends_return] >> Cases_on `ret` >>
  simp[cs_appends_emit_helpers]
QED

Theorem compiler_block_tail_new_block_label_segment:
  compiler_block_tail m /\ cs_appends m /\ m entry = (r,final) /\
  new_block label before = (old,entry) /\ ~compiler_label label /\
  (!st v out. m st = (v,out) /\ compile_state_ok st ==>
    compile_state_ok out /\
    bound_labels out SUBSET (bound_labels st UNION compiler_labels_future st.cs_next_label)) ==>
  ?seg. all_blocks final = all_blocks before ++ seg /\
    seg <> [] /\ (HD seg).bb_label = label /\
    EVERY compiler_label (MAP (\bb. bb.bb_label) (TL seg))
Proof
  strip_tac >>
  `cs_extends entry final` by metis_tac[cs_appends_def] >>
  drule_all new_block_cs_extends_segment_head >> strip_tac >>
  `compile_state_ok (entry with cs_blocks := [])` by
    metis_tac[new_block_clean_entry_ok] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) seg)` by
    (irule compiler_block_tail_segment_distinct >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  Cases_on `m (entry with cs_blocks := [])` >> rename1 `_ = (v,clean)` >>
  `compile_state_ok clean /\ bound_labels clean SUBSET
    (bound_labels (entry with cs_blocks := []) UNION
     compiler_labels_future entry.cs_next_label)` by
    (first_x_assum (drule_at (Pat `m _ = _`)) >> simp[]) >>
  drule_all compiler_block_tail_clean_run >> strip_tac >>
  `compiler_labels_future entry.cs_next_label SUBSET compiler_labels_future 0` by
    (irule compiler_labels_future_antimono >> simp[]) >>
  `!bb. MEM bb seg ==> bb.bb_label = label \/ compiler_label bb.bb_label` by
    (qpat_x_assum `(HD seg).bb_label = label` kall_tac >>
     qpat_x_assum `!st v out. _` kall_tac >>
     qpat_x_assum `m entry = _` kall_tac >>
     qpat_x_assum `cs_extends _ _` kall_tac >>
     gvs[new_block_def, loweringShapeDefsTheory.all_blocks_def,
         REVERSE_APPEND, APPEND_ASSOC, bound_labels_def, SUBSET_DEF,
         compiler_label_def, MEM_MAP, MEM_REVERSE] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  qexists_tac `seg` >> simp[] >>
  Cases_on `seg` >> gvs[ALL_DISTINCT, EVERY_MEM, MEM_MAP] >> metis_tac[]
QED

Theorem compile_runtime_internal_singleton_label_segment:
  supported_stmts tops bindings ss /\
  ~supported_stmts_expr_exists expr_internal_call_root ss /\
  ~compiler_label label /\
  compile_internal_fn_bodies
    [(label,ce,params,has_buf,F,nkey,transient,view,F,imm_len,ss,ret)]
    before = (r,final) ==>
  ?seg. all_blocks final = all_blocks before ++ seg /\
    seg <> [] /\ (HD seg).bb_label = label /\
    EVERY compiler_label (MAP (\bb. bb.bb_label) (TL seg))
Proof
  strip_tac >> drule compile_internal_fn_bodies_singleton >> strip_tac >>
  irule (INST_TYPE [alpha |-> ``:unit``] compiler_block_tail_new_block_label_segment) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  reverse conj_tac
  >- (simp[compile_runtime_internal_function_cs_appends] >>
      irule compiler_block_tail_runtime_internal_function >> metis_tac[]) >>
  rpt strip_tac >>
  drule_all compile_runtime_internal_function_label_bounds >> simp[]
QED

Theorem compile_runtime_internal_label_segments:
  !fns st r final.
  EVERY (\(lbl,ce,params,has_buf,nr,key,trans,view,ctor,imm_len,ss,ret).
    ~nr /\ ~ctor /\ ~compiler_label lbl /\
    ?bindings. supported_stmts tops bindings ss /\
      ~supported_stmts_expr_exists expr_internal_call_root ss) fns /\
  compile_internal_fn_bodies fns st = (r,final) ==>
  ?segs. all_blocks final = all_blocks st ++ FLAT segs /\
    LIST_REL (\d seg. seg <> [] /\ (HD seg).bb_label = FST d /\
      EVERY compiler_label (MAP (\bb. bb.bb_label) (TL seg)))
      (internal_fn_descriptors fns) segs
Proof
  Induct >- simp[compile_internal_fn_bodies_def, comp_return_def,
                 internal_fn_descriptors_def] >>
  rpt gen_tac >> strip_tac >>
  `compile_internal_fn_bodies (h::fns) st =
    comp_ignore_bind (compile_internal_fn_bodies [h])
      (compile_internal_fn_bodies fns) st` by
    simp[GSYM compile_internal_fn_bodies_append] >>
  Cases_on `compile_internal_fn_bodies [h] st` >> rename1 `_ = (u,mid)` >>
  gvs[comp_ignore_bind_def, comp_bind_def] >>
  first_x_assum drule >> strip_tac >>
  PairCases_on `h` >> gvs[] >>
  drule_all compile_runtime_internal_singleton_label_segment >> strip_tac >>
  qexists_tac `seg::segs` >>
  simp[internal_fn_descriptors_def, APPEND_ASSOC]
QED

Theorem compile_runtime_internal_selected_label_segments:
  EVERY (\(lbl,ce,params,has_buf,nr,key,trans,view,ctor,imm_len,ss,ret).
    ~nr /\ ~ctor /\ ~compiler_label lbl /\
    ?bindings. supported_stmts tops bindings ss /\
      ~supported_stmts_expr_exists expr_internal_call_root ss)
    (xs ++ [selected] ++ ys) /\
  compile_internal_fn_bodies (xs ++ [selected] ++ ys) st = (r,final) ==>
  ?before after seg pre post.
    (?u. compile_internal_fn_bodies xs st = (u,before)) /\
    (?v. compile_internal_fn_bodies [selected] before = (v,after)) /\
    all_blocks after = all_blocks before ++ seg /\
    all_blocks final = all_blocks st ++ FLAT (pre ++ [seg] ++ post) /\
    LIST_REL (\d seg. seg <> [] /\ (HD seg).bb_label = FST d /\
      EVERY compiler_label (MAP (\bb. bb.bb_label) (TL seg)))
      (internal_fn_descriptors (xs ++ [selected] ++ ys)) (pre ++ [seg] ++ post) /\
    LENGTH pre = LENGTH (internal_fn_descriptors xs)
Proof
  strip_tac >> drule compile_internal_fn_bodies_selected >> strip_tac >> fs[] >>
  qpat_assum `compile_internal_fn_bodies xs st = _`
    (mp_then Any (qspec_then `tops` mp_tac) compile_runtime_internal_label_segments) >>
  simp[] >> strip_tac >>
  qpat_assum `compile_internal_fn_bodies [selected] before = _`
    (mp_then Any (qspec_then `tops` mp_tac) compile_runtime_internal_label_segments) >>
  simp[] >> strip_tac >>
  qpat_assum `compile_internal_fn_bodies ys after = _`
    (mp_then Any (qspec_then `tops` mp_tac) compile_runtime_internal_label_segments) >>
  simp[] >> strip_tac >>
  PairCases_on `selected` >>
  gvs[internal_fn_descriptors_def, LIST_REL_CONS1] >>
  imp_res_tac LIST_REL_LENGTH >>
  rename1 `LIST_REL _ (internal_fn_descriptors xs) pre` >>
  rename1 `LIST_REL _ (internal_fn_descriptors ys) post` >>
  qexistsl_tac [`pre`, `post`] >>
  simp[FLAT_APPEND, APPEND_ASSOC, internal_fn_descriptors_append,
       internal_fn_descriptors_def, LIST_REL_APPEND_suff]
QED

Theorem run_lowering_source_selected_label_code:
  supported_program tops /\
  external_fns = MAP
    (set_external_package_target target o package_external_fn tops use_trans nkeys)
    (FST (classify_functions tops)) /\
  fallback_fn = set_fallback_package_target target
    (package_fallback_fn tops use_trans nkeys
      (FST (SND (SND (classify_functions tops))))) /\
  run_lowering selectors external_fns (xs ++ [selected] ++ ys) fallback_fn rpolicy
    bucket_count fn_metadata_bytes dense_buckets entry_info "__entry" = SOME unit /\
  EVERY (\(lbl,ce,params,has_buf,nr,key,trans,view,ctor,imm_len,ss,ret).
    ~nr /\ ~ctor /\ ~compiler_label lbl /\
    ?bindings. supported_stmts tops bindings ss /\
      ~supported_stmts_expr_exists expr_internal_call_root ss)
    (xs ++ [selected] ++ ys) /\
  EVERY (\d. internal_label_ok (FST d))
    (internal_fn_descriptors (xs ++ [selected] ++ ys)) ==>
  ?before after seg.
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
  drule_all compile_generate_runtime_source_noninternal_start >> strip_tac >>
  drule_all compile_runtime_internal_selected_label_segments >> strip_tac >>
  `ALL_DISTINCT (MAP FST (internal_fn_descriptors (xs ++ [selected] ++ ys)))` by
    metis_tac[run_lowering_descriptors_distinct] >>
  drule run_lowering_label_partition_lookup >>
  disch_then drule >>
  disch_then (qspecl_then [`pre ++ [seg] ++ post`, `all_blocks start`] mp_tac) >>
  simp[] >> disch_then (qspec_then `LENGTH pre` mp_tac) >>
  drule LIST_REL_LENGTH >>
  simp[internal_fn_descriptors_append, internal_fn_descriptors_def] >>
  rpt strip_tac >> PairCases_on `selected` >>
  gvs[internal_fn_descriptors_append, internal_fn_descriptors_def, EL_APPEND_EQN] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem run_lowering_source_runtime_internal_code:
  selected = (label,ce,params,has_buf,F,nkey,transient,view,F,imm_len,ss,ret) /\
  supported_program tops /\
  external_fns = MAP
    (set_external_package_target target o package_external_fn tops use_trans nkeys)
    (FST (classify_functions tops)) /\
  fallback_fn = set_fallback_package_target target
    (package_fallback_fn tops use_trans nkeys
      (FST (SND (SND (classify_functions tops))))) /\
  run_lowering selectors external_fns (xs ++ [selected] ++ ys) fallback_fn rpolicy
    bucket_count fn_metadata_bytes dense_buckets entry_info "__entry" = SOME unit /\
  EVERY (\(lbl,ce,params,has_buf,nr,key,trans,view,ctor,imm_len,ss,ret).
    ~nr /\ ~ctor /\ ~compiler_label lbl /\
    ?bindings. supported_stmts tops bindings ss /\
      ~supported_stmts_expr_exists expr_internal_call_root ss)
    (xs ++ [selected] ++ ys) /\
  EVERY (\d. internal_label_ok (FST d))
    (internal_fn_descriptors (xs ++ [selected] ++ ys)) ==>
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
  strip_tac >> drule_all run_lowering_source_selected_label_code >> strip_tac >>
  gvs[internal_fn_descriptors_def] >>
  qmatch_asmsub_abbrev_tac `lookup_function label _ = SOME func` >>
  `all_blocks after = all_blocks before ++ func.fn_blocks` by
    simp[Abbr `func`, mk_internal_function_def, mk_raw_function_def] >>
  drule_all compile_runtime_internal_singleton_segment_code >> strip_tac >>
  drule compile_internal_function_body_states >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem package_internal_supported_label_body:
  supported_program tops /\
  MEM src (FST (SND (classify_functions tops))) ==>
  (\(lbl,ce,params,has_buf,nr,key,trans,view,ctor,imm_len,ss,ret).
    ~nr /\ ~ctor /\ ~compiler_label lbl /\
    ?bindings. supported_stmts tops bindings ss /\
      ~supported_stmts_expr_exists expr_internal_call_root ss)
    (set_internal_package_target target
      (package_internal_fn tops use_trans nkeys F 0 src))
Proof
  strip_tac >> PairCases_on `src` >>
  drule (iffLR MEM_classify_internal) >> strip_tac >>
  drule_all supported_program_function >> strip_tac >>
  drule_all supported_program_declaration >>
  simp[supported_declaration_body_def, supported_function_header_contract] >>
  strip_tac >>
  simp[package_internal_fn_def, set_internal_package_target_def] >>
  conj_tac
  >- (irule internal_label_not_compiler >>
      simp[internal_label_ok_def, internal_fn_label_prefix]) >>
  gvs[supported_function_body_def] >> metis_tac[]
QED

Theorem supported_runtime_internal_packages:
  supported_program tops ==>
  EVERY (\(lbl,ce,params,has_buf,nr,key,trans,view,ctor,imm_len,ss,ret).
    ~nr /\ ~ctor /\ ~compiler_label lbl /\
    ?bindings. supported_stmts tops bindings ss /\
      ~supported_stmts_expr_exists expr_internal_call_root ss)
    (MAP (set_internal_package_target target o
      package_internal_fn tops use_trans nkeys F 0)
      (FST (SND (classify_functions tops)))) /\
  EVERY (\d. internal_label_ok (FST d))
    (internal_fn_descriptors
      (MAP (set_internal_package_target target o
        package_internal_fn tops use_trans nkeys F 0)
        (FST (SND (classify_functions tops)))))
Proof
  strip_tac >> conj_tac
  >- (simp[EVERY_MAP, EVERY_MEM, combinTheory.o_DEF] >> rpt strip_tac >>
      irule package_internal_supported_label_body >> simp[]) >>
  simp[GSYM MAP_MAP_o, internal_fn_descriptors_set_internal_package_target,
       internal_fn_descriptors_MAP_package_internal_fn] >>
  drule supported_internal_descriptors_ok >> simp[]
QED

Theorem lower_vyper_runtime_unit_selected_internal_code:
  supported_program tops /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  MEM src (FST (SND (classify_functions tops))) /\
  set_internal_package_target rpolicy.rpol_target
    (package_internal_fn tops F (assign_nkeys tops 0) F 0 src) =
    (label,ce,params,has_buf,F,nkey,transient,view,F,imm_len,ss,ret) ==>
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
  strip_tac >>
  `MEM (label,ce,params,has_buf,F,nkey,transient,view,F,imm_len,ss,ret)
    (MAP (set_internal_package_target rpolicy.rpol_target o
      package_internal_fn tops F (assign_nkeys tops 0) F 0)
      (FST (SND (classify_functions tops))))` by
    (simp[MEM_MAP] >> qexists_tac `src` >> simp[]) >>
  drule (iffLR MEM_SPLIT) >> strip_tac >>
  drule supported_runtime_internal_packages >>
  disch_then (qspecl_then [`F`, `rpolicy.rpol_target`, `assign_nkeys tops 0`]
    strip_assume_tac) >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def, bool_case_eq] >>
  pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >>
  qpat_x_assum `MAP _ int_fns = _` (assume_tac o GSYM) >>
  `l1 ++ (label,ce,params,has_buf,F,nkey,transient,view,F,imm_len,ss,ret)::l2 =
    l1 ++ [(label,ce,params,has_buf,F,nkey,transient,view,F,imm_len,ss,ret)] ++ l2` by simp[] >>
  drule_at (Pat `run_lowering _ _ _ _ _ _ _ _ _ _ = _`)
    run_lowering_source_runtime_internal_code >>
  simp[] >>
  disch_then (qspecl_then [`F`, `tops`, `rpolicy.rpol_target`, `assign_nkeys tops 0`]
    mp_tac) >> simp[] >>
  impl_tac >- (qexists_tac `bindings` >> simp[]) >>
  strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> gvs[] >>
  Cases_on `block_is_terminated body_end` >> gvs[]
QED
