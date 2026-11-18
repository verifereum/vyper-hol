(* A selected package's compile interval in the extracted context. *)
Theory bodyFullShadowInternalCode
Ancestors
  moduleLowering compileEnv fragExec loweringShapeProps loweringShapeDefs
  vyperCompiler venomExecProps venomInst list intCallLookup ctorUnitShape
  gasShadowInternal gasShadowState gasShadowModuleDefs gasShadowUnit
  gasShadowUnitGuards gasShadowUnitExtract gasShadow

Theorem compile_internal_fn_bodies_append[local]:
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

Theorem compile_internal_fn_bodies_selected[local]:
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

Theorem compile_internal_fn_bodies_singleton[local]:
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

Theorem fn_has_code_block_suffix[local]:
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

Theorem fn_has_code_new_block_segment[local]:
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

Theorem internal_fn_descriptors_append[simp,local]:
  !xs ys. internal_fn_descriptors (xs ++ ys) =
          internal_fn_descriptors xs ++ internal_fn_descriptors ys
Proof
  Induct >> simp[internal_fn_descriptors_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[internal_fn_descriptors_def]
QED

Theorem compile_internal_fn_bodies_selected_segments[local]:
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

Theorem internal_singleton_code[local]:
  compile_internal_fn_bodies
    [(label,ce,params,has_buf,nr,key,trans,view,ctor,imm_len,ss,ret)] before =
    (r,after) /\
  shape_state before /\ internal_label_ok label /\
  internal_fn_shape_ok
    (label,ce,params,has_buf,nr,key,trans,view,ctor,imm_len,ss,ret) /\
  all_blocks after = all_blocks before ++ func.fn_blocks /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) ==>
  ?old entry.
    new_block label before = (old,entry) /\
    compile_internal_function ce params has_buf nr key trans view ctor imm_len
      ss ret entry = ((),after) /\
    fn_has_code entry after func
Proof
  strip_tac >> drule compile_internal_fn_bodies_singleton >> strip_tac >>
  `shape_state entry` by (irule shape_state_new_block >> metis_tac[]) >>
  `internal_label_ok entry.cs_current_bb` by
    gvs[internal_fn_shape_ok_def, new_block_def] >>
  `shape_step T compiler_label (\st. internal_label_ok st.cs_current_bb)
     (compile_internal_function ce params has_buf nr key trans view ctor imm_len
        ss ret) (\x st. T)` by
    (irule compile_internal_function_shape >> gvs[internal_fn_shape_ok_def]) >>
  `cs_extends entry after` by
    (gvs[shape_step_def, shape_extends_def] >> metis_tac[]) >>
  goal_assum (drule_at Any) >> simp[] >>
  irule fn_has_code_new_block_segment >> metis_tac[]
QED

Theorem extract_context_partition_lookup[local]:
  extract_context_with_internals entry ints final = SOME (ctx,data) /\
  ALL_DISTINCT (MAP (\f. f.fn_name) ctx.ctx_functions) /\
  all_blocks final = entry_blocks ++ FLAT segs /\
  LIST_REL internal_segment_ok (internal_fn_descriptors ints) segs /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors ints)) /\
  EVERY (\d. ~compiler_label (FST d) /\
    ~MEM (FST d) (MAP (\bb. bb.bb_label) entry_blocks))
    (internal_fn_descriptors ints) ==>
  !i. i < LENGTH segs ==>
    lookup_function (FST (EL i (internal_fn_descriptors ints)))
      ctx.ctx_functions =
    SOME (mk_internal_function (FST (EL i (internal_fn_descriptors ints)))
      (EL i segs) (FST (SND (EL i (internal_fn_descriptors ints))))
      (SND (SND (EL i (internal_fn_descriptors ints)))))
Proof
  strip_tac >> drule_all package_internal_blocks_segments >> strip_tac >>
  rpt strip_tac >> imp_res_tac LIST_REL_LENGTH >>
  qpat_x_assum `extract_context_with_internals _ _ _ = _` mp_tac >>
  qpat_x_assum `all_blocks final = _`
    (assume_tac o REWRITE_RULE [all_blocks_def]) >>
  simp[extract_context_with_internals_def] >> strip_tac >>
  gvs[mk_venom_context_def] >>
  qmatch_goalsub_abbrev_tac `lookup_function _ fns = SOME f` >>
  `MEM f fns` by
    (simp[Abbr `fns`, Abbr `f`, MEM_EL] >> disj2_tac >>
     qexists_tac `i` >> simp[EL_MAP2]) >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) fns)` by simp[Abbr `fns`] >>
  drule_all lookup_function_distinct_mem >>
  simp[Abbr `f`, mk_internal_function_metadata]
QED

Theorem extract_context_selected_segment_lookup[local]:
  extract_context_with_internals entry (xs ++ [selected] ++ ys) final =
    SOME (ctx,data) /\
  ALL_DISTINCT (MAP (\f. f.fn_name) ctx.ctx_functions) /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors (xs ++ [selected] ++ ys))) /\
  all_blocks start <> [] /\ (HD (all_blocks start)).bb_label = entry /\
  EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks start))) /\
  (entry = "__entry" \/ entry = "__deploy") /\
  EVERY (\d. internal_label_ok (FST d))
    (internal_fn_descriptors (xs ++ [selected] ++ ys)) /\
  all_blocks before = all_blocks start ++ FLAT pre /\
  all_blocks after = all_blocks before ++ seg /\
  all_blocks final = all_blocks after ++ FLAT post /\
  LIST_REL internal_segment_ok (internal_fn_descriptors xs) pre /\
  LIST_REL internal_segment_ok (internal_fn_descriptors [selected]) [seg] /\
  LIST_REL internal_segment_ok (internal_fn_descriptors ys) post ==>
  lookup_function (FST (HD (internal_fn_descriptors [selected])))
    ctx.ctx_functions =
  SOME (mk_internal_function (FST (HD (internal_fn_descriptors [selected]))) seg
    (FST (SND (HD (internal_fn_descriptors [selected]))))
    (SND (SND (HD (internal_fn_descriptors [selected])))))
Proof
  strip_tac >>
  `LIST_REL internal_segment_ok
     (internal_fn_descriptors (xs ++ [selected] ++ ys))
     (pre ++ [seg] ++ post)` by
    (simp[] >> irule LIST_REL_APPEND_suff >> simp[] >>
     irule LIST_REL_APPEND_suff >> simp[]) >>
  `EVERY (\d. ~compiler_label (FST d) /\
     ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks start)))
       (internal_fn_descriptors (xs ++ [selected] ++ ys))` by
    (rewrite_tac[EVERY_MEM] >> gen_tac >> disch_tac >> BETA_TAC >>
     `internal_label_ok (FST e)` by (fs[EVERY_MEM] >> metis_tac[]) >>
     metis_tac[internal_name_not_entry_label, deploy_internal_label_separate]) >>
  `all_blocks final = all_blocks start ++ FLAT (pre ++ [seg] ++ post)` by
    simp[FLAT_APPEND, APPEND_ASSOC] >>
  qpat_x_assum `all_blocks final = all_blocks after ++ FLAT post` kall_tac >>
  drule extract_context_partition_lookup >>
  disch_then (qspecl_then [`pre ++ [seg] ++ post`, `all_blocks start`,
                          `LENGTH pre`] mp_tac) >>
  simp[] >> imp_res_tac LIST_REL_LENGTH >> PairCases_on `selected` >>
  gvs[internal_fn_descriptors_def, EL_APPEND_EQN]
QED

Theorem extract_context_selected_internal_code[local]:
  extract_context_with_internals entry
    (xs ++ [(label,ce,params,has_buf,nr,key,trans,view,ctor,imm_len,ss,ret)] ++ ys)
    final = SOME (ctx,data) /\
  ALL_DISTINCT (MAP (\f. f.fn_name) ctx.ctx_functions) /\
  EVERY (\f. ALL_DISTINCT (MAP (\bb. bb.bb_label) f.fn_blocks)) ctx.ctx_functions /\
  ctx_inst_ids_distinct ctx /\
  compile_internal_fn_bodies
    (xs ++ [(label,ce,params,has_buf,nr,key,trans,view,ctor,imm_len,ss,ret)] ++ ys)
    start = ((),final) /\ shape_state start /\
  all_blocks start <> [] /\ (HD (all_blocks start)).bb_label = entry /\
  EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks start))) /\
  (entry = "__entry" \/ entry = "__deploy") /\
  EVERY internal_fn_shape_ok
    (xs ++ [(label,ce,params,has_buf,nr,key,trans,view,ctor,imm_len,ss,ret)] ++ ys) /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors
    (xs ++ [(label,ce,params,has_buf,nr,key,trans,view,ctor,imm_len,ss,ret)] ++ ys)) /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors
    (xs ++ [(label,ce,params,has_buf,nr,key,trans,view,ctor,imm_len,ss,ret)] ++ ys))) ==>
  ?func before old st0 after.
    lookup_function label ctx.ctx_functions = SOME func /\
    (?u. compile_internal_fn_bodies xs start = (u,before)) /\
    new_block label before = (old,st0) /\
    compile_internal_function ce params has_buf nr key trans view ctor imm_len
      ss ret st0 = ((),after) /\
    fn_has_code st0 after func /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) /\
    ctx_inst_ids_distinct ctx
Proof
  strip_tac >>
  drule_all compile_internal_fn_bodies_selected_segments >> strip_tac >>
  drule extract_context_selected_segment_lookup >>
  disch_then (qspecl_then [`start`, `seg`, `pre`, `post`, `before`, `after`] mp_tac) >>
  simp[] >>
  simp[internal_fn_descriptors_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lookup_function label _ = SOME func` >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) /\
   ctx_inst_ids_distinct ctx` by
    (fs[lowering_context_ok_def, EVERY_MEM, fn_labels_def] >>
     drule lookup_function_MEM >> strip_tac >> simp[]) >>
  `all_blocks after = all_blocks before ++ func.fn_blocks` by
    simp[Abbr `func`, mk_internal_function_def, mk_raw_function_def] >>
  `shape_state before` by
    (qpat_assum `compile_internal_fn_bodies xs start = _`
       (mp_then Any mp_tac compile_internal_fn_bodies_shape) >>
     fs[] >> metis_tac[]) >>
  `internal_label_ok label` by fs[internal_fn_descriptors_def] >>
  fs[] >> drule_all internal_singleton_code >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any)
QED

Theorem extract_context_internal_names:
  extract_context_with_internals name ips s = SOME (ctx,data) ==>
  MAP (\f. f.fn_name) ctx.ctx_functions =
    name :: MAP FST (internal_fn_descriptors ips)
Proof
  simp[extract_context_with_internals_def, AllCaseEqs()] >>
  strip_tac >> gvs[mk_venom_context_def, mk_raw_function_def] >>
  drule package_internal_blocks_metadata >> strip_tac >>
  irule LIST_EQ >> simp[EL_MAP] >>
  gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  first_x_assum drule >> Cases_on `EL x (internal_fn_descriptors ips)` >>
  rename1 `EL x (internal_fn_descriptors ips) = desc` >>
  PairCases_on `desc` >> gvs[internal_fn_matches_descriptor_def, EL_MAP]
QED

Theorem selected_internal_shadow_code:
  pkg = (label,ce,params,has_rb,nr,key,trans,view,ctor,ilen,ss,rt) /\
  ips = xs ++ [pkg] ++ ys /\ sips = MAP gas_shadow_internal_package ips /\
  compile_internal_fn_bodies ips start = ((),run_end) /\
  compile_internal_fn_bodies sips startS = ((),run_endS) /\
  extract_context_with_internals name ips run_end = SOME (ctx,data) /\
  extract_context_with_internals name sips run_endS = SOME (sctx,sdata) /\
  shape_state start /\ shape_state startS /\
  gas_shadow_state start startS /\ gas_shadow_context ctx sctx /\
  (name = "__entry" \/ name = "__deploy") /\
  all_blocks start <> [] /\ all_blocks startS <> [] /\
  (HD (all_blocks start)).bb_label = name /\
  (HD (all_blocks startS)).bb_label = name /\
  EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks start))) /\
  EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks startS))) /\
  EVERY internal_fn_shape_ok ips /\ EVERY internal_fn_shape_ok sips /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips) /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors ips)) /\
  ALL_DISTINCT (MAP (\f. f.fn_name) ctx.ctx_functions) /\
  ALL_DISTINCT (MAP (\f. f.fn_name) sctx.ctx_functions) /\
  EVERY (\f. ALL_DISTINCT (MAP (\bb. bb.bb_label) f.fn_blocks))
    ctx.ctx_functions /\
  EVERY (\f. ALL_DISTINCT (MAP (\bb. bb.bb_label) f.fn_blocks))
    sctx.ctx_functions /\
  ctx_inst_ids_distinct ctx /\ ctx_inst_ids_distinct sctx /\
  lookup_function label ctx.ctx_functions = SOME callee ==>
  ?before old entry final sf beforeS oldS entryS finalS.
    new_block label before = (old,entry) /\
    compile_internal_function ce params has_rb nr key trans view ctor ilen
      ss rt entry = ((),final) /\
    fn_has_code entry final callee /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) callee.fn_blocks) /\
    MEM sf sctx.ctx_functions /\ gas_shadow_function callee sf /\
    new_block label beforeS = (oldS,entryS) /\
    compile_internal_function ce params has_rb nr key trans view ctor ilen
      (MAP gas_shadow_stmt ss) rt entryS = ((),finalS) /\
    gas_shadow_state entry entryS /\ gas_shadow_state final finalS /\
    fn_has_code entryS finalS sf
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `sips = _` SUBST_ALL_TAC >>
  qpat_x_assum `ips = _` SUBST_ALL_TAC >>
  qpat_x_assum `pkg = _` SUBST_ALL_TAC >>
  fs[gas_shadow_internal_package_def, internal_fn_descriptors_def] >>
  `?real_callee real_before real_old real_entry real_final.
    lookup_function label ctx.ctx_functions = SOME real_callee /\
    compile_internal_fn_bodies xs start = ((),real_before) /\
    new_block label real_before = (real_old,real_entry) /\
    compile_internal_function ce params has_rb nr key trans view ctor ilen
      ss rt real_entry = ((),real_final) /\
    fn_has_code real_entry real_final real_callee /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) real_callee.fn_blocks)` by
    (mp_tac (Q.INST [`entry` |-> `name`, `final` |-> `run_end`,
       `has_buf` |-> `has_rb`, `imm_len` |-> `ilen`, `ret` |-> `rt`]
       extract_context_selected_internal_code) >>
     simp[internal_fn_descriptors_def, oneTheory.one] >> metis_tac[]) >>
  `?shadow_callee shadow_before shadow_old shadow_entry shadow_final.
    lookup_function label sctx.ctx_functions = SOME shadow_callee /\
    compile_internal_fn_bodies (MAP gas_shadow_internal_package xs)
      startS = ((),shadow_before) /\
    new_block label shadow_before = (shadow_old,shadow_entry) /\
    compile_internal_function ce params has_rb nr key trans view ctor ilen
      (MAP gas_shadow_stmt ss) rt shadow_entry = ((),shadow_final) /\
    fn_has_code shadow_entry shadow_final shadow_callee` by
    (mp_tac (Q.INST [`entry` |-> `name`, `final` |-> `run_endS`,
       `ctx` |-> `sctx`, `data` |-> `sdata`, `start` |-> `startS`,
       `xs` |-> `MAP gas_shadow_internal_package xs`,
       `ys` |-> `MAP gas_shadow_internal_package ys`,
       `ss` |-> `MAP gas_shadow_stmt ss`,
       `has_buf` |-> `has_rb`, `imm_len` |-> `ilen`, `ret` |-> `rt`]
       extract_context_selected_internal_code) >>
     simp[internal_fn_descriptors_def, oneTheory.one] >> metis_tac[]) >>
  `real_callee = callee` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `real_callee = callee` SUBST_ALL_TAC >>
  `MEM shadow_callee sctx.ctx_functions /\ gas_shadow_function callee shadow_callee` by
    (conj_tac >- metis_tac[venomInstTheory.lookup_function_MEM] >>
     mp_tac (Q.SPECL [`ctx.ctx_functions`, `sctx.ctx_functions`, `label`]
       gas_shadow_lookup_function) >>
     fs[gas_shadow_context_def, optionTheory.OPTREL_def]) >>
  `gas_shadow_state real_before shadow_before` by
    (mp_tac (Q.SPEC `xs` gas_shadow_compile_internal_fn_bodies) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`start`, `startS`] mp_tac) >> simp[]) >>
  `gas_shadow_state real_entry shadow_entry` by
    (mp_tac gas_shadow_compiles_new_block >> simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`real_before`, `shadow_before`] mp_tac) >> simp[]) >>
  `gas_shadow_state real_final shadow_final` by
    (mp_tac (Q.SPECL [`ce`, `params`, `has_rb`, `nr`, `key`, `trans`, `view`,
      `ctor`, `ilen`, `ss`, `rt`] gas_shadow_compile_internal_function) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`real_entry`, `shadow_entry`] mp_tac) >> simp[]) >>
  qexistsl_tac [`real_before`, `real_old`, `real_entry`, `real_final`, `shadow_callee`,
    `shadow_before`, `shadow_old`, `shadow_entry`, `shadow_final`] >>
  fs[]
QED
