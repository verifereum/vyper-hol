(* Internal segment lookup independent of runtime/deployment extraction. *)
Theory bodyIntCallExtractCode
Ancestors
  bodyIntCallRuntimeCode bodyIntCallCodeTrace intCallLookup ctorUnitShape loweringShapeProps loweringShapeDefs vyperCompiler
  compileEnv fragExec venomExecProps venomInst list

Theorem extract_context_partition_lookup:
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

Theorem extract_context_selected_segment_lookup:
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

Theorem extract_context_selected_internal_code:
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
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any)
QED
