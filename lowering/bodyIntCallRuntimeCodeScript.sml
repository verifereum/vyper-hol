(* Selected internal compilation intervals in a runtime package. *)
Theory bodyIntCallRuntimeCode
Ancestors
  bodyIntCallCodeTrace bodyIntCallBodyTrace intCallLookup
  loweringShapeProps loweringShapeDefs vyperCompiler moduleLowering
  compileEnv fragExec venomExecProps venomInst list
  supportedNames supportedProgram supportedDecls compileVyper loweringShapeSource

Theorem compile_runtime_internal_start:
  compile_generate_runtime sels exts ints fb Linear buckets metadata dense info
    (initial_compile_state "__entry") = ((),final) /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels /\
  EVERY external_fn_shape_ok exts /\ fallback_shape_ok fb ==>
  ?start.
    shape_state start /\
    compile_internal_fn_bodies ints start = ((),final) /\
    all_blocks start <> [] /\ (HD (all_blocks start)).bb_label = "__entry" /\
    EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks start)))
Proof
  strip_tac >> drule_all runtime_entry_prefix_shape >> strip_tac >>
  qmatch_asmsub_abbrev_tac `shape_step F jump_label_ok (\st. T) prefix _` >>
  `compile_generate_runtime sels exts ints fb Linear buckets metadata dense info =
   comp_ignore_bind prefix
     (comp_bind (compile_internal_fn_bodies ints) (\x. comp_return ()))`
    by simp[compile_generate_runtime_def, Abbr `prefix`,
            comp_ignore_bind_def, comp_bind_assoc] >>
  qpat_x_assum `compile_generate_runtime _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac [] >>
  Cases_on `prefix (initial_compile_state "__entry")` >>
  rename1 `prefix _ = (u,start)` >> Cases_on `u` >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `shape_step _ _ _ _ _` mp_tac >>
  simp[shape_step_def] >> disch_then drule >>
  simp[shape_state_initial_compile_state] >> strip_tac >>
  drule runtime_entry_blocks_shape >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem internal_singleton_code:
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

(* A descriptor's code can be identified from any certified partition of the
   emitted stream, not only the partition chosen by the shape theorem. *)
Theorem run_lowering_partition_lookup:
  run_lowering sels exts ints fb policy buckets metadata dense info "__entry" =
    SOME unit /\
  compile_generate_runtime sels exts ints fb Linear buckets metadata dense info
    (initial_compile_state "__entry") = ((),final) /\
  all_blocks final = entry_blocks ++ FLAT segs /\
  LIST_REL internal_segment_ok (internal_fn_descriptors ints) segs /\
  EVERY (\d. ~compiler_label (FST d) /\
    ~MEM (FST d) (MAP (\bb. bb.bb_label) entry_blocks))
    (internal_fn_descriptors ints) ==>
  !i. i < LENGTH segs ==>
    lookup_function (FST (EL i (internal_fn_descriptors ints)))
      unit.cu_context.ctx_functions =
    SOME (mk_internal_function (FST (EL i (internal_fn_descriptors ints)))
      (EL i segs) (FST (SND (EL i (internal_fn_descriptors ints))))
      (SND (SND (EL i (internal_fn_descriptors ints)))))
Proof
  strip_tac >> drule run_lowering_descriptors_distinct >> strip_tac >>
  `lowering_policy_ok policy` by
    (qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rw[run_lowering_def]) >>
  `policy.rpol_frontend_dispatch = Linear` by fs[lowering_policy_ok_def] >>
  drule_all package_internal_blocks_segments >> strip_tac >>
  rpt strip_tac >> imp_res_tac LIST_REL_LENGTH >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `all_blocks final = _`
    (assume_tac o REWRITE_RULE [all_blocks_def]) >>
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

Theorem run_lowering_selected_segment_lookup:
  run_lowering sels exts (xs ++ [selected] ++ ys) fb policy buckets metadata
    dense info "__entry" = SOME unit /\
  compile_generate_runtime sels exts (xs ++ [selected] ++ ys) fb Linear buckets
    metadata dense info (initial_compile_state "__entry") = ((),final) /\
  compile_internal_fn_bodies (xs ++ [selected] ++ ys) start = ((),final) /\
  all_blocks start <> [] /\ (HD (all_blocks start)).bb_label = "__entry" /\
  EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks start))) /\
  EVERY (\d. internal_label_ok (FST d))
    (internal_fn_descriptors (xs ++ [selected] ++ ys)) /\
  all_blocks before = all_blocks start ++ FLAT pre /\
  all_blocks after = all_blocks before ++ seg /\
  all_blocks final = all_blocks after ++ FLAT post /\
  LIST_REL internal_segment_ok (internal_fn_descriptors xs) pre /\
  LIST_REL internal_segment_ok (internal_fn_descriptors [selected]) [seg] /\
  LIST_REL internal_segment_ok (internal_fn_descriptors ys) post ==>
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
    (simp[] >> irule LIST_REL_APPEND_suff >> simp[] >>
     irule LIST_REL_APPEND_suff >> simp[]) >>
  `EVERY (\d. ~compiler_label (FST d) /\
     ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks start)))
       (internal_fn_descriptors (xs ++ [selected] ++ ys))` by
    (rewrite_tac[EVERY_MEM] >> gen_tac >> disch_tac >> BETA_TAC >>
     irule internal_name_not_entry_label >> simp[] >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `all_blocks final = all_blocks start ++ FLAT (pre ++ [seg] ++ post)` by
    simp[FLAT_APPEND, APPEND_ASSOC] >>
  qpat_x_assum `all_blocks final = all_blocks after ++ FLAT post` kall_tac >>
  drule run_lowering_partition_lookup >>
  disch_then (qspecl_then [`pre ++ [seg] ++ post`, `final`,
                          `all_blocks start`, `LENGTH pre`] mp_tac) >>
  simp[] >>
  imp_res_tac LIST_REL_LENGTH >>
  PairCases_on `selected` >>
  gvs[internal_fn_descriptors_def, EL_APPEND_EQN]
QED

Theorem run_lowering_function_labels:
  run_lowering sels exts ints fb policy buckets metadata dense info entry =
    SOME unit /\
  lookup_function label unit.cu_context.ctx_functions = SOME func ==>
  ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) /\
  ctx_inst_ids_distinct unit.cu_context
Proof
  strip_tac >> drule run_lowering_context_ok >>
  simp[lowering_context_ok_def, EVERY_MEM, fn_labels_def] >>
  strip_tac >> drule lookup_function_MEM >> strip_tac >> simp[]
QED

Theorem run_lowering_selected_internal_code:
  run_lowering sels exts
    (xs ++ [(label,ce,params,has_buf,nr,key,trans,view,ctor,imm_len,ss,ret)] ++ ys)
    fb policy buckets metadata dense info "__entry" = SOME unit /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels /\
  EVERY external_fn_shape_ok exts /\ fallback_shape_ok fb /\
  EVERY internal_fn_shape_ok
    (xs ++ [(label,ce,params,has_buf,nr,key,trans,view,ctor,imm_len,ss,ret)] ++ ys) /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors
    (xs ++ [(label,ce,params,has_buf,nr,key,trans,view,ctor,imm_len,ss,ret)] ++ ys)) ==>
  ?func before old entry after.
    lookup_function label unit.cu_context.ctx_functions = SOME func /\
    new_block label before = (old,entry) /\
    compile_internal_function ce params has_buf nr key trans view ctor imm_len
      ss ret entry = ((),after) /\
    fn_has_code entry after func /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) /\
    ctx_inst_ids_distinct unit.cu_context
Proof
  strip_tac >>
  `lowering_policy_ok policy` by
    (qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rw[run_lowering_def]) >>
  `policy.rpol_frontend_dispatch = Linear` by fs[lowering_policy_ok_def] >>
  Cases_on `compile_generate_runtime sels exts
    (xs ++ [(label,ce,params,has_buf,nr,key,trans,view,ctor,imm_len,ss,ret)] ++ ys)
    fb Linear buckets metadata dense info (initial_compile_state "__entry")` >>
  rename1 `_ = (u,final)` >> Cases_on `u` >>
  drule_all compile_runtime_internal_start >> strip_tac >>
  drule_all compile_internal_fn_bodies_selected_segments >> strip_tac >>
  drule_all run_lowering_selected_segment_lookup >>
  simp[internal_fn_descriptors_def] >> strip_tac >>
  drule_all run_lowering_function_labels >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lookup_function label _ = SOME func` >>
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

Theorem lower_vyper_runtime_unit_selected_internal_code:
  supported_program tops /\ lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  set_internal_package_target rpolicy.rpol_target
    (package_internal_fn tops F (assign_nkeys tops 0) F 0
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (label,ce,params,has_buf,nr',key,trans,view,ctor,imm_len,compiled_ss,rty) ==>
  ?func before old entry after.
    lookup_function label unit.cu_context.ctx_functions = SOME func /\
    new_block label before = (old,entry) /\
    compile_internal_function ce params has_buf nr' key trans view ctor imm_len
      compiled_ss rty entry = ((),after) /\
    fn_has_code entry after func /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) /\
    ctx_inst_ids_distinct unit.cu_context
Proof
  strip_tac >>
  `runtime_bodies_shape_ok tops` by
    metis_tac[supported_program_runtime_bodies_shape_ok] >>
  `ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
    (FST (SND (classify_functions tops))))` by
    (irule supported_names_internal_names_distinct >>
     fs[supported_program_def, supported_declaration_names_def]) >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def, bool_case_eq] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts,ints,fb,ctor_src)` >>
  simp[] >> strip_tac >>
  `MEM (mut,nr,rr,name,args,dflts,ret,ss) ints` by
    metis_tac[MEM_classify_internal, pairTheory.FST, pairTheory.SND] >>
  `EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl)
    (build_selectors (type_env tops) exts)` by
    rewrite_tac[build_selectors_fn_labels] >>
  `EVERY external_fn_shape_ok
    (MAP (set_external_package_target rpolicy.rpol_target o
      package_external_fn tops F (assign_nkeys tops 0)) exts)` by
    (simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     irule package_external_fn_shape_ok >> gs[]) >>
  `fallback_shape_ok (set_fallback_package_target rpolicy.rpol_target
    (package_fallback_fn tops F (assign_nkeys tops 0) fb))` by
    (qspecl_then [`tops`, `F`, `assign_nkeys tops 0`,
       `rpolicy.rpol_target`] mp_tac package_fallback_fn_shape_ok >> gs[]) >>
  `EVERY internal_fn_shape_ok
    (MAP (set_internal_package_target rpolicy.rpol_target o
      package_internal_fn tops F (assign_nkeys tops 0) F 0) ints)` by
    (simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     irule package_internal_fn_shape_ok >> gs[]) >>
  qspecl_then [`tops`, `F`] mp_tac internal_descriptors_ok >>
  impl_tac >- fs[] >> strip_tac >> gvs[] >>
  `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors
    (MAP (set_internal_package_target rpolicy.rpol_target o
      package_internal_fn tops F (assign_nkeys tops 0) F 0) ints))` by
    (fs[] >> simp[GSYM MAP_MAP_o,
      internal_fn_descriptors_set_internal_package_target,
      internal_fn_descriptors_MAP_package_internal_fn]) >>
  qmatch_asmsub_abbrev_tac `run_lowering _ _ intpkgs _` >>
  `MEM (label,ce,params,has_buf,nr',key,trans,view,ctor,imm_len,compiled_ss,rty)
     intpkgs` by
    (simp[Abbr `intpkgs`, MEM_MAP] >>
     qexists_tac `(mut,nr,rr,name,args,dflts,ret,ss)` >> simp[]) >>
  qpat_x_assum `MEM _ intpkgs`
    (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  gvs[] >>
  irule run_lowering_selected_internal_code >>
  qrefinel [`_`, `_`, `_`, `_`, `_`, `_`, `_`, `_`, `l1`, `l2`] >>
  simp[] >> goal_assum (drule_at (Pos hd)) >>
  gvs[internal_fn_descriptors_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any)
QED
