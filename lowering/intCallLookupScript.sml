(*
 * Internal calls: finding the callee in the unit (#638)
 *
 * package_internal_blocks splits a unit's blocks into one function per
 * internal body, so an INVOKE's target is looked up among the unit's
 * functions, not in the caller's fragment.  The lowering accepts a unit
 * only when its function names are distinct (lowering_context_ok), so the
 * lookup finds the function packaged for the label.  With the generator's
 * shape facts, that function's blocks are the label's segment of the
 * emitted block stream; which compile states made the segment is not
 * stated here.
 *
 * TOP-LEVEL:
 *   package_internal_blocks_mem  — every descriptor gets its function, whose
 *                                  blocks start at the descriptor's label
 *   run_lowering_internal_lookup — a lowered unit resolves an internal
 *                                  function's label to a function packaged
 *                                  under it, starting at its entry block
 *   run_lowering_internal_segments — with the shape facts
 *                                  run_lowering_source_unit_ok takes, that
 *                                  function's blocks are the descriptor's
 *                                  segment of compile_generate_runtime's
 *                                  block stream
 *   lower_vyper_runtime_unit_internal_lookup — run_lowering_internal_lookup
 *                                  for a source internal function, at its
 *                                  label
 *   compile_call_intcall_label   — for a supported program, the label
 *                                  compile_call's INVOKE names is that label
 *)

Theory intCallLookup
Ancestors
  list rich_list vyperCompiler compileVyper compileEnv loweringShapeProps
  supportedProgram supportedNames venomInst

Theorem split_blocks_at_SOME[local]:
  !label blocks prefix suffix.
    split_blocks_at label blocks = SOME (prefix, suffix) ==>
    ?bb rest. suffix = bb :: rest /\ bb.bb_label = label
Proof
  Induct_on `blocks` >> rw[split_blocks_at_def] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

(* An entry block whose label no later descriptor names stays at the head
   of the first function's blocks. *)
Theorem package_internal_blocks_head[local]:
  !ds bb bs p fs.
    package_internal_blocks ds (bb :: bs) = SOME (p, fs) /\
    ~MEM bb.bb_label (MAP FST ds) ==>
    ?p'. p = bb :: p'
Proof
  Cases >> rw[package_internal_blocks_def] >>
  PairCases_on `h` >>
  gvs[package_internal_blocks_def, split_blocks_at_def, AllCaseEqs()]
QED

Theorem package_internal_blocks_mem:
  !ds blocks entry fs name has_ret_buf ret_count.
    package_internal_blocks ds blocks = SOME (entry, fs) /\
    ALL_DISTINCT (MAP FST ds) /\ MEM (name, has_ret_buf, ret_count) ds ==>
    ?fbs. MEM (mk_internal_function name fbs has_ret_buf ret_count) fs /\
          fbs <> [] /\ (HD fbs).bb_label = name
Proof
  Induct >- simp[] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[package_internal_blocks_def, AllCaseEqs()] >> strip_tac >>
  gvs[]
  >- (drule split_blocks_at_SOME >> strip_tac >> gvs[] >>
      drule package_internal_blocks_head >> simp[] >> strip_tac >>
      gvs[] >> qexists_tac `bb :: p'` >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `fbs` >> simp[]
QED

Theorem descriptor_names_fn_names[local]:
  !ds fs.
    LIST_REL internal_fn_matches_descriptor ds fs ==>
    MAP FST ds = MAP (\f. f.fn_name) fs
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
  rw[internal_fn_matches_descriptor_def] >> gvs[internal_fn_matches_descriptor_def]
QED

Theorem lookup_function_distinct_mem[local]:
  !fns f.
    ALL_DISTINCT (MAP (\f. f.fn_name) fns) /\ MEM f fns ==>
    lookup_function f.fn_name fns = SOME f
Proof
  Induct >> rw[lookup_function_def, FIND_thm] >>
  gvs[MEM_MAP, GSYM lookup_function_def] >> metis_tac[]
QED

(* A lowered unit resolves an internal function's label to the function
   package_internal_blocks made for it. *)
Theorem run_lowering_internal_lookup:
  !selectors external_fns internal_fns fallback_fn rpolicy bucket_count
   fn_metadata_bytes dense_buckets entry_info entry_label unit
   name has_ret_buf ret_count.
    run_lowering selectors external_fns internal_fns fallback_fn rpolicy
      bucket_count fn_metadata_bytes dense_buckets entry_info entry_label =
      SOME unit /\
    MEM (name, has_ret_buf, ret_count) (internal_fn_descriptors internal_fns) ==>
    ?fbs. lookup_function name unit.cu_context.ctx_functions =
            SOME (mk_internal_function name fbs has_ret_buf ret_count) /\
          fbs <> [] /\ (HD fbs).bb_label = name
Proof
  rpt gen_tac >>
  simp[run_lowering_def, extract_context_with_internals_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[AllCaseEqs(), lowering_context_ok_def, ctx_fn_names_def,
      mk_venom_context_def] >>
  drule package_internal_blocks_metadata >> strip_tac >>
  drule descriptor_names_fn_names >> strip_tac >>
  `ALL_DISTINCT (MAP FST (internal_fn_descriptors internal_fns))` by
    gvs[] >>
  drule_all package_internal_blocks_mem >> strip_tac >>
  qexists_tac `fbs` >> simp[] >>
  qspecl_then
    [`mk_raw_function entry_label entry_blocks :: functions`,
     `mk_internal_function name fbs has_ret_buf ret_count`]
    mp_tac lookup_function_distinct_mem >>
  simp[mk_internal_function_metadata]
QED

Theorem run_lowering_descriptors_distinct[local]:
  !selectors external_fns internal_fns fallback_fn rpolicy bucket_count
   fn_metadata_bytes dense_buckets entry_info entry_label unit.
    run_lowering selectors external_fns internal_fns fallback_fn rpolicy
      bucket_count fn_metadata_bytes dense_buckets entry_info entry_label =
      SOME unit ==>
    ALL_DISTINCT (MAP FST (internal_fn_descriptors internal_fns))
Proof
  rpt gen_tac >>
  simp[run_lowering_def, extract_context_with_internals_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[AllCaseEqs(), lowering_context_ok_def, ctx_fn_names_def,
      mk_venom_context_def] >>
  drule package_internal_blocks_metadata >> strip_tac >>
  drule descriptor_names_fn_names >> strip_tac >> gvs[]
QED

(* With the generator's shape facts (those run_lowering_source_unit_ok
   takes), the function an internal label resolves to is exactly that
   descriptor's segment of the runtime block stream compile_generate_runtime
   emits. *)
Theorem run_lowering_internal_segments:
  !selectors external_fns internal_fns fallback_fn rpolicy bucket_count
   fn_metadata_bytes dense_buckets entry_info unit.
    run_lowering selectors external_fns internal_fns fallback_fn rpolicy
      bucket_count fn_metadata_bytes dense_buckets entry_info "__entry" =
      SOME unit /\
    EVERY (\(sel, lbl, z). isPREFIX "fn_" lbl) selectors /\
    EVERY external_fn_shape_ok external_fns /\
    fallback_shape_ok fallback_fn /\
    EVERY internal_fn_shape_ok internal_fns /\
    EVERY (\d. internal_label_ok (FST d))
      (internal_fn_descriptors internal_fns) ==>
    ?entry_blocks segs.
      all_blocks (SND (compile_generate_runtime selectors external_fns
                         internal_fns fallback_fn Linear bucket_count
                         fn_metadata_bytes dense_buckets entry_info
                         (initial_compile_state "__entry"))) =
        entry_blocks ++ FLAT segs /\
      LIST_REL internal_segment_ok (internal_fn_descriptors internal_fns) segs /\
      !i. i < LENGTH segs ==>
        lookup_function (FST (EL i (internal_fn_descriptors internal_fns)))
          unit.cu_context.ctx_functions =
        SOME (mk_internal_function
                (FST (EL i (internal_fn_descriptors internal_fns)))
                (EL i segs)
                (FST (SND (EL i (internal_fn_descriptors internal_fns))))
                (SND (SND (EL i (internal_fn_descriptors internal_fns)))))
Proof
  rpt gen_tac >> strip_tac >>
  drule run_lowering_descriptors_distinct >> strip_tac >>
  `lowering_policy_ok rpolicy`
    by (qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
        rw[run_lowering_def]) >>
  `rpolicy.rpol_frontend_dispatch = Linear` by fs[lowering_policy_ok_def] >>
  Cases_on `compile_generate_runtime selectors external_fns internal_fns
              fallback_fn Linear bucket_count fn_metadata_bytes dense_buckets
              entry_info (initial_compile_state "__entry")` >>
  rename1 `_ = (u, st1)` >> Cases_on `u` >>
  drule_all compile_generate_runtime_shape >> strip_tac >>
  `package_internal_blocks (internal_fn_descriptors internal_fns)
     (entry_blocks ++ FLAT segs) =
   SOME (entry_blocks,
         MAP2 (\d seg. mk_internal_function (FST d) seg (FST (SND d))
                         (SND (SND d))) (internal_fn_descriptors internal_fns)
              segs)`
    by (match_mp_tac package_internal_blocks_segments >> ASM_REWRITE_TAC [] >>
        REWRITE_TAC [EVERY_MEM] >> gen_tac >> strip_tac >> BETA_TAC >>
        match_mp_tac internal_name_not_entry_label >> fs[EVERY_MEM]) >>
  qexistsl_tac [`entry_blocks`, `segs`] >> simp[] >> rpt strip_tac >>
  imp_res_tac LIST_REL_LENGTH >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `all_blocks st1 = _`
    (assume_tac o REWRITE_RULE [loweringShapeDefsTheory.all_blocks_def]) >>
  gs[run_lowering_def, extract_context_with_internals_def] >>
  strip_tac >> gvs[lowering_context_ok_def, ctx_fn_names_def,
                   mk_venom_context_def] >>
  qmatch_goalsub_abbrev_tac `lookup_function _ fns = SOME f` >>
  `MEM f fns` by
    (simp[Abbr `fns`, Abbr `f`, MEM_EL] >> disj2_tac >>
     qexists_tac `i` >> simp[EL_MAP2]) >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) fns)` by simp[Abbr `fns`] >>
  qspecl_then [`fns`, `f`] mp_tac lookup_function_distinct_mem >>
  simp[Abbr `f`, mk_internal_function_metadata]
QED

(* The same for a source internal function of a lowered runtime unit, at
   the label package_internal_fn gives it. *)
Theorem lower_vyper_runtime_unit_internal_lookup:
  !tops rpolicy unit mut nr rr name args dflts ret stmts.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret stmts) tops ==>
    ?fbs.
      lookup_function
        (internal_fn_label (build_func_ids 0 tops name) name (MAP SND args) F)
        unit.cu_context.ctx_functions =
      SOME (mk_internal_function
              (internal_fn_label (build_func_ids 0 tops name) name
                 (MAP SND args) F)
              fbs
              (FST (SND (source_internal_fn_descriptor tops F
                           (mut,nr,rr,name,args,dflts,ret,stmts))))
              (SND (SND (source_internal_fn_descriptor tops F
                           (mut,nr,rr,name,args,dflts,ret,stmts)))))
      /\ fbs <> [] /\
      (HD fbs).bb_label =
        internal_fn_label (build_func_ids 0 tops name) name (MAP SND args) F
Proof
  rpt gen_tac >>
  simp[lower_vyper_runtime_unit_def, bool_case_eq] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts, ints, fb, ctor)` >>
  simp[] >> strip_tac >>
  `MEM (mut,nr,rr,name,args,dflts,ret,stmts) ints` by
    metis_tac[MEM_classify_internal, pairTheory.FST, pairTheory.SND] >>
  `MEM (source_internal_fn_descriptor tops F
          (mut,nr,rr,name,args,dflts,ret,stmts))
       (internal_fn_descriptors
          (MAP (set_internal_package_target rpolicy.rpol_target o
                package_internal_fn tops F (assign_nkeys tops 0) F 0) ints))`
    by (simp[GSYM MAP_MAP_o,
            internal_fn_descriptors_set_internal_package_target,
            internal_fn_descriptors_MAP_package_internal_fn, MEM_MAP] >>
    qexists_tac `(mut,nr,rr,name,args,dflts,ret,stmts)` >> simp[]) >>
  Cases_on `source_internal_fn_descriptor tops F
              (mut,nr,rr,name,args,dflts,ret,stmts)` >>
  rename1 `_ = (lbl, rest)` >> PairCases_on `rest` >>
  `lbl = internal_fn_label (build_func_ids 0 tops name) name (MAP SND args) F`
    by metis_tac[source_internal_fn_descriptor_label, pairTheory.FST] >>
  gvs[] >>
  drule_all run_lowering_internal_lookup >> simp[]
QED

Theorem build_func_param_types_distinct[local]:
  !tops vis mut nr rr name args dflts ret stmts.
    ALL_DISTINCT (supported_function_names tops) /\ vis <> External /\
    MEM (FunctionDecl vis mut nr rr name args dflts ret stmts) tops ==>
    build_func_param_types tops name = MAP SND args
Proof
  Induct >> simp[] >> Cases >>
  simp[build_func_param_types_def, supported_function_names_def] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  `MEM name (supported_function_names tops)` by
    (simp[MEM_supported_function_names] >> metis_tac[]) >>
  `name <> s` by (strip_tac >> gvs[]) >> rw[]
QED

(* For a supported program, the label compile_call gives the INVOKE of a
   main-module internal function is the label package_internal_fn gives
   that function, when the call site's compile env is the program's. *)
Theorem compile_call_intcall_label:
  !tops cenv mut nr rr name args dflts ret stmts.
    supported_program tops /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret stmts) tops /\
    cenv.ce_func_ids = build_func_ids 0 tops /\
    cenv.ce_func_param_types = build_func_param_types tops /\
    ~cenv.ce_is_ctor ==>
    internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE, name)))
      (nsid_to_string (NONE, name))
      (cenv.ce_func_param_types (nsid_to_string (NONE, name)))
      cenv.ce_is_ctor =
    internal_fn_label (build_func_ids 0 tops name) name (MAP SND args) F
Proof
  rpt strip_tac >> simp[nsid_to_string_def] >>
  `ALL_DISTINCT (supported_function_names tops)` by
    metis_tac[supported_program_names, supported_declaration_names_unique] >>
  qspecl_then [`tops`, `Internal`, `mut`, `nr`, `rr`, `name`, `args`,
               `dflts`, `ret`, `stmts`] mp_tac build_func_param_types_distinct >>
  simp[]
QED
