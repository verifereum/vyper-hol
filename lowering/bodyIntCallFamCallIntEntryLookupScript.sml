(* Selected internal compilation witnesses, for both lowering modes. *)
Theory bodyIntCallFamCallIntEntryLookup
Ancestors
  loweringShapeDefs loweringShapeProps moduleLowering compileEnv vyperCompiler intCallLookup ctorDeployShape ctorDeployLoweringCode intCallCallee
  bodyIntCallFamCallIntEntryPackage bodyIntCallFamCallIntEntrySelectedSegment bodyIntCallFamCallIntEntrySegmentCode


Theorem intcall_extracted_internal_lookup:
  !entry packages sf ctx data imm name rb rc.
    extract_context_with_internals entry packages sf = SOME (ctx,data) /\
    lowering_context_ok (install_immutable_reservation imm ctx) /\
    MEM (name,rb,rc) (internal_fn_descriptors packages) ==>
    ?blocks.
      lookup_function name
        (install_immutable_reservation imm ctx).ctx_functions =
        SOME (mk_internal_function name blocks rb rc) /\
      blocks <> [] /\ (HD blocks).bb_label = name
Proof
  rpt gen_tac >>
  simp[vyperCompilerTheory.extract_context_with_internals_def,
       vyperCompilerTheory.install_immutable_reservation_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[AllCaseEqs(), vyperCompilerTheory.lowering_context_ok_def,
      venomInstTheory.ctx_fn_names_def, venomInstTheory.mk_venom_context_def] >>
  drule package_internal_blocks_metadata >> strip_tac >>
  drule descriptor_names_fn_names >> strip_tac >>
  `ALL_DISTINCT (MAP FST (internal_fn_descriptors packages))` by gvs[] >>
  drule_all package_internal_blocks_mem >> strip_tac >>
  qexists_tac `fbs` >> simp[] >>
  metis_tac[lookup_function_distinct_mem, mk_internal_function_metadata,
            listTheory.MEM, listTheory.MAP, listTheory.ALL_DISTINCT]
QED

Theorem intcall_deploy_internal_lookup:
  !has_ctor policy runtime imm args size packages ce body pay nr key tr
   entry unit name rb nret.
    run_deploy_lowering has_ctor policy runtime imm args size packages
      ce body pay nr key tr entry = SOME unit /\
    MEM (name,rb,nret) (internal_fn_descriptors packages) ==>
    ?blocks.
      lookup_function name unit.cu_context.ctx_functions =
        SOME (mk_internal_function name blocks rb nret) /\
      blocks <> [] /\ (HD blocks).bb_label = name
Proof
  rpt gen_tac >> simp[run_deploy_lowering_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[AllCaseEqs()] >>
  drule_all intcall_extracted_internal_lookup >> simp[]
QED

Theorem intcall_deploy_source_lookup:
  !tops policy runtime unit exts ints fb cf src.
    lower_vyper_deploy_unit tops policy runtime = SOME unit /\
    classify_functions tops = (exts,ints,fb,SOME cf) /\ MEM src ints ==>
    ?blocks.
      lookup_function (FST (source_internal_fn_descriptor tops T src))
        unit.cu_context.ctx_functions =
      SOME (mk_internal_function
        (FST (source_internal_fn_descriptor tops T src)) blocks
        (FST (SND (source_internal_fn_descriptor tops T src)))
        (SND (SND (source_internal_fn_descriptor tops T src)))) /\
      blocks <> [] /\
      (HD blocks).bb_label = FST (source_internal_fn_descriptor tops T src)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_ctor_lowering_trace >> strip_tac >>
  `MEM (source_internal_fn_descriptor tops T src)
    (internal_fn_descriptors
      (MAP (set_internal_package_target policy.rpol_target o
        package_internal_fn tops F (assign_nkeys tops 0) T (imm_len tops)) ints))`
    by (simp[GSYM listTheory.MAP_MAP_o,
          compileVyperTheory.internal_fn_descriptors_set_internal_package_target,
          compileVyperTheory.internal_fn_descriptors_MAP_package_internal_fn,
          listTheory.MEM_MAP] >>
        qexists_tac `src` >> simp[]) >>
  Cases_on `source_internal_fn_descriptor tops T src` >>
  rename1 `_ = (lbl,metadata)` >> PairCases_on `metadata` >> gvs[] >>
  drule_all intcall_extracted_internal_lookup >> simp[]
QED

Theorem intcall_extracted_selected_segment:
  !entry pre post before seg after lbl rb rc ctx data cap.
    LIST_REL internal_segment_ok (internal_fn_descriptors pre) before /\
    internal_segment_ok (lbl,rb,rc) seg /\
    LIST_REL internal_segment_ok (internal_fn_descriptors post) after /\
    ALL_DISTINCT (MAP FST
      (internal_fn_descriptors pre ++ (lbl,rb,rc)::internal_fn_descriptors post)) /\
    EVERY (\d. ~compiler_label (FST d) /\
      ~MEM (FST d) (MAP (\bb. bb.bb_label) entry))
      (internal_fn_descriptors pre ++ (lbl,rb,rc)::internal_fn_descriptors post) /\
    package_internal_blocks
      (internal_fn_descriptors pre ++ (lbl,rb,rc)::internal_fn_descriptors post)
      (entry ++ FLAT (before ++ seg::after)) = SOME (entry,ctx) /\
    lowering_context_ok
      (install_immutable_reservation cap
        (mk_venom_context (mk_raw_function data entry::ctx) (SOME data))) ==>
    lookup_function lbl ctx = SOME (mk_internal_function lbl seg rb rc) /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) seg)
Proof
  rpt gen_tac >> strip_tac >> rename1 `internal_segment_ok (lbl,rb,nret) seg` >>
  `LIST_REL internal_segment_ok
    (internal_fn_descriptors pre ++ (lbl,rb,nret)::internal_fn_descriptors post)
    (before ++ seg::after)` by
    (irule listTheory.LIST_REL_APPEND_suff >> simp[]) >>
  drule_all package_internal_blocks_segments >> strip_tac >> gvs[] >>
  `LENGTH (internal_fn_descriptors pre) = LENGTH before` by
    metis_tac[listTheory.LIST_REL_LENGTH] >>
  `MEM (mk_internal_function lbl seg rb nret)
    (MAP2 (\d seg. mk_internal_function (FST d) seg
      (FST (SND d)) (SND (SND d)))
      (internal_fn_descriptors pre ++ (lbl,rb,nret)::internal_fn_descriptors post)
      (before ++ seg::after))` by simp[listTheory.MAP2_APPEND] >>
  gvs[lowering_context_ok_def, install_immutable_reservation_def,
      venomInstTheory.ctx_fn_names_def, venomInstTheory.mk_venom_context_def,
      listTheory.APPEND] >>
  rule_assum_tac (PURE_REWRITE_RULE
    [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  conj_tac
  >- (drule_all lookup_function_distinct_mem >>
      simp[mk_internal_function_metadata]) >>
  qpat_x_assum `EVERY (\fn. ALL_DISTINCT _ /\ _) _` mp_tac >>
  pure_rewrite_tac [listTheory.EVERY_MEM] >> disch_then drule >>
  simp[venomInstTheory.fn_labels_def, mk_internal_function_metadata]
QED

Theorem intcall_selected_packaged_compilation:
  !pre post lbl ce params rb nr key tr view ctor imm body rt s t
   entry ctx data cap.
    compile_internal_fn_bodies
      (pre ++ (lbl,ce,params,rb,nr,key,tr,view,ctor,imm,body,rt)::post) s =
      ((),t) /\ shape_state s /\
    EVERY internal_fn_shape_ok
      (pre ++ (lbl,ce,params,rb,nr,key,tr,view,ctor,imm,body,rt)::post) /\
    EVERY (\d. internal_label_ok (FST d))
      (internal_fn_descriptors
        (pre ++ (lbl,ce,params,rb,nr,key,tr,view,ctor,imm,body,rt)::post)) /\
    ALL_DISTINCT (MAP FST (internal_fn_descriptors
      (pre ++ (lbl,ce,params,rb,nr,key,tr,view,ctor,imm,body,rt)::post))) /\
    EVERY (\d. ~compiler_label (FST d) /\
      ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks s)))
      (internal_fn_descriptors
        (pre ++ (lbl,ce,params,rb,nr,key,tr,view,ctor,imm,body,rt)::post)) /\
    extract_context_with_internals entry
      (pre ++ (lbl,ce,params,rb,nr,key,tr,view,ctor,imm,body,rt)::post) t =
      SOME (ctx,data) /\
    lowering_context_ok (install_immutable_reservation cap ctx) ==>
    ?a old b c seg.
      compile_internal_fn_bodies pre s = ((),a) /\
      new_block lbl a = (old,b) /\
      compile_internal_function ce params rb nr key tr view ctor imm body rt b =
        ((),c) /\
      compile_internal_fn_bodies post c = ((),t) /\
      lookup_function lbl (install_immutable_reservation cap ctx).ctx_functions =
        SOME (mk_internal_function lbl seg rb ce.ce_returns_count) /\
      seg <> [] /\ (HD seg).bb_label = lbl /\
      fn_has_code b c (mk_internal_function lbl seg rb ce.ce_returns_count)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all intcall_selected_segment_trace >> strip_tac >>
  `all_blocks t = all_blocks s ++ FLAT (before ++ seg::after)` by simp[] >>
  `LIST_REL internal_segment_ok
    (internal_fn_descriptors pre ++ (lbl,rb,ce.ce_returns_count)::
      internal_fn_descriptors post) (before ++ seg::after)` by
    (irule listTheory.LIST_REL_APPEND_suff >> simp[]) >>
  gvs[intcall_internal_descriptors_append, internal_fn_descriptors_def] >>
  qpat_assum `LIST_REL _ (_ ++ _) _`
    (mp_then Any (qspec_then `all_blocks s` mp_tac)
      package_internal_blocks_segments) >>
  (impl_tac >- simp[]) >> strip_tac >>
  gvs[extract_context_with_internals_def, GSYM all_blocks_def,
      intcall_internal_descriptors_append, internal_fn_descriptors_def] >>
  drule_all (SRULE [] intcall_extracted_selected_segment) >> strip_tac >>
  `fn_has_code b c (mk_internal_function lbl seg rb ce.ce_returns_count)` by
    (metis_tac[intcall_segment_contains_code]) >>
  qexists_tac `seg` >>
  gvs[install_immutable_reservation_def, venomInstTheory.mk_venom_context_def,
      internal_segment_ok_def] >>
  drule venomInstTheory.lookup_function_mem >> strip_tac >>
  gvs[lowering_context_ok_def, venomInstTheory.ctx_fn_names_def] >>
  `(mk_raw_function entry (all_blocks s)).fn_name <> (HD seg).bb_label` by
    (strip_tac >> gvs[]) >>
  gvs[venomInstTheory.lookup_function_def, listTheory.FIND_thm]
QED
