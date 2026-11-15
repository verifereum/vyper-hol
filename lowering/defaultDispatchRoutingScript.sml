(* Raw selector routing: bytes are word8, so byte validity is intrinsic. *)
Theory defaultDispatchRouting
Ancestors entryDispatchProps checkedSelectorTableProps sourceEntrySelection
  vyperCalldata selectorCompilerProps supportedProgram supportedProgramProps
  vyperABIEntries compileVyper loweringShapeProps mem2varBlockSimHelpers list rich_list

Theorem cd_selector_method_id[local]:
  4 <= LENGTH cd ==> cd_selector cd = w2n (calldata_method_id cd)
Proof
  strip_tac >>
  `LENGTH (TAKE 4 cd) = 4` by simp[LENGTH_TAKE] >>
  drule selectorCompilerPropsTheory.calldata_method_id_four_bytes >>
  simp[GSYM cd_selector_def] >> strip_tac >>
  `calldata_method_id (TAKE 4 cd ++ DROP 4 cd) =
   calldata_method_id (TAKE 4 cd)` by
    (irule calldata_method_id_append >> simp[]) >> gvs[]
QED

Theorem default_raw_selected_target:
  MEM (mut,nr,rr,name,args,([]:expr list),ret,fbody) exts /\
  FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
    (abi_external_signatures tops) = SOME (name,MAP SND args) /\
  4 <= LENGTH cd /\
  ALL_DISTINCT (MAP FST (build_selectors (type_env tops) exts)) ==>
  linear_dispatch_target cd
    (MAP (\(sel,lbl,z). (sel,lbl)) (build_selectors (type_env tops) exts))
    fallback = "fn_" ++ name
Proof
  strip_tac >>
  drule build_selectors_mem >>
  disch_then (qspec_then `type_env tops` mp_tac) >>
  simp[compute_selector_method_id] >> strip_tac >>
  `abi_method_id (type_env tops) name (MAP SND args) = cd_selector cd` by
    (drule venomInstTheory.FIND_P >> simp[]) >>
  irule linear_dispatch_target_distinct >>
  conj_tac
  >- (`(\x:num#string#bool. FST ((\(a,b,c). (a,b)) x)) = FST` by
        simp[FUN_EQ_THM, pairTheory.FORALL_PROD] >>
      gvs[MAP_MAP_o, combinTheory.o_DEF]) >>
  qexists_tac `abi_method_id (type_env tops) name (MAP SND args)` >>
  simp[selectorDispatchTheory.calldata_hits_selector_def, GSYM cd_selector_method_id] >>
  simp[MEM_MAP] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem default_classified_signature[local]:
  MEM (mut,nr,rr,name,args,([]:expr list),ret,fbody)
    (FST (classify_functions tops)) ==>
  MEM (name,MAP SND args) (abi_external_signatures tops)
Proof
  strip_tac >>
  `MEM (name,MAP SND args)
     (FLAT (MAP (\(mut,nr,rr,name,args,dflts,ret,stmts).
       abi_function_signatures name args dflts)
       (FST (classify_functions tops))))` by
    (simp[MEM_FLAT, MEM_MAP] >>
     qexists_tac `abi_function_signatures name args ([]:expr list)` >>
     simp[vyperABIEntriesTheory.abi_function_signatures_no_defaults] >>
     goal_assum (drule_at Any) >> simp[]) >>
  pop_assum mp_tac >> rewrite_tac[classify_external_signatures, MEM_APPEND] >>
  simp[abi_external_signatures_def] >>
  metis_tac[mem_flat_map_filter]
QED

Theorem default_raw_fallback_target:
  supported_program tops /\
  (LENGTH cd < 4 \/
   FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
     (abi_external_signatures tops) = NONE) ==>
  linear_dispatch_target cd
    (MAP (\(sel,lbl,z). (sel,lbl))
      (build_selectors (type_env tops) (FST (classify_functions tops))))
    fallback = fallback
Proof
  strip_tac >> irule linear_dispatch_target_fallback >>
  Cases_on `LENGTH cd < 4` >- simp[] >>
  gvs[] >> rpt gen_tac >> strip_tac >>
  gvs[MEM_MAP, pairTheory.EXISTS_PROD] >>
  drule build_selectors_mem_inv >> strip_tac >>
  `dflts = []` by
    (drule loweringShapePropsTheory.supported_program_no_external_defaults >>
     simp[EVERY_MEM, combinTheory.o_DEF] >> strip_tac >>
     first_x_assum drule >>
     simp[compileVyperTheory.external_has_defaults_def, NULL_EQ]) >> gvs[] >>
  drule default_classified_signature >> strip_tac >>
  gvs[compute_selector_method_id,
    selectorDispatchTheory.calldata_hits_selector_def, GSYM cd_selector_method_id] >>
  qpat_x_assum `FIND _ _ = NONE` mp_tac >>
  simp[mem2varBlockSimHelpersTheory.FIND_NONE_EVERY, EVERY_MEM,
    combinTheory.o_DEF, pairTheory.FORALL_PROD] >> metis_tac[]
QED
