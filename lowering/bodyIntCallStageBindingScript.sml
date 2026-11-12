(* Positional package and source-binding alignment for staged descriptors. *)
Theory bodyIntCallStageBinding
Ancestors
  bodyIntCallStagePackage bodyIntCallPackageLayout compileVyper compileEnv
  entryArgPtrs entryStateRel vyperCall intCallArgs structFieldsProps list pair finite_map

Theorem internal_package_staging_layout:
  !target tops trans keys ctor imm mut nr rr name args dflts ret body
   lbl ce params has_rb is_nr key use_tr view is_ctor imm_len ss rt.
  set_internal_package_target target
    (package_internal_fn tops trans keys ctor imm
      (mut,nr,rr,name,args,dflts,ret,body)) =
      (lbl,ce,params,has_rb,is_nr,key,use_tr,view,is_ctor,imm_len,ss,rt) ==>
  MAP FST params = MAP FST args /\
  MAP SND params = compute_pass_via_stack (MAP SND args)
    (returns_stack_count
      (\n. MAP (FST o SND) (get_struct_fields (make_struct_fields_map tops) n)) ret)
Proof
  simp[set_internal_package_target_def, package_internal_fn_def,
       update_cenv_nonreentrant_def] >> strip_tac >> gvs[] >>
  simp[MAP_ZIP, LENGTH_compute_pass_via_stack]
QED

Theorem internal_package_staging_slot:
  !target tops trans keys ctor imm mut nr rr name args dflts ret body
   lbl ce params has_rb is_nr key use_tr view is_ctor imm_len ss rt i.
  set_internal_package_target target
    (package_internal_fn tops trans keys ctor imm
      (mut,nr,rr,name,args,dflts,ret,body)) =
      (lbl,ce,params,has_rb,is_nr,key,use_tr,view,is_ctor,imm_len,ss,rt) /\
  ALL_DISTINCT (MAP FST args) /\ i < LENGTH args ==>
  FST (EL i params) = FST (EL i args) /\
  ?off. FLOOKUP ce.ce_vars (FST (EL i params)) =
    SOME (MemLoc off (type_memory_bytes ce (SND (EL i args))))
Proof
  rpt gen_tac >> strip_tac >>
  `MAP FST params = MAP FST args` by
    (drule internal_package_staging_layout >> simp[]) >>
  `FST (EL i params) = FST (EL i args)` by
    (`LENGTH params = LENGTH args` by metis_tac[LENGTH_MAP] >>
     qpat_x_assum `MAP FST params = _`
       (mp_tac o Q.AP_TERM `EL i`) >> simp[EL_MAP]) >>
  simp[] >>
  `MEM (FST (EL i args), SND (EL i args)) args` by
    (simp[MEM_EL] >> qexists_tac `i` >> simp[]) >>
  gvs[set_internal_package_target_def, package_internal_fn_def,
      update_cenv_nonreentrant_def] >>
  simp[GSYM type_mem_bytes_type_memory_bytes,
       build_compile_env_ce_struct_fields] >>
  irule build_compile_env_arg_sizes >> simp[]
QED

Theorem internal_package_staged_alignment:
  !target tops trans keys ctor imm mut nr rr name args dflts ret body
   lbl ce params has_rb is_nr key use_tr view is_ctor imm_len ss rt
   D tenv vs env.
  set_internal_package_target target
    (package_internal_fn tops trans keys ctor imm
      (mut,nr,rr,name,args,dflts,ret,body)) =
      (lbl,ce,params,has_rb,is_nr,key,use_tr,view,is_ctor,imm_len,ss,rt) /\
  ALL_DISTINCT (MAP FST args) /\
  MAP (\(ty,tv,v,flag,op). ty) D = MAP SND args /\
  MAP (\(ty,tv,v,flag,op). flag) D = MAP SND params /\
  MAP (\(ty,tv,v,flag,op). v) D = vs /\
  bind_arguments tenv args vs = SOME env /\
  EVERY (\(ty,tv,v,flag,op).
    evaluate_type tenv ty = SOME tv /\
    type_memory_bytes ce ty = type_memory_size tv /\
    (flag ==> is_word_type ty)) D ==>
  LENGTH params = LENGTH D /\ ALL_DISTINCT (MAP FST params) /\
  FDOM env = set (MAP FST params) /\
  (!i. i < LENGTH D ==>
    (\(ty,tv,v,flag,op).
      flag = SND (EL i params) /\ evaluate_type tenv ty = SOME tv /\
      (flag ==> is_word_type ty) /\
      FLOOKUP env (FST (EL i params)) =
        SOME <|assignable := T; type := tv; value := v; popped := []|> /\
      ?off. FLOOKUP ce.ce_vars (FST (EL i params)) =
        SOME (MemLoc off (type_memory_size tv))) (EL i D))
Proof
  rpt gen_tac >> strip_tac >>
  drule internal_package_staging_layout >> strip_tac >>
  `LENGTH params = LENGTH D /\ LENGTH args = LENGTH D` by
    metis_tac[LENGTH_MAP] >>
  `FDOM env = set (MAP FST params)` by
    metis_tac[bind_arguments_fdom] >> simp[] >> rpt strip_tac >>
  `i < LENGTH args` by simp[] >>
  drule_all internal_package_staging_slot >> strip_tac >>
  drule_all bind_arguments_lookup_index >> strip_tac >>
  qpat_x_assum `EVERY _ D` mp_tac >> simp[EVERY_EL] >>
  disch_then (qspec_then `i` mp_tac) >>
  (impl_tac >- simp[]) >> disch_tac >>
  qpat_x_assum `MAP (\(ty,tv,v,flag,op). ty) D = _`
    (mp_tac o Q.AP_TERM `EL i`) >>
  qpat_x_assum `MAP (\(ty,tv,v,flag,op). flag) D = _`
    (mp_tac o Q.AP_TERM `EL i`) >>
  qpat_x_assum `MAP (\(ty,tv,v,flag,op). v) D = _`
    (mp_tac o Q.AP_TERM `EL i`) >>
  Cases_on `EL i D` >> rename1 `(ty,rest)` >> PairCases_on `rest` >>
  fs[EL_MAP] >> rpt strip_tac >> gvs[]
QED
