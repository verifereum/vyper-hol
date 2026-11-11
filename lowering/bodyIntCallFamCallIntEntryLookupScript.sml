(* Selected internal compilation witnesses, for both lowering modes. *)
Theory bodyIntCallFamCallIntEntryLookup
Ancestors
  moduleLowering compileEnv vyperCompiler intCallLookup ctorDeployShape ctorDeployLoweringCode intCallCallee
  bodyIntCallFamCallIntEntryPackage

Theorem intcall_internal_bodies_append:
  !xs ys s.
    compile_internal_fn_bodies (xs ++ ys) s =
    comp_ignore_bind (compile_internal_fn_bodies xs)
      (compile_internal_fn_bodies ys) s
Proof
  Induct
  >- simp[compile_internal_fn_bodies_def, comp_ignore_bind_def,
          comp_bind_def, comp_return_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >>
  simp[compile_internal_fn_bodies_def, comp_ignore_bind_def, comp_bind_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem intcall_selected_internal_compilation:
  !pre post lbl ce params rb nr key tr view ctor imm body rt s t.
    compile_internal_fn_bodies
      (pre ++ (lbl,ce,params,rb,nr,key,tr,view,ctor,imm,body,rt)::post) s =
      ((),t) ==>
    ?a old b c.
      compile_internal_fn_bodies pre s = ((),a) /\
      new_block lbl a = (old,b) /\
      compile_internal_function ce params rb nr key tr view ctor imm body rt b =
        ((),c) /\
      compile_internal_fn_bodies post c = ((),t)
Proof
  rpt gen_tac >>
  simp[intcall_internal_bodies_append, compile_internal_fn_bodies_def,
       comp_ignore_bind_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any))
QED

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
