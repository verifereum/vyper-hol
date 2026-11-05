(* A piece of S1 (loweringRuntimeCorrect's lower_vyper_runtime_unit_correct). *)
Theory stmtsEnvRetTy
Ancestors
  stmtSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list pair fragExec  bodySim bodySimMain loweringHalt stmtLoweringMono  exprLoweringProps
  compileEnv compileVyper moduleLowering stmtLowering
  e2eDefs supportedProgram supportedDecls supportedExprForms supportedStmts
  vyperLoweringCorrect rawReturnHeader
  vyperTypeSelectedEntrySoundness vyperTypeSystem
  vyperInterpreter vyperState vyperContext
  venomState venomExecSemantics venomWf

val _ = Parse.hide "body";

Theorem supported_variable_decl_var_type[local]:
  !tops name vis mut ty slot.
    supported_variable_decl tops (NONE, name) = SOME (vis, mut, ty, slot) ==>
    build_var_type_map tops (NONE, name) = SOME ty
Proof
  Induct >> simp[supported_variable_decl_def, build_var_type_map_def] >>
  Cases >> rw[supported_variable_decl_def, build_var_type_map_def]
QED

Theorem body_inv_dynarrays_typed[local]:
  !tops ctx cenv cx id.
    body_inv tops ctx cenv cx /\ supported_storage_dynamic_array tops id ==>
    ?t b. cenv.ce_module_var_type id = SOME (ArrayT t b)
Proof
  rw[body_inv_def] >> PairCases_on `id` >>
  `id0 = NONE` by
    (CCONTR_TAC >> Cases_on `tops` >>
     gvs[supported_storage_dynamic_array_def, supported_variable_decl_def]) >>
  gvs[supported_storage_dynamic_array_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  drule supported_variable_decl_var_type >> simp[]
QED

Theorem declare_local_module_var_type[local]:
  !cenv id ty st c st'.
    declare_local cenv id ty st = (c, st') ==>
    c.ce_module_var_type = cenv.ce_module_var_type
Proof
  rw[declare_local_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[compileEnvTheory.compile_env_accfupds]
QED

Theorem declare_stmt_local_module_var_type[local]:
  !cenv s st c st'.
    declare_stmt_local cenv s st = (c, st') ==>
    c.ce_module_var_type = cenv.ce_module_var_type
Proof
  Cases_on `s` >> rw[declare_stmt_local_def, comp_return_def] >>
  metis_tac[declare_local_module_var_type]
QED

(* Congruences for simp: under a declaration's binder, the declared
   environment keeps the module variable types. *)
Theorem declare_local_bind_cong[local]:
  !cenv id t f1 f2.
    (!c. c.ce_module_var_type = cenv.ce_module_var_type ==> f1 c = f2 c) ==>
    comp_bind (declare_local cenv id t) f1 =
    comp_bind (declare_local cenv id t) f2
Proof
  rw[FUN_EQ_THM, comp_bind_def] >> pairarg_tac >> gvs[] >>
  imp_res_tac declare_local_module_var_type >> res_tac >> simp[]
QED

Theorem declare_stmt_local_bind_cong[local]:
  !cenv s f1 f2.
    (!c. c.ce_module_var_type = cenv.ce_module_var_type ==> f1 c = f2 c) ==>
    comp_bind (declare_stmt_local cenv s) f1 =
    comp_bind (declare_stmt_local cenv s) f2
Proof
  rw[FUN_EQ_THM, comp_bind_def] >> pairarg_tac >> gvs[] >>
  imp_res_tac declare_stmt_local_module_var_type >> res_tac >> simp[]
QED

(* compile_stmt reads the return type only to compile a valued return and
   as the element type of an Append whose target root has no array type; a
   supported Append targets a storage dynamic array, which
   has an array type in the compile env, and no declaration changes module types. *)
Theorem compile_stmt_ret_ty[local]:
  (!cenv lctx ty s.
     (!id. supported_storage_dynamic_array tops id ==>
          ?t b. cenv.ce_module_var_type id = SOME (ArrayT t b)) /\
     supported_stmt tops bindings s /\
     ~stmt_valued_return s ==>
     compile_stmt cenv lctx ty s = compile_stmt cenv lctx ty' s) /\
  (!cenv lctx ty ss.
     (!id. supported_storage_dynamic_array tops id ==>
          ?t b. cenv.ce_module_var_type id = SOME (ArrayT t b)) /\
     supported_stmts tops bindings ss /\
     ~stmts_valued_return ss ==>
     compile_stmts cenv lctx ty ss = compile_stmts cenv lctx ty' ss)
Proof
  ho_match_mp_tac compile_stmt_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`compile_stmts _ _ _ (_::_)`]
  >- (rpt strip_tac >> simp[FUN_EQ_THM] >> qx_gen_tac `cs0` >>
      ONCE_REWRITE_TAC [compile_stmt_def] >>
      simp[comp_bind_def, comp_get_def] >>
      IF_CASES_TAC >> simp[] >>
      rpt (qpat_x_assum `!cs cenv. _` (qspec_then `cs0` mp_tac)) >>
      gvs[supported_stmt_def, stmt_valued_return_def] >> rpt strip_tac >>
      simp[Cong declare_stmt_local_bind_cong])
  >~ [`Append target _`]
  >- (rpt strip_tac >> Cases_on `target` >>
      gvs[supported_stmt_def, supported_append_target_def,
          stmt_valued_return_def] >>
      first_x_assum (drule_then strip_assume_tac) >>
      ONCE_REWRITE_TAC [compile_stmt_def] >> simp[target_root_type_def]) >>
  rpt strip_tac >> gvs[supported_stmt_def, stmt_valued_return_def] >>
  ONCE_REWRITE_TAC [compile_stmt_def] >>
  simp[Cong declare_local_bind_cong]
QED

(* A supported body without a valued return compiles the same at every
   return type. *)

(* compile_stmt reads the return type only to compile
   a valued return and as the element type of an Append whose target root
   has no array type.  A supported Append targets a storage dynamic array,
   whose type body_inv's compile env gives (ce_module_var_type), and no
   declaration changes that. *)
Theorem stmts_env_ret_ty:
  !ss tops bindings ctx cenv cx lctx ty ty'.
    supported_stmts tops bindings ss /\ body_inv tops ctx cenv cx /\
    ~stmts_valued_return ss ==>
    stmts_env cenv lctx ty ss = stmts_env cenv lctx ty' ss
Proof
  rpt strip_tac >>
  `!id. supported_storage_dynamic_array tops id ==>
        ?t b. cenv.ce_module_var_type id = SOME (ArrayT t b)` by
    metis_tac[body_inv_dynarrays_typed] >>
  qpat_x_assum `body_inv _ _ _ _` kall_tac >>
  pop_assum mp_tac >> pop_assum mp_tac >> pop_assum mp_tac >>
  qid_spec_tac `cenv` >> Induct_on `ss` >> simp[stmts_env_def] >>
  rpt strip_tac >> simp[FUN_EQ_THM] >> qx_gen_tac `cs0` >>
  gvs[supported_stmt_def, stmt_valued_return_def] >>
  simp[comp_bind_def, comp_get_def] >>
  IF_CASES_TAC >> simp[] >>
  `!c. c.ce_module_var_type = cenv.ce_module_var_type ==>
       compile_stmt c lctx ty h = compile_stmt c lctx ty' h` by
    (rpt strip_tac >> irule (cj 1 compile_stmt_ret_ty) >> simp[] >>
     metis_tac[]) >>
  simp[Cong declare_stmt_local_bind_cong]
QED

