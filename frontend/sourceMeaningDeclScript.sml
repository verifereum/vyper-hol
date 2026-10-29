Theory sourceMeaningDecl
Ancestors
  sourceMeaningCall sourceMeaningCallDefs sourceMeaningProgram sourceMeaningProgramDefs
  sourceMeaningStmt sourceMeaningStmtDefs sourceMeaningRuntime sourceMeaningDefs
  sourceMeaningValue sourceMeaningElaborate sourceMeaningCode sourceExprProps sourceExprDefs
  sourceModuleSignature sourceModuleDecl sourceModuleDefs sourceTypeDefs sourceSyntax
  vyperInterpreter vyperState vyperContext vyperAST vyperValue
  vyperTypeSystem finite_map alist list rich_list pair

Theorem source_meaning_local_fields:
  (source_module_local cx name ty assignable).sm_owner = cx.sm_owner /\
  (source_module_local cx name ty assignable).sm_env.type_defs = cx.sm_env.type_defs
Proof
  simp[source_module_local_def, extend_local_def]
QED

Theorem source_meaning_argument_fold:
  !aps cx types.
  EVERY (\(arg,id,ty). case arg of SourceArg ignored (SOME a) =>
    source_module_interface_fields annotations a = NONE | _ => T) aps /\
  source_meaning_locals types cx ==>
  let next = FOLDL (\local (arg,id,ty). case arg of
      SourceArg ignored (SOME a) => source_module_annotated_local annotations local id a ty T
    | _ => source_module_local local id ty T) cx aps in
  source_meaning_locals
    (FOLDL (\ts (arg,id,ty). (cx.sm_owner ++ [id],ty)::ts) types aps) next /\
  next.sm_owner = cx.sm_owner /\ next.sm_env.type_defs = cx.sm_env.type_defs
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
  Cases_on `h0` >> rename1 `SourceArg ignored annotation` >>
  Cases_on `annotation` >>
  simp[source_module_annotated_local_def] >> strip_tac >>
  first_x_assum (qspecl_then [`source_module_local cx h1 h2 T`,
    `((cx.sm_owner ++ [h1],h2)::types)`] mp_tac) >>
  simp[source_meaning_locals_extend, source_meaning_local_fields,
    source_module_annotated_local_def]
QED

Theorem source_meaning_parameter_path:
  (owner ++ [name]) ++ [id] = owner ++ [name;id]
Proof
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND]
QED

Theorem source_meaning_parameters_locals:
  EVERY (\(arg,id,ty). case arg of SourceArg ignored (SOME a) =>
    source_module_interface_fields ctx a = NONE | _ => T) (ZIP (args,params)) ==>
  source_meaning_locals (source_meaning_parameter_types ctx name args params)
    (source_module_function_context ctx name args params) /\
  (source_module_function_context ctx name args params).sm_env.type_defs = ctx.sm_env.type_defs
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`ZIP (args,params)`, `ctx with sm_owner := ctx.sm_owner ++ [name]`, `[]`]
    (Q.INST [`annotations` |-> `ctx`] source_meaning_argument_fold)) >>
  simp[source_meaning_locals_def, source_module_function_context_def,
    source_meaning_parameter_types_def, source_meaning_parameter_path]
QED

Theorem source_meaning_default_sources_transport:
  !originals meanings.
  LIST_REL (\(ty,e) m. source_meaning_source [] ctx.sm_scopes ctx.sm_table
    ctx.sm_constants ty e m) originals meanings ==>
  !code. source_module_collect (MAP (\(ty,e). source_module_expression fuel ctx ty e)
      originals) = SM_Ok code ==>
  !cx. get_tenv cx = ctx.sm_env.type_defs ==>
    LIST_REL (\m e. eval_expr cx e =
      source_meaning_eval cx (\p. source_meaning_local (LAST p)) m) meanings code
Proof
  Induct >> Cases_on `meanings` >> simp[source_module_collect_def] >>
  rpt gen_tac >>
  qmatch_goalsub_rename_tac `(\(ty,e). source_module_expression fuel ctx ty e) original` >>
  PairCases_on `original` >> simp[source_meaning_bind_success] >> rpt strip_tac >> gvs[] >>
  irule source_meaning_expression_transport >>
  qexistsl_tac [`ctx`,`fuel`,`original1`,`original0`,`[]`] >>
  simp[source_meaning_locals_def]
QED

(* Every premise here is a source rule or a phase equation; code agreement is
   a conclusion. In particular no post-hoc chosen executable body is a meaning. *)
Theorem source_meaning_declaration_transport:
  source_meaning_declaration ctx declaration meaning /\
  source_module_body fuel ctx slots declaration = SM_Ok emitted ==>
  ?tl. emitted = [tl] /\
    source_meaning_decl_code ctx.sm_env.type_defs meaning tl
Proof
  simp[Once source_meaning_declaration_cases] >> strip_tac
  >- (gvs[source_module_body_def, source_module_signature_def,
        source_meaning_bind_success, source_meaning_bind_pair_success] >>
      drule source_meaning_parameters_locals >>
      disch_then (qspec_then `name` strip_assume_tac) >>
      simp[source_meaning_decl_code_def] >> gen_tac >> disch_tac >> conj_tac
      >- (gvs[source_meaning_default_sources_def] >>
          drule_all source_meaning_default_sources_transport >> simp[]) >>
      `get_tenv cx = (source_module_function_context ctx name args params).sm_env.type_defs`
        by simp[] >>
      drule_all (CONJUNCT2 source_meaning_body_transport) >>
      simp[source_meaning_execute_def])
  >- (gvs[source_module_body_def, source_module_signature_def, source_module_variable_def,
        source_meaning_bind_success] >>
      simp[source_meaning_decl_code_def] >> rpt strip_tac >>
      `source_meaning_locals [] ctx` by simp[source_meaning_locals_def] >>
      drule_all source_meaning_expression_transport >>
      simp[source_meaning_locals_def, source_meaning_eval_def]) >>
  gvs[source_module_body_def, source_module_signature_def, source_module_variable_def,
    source_meaning_bind_success, source_module_expression_def,
    source_module_expr_result_def, AllCaseEqs()] >>
  Cases_on `source_expr_elaborate fuel ctx.sm_env ctx.sm_scopes ctx.sm_table
    ctx.sm_constants ctx.sm_bindings ty original` >>
  gvs[source_module_expr_result_def] >>
  drule source_expr_elaborate_build >> strip_tac >>
  drule_all source_meaning_build_constant >> strip_tac >>
  drule source_meaning_value_reify >> strip_tac >>
  simp[source_meaning_decl_code_def] >>
  simp[FUN_EQ_THM, return_def]
QED
