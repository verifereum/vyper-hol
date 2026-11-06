Theory bodyIntCallMetadata
Ancestors
  bodyIntCallAssembly loweringShapeProps supportedNames compileVyper bodySim
  exprLowering supportedProgram compileEnv

Theorem build_func_info_distinct:
  !tops vis mut nr rr name args dflts ret stmts sft.
    ALL_DISTINCT (supported_function_names tops) /\ vis <> External /\
    MEM (FunctionDecl vis mut nr rr name args dflts ret stmts) tops ==>
    build_func_info sft tops name =
      compute_func_info (\n. MAP (FST o SND) (sft n)) ret
        (type_mem_bytes sft ret) (MAP SND args)
Proof
  Induct_on `tops` >- simp[] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[supported_function_names_def, build_func_info_def] >>
  rpt strip_tac >> gvs[]
  >~ [`~MEM headname (supported_function_names tops)`]
    >- (`MEM name (supported_function_names tops)` by
          (simp[MEM_supported_function_names] >> metis_tac[]) >>
        `name <> headname` by metis_tac[] >>
        Cases_on `f = External` >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem body_internal_decl_return_count:
  body_inv tops ctx ce cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret stmts) tops /\
  ce.ce_func_info (nsid_to_string (NONE,name)) = (nret,rbs,pvs) ==>
  nret = returns_stack_count
    (\n. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields n)) ret
Proof
  strip_tac >>
  `ALL_DISTINCT (supported_function_names tops)` by
    (fs[body_inv_def] >> drule supported_program_names >>
     simp[supported_declaration_names_def]) >>
  drule_all (SRULE [] (Q.SPEC `Internal`
    (Q.GEN `vis` (SPEC_ALL build_func_info_distinct)))) >>
  disch_then (qspec_then `get_struct_fields ce.ce_struct_fields` mp_tac) >>
  fs[body_inv_def, nsid_to_string_def, compute_func_info_def] >>
  qpat_x_assum `ce.ce_func_info = _` (fn th =>
    qpat_x_assum `ce.ce_func_info name = _` (mp_tac o REWRITE_RULE [th])) >>
  simp[]
QED
