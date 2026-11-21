(* Whitelist removal: every single-module program check_contract accepts is
   in the supported_* gate.

   TOP-LEVEL: check_contract_supported_program (runtime check and the
   layouts the call relation fixes) and check_contract_supported_program_deploy
   (deployment check). The four top theorems discharge their gate through
   these, so neither is assumed whole: each conjunct of the gate has its own
   lemma below.

   - Storage, transient and hashmap slots: the checker reads them from the
     layouts and ignores the AST annotation, so headers and bodies (whose
     storage clauses ask for the annotation) take layouts_agree, which the
     call and deployment relations carry; the checker allocates every
     variable (check_contract_main_module_allocated). Types come from
     assignable_type.
   - Function bodies and defaults: from check_function_body. The statement
     and expression layers carry the typing environment of the body, which
     extends the artifact's and binds exactly the arguments, locals and loop
     variables; custom-error reasons come from custom_errors_stmt_ok.
   - Constants: from the checker's constant typing. *)
Theory whitelistCheckerGate
Ancestors
  list alist vyperAST vyperTypeSystem vyperTypeContract vyperTypeContractContext
  e2eDefs e2eDeployDefs
  supportedTypes supportedDecls supportedNames supportedExprs supportedStmts
  supportedStmtTraverse supportedProgram
  whitelistCheckerDecls whitelistCheckerDeploy whitelistCheckerTypes
  whitelistCheckerProgram

(* ===== Runtime gate ===== *)

Theorem check_contract_supported_declaration_headers:
  check_contract F am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx ==>
  supported_declaration_headers tops
Proof
  cheat
QED

Theorem check_contract_supported_internal_function_names:
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  ALL_DISTINCT (supported_internal_function_names tops)
Proof
  strip_tac >>
  drule check_contract_function_names_same_vis_distinct >>
  disch_then (qspec_then `Internal` mp_tac) >> simp[] >>
  `!ts. supported_internal_function_names ts =
        supported_function_names
          (FILTER (\t. ?m nr rr n a d r b.
                     t = FunctionDecl Internal m nr rr n a d r b) ts)`
    suffices_by simp[] >>
  Induct >> simp[supported_internal_function_names_def,
                 supported_function_names_def] >>
  Cases >> simp[supported_function_names_def] >> rw[] >>
  gvs[supported_function_names_def] >>
  rename1 `vis <> Internal` >> Cases_on `vis` >> gvs[]
QED

Theorem check_contract_supported_function_body:
  check_contract F am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops /\
  vis <> Deploy ==>
  supported_function_body tops vis args fbody
Proof
  cheat
QED

Theorem check_contract_supported_defaults:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops /\
  vis <> Deploy ==>
  EVERY (supported_default_expression tops) dflts /\
  supported_pure_exprs tops dflts
Proof
  cheat
QED

Theorem check_contract_supported_consts:
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  EVERY (supported_pure_expr tops o SND) (module_consts_env tops [])
Proof
  cheat
QED

Theorem check_contract_supported_declaration_bodies:
  check_contract F am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx ==>
  EVERY (supported_declaration_body tops) tops
Proof
  rw[EVERY_MEM] >> rename1 `MEM tl tops` >>
  Cases_on `tl` >> simp[supported_declaration_body_def] >>
  metis_tac[check_contract_supported_function_body,
            check_contract_supported_defaults]
QED

(* TOP-LEVEL *)
Theorem check_contract_supported_program:
  check_contract F am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx ==>
  supported_program tops
Proof
  metis_tac[supported_program_def, check_contract_supported_declaration_headers,
            check_contract_supported_declaration_names,
            check_contract_supported_internal_function_names,
            check_contract_supported_declaration_bodies,
            check_contract_supported_consts]
QED

(* ===== Deployment gate ===== *)

Theorem check_contract_deploy_function_body:
  check_contract T am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx /\
  MEM (FunctionDecl Deploy mut nr rr name args dflts ret fbody) tops ==>
  EVERY (supported_value_type tops o SND) args /\
  supported_function_body tops Deploy args fbody
Proof
  cheat
QED

(* TOP-LEVEL *)
Theorem check_contract_supported_program_deploy:
  check_contract T am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx ==>
  supported_program_deploy tops
Proof
  rw[supported_program_deploy_def, EVERY_MEM] >> rename1 `MEM tl tops` >>
  Cases_on `tl` >> simp[supported_deploy_declaration_def] >>
  rename1 `FunctionDecl vis` >> Cases_on `vis` >> simp[] >>
  metis_tac[check_contract_deploy_function_body]
QED

(* ===== The gate from the top theorems' typing premises ===== *)

(* TOP-LEVEL *)
Theorem source_typing_ok_supported_program:
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx ==>
  supported_program tops
Proof
  rw[source_typing_ok_def, source_deployment_rel_def] >>
  metis_tac[check_contract_supported_program]
QED

(* TOP-LEVEL *)
Theorem deploy_typing_ok_supported_programs:
  deploy_typing_ok tops am tx /\ layouts_agree tops am tx ==>
  supported_program tops /\ supported_program_deploy tops
Proof
  rw[deploy_typing_ok_def] >>
  metis_tac[check_contract_supported_program,
            check_contract_supported_program_deploy]
QED
