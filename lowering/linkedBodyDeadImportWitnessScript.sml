(* A checked uses-only import may have neither state allocation nor a typed body. *)
Theory linkedBodyDeadImportWitness
Ancestors
  e2eWitnessCompute bodyInvSplit supportedProgram supportedStmts
  vyperTypeContract vyperTypeCallGraph vyperAST compileUnit asmOptimizer
  bodyCallSupport typedCopyDomain vyperContext alist finite_map list
Libs
  vyperCheckContractLib computeLib finite_mapLib intReduce wordsLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset;
val () = computeLib.upd_compset intReduce.add_int_compset;

val ty = ``BaseT (UintT 256)``;
val dead_body = ``
  [Assign (BaseTarget (NameTarget "missing")) (Literal ^ty (IntL 0))]
``;
val dead_tops = ``
  [VariableDecl Private Storage "dead_slot" ^ty NONE;
   FunctionDecl Internal NonPayable F F "dead_fn" [] [] NoneT ^dead_body]
``;
val dead_mods = ``[(NONE : num option,[]);(SOME 1,^dead_tops)]``;
val acyclic = EVAL ``contract_call_graph_acyclic ^dead_mods``;
val checked = SIMP_RULE (srw_ss()) [acyclic]
  (vyperCheckContractLib.check_contract_conv
    ``check_contract F [] (2w:160 word) ^dead_mods``);
val compiled = EVAL
  ``compile_vyper_mods asm_opt_finalizer (o1_policy all_capabilities) ^dead_mods []``

Triviality dead_import_runtime_lowering:
  ?p unit. lower_vyper_runtime_unit_mods ^dead_mods [] p = SOME unit
Proof
  mp_tac compiled >>
  simp[compile_vyper_mods_def, compile_vyper_with_mods_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem linked_dead_import_contract_inv:
  (?art. check_contract F [] (2w:160 word) ^dead_mods = SOME art) /\
  (?bs. compile_vyper_mods asm_opt_finalizer (o1_policy all_capabilities)
     ^dead_mods [] = SOME bs) /\
  ~supported_function_body ^dead_tops Internal [] ^dead_body /\
  !cx. ~cx.in_deploy /\ cx.layouts = [] /\
    ALOOKUP cx.sources cx.txn.target = SOME ^dead_mods ==>
    ?ctx ce. contract_inv ^dead_mods [] ctx ce cx
Proof
  simp[checked, compiled] >>
  conj_tac >- EVAL_TAC >>
  rpt strip_tac >>
  `~context_function_live cx (SOME 1,"dead_fn")` by
    (simp[context_function_live_def, function_live_def] >> EVAL_TAC) >>
  strip_assume_tac dead_import_runtime_lowering >>
  qexists_tac `unit.cu_context` >>
  qexists_tac `build_compile_env_unit ^dead_mods NONE External NonPayable
    "" [] NoneT [] T with ce_target := p.rpol_target` >>
  PURE_REWRITE_TAC [contract_inv_def] >>
  simp[get_tenv_def, LET_THM] >>
  rpt conj_tac
  >- EVAL_TAC
  >- EVAL_TAC
  >- (rpt strip_tac >> gvs[ALOOKUP_def, AllCaseEqs()] >> EVAL_TAC)
  >- EVAL_TAC
  >- (qexistsl [`p`, `unit`] >> simp[]) >>
  TRY (simp[build_compile_env_unit_def, LET_THM] >> NO_TAC) >>
  TRY (simp[linked_body_calls_resolved_def, ALOOKUP_def, AllCaseEqs()] >>
       rpt strip_tac >> gvs[] >> NO_TAC) >>
  TRY (simp[cenv_module_pins_mods_def, build_compile_env_unit_def, LET_THM] >> NO_TAC) >>
  TRY (simp[acyclic_struct_metadata_def, build_compile_env_unit_def, LET_THM] >>
       EVAL_TAC >> NO_TAC) >>
  rpt strip_tac >> gvs[ALOOKUP_def, AllCaseEqs(),
    immutable_section_layout_mods_def, immutable_region_mods_def, imm_len_mods_def,
    build_compile_env_unit_def, LET_THM] >> EVAL_TAC
QED
