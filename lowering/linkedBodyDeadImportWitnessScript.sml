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

Triviality dead_import_immutable_layout:
  ce.ce_module_vars = add_immutable_locations_unit
    (get_struct_fields (make_struct_fields_map_mods ^dead_mods)) ^dead_mods
    (add_module_var_locations_mods ^dead_mods FEMPTY) ==>
  immutable_section_layout_mods ^dead_mods ce
Proof
  `!src name off size. ~immutable_region_mods ^dead_mods src name off size` by
    (PURE_REWRITE_TAC[immutable_region_mods_def] >> rpt strip_tac >>
     rename1 `tops = pre ++ VariableDecl vis Immutable name vty slot :: post` >>
     `MEM (VariableDecl vis Immutable name vty slot) tops` by simp[] >>
     qpat_x_assum `tops = pre ++ _ :: post` kall_tac >>
     Cases_on `src = NONE` >> gvs[ALOOKUP_def] >>
     Cases_on `src = SOME 1` >> gvs[ALOOKUP_def]) >>
  strip_tac >>
  `ce.ce_module_vars = FEMPTY` by (simp[] >> EVAL_TAC) >>
  `imm_len_mods ^dead_mods = 0` by (simp[imm_len_mods_def] >> EVAL_TAC) >>
  simp[immutable_section_layout_mods_def]
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
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `src = NONE` >> gvs[ALOOKUP_def] >- EVAL_TAC >>
      Cases_on `src = SOME 1` >> gvs[ALOOKUP_def] >> EVAL_TAC)
  >- EVAL_TAC
  >- (qexistsl [`p`, `unit`] >> simp[])
  >- (simp[linked_body_calls_resolved_def] >> rpt strip_tac >>
      Cases_on `src = NONE` >> gvs[ALOOKUP_def] >>
      Cases_on `src = SOME 1` >> gvs[ALOOKUP_def]) >>
  qabbrev_tac `mods = ^dead_mods` >>
  (* Reduce builder projections without evaluating the concrete metadata tables. *)
  simp_tac bool_ss [cenv_module_pins_mods_def, build_compile_env_unit_def,
    LET_THM, pairTheory.ELIM_UNCURRY, pairTheory.FST, pairTheory.SND,
    combinTheory.K_THM, compileEnvTheory.compile_env_accfupds,
    compileEnvTheory.compile_env_accessors] >>
  simp[]
  >- (`make_struct_fields_map_mods mods = FEMPTY` by
        (simp[Abbr `mods`] >> EVAL_TAC) >> simp[])
  >- (simp[Abbr `mods`] >> rpt strip_tac >>
      Cases_on `src = NONE` >> gvs[ALOOKUP_def] >>
      Cases_on `src = SOME 1` >> gvs[ALOOKUP_def] >> EVAL_TAC)
  >- (simp[Abbr `mods`] >> rpt strip_tac >>
      Cases_on `src = NONE` >> gvs[ALOOKUP_def] >>
      Cases_on `src = SOME 1` >> gvs[ALOOKUP_def]) >>
  unabbrev_all_tac >>
  irule dead_import_immutable_layout >> simp[]
QED
