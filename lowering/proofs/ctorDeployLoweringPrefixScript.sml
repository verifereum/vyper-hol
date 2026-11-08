(* Constructor deployment failure before entry to the source body. *)
Theory ctorDeployLoweringPrefix
Ancestors
  ctorDeployLoweringDefs o1PassContract vyperTypeContractSoundness
  vyperContext e2eDefs vyperInterpreter ctorDeployLoweringCode ctorDeployInitcode deployUnitProducers ctorDeployShape

Theorem deploy_prefix_short_parse:
  parse_code 0 FEMPTY [91w;96w;32w] =
    FEMPTY |+ (0, JumpDest) |+ (1, Push 1 [32w])
Proof
  simp[Once vfmContextTheory.parse_code_def, vfmOperationTheory.parse_opcode_cond_thm,
       vfmOperationTheory.opcode_def, wordsTheory.dimword_8] >>
  simp[Once vfmContextTheory.parse_code_def, vfmOperationTheory.parse_opcode_cond_thm,
       vfmOperationTheory.opcode_def, wordsTheory.dimword_8] >>
  simp[Once vfmContextTheory.parse_code_def] >> EVAL_TAC
QED

val prefix_parse_unfold_tac = CONV_TAC
  (LAND_CONV (ONCE_REWRITE_CONV [vfmContextTheory.parse_code_def]));
val prefix_parse_reduce_tac = CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss())
  [vfmOperationTheory.parse_opcode_cond_thm,
   vfmOperationTheory.opcode_def, wordsTheory.dimword_8]));
val prefix_parse_let_tac = CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss())
  [LET_THM, vfmOperationTheory.opcode_def, wordsTheory.dimword_8]));

Theorem deploy_prefix_safe_step_no_abort:
  !inst s fuel ctx a ss.
    MEM inst.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE; JMP; CODECOPY; RETURN] ==>
    step_inst fuel ctx inst s <> Abort a ss
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  simp[Once venomExecSemanticsTheory.step_inst_def] >>
  pure_once_rewrite_tac[venomExecSemanticsTheory.step_inst_base_def] >>
  asm_rewrite_tac[] >>
  simp[venomExecSemanticsTheory.exec_alloca_def,
       venomExecSemanticsTheory.exec_pure2_def,
       venomExecSemanticsTheory.exec_read1_def,
       venomExecSemanticsTheory.exec_write2_def, LET_THM] >>
  simp[AllCaseEqs()]
QED

Theorem deploy_prefix_safe_exec_no_abort:
  !bb s fuel ctx a ss.
    EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE; JMP; CODECOPY; RETURN])
      bb.bb_instructions ==> exec_block fuel ctx bb s <> Abort a ss
Proof
  rpt gen_tac >> qid_spec_tac `s` >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt gen_tac >> disch_tac >> disch_tac >>
  simp[Once venomExecSemanticsTheory.exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >- simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `MEM inst bb.bb_instructions /\ s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (gvs[venomInstTheory.get_instruction_def] >> simp[listTheory.EL_MEM]) >>
  `MEM inst.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE; JMP; CODECOPY; RETURN]` by
    (qpat_x_assum `EVERY _ _` mp_tac >>
     rewrite_tac[listTheory.EVERY_MEM] >>
     disch_then (qspec_then `inst` mp_tac) >> simp[]) >>
  Cases_on `step_inst fuel ctx inst s` >> simp[]
  >- (Cases_on `is_terminator inst.inst_opcode` >- (Cases_on `v'.vs_halted` >> simp[]) >>
      simp[] >> first_x_assum irule >> simp[])
  >> qpat_x_assum `!y. _` kall_tac >>
  drule_all deploy_prefix_safe_step_no_abort >> metis_tac[]
QED

Theorem deploy_prefix_safe_block_no_abort:
  !bb s fuel ctx a ss.
    EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE; JMP; CODECOPY; RETURN])
      bb.bb_instructions ==> run_block fuel ctx bb s <> Abort a ss
Proof
  rpt gen_tac >> disch_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    venomExecSemanticsTheory.eval_phis_ok_or_error_defs >>
  simp[venomExecSemanticsTheory.run_block_def] >>
  irule deploy_prefix_safe_exec_no_abort >> simp[]
QED

Theorem deploy_prefix_lookup_block_mem[local]:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  Induct_on `bbs` >> simp[venomInstTheory.lookup_block_def, listTheory.FIND_thm] >>
  rw[] >> disj2_tac >> first_x_assum irule >>
  fs[venomInstTheory.lookup_block_def] >> metis_tac[]
QED

Theorem deploy_prefix_safe_blocks_no_abort:
  !fuel fn s ctx a ss.
    EVERY (\bb. EVERY (\i.
      MEM i.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE; JMP; CODECOPY; RETURN])
      bb.bb_instructions) fn.fn_blocks ==>
    run_blocks fuel ctx fn s <> Abort a ss
Proof
  Induct_on `fuel` >- simp[Once venomExecSemanticsTheory.run_blocks_def] >>
  rpt gen_tac >> disch_tac >>
  simp[venomExecSemanticsTheory.run_blocks_unfold] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >- simp[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[deploy_prefix_lookup_block_mem] >>
  `EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE; JMP; CODECOPY; RETURN])
    bb.bb_instructions` by
    (qpat_x_assum `EVERY _ _` mp_tac >> rewrite_tac[listTheory.EVERY_MEM] >>
     disch_then (qspec_then `bb` mp_tac) >> simp[]) >>
  Cases_on `run_block fuel ctx bb s` >> simp[]
  >- (Cases_on `v.vs_halted` >> simp[] >> first_x_assum irule >> simp[])
  >> drule_all deploy_prefix_safe_block_no_abort >> metis_tac[]
QED

Theorem deploy_prefix_singleton_type_env:
  type_env_all_modules [(NONE,tops)] = type_env tops
Proof
  simp[type_env_all_modules_def, type_env_def]
QED

Theorem deploy_prefix_constructor_binding:
  deploy_state_rel tops deploy_bc am tx es ==>
  ?mut args body env.
    lookup_function NONE tx.function_name Deploy tops =
      SOME (mut,F,args,[],NoneT,body) /\
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env_all_modules [(NONE,tops)]) args tx.args = SOME env
Proof
  simp[e2eDeployDefsTheory.deploy_state_rel_def,
       e2eDeployDefsTheory.constructor_args_encode_def,
       deploy_prefix_singleton_type_env] >>
  rpt strip_tac >> gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]
QED

Theorem deploy_prefix_constants_ready:
  e2eDeployDefs$deploy_typing_ok tops am tx ==>
  ?imms am_c.
    initial_immutables (type_env_all_modules [(NONE,tops)]) [(NONE,tops)] = SOME imms /\
    evaluate_all_constants (deploy_evaluation_context tops am tx)
      (am with <| immutables updated_by CONS (tx.target,imms);
                  exports updated_by CONS (tx.target,[]) |>)
      tx.target [(NONE,tops)] = SOME am_c /\
    am_c.accounts = am.accounts
Proof
  strip_tac >> gvs[e2eDeployDefsTheory.deploy_typing_ok_def] >>
  drule vyperTypeEntryReadinessTheory.checked_deployment_constants_ready_setup >>
  strip_tac >>
  drule vyperTypeEntryReadinessTheory.evaluate_all_constants_preserves_accounts >>
  simp[] >> metis_tac[]
QED

Theorem deploy_prefix_constants_transfer_ready:
  evaluate_all_constants (deploy_evaluation_context tops am tx)
    (am with <| immutables updated_by CONS (tx.target,imms);
                exports updated_by CONS (tx.target,[]) |>)
    tx.target [(NONE,tops)] = SOME am_c /\
  deploy_state_rel tops deploy_bc am tx es ==>
  value_transfer_ok tx am_c.accounts
Proof
  strip_tac >>
  drule vyperTypeEntryReadinessTheory.evaluate_all_constants_preserves_accounts >>
  simp[] >> strip_tac >>
  gvs[e2eDeployDefsTheory.deploy_state_rel_def]
QED

Theorem deploy_prefix_send_value_ready:
  value_transfer_ok cx.txn st.accounts /\
  (cx.txn.value = 0 \/ mut = Payable) ==>
  send_call_value mut cx st =
    (INL (), st with accounts := accounts_after_transfer cx.txn st.accounts)
Proof
  rw[send_call_value_def, e2eDefsTheory.value_transfer_ok_def,
     e2eDefsTheory.accounts_after_transfer_def,
     vyperStateTheory.return_def, vyperStateTheory.bind_def,
     vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
     vyperStateTheory.assert_def, transfer_value_def,
     vyperStateTheory.get_accounts_def, vyperStateTheory.update_accounts_def] >>
  gvs[vyperStateTheory.evaluation_state_component_equality]
QED

Theorem deploy_prefix_start_ready:
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  (tx.value = 0 \/ !mut args body.
    lookup_function NONE tx.function_name Deploy tops =
      SOME (mut,F,args,[],NoneT,body) ==> mut = Payable) ==>
  ?mut body am_c es0. deploy_ctor_start tops am tx (mut,F,body,am_c,es0)
Proof
  strip_tac >>
  drule deploy_prefix_constructor_binding >> strip_tac >>
  `e2eDeployDefs$deploy_typing_ok tops am tx` by fs[ctorDeployDefsTheory.deploy_source_ok_def] >>
  drule deploy_prefix_constants_ready >> strip_tac >>
  drule_all deploy_prefix_constants_transfer_ready >> strip_tac >>
  `tx.value = 0 \/ mut = Payable` by metis_tac[] >>
  rename1 `lookup_function NONE _ Deploy tops = SOME (mut,F,args,[],NoneT,ctor_body)` >>
  pure_rewrite_tac[deploy_ctor_start_def] >>
  qexistsl [`mut`, `ctor_body`, `am_c`] >>
  qexists `initial_state am_c [env] with <| outcomes := NONE; requests := [];
    accounts := accounts_after_transfer tx am_c.accounts |>` >>
  qexistsl [`args`, `env`, `imms`] >> simp[] >>
  rewrite_tac[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def] >>
  dep_rewrite.DEP_REWRITE_TAC[deploy_prefix_send_value_ready] >>
  simp[e2eDeployDefsTheory.deploy_evaluation_context_def,
       initial_evaluation_context_def, initial_state_def,
       vyperStateTheory.return_def] >> gvs[]
QED

Theorem deploy_prefix_no_start_nonpayable:
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  (!mut nr body am_c es0.
    ~deploy_ctor_start tops am tx (mut,nr,body,am_c,es0)) ==>
  ?mut args body.
    lookup_function NONE "__init__" Deploy tops =
      SOME (mut,F,args,[],NoneT,body) /\
    mut <> Payable /\ tx.value <> 0
Proof
  rpt strip_tac >>
  `tx.value <> 0` by metis_tac[deploy_prefix_start_ready] >>
  `?mut args body.
     lookup_function NONE tx.function_name Deploy tops =
       SOME (mut,F,args,[],NoneT,body) /\ mut <> Payable` by
    metis_tac[deploy_prefix_start_ready] >>
  `tx.function_name = "__init__"` by
    fs[e2eDeployDefsTheory.deploy_state_rel_def] >>
  metis_tac[]
QED

Theorem deploy_prefix_nonpayable_source_error:
  !tops am tx deploy_bc es mut args body gobs.
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  vyperInterpreter$lookup_function NONE "__init__" Deploy tops =
    SOME (mut,F,args,[],NoneT,body) /\
  mut <> Payable /\ tx.value <> 0 ==>
  load_contract NONE gobs am tx [(NONE,tops)] [] =
    INR (Error (RuntimeError "not Payable"))
Proof
  rpt gen_tac >> strip_tac >>
  `e2eDeployDefs$deploy_typing_ok tops am tx` by
    fs[ctorDeployDefsTheory.deploy_source_ok_def] >>
  drule deploy_prefix_constants_ready >> strip_tac >>
  `tx.function_name = "__init__"` by
    fs[e2eDeployDefsTheory.deploy_state_rel_def] >>
  `LENGTH tx.args = LENGTH args` by
    (drule deploy_prefix_constructor_binding >> strip_tac >> gvs[]) >>
  simp[load_contract_def, GSYM e2eDeployDefsTheory.deploy_evaluation_context_def] >>
  `deploy_evaluation_context tops
     (am with <|exports updated_by CONS (tx.target,[]);
                immutables updated_by CONS (tx.target,imms)|>) tx =
   deploy_evaluation_context tops am tx` by
    simp[e2eDeployDefsTheory.deploy_evaluation_context_def] >>
  simp[call_external_function_def] >>
  simp[send_call_value_def, e2eDeployDefsTheory.deploy_evaluation_context_def,
       initial_evaluation_context_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.bind_def, vyperStateTheory.check_def,
       vyperStateTheory.assert_def, vyperStateTheory.raise_def] >>
  gvs[e2eDeployDefsTheory.deploy_evaluation_context_def,
      initial_evaluation_context_def]
QED

Theorem deploy_prefix_packaged_payable:
  !tops rp runtime unit exts ints fb cf mut args body ce pa pay nr key ut ss ret.
  lower_vyper_deploy_unit tops rp runtime = SOME unit /\
  classify_functions tops = (exts,ints,fb,SOME cf) /\
  vyperInterpreter$lookup_function NONE "__init__" Deploy tops =
    SOME (mut,F,args,[],NoneT,body) /\
  set_constructor_package_target rp.rpol_target
    (package_constructor tops F (assign_nkeys tops 0) cf) =
    (ce,pa,pay,nr,key,ut,ss,ret) ==>
  pay = (mut = Payable)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compileVyperTheory.lower_vyper_deploy_unit_ctor_named_init >>
  strip_tac >> PairCases_on `cf` >>
  gvs[compileVyperTheory.ctor_named_init_def] >>
  qspecl_then [`tops`, `NONE`, `"__init__"`] mp_tac
    ctorDeployInitcodeTheory.classify_functions_ctor_lookup >>
  simp[] >> strip_tac >>
  gvs[compileVyperTheory.package_constructor_def,
      compileVyperTheory.set_constructor_package_target_def]
QED

Theorem deploy_prefix_after_guard_extends:
  !cap cenv args nr key trans st_pay imm st1 ce st2 st3 lbl sa.
  (if cap > 0 then
     comp_bind (compile_fixed_region_with_id cap)
       (\p. comp_return (SND p).buf_operand)
   else comp_return (Lit 0w)) st_pay = (imm,st1) /\
  compile_register_constructor_args
    (cenv with ce_imm_alloca := (if cap > 0 then SOME imm else NONE))
    args 0 0 st1 = (ce,st2) /\
  (if nr then compile_nonreentrant_lock key trans F else comp_return ()) st2 = ((),st3) /\
  fresh_label "ctor_exit" st3 = (lbl,sa) ==>
  cs_extends st_pay sa
Proof
  rpt gen_tac >> strip_tac >>
  qspec_then `T` mp_tac ctorDeployLoweringCodeShapeTheory.ctor_code_setup_extension >>
  simp[compileEnvTheory.comp_return_def] >>
  disch_then irule >> rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem deploy_prefix_guard_fields:
  comp_bind (emit_op CALLVALUE [])
    (\cv. comp_bind (emit_op ISZERO [cv]) (\v. emit_void ASSERT [v]))
    (initial_compile_state "__deploy") = ((),st) ==>
  st.cs_current_bb = "__deploy" /\
  st.cs_current_insts =
    [<|inst_id := 0; inst_opcode := CALLVALUE; inst_operands := []; inst_outputs := ["%0"]|>;
     <|inst_id := 1; inst_opcode := ISZERO; inst_operands := [Var "%0"]; inst_outputs := ["%1"]|>;
     <|inst_id := 2; inst_opcode := ASSERT; inst_operands := [Var "%1"]; inst_outputs := []|>]
Proof
  EVAL_TAC >> strip_tac >> gvs[]
QED

Theorem deploy_prefix_code_guard:
  !tops rp runtime unit src ce nr key ut imm lbl sa sb sj se sp sf fn mut args body.
  deploy_ctor_code tops rp runtime unit
    (src,ce,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,fn) /\
  vyperInterpreter$lookup_function NONE "__init__" Deploy tops =
    SOME (mut,F,args,[],NoneT,body) /\ mut <> Payable ==>
  ?bb tail.
    venomInst$lookup_block "__deploy" fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
    [<|inst_id := 0; inst_opcode := CALLVALUE; inst_operands := []; inst_outputs := ["%0"]|>;
     <|inst_id := 1; inst_opcode := ISZERO; inst_operands := [Var "%0"]; inst_outputs := ["%1"]|>;
     <|inst_id := 2; inst_opcode := ASSERT; inst_operands := [Var "%1"]; inst_outputs := []|>] ++ tail
Proof
  rpt gen_tac >> simp[deploy_ctor_code_def] >> rpt strip_tac >>
  drule_all deploy_prefix_packaged_payable >> strip_tac >> gvs[] >>
  drule_all deploy_prefix_after_guard_extends >> strip_tac >>
  qpat_x_assum `((),st_pay) = _` (assume_tac o GSYM) >>
  drule deploy_prefix_guard_fields >> strip_tac >>
  `cs_extends (initial_compile_state "__deploy") st_pay` by
    (qpat_x_assum `_ = ((),st_pay)` mp_tac >> EVAL_TAC >> strip_tac >>
     gvs[compileEnvTheory.cs_extends_def]) >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  `?bb. venomInst$lookup_block st_pay.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX st_pay.cs_current_insts bb.bb_instructions` by
    metis_tac[fragExecTheory.fn_has_code_start] >>
  gvs[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]
QED

Theorem deploy_prefix_member_lookup[local]:
  !fns fn.
    ALL_DISTINCT (MAP (\f. f.fn_name) fns) /\ MEM fn fns ==>
    venomInst$lookup_function fn.fn_name fns = SOME fn
Proof
  Induct_on `fns` >> simp[venomInstTheory.lookup_function_def, listTheory.FIND_thm] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `fn.fn_name = h.fn_name`
  >- (gvs[listTheory.MEM_MAP] >>
      first_x_assum (qspec_then `fn` mp_tac) >> simp[]) >>
  gvs[] >>
  qpat_x_assum `!x. MEM x fns ==> _` (qspec_then `fn` mp_tac) >>
  simp[venomInstTheory.lookup_function_def]
QED

Theorem deploy_prefix_selected_guard:
  !tops rp runtime unit src ce nr key ut imm lbl sa sb sj se sp sf fn mut args body.
  deploy_ctor_code tops rp runtime unit
    (src,ce,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,fn) /\
  vyperInterpreter$lookup_function NONE "__init__" Deploy tops =
    SOME (mut,F,args,[],NoneT,body) /\ mut <> Payable ==>
  unit.cu_context.ctx_entry = SOME "__deploy" /\
  venomInst$lookup_function "__deploy" unit.cu_context.ctx_functions = SOME fn /\
  ?bb tail.
    venomInst$lookup_block "__deploy" fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
    [<|inst_id := 0; inst_opcode := CALLVALUE; inst_operands := []; inst_outputs := ["%0"]|>;
     <|inst_id := 1; inst_opcode := ISZERO; inst_operands := [Var "%0"]; inst_outputs := ["%1"]|>;
     <|inst_id := 2; inst_opcode := ASSERT; inst_operands := [Var "%1"]; inst_outputs := []|>] ++ tail
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_prefix_code_guard >> strip_tac >>
  fs[deploy_ctor_code_def] >>
  drule deployUnitProducersTheory.lower_vyper_deploy_unit_entry >> strip_tac >>
  drule deployUnitProducersTheory.lower_vyper_deploy_unit_context_ok >>
  simp[vyperCompilerTheory.lowering_context_ok_def, venomInstTheory.ctx_fn_names_def] >>
  strip_tac >>
  drule_all deploy_prefix_member_lookup >> simp[] >> metis_tac[]
QED

Theorem deploy_prefix_member_entry_label:
  !tops rp runtime unit fn.
  lower_vyper_deploy_unit tops rp runtime = SOME unit /\
  supported_program tops /\ MEM fn unit.cu_context.ctx_functions ==>
  fn_entry_label fn = SOME fn.fn_name
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ctorDeployShapeTheory.lower_vyper_deploy_unit_source_unit_ok >>
  simp[unitShapeDefsTheory.o1_source_unit_ok_def,
       unitShapeDefsTheory.unit_shape_ok_def,
       unitShapeDefsTheory.fn_shape_ok_def, listTheory.EVERY_MEM] >>
  metis_tac[]
QED

Theorem deploy_prefix_ctor_entry_label:
  !tops rp runtime unit src ce nr key ut imm lbl sa sb sj se sp sf fn.
  supported_program tops /\
  deploy_ctor_code tops rp runtime unit
    (src,ce,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,fn) ==>
  fn_entry_label fn = SOME "__deploy"
Proof
  rpt gen_tac >> simp[deploy_ctor_code_def] >> rpt strip_tac >>
  drule_all deploy_prefix_member_entry_label >> simp[]
QED

Theorem deploy_prefix_guard_abort:
  !bb tail s fuel ctx.
  bb.bb_instructions =
    [<|inst_id := 0; inst_opcode := CALLVALUE; inst_operands := []; inst_outputs := ["%0"]|>;
     <|inst_id := 1; inst_opcode := ISZERO; inst_operands := [Var "%0"]; inst_outputs := ["%1"]|>;
     <|inst_id := 2; inst_opcode := ASSERT; inst_operands := [Var "%1"]; inst_outputs := []|>] ++ tail /\
  s.vs_inst_idx = 0 /\ s.vs_call_ctx.cc_callvalue <> 0w ==>
  ?ss. exec_block fuel ctx bb s = Abort Revert_abort ss
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once venomExecSemanticsTheory.exec_block_def, venomInstTheory.get_instruction_def,
       venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_read0_def] >>
  simp[venomInstTheory.is_terminator_def] >>
  simp[Once venomExecSemanticsTheory.exec_block_def,
       venomInstTheory.get_instruction_def, venomStateTheory.update_var_def,
       venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure1_def,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       venomExecSemanticsTheory.bool_to_word_def] >>
  simp[finite_mapTheory.FLOOKUP_UPDATE, venomInstTheory.is_terminator_def,
       venomExecSemanticsTheory.bool_to_word_def] >>
  simp[Once venomExecSemanticsTheory.exec_block_def,
       venomInstTheory.get_instruction_def,
       venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_def,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem deploy_prefix_context_guard_abort:
  !ctx fn bb tail s.
  ctx.ctx_entry = SOME "__deploy" /\
  venomInst$lookup_function "__deploy" ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__deploy" /\
  venomInst$lookup_block "__deploy" fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [<|inst_id := 0; inst_opcode := CALLVALUE; inst_operands := []; inst_outputs := ["%0"]|>;
     <|inst_id := 1; inst_opcode := ISZERO; inst_operands := [Var "%0"]; inst_outputs := ["%1"]|>;
     <|inst_id := 2; inst_opcode := ASSERT; inst_operands := [Var "%1"]; inst_outputs := []|>] ++ tail /\
  s.vs_call_ctx.cc_callvalue <> 0w ==>
  ?ss. run_context 1 ctx s = Abort Revert_abort ss
Proof
  rpt gen_tac >> strip_tac >>
  simp[venomExecSemanticsTheory.run_context_def,
       venomExecSemanticsTheory.run_function_def,
       Once venomExecSemanticsTheory.run_blocks_def,
       venomExecSemanticsTheory.eval_phis_def,
       venomExecSemanticsTheory.phi_prefix_length_def] >>
  drule deploy_prefix_guard_abort >>
  disch_then (qspecl_then
    [`s with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>`,
     `0`, `ctx`] mp_tac) >> simp[] >> strip_tac >> simp[]
QED

Theorem deploy_prefix_entry_callvalue:
  !tops bc am tx es vs prog cp.
  deploy_source_ok tops am tx /\ deploy_state_rel tops bc am tx es /\
  gas_variant vs (deploy_entry_state prog cp tops es) /\ tx.value <> 0 ==>
  vs.vs_call_ctx.cc_callvalue <> 0w
Proof
  rpt gen_tac >> strip_tac >>
  `vs.vs_call_ctx.cc_callvalue = n2w tx.value` by
    (fs[e2eDeployDefsTheory.deploy_state_rel_def, gas_variant_def,
        ctorDeployDefsTheory.deploy_entry_state_def,
        e2eEntryTheory.entry_venom_state_def] >>
     qpat_x_assum `_ = vs with vs_gas_readings := _`
       (mp_tac o Q.AP_TERM `\s. s.vs_call_ctx.cc_callvalue`) >> simp[]) >>
  `tx.value < 2 ** 256` by
    fs[ctorDeployDefsTheory.deploy_source_ok_def,
       e2eDeployDefsTheory.deploy_typing_ok_def, call_tx_well_typed_def] >>
  fs[wordsTheory.n2w_11, wordsTheory.dimword_def, arithmeticTheory.LESS_MOD]
QED

Theorem deploy_prefix_nonpayable_target_abort:
  !policy tops deploy_bc runtime_bc rp unit dout prog cp am tx es vs
   exts ints fb cf mut args body.
  deploy_phases policy tops (deploy_bc,runtime_bc) (rp,unit,dout,prog,cp) /\
  deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cp tops es) /\
  classify_functions tops = (exts,ints,fb,SOME cf) /\
  vyperInterpreter$lookup_function NONE "__init__" Deploy tops =
    SOME (mut,F,args,[],NoneT,body) /\ mut <> Payable /\ tx.value <> 0 ==>
  ?ss. run_context 1 unit.cu_context vs = Abort Revert_abort ss
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_prefix_entry_callvalue >> strip_tac >>
  drule_all ctorDeployLoweringCodeTheory.deploy_ctor_code_exists >> strip_tac >>
  drule_all deploy_prefix_selected_guard >> strip_tac >>
  `supported_program tops` by fs[ctorDeployDefsTheory.deploy_source_ok_def] >>
  drule_all deploy_prefix_ctor_entry_label >> strip_tac >>
  irule deploy_prefix_context_guard_abort >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

(* When the source fails before the constructor body (the value transfer
   into a non-payable constructor, the reentrancy lock), so does the unit:
   its payable check and lock come first too. *)
Theorem deploy_ctor_prefix_fail:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs exts ints fb cf.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    classify_functions tops = (exts, ints, fb, SOME cf) /\
    (!mut nr body am_c es0.
       ~deploy_ctor_start tops am tx (mut, nr, body, am_c, es0)) ==>
    ?fuel. !gobs.
      deploy_venom_result_rel tops runtime_bc tx
        (load_contract NONE gobs am tx [(NONE, tops)] [])
        (run_context fuel dunit.cu_context vs)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_prefix_no_start_nonpayable >> strip_tac >>
  drule_all deploy_prefix_nonpayable_target_abort >> strip_tac >>
  qexists_tac `1` >> gen_tac >>
  drule_all deploy_prefix_nonpayable_source_error >>
  disch_then (qspec_then `gobs` assume_tac) >>
  simp[ctorDeployDefsTheory.deploy_venom_result_rel_def]
QED

Theorem deploy_ctor_prefix_source_readings:
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  (!mut nr body am_c es0.
    ~deploy_ctor_start tops am tx (mut,nr,body,am_c,es0)) ==>
  !gs gs'. load_contract NONE gs am tx [(NONE,tops)] [] =
    load_contract NONE gs' am tx [(NONE,tops)] []
Proof
  strip_tac >> drule_all deploy_prefix_no_start_nonpayable >> strip_tac >>
  metis_tac[deploy_prefix_nonpayable_source_error]
QED
