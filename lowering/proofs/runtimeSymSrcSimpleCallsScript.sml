Theory runtimeSymSrcSimpleCalls
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission runtimeSymSrcInterfaces
  exprLowering compileEnv emitHelper loweringShapeDefs list venomInst stackPlanTypes
  supportedExprs supportedExprTraverse runtimeSymSrcOpenValues
  runtimeSymSrcContext runtimeSymSrcContextComplete runtimeSymSrcOpenLists
  exprOracleStorageInterfaces
  builtinSystem

Theorem runtime_sym_call_lower_argument:
  runtime_sym_lower_value_clause tops /\ runtime_sym_env tops ce /\
  EVERY (supported_pure_expr tops) args /\
  ~supported_exprs_exists is_self_code args /\
  (!e t. MEM e args ==> runtime_sym_expr_contract tops cfn ce t e) ==>
  !e t s op s'. MEM e args /\ EVERY runtime_sym_inst (state_insts s) /\
    lower_value cfn ce t e s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[runtime_sym_lower_value_clause_def, supported_exprs_exists_not_every,
       EVERY_MEM, supported_expr_def] >> metis_tac[]
QED

Theorem runtime_sym_call_invalid:
  EVERY runtime_sym_inst (state_insts s) /\ emit_inst INVALID [] [] s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> irule runtime_sym_emit_inst >>
  goal_assum (drule_at Any) >> qexists `s.cs_next_id` >>
  simp[runtime_sym_inst_def, mk_inst_def]
QED

fun call_argument_tac pat =
  first_assum (drule_at_then (Pat pat) mp_tac) >> simp[] >> strip_tac;

fun lower_argument_tac pat =
  qpat_assum pat (fn step =>
    let
      val (lhs,rhs) = dest_eq (concl step)
      val (_,[_,_,ty,expr,state]) = strip_comb lhs
      val (operand,state') = pairSyntax.dest_pair rhs
    in
      qpat_assum `!e t st op st'. _ ==> _`
        (mp_tac o SPECL [expr,ty,state,operand,state']) >>
      simp[] >> strip_tac
    end);

val call_invalid_tac =
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_all runtime_sym_call_invalid >> simp[runtime_sym_value_def, is_label_operand_def];

Theorem runtime_sym_log_topics[local]:
  supported_pure_expr tops topics /\ ~supported_expr_exists is_self_code topics ==>
  EVERY (supported_pure_expr tops) (raw_log_topic_exprs topics) /\
  ~supported_exprs_exists is_self_code (raw_log_topic_exprs topics)
Proof
  Cases_on `topics` >> simp[raw_log_topic_exprs_def, supported_expr_exists_def] >>
  rename1 `Builtin ann bi es` >> Cases_on `bi` >>
  simp[raw_log_topic_exprs_def, supported_expr_exists_def,
       supported_pure_expr_def, supported_pure_exprs_every]
QED

Theorem runtime_sym_emit_log[local]:
  EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) /\ emit_inst LOG ops [] s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> irule runtime_sym_emit_inst >>
  goal_assum (drule_at Any) >> qexists `0` >> simp[] >>
  irule runtime_sym_labeled_inst >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem runtime_sym_call_log:
  !cfn ce rt ty es default s v s'.
    (!e t. MEM e es \/ default = SOME e ==>
           runtime_sym_expr_contract tops cfn ce t e) /\
    (!topics data e t. es = [topics;data] /\ MEM e (raw_log_topic_exprs topics) ==>
       runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env tops ce /\ supported_expr tops (Call rt RawLog es default) /\
    ~supported_expr_exists is_self_code (Call rt RawLog es default) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_call cfn ce rt (ty : type) RawLog es default s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (supported_pure_expr tops) es` by
    (Cases_on `default` >> fs[supported_expr_def, supported_pure_expr_def,
      supported_effect_expr_def, supported_pure_exprs_every]) >>
  `~supported_exprs_exists is_self_code es` by fs[supported_expr_exists_def] >>
  `runtime_sym_lower_value_clause tops` by
    (irule runtime_sym_lower_value >> metis_tac[runtime_sym_unwrap_value]) >>
  `!e t st op st'. MEM e es /\ EVERY runtime_sym_inst (state_insts st) /\
     lower_value cfn ce t e st = (op,st') ==>
     EVERY runtime_sym_inst (state_insts st') /\ ~is_label_operand op` by
    (mp_tac (Q.INST [`args` |-> `es`] runtime_sym_call_lower_argument) >>
     simp[] >> metis_tac[]) >>
  drule runtime_sym_multi_exprs >>
  pure_rewrite_tac[runtime_sym_multi_exprs_clause_def] >> disch_tac >>
  qpat_x_assum `compile_call _ _ _ _ _ _ _ _ = _` mp_tac >>
  namedCases_on `es` ["", "topics args_after_topics"] >>
  TRY (namedCases_on `args_after_topics` ["", "data excess"]) >>
  TRY (Cases_on `excess`) >>
  simp[NoAsms, compile_call_def] >> TRY call_invalid_tac >>
  pairarg_tac >> simp[] >>
  `EVERY (supported_pure_expr tops) (raw_log_topic_exprs topics) /\
   ~supported_exprs_exists is_self_code (raw_log_topic_exprs topics)` by
    (irule runtime_sym_log_topics >> gvs[supported_expr_exists_def]) >>
  qpat_x_assum `!cfn ce es s ops s'. _`
    (drule_at (Pat `compile_multi_exprs _ _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  IF_CASES_TAC >> rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  simp[runtime_sym_value_def, is_label_operand_def]
  >- (qpat_assum `compile_alloc_buffer _ _ = _`
        (mp_then Any mp_tac runtime_sym_alloc_buffer) >> simp[] >> strip_tac >>
      lower_argument_tac `lower_value _ _ _ data _ = _` >>
      qpat_assum `emit_void MSTORE _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_void_result) >> simp[] >> strip_tac >>
      drule_at (Pat `emit_inst LOG _ _ _ = _`) runtime_sym_emit_log >>
      simp[EVERY_APPEND, rich_listTheory.EVERY_REVERSE, is_label_operand_def]) >>
  lower_argument_tac `lower_value _ _ _ data _ = _` >>
  qpat_assum `emit_op MLOAD _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op_result) >> simp[] >> strip_tac >>
  qpat_assum `emit_op ADD _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op_result) >>
  simp[is_label_operand_def] >> strip_tac >>
  drule_at (Pat `emit_inst LOG _ _ _ = _`) runtime_sym_emit_log >>
  simp[EVERY_APPEND, rich_listTheory.EVERY_REVERSE, is_label_operand_def]
QED

Theorem runtime_sym_call_revert:
  !cfn ce rt ty es default s v s'.
    (!e t. MEM e es \/ default = SOME e ==>
           runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env tops ce /\ supported_expr tops (Call rt RawRevert es default) /\
    ~supported_expr_exists is_self_code (Call rt RawRevert es default) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_call cfn ce rt (ty : type) RawRevert es default s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (supported_pure_expr tops) es` by
    (Cases_on `default` >> fs[supported_expr_def, supported_pure_expr_def,
      supported_effect_expr_def, supported_pure_exprs_every]) >>
  `~supported_exprs_exists is_self_code es` by fs[supported_expr_exists_def] >>
  `!e t st op st'. MEM e es /\ EVERY runtime_sym_inst (state_insts st) /\
     lower_value cfn ce t e st = (op,st') ==>
     EVERY runtime_sym_inst (state_insts st') /\ ~is_label_operand op` by
    (mp_tac (Q.INST [`args` |-> `es`] runtime_sym_call_lower_argument) >>
     `runtime_sym_lower_value_clause tops` by
       (irule runtime_sym_lower_value >> metis_tac[runtime_sym_unwrap_value]) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `compile_call _ _ _ _ _ _ _ _ = _` mp_tac >>
  namedCases_on `es` ["", "arg rest"] >> TRY (Cases_on `rest`) >>
  simp[NoAsms, compile_call_def, compile_raw_revert_def, comp_bind_def]
  >- call_invalid_tac
  >- (ntac 4 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      simp[runtime_sym_value_def, is_label_operand_def] >>
      call_argument_tac `lower_value _ _ _ _ _ = _` >>
      qpat_assum `emit_op MLOAD _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
      qpat_x_assum `_ (emit_op ADD _ _) = _` mp_tac >>
      pairarg_tac >> simp[] >> strip_tac >>
      qpat_assum `emit_op ADD _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >>
      simp[is_label_operand_def] >> strip_tac >>
      qpat_assum `emit_inst REVERT _ _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_inst) >>
      disch_then (qspec_then `0` mp_tac) >> simp[] >>
      disch_then irule >> irule runtime_sym_labeled_inst >> simp[]) >>
  call_invalid_tac
QED

Theorem runtime_sym_call_selfdestruct:
  !cfn ce rt ty es default s v s'.
    (!e t. MEM e es \/ default = SOME e ==>
           runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env tops ce /\ supported_expr tops (Call rt SelfDestructTarget es default) /\
    ~supported_expr_exists is_self_code (Call rt SelfDestructTarget es default) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_call cfn ce rt (ty : type) SelfDestructTarget es default s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (supported_pure_expr tops) es` by
    (Cases_on `default` >> fs[supported_expr_def, supported_pure_expr_def,
      supported_effect_expr_def, supported_pure_exprs_every]) >>
  `~supported_exprs_exists is_self_code es` by fs[supported_expr_exists_def] >>
  `!e t st op st'. MEM e es /\ EVERY runtime_sym_inst (state_insts st) /\
     lower_value cfn ce t e st = (op,st') ==>
     EVERY runtime_sym_inst (state_insts st') /\ ~is_label_operand op` by
    (mp_tac (Q.INST [`args` |-> `es`] runtime_sym_call_lower_argument) >>
     `runtime_sym_lower_value_clause tops` by
       (irule runtime_sym_lower_value >> metis_tac[runtime_sym_unwrap_value]) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `compile_call _ _ _ _ _ _ _ _ = _` mp_tac >>
  namedCases_on `es` ["", "arg rest"] >> TRY (Cases_on `rest`) >>
  simp[NoAsms, compile_call_def, compile_selfdestruct_def, comp_bind_def]
  >- call_invalid_tac
  >- (ntac 2 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      simp[runtime_sym_value_def, is_label_operand_def] >>
      call_argument_tac `lower_value _ _ _ _ _ = _` >>
  qpat_assum `emit_void _ _ _ = _` (mp_then Any mp_tac runtime_sym_emit_void) >>
  simp[]) >> call_invalid_tac
QED

Theorem runtime_sym_call_send:
  runtime_sym_lower_value_clause tops ==>
  !cfn ce rt ty has_gas es default s v s'.
    (!e t. MEM e es \/ default = SOME e ==>
           runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env tops ce /\ supported_expr tops (Call rt (Send has_gas) es default) /\
    ~supported_expr_exists is_self_code (Call rt (Send has_gas) es default) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_call cfn ce rt (ty : type) (Send has_gas) es default s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `EVERY (supported_pure_expr tops) es` by
    (qpat_x_assum `supported_expr tops _` mp_tac >>
     Cases_on `rt` >> Cases_on `default` >> Cases_on `has_gas` >>
     Cases_on `es` >> simp[supported_expr_def, supported_pure_expr_def,
                           supported_effect_expr_def, supported_pure_exprs_every] >>
     rename1 `addr::rest` >> Cases_on `rest` >>
     simp[supported_effect_expr_def, supported_pure_expr_def] >>
     rename1 `addr::amount::rest` >> Cases_on `rest` >>
     simp[supported_effect_expr_def, supported_pure_expr_def] >>
     rename1 `addr::amount::gas::rest` >> Cases_on `rest` >>
     simp[supported_effect_expr_def, supported_pure_expr_def]) >>
  `~supported_exprs_exists is_self_code es` by fs[supported_expr_exists_def] >>
  `!e t st op st'. MEM e es /\ EVERY runtime_sym_inst (state_insts st) /\
     lower_value cfn ce t e st = (op,st') ==>
     EVERY runtime_sym_inst (state_insts st') /\ ~is_label_operand op` by
    (mp_tac (Q.INST [`args` |-> `es`] runtime_sym_call_lower_argument) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `compile_call _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `has_gas` >>
  namedCases_on `es` ["", "addr tail"] >>
  TRY (namedCases_on `tail` ["", "amount gas_args"]) >>
  TRY (namedCases_on `gas_args` ["", "gas rest"]) >>
  TRY (Cases_on `rest`) >> simp[NoAsms, compile_call_def] >>
  TRY call_invalid_tac >>
  ntac 4 (pairarg_tac >> simp[]) >>
  TRY (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  simp[runtime_sym_value_def, is_label_operand_def] >>
  lower_argument_tac `lower_value _ _ _ addr _ = _` >>
  lower_argument_tac `lower_value _ _ _ amount _ = _` >>
  TRY (lower_argument_tac `lower_value _ _ _ gas _ = _`) >>
  qpat_assum `emit_op _ _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_void _ _ _ = _` (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]
QED
