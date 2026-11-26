Theory runtimeSymSrcBuiltinBody
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission supportedTypes
  runtimeSymSrcInterfaces exprCallBounds list supportedExprTraverse exprLowering
  supportedExprs supportedExprForms context compileEnv venomInst vyperAST
  memoryValueDefs typedCopyDomain builtinMisc builtinBytes builtinSimple
  runtimeSymSrcBuiltinMisc runtimeSymSrcBuiltinByteSimple
  runtimeSymSrcBuiltinHash runtimeSymSrcBuiltinData
  builtinHashing stackPlanTypes vyperContext runtimeSymSrcContext exprCallbackContracts
  runtimeSymSrcContextCopy runtimeSymSrcBlockEmission runtimeSymSrcBoolChainOps
  boolChainOperandsGuarded

Theorem runtime_sym_builtin_child:
  (!e ty. expr_size e < list_size expr_size args ==>
     runtime_sym_expr_contract tops cfn ce ty e) /\
  EVERY (supported_pure_expr tops) args /\
  ~supported_exprs_exists is_self_code args /\ MEM e args ==>
  (!ty. runtime_sym_expr_contract tops cfn ce ty e) /\
  supported_expr tops e /\ ~supported_expr_exists is_self_code e
Proof
  rpt strip_tac
  >- (first_x_assum irule >> metis_tac[expr_list_member_bound])
  >- metis_tac[runtime_sym_supported_argument]
  >> gvs[supported_exprs_exists_every, EVERY_MEM]
QED

Theorem runtime_sym_builtin_env[local]:
  runtime_sym_generator_contracts tops ==>
  runtime_sym_builtin_contract tops (compile_builtin_dispatch_body cfn) ce rt ty (Env item) args
Proof
  strip_tac >> drule runtime_sym_generators_expr_primitive >>
  disch_then (assume_tac o cj 2 o SRULE [runtime_sym_expr_primitive_clauses_def]) >>
  pure_rewrite_tac[runtime_sym_builtin_contract_def] >> rpt strip_tac >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_builtin_dispatch_body_def, as_stack_val_def] >>
  Cases_on `compile_env_var item s` >>
  simp[NoAsms, as_stack_val_def] >> strip_tac >> gvs[] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  simp[runtime_sym_value_def]
QED
Theorem runtime_sym_builtin_lower_value:
  runtime_sym_generator_contracts tops /\
  (!e t. expr_size e < list_size expr_size args ==>
     runtime_sym_expr_contract tops cfn ce t e) /\
  runtime_sym_env tops ce /\ EVERY (supported_pure_expr tops) args /\
  ~supported_exprs_exists is_self_code args ==>
  !e t s op s'. MEM e args /\ EVERY runtime_sym_inst (state_insts s) /\
    lower_value cfn ce t e s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  strip_tac >> drule runtime_sym_generators_lower_value >>
  pure_rewrite_tac[runtime_sym_lower_value_clause_def] >> strip_tac >>
  rpt strip_tac >> drule_all runtime_sym_builtin_child >> strip_tac >>
  qpat_x_assum `!cfn ce ty e s op s'. _` (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[]
QED

Theorem runtime_sym_builtin_callback[local]:
  (!e t. expr_size e < list_size expr_size args ==>
     runtime_sym_expr_contract tops cfn ce t e) /\
  runtime_sym_env tops ce /\ EVERY (supported_pure_expr tops) args /\
  ~supported_exprs_exists is_self_code args ==>
  !e t s v s'. MEM e args /\ EVERY runtime_sym_inst (state_insts s) /\
     cfn ce t e s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all runtime_sym_builtin_child >> strip_tac >>
  qpat_x_assum `!ty. runtime_sym_expr_contract _ _ _ _ _`
    (mp_tac o Q.SPEC `t`) >>
  pure_rewrite_tac[runtime_sym_expr_contract_def] >>
  disch_then (drule_at_then (Pat `cfn _ _ _ _ = _`) mp_tac) >> simp[]
QED

val runtime_sym_unary_args_tac =
  `?a. args = [a]` by
    (namedCases_on `args` ["", "first rest"] >>
     gvs[runtime_sym_builtin_domain, supported_builtin_form_def,
         builtin_args_length_ok_def] >>
     Cases_on `rest` >> gvs[]) >>
  pop_assum SUBST_ALL_TAC >> rename1 `Builtin _ _ [a]`;

val runtime_sym_assume_lower_value_tac =
  `!e t s op s'. MEM e args /\ EVERY runtime_sym_inst (state_insts s) /\
     lower_value cfn ce t e s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op` by
    (rpt gen_tac >> strip_tac >>
     drule_all runtime_sym_builtin_lower_value >> simp[]);

fun runtime_sym_result_tac value_def wrap =
  qmatch_goalsub_abbrev_tac wrap >>
  Cases_on `output` >> simp[NoAsms, value_def] >>
  disch_then (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) >>
  qpat_x_assum `Abbrev _` (assume_tac o SYM o SRULE [markerTheory.Abbrev_def]);

val runtime_sym_stack_result_tac =
  runtime_sym_result_tac as_stack_val_def `as_stack_val _ output`;

fun runtime_sym_finish_unary_tac result_tac leaf =
  result_tac >>
  qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >> drule_all leaf >> simp[runtime_sym_value_def,mk_ptr_def];

fun runtime_sym_unary_stack_tac leaf =
  pairarg_tac >> simp[] >>
  runtime_sym_finish_unary_tac runtime_sym_stack_result_tac leaf;

fun runtime_sym_round_tac leaf =
  runtime_sym_unary_args_tac >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_builtin_dispatch_body_def] >>
  runtime_sym_unary_stack_tac leaf;

Theorem runtime_sym_builtin_floor:
  runtime_sym_generator_contracts tops /\
  (!e t. expr_size e < list_size expr_size args ==>
    runtime_sym_expr_contract tops cfn ce t e) ==>
  runtime_sym_builtin_contract tops (compile_builtin_dispatch_body cfn) ce rt ty Floor args
Proof
  strip_tac >> pure_rewrite_tac[runtime_sym_builtin_contract_def] >>
  rpt gen_tac >> strip_tac >>
  `EVERY (supported_pure_expr tops) args /\
   ~supported_exprs_exists is_self_code args` by
    gvs[runtime_sym_builtin_domain, supported_expr_exists_def] >>
  runtime_sym_assume_lower_value_tac >>
  runtime_sym_round_tac runtime_sym_floor
QED

Theorem runtime_sym_builtin_keccak:
  runtime_sym_generator_contracts tops /\
  (!e t. expr_size e < list_size expr_size args ==>
    runtime_sym_expr_contract tops cfn ce t e) ==>
  runtime_sym_builtin_contract tops (compile_builtin_dispatch_body cfn) ce rt ty Keccak256 args
Proof
  strip_tac >> pure_rewrite_tac[runtime_sym_builtin_contract_def] >>
  rpt gen_tac >> strip_tac >>
  `EVERY (supported_pure_expr tops) args /\
   ~supported_exprs_exists is_self_code args` by
    gvs[runtime_sym_builtin_domain, supported_expr_exists_def] >>
  runtime_sym_assume_lower_value_tac >>
  runtime_sym_unary_args_tac >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_builtin_dispatch_body_def] >>
  IF_CASES_TAC >> simp[NoAsms] >>
  rpt (CASE_TAC >> simp[NoAsms]) >>
  FIRST [runtime_sym_unary_stack_tac runtime_sym_keccak256_bytes,
         runtime_sym_unary_stack_tac runtime_sym_keccak256_bytesm,
         runtime_sym_unary_stack_tac runtime_sym_keccak256_word]
QED

Theorem runtime_sym_builtin_concat:
  runtime_sym_generator_contracts tops /\
  (!e t. expr_size e < list_size expr_size args ==>
    runtime_sym_expr_contract tops cfn ce t e) ==>
  runtime_sym_builtin_contract tops (compile_builtin_dispatch_body cfn) ce rt ty (Concat n) args
Proof
  strip_tac >> pure_rewrite_tac[runtime_sym_builtin_contract_def] >>
  rpt gen_tac >> strip_tac >>
  `EVERY (supported_pure_expr tops) args /\
   ~supported_exprs_exists is_self_code args` by
    gvs[runtime_sym_builtin_domain, supported_expr_exists_def] >>
  `!e t. MEM e args ==> runtime_sym_expr_contract tops cfn ce t e` by
    (rpt strip_tac >> first_x_assum irule >> metis_tac[expr_list_member_bound]) >>
  drule runtime_sym_generators_concat >>
  disch_then (strip_assume_tac o SRULE [runtime_sym_concat_clause_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  qpat_assum `compile_alloc_buffer (concat_alloc_size _) _ = _`
    (mp_then Any mp_tac runtime_sym_alloc_buffer) >> simp[] >> strip_tac >>
  qpat_assum `emit_op ADD _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op_result) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `compile_alloc_buffer 64 _ = _`
    (mp_then Any mp_tac runtime_sym_alloc_buffer) >> simp[] >> strip_tac >>
  qpat_assum `emit_void MSTORE [_; Lit 0w] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void_result) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `!cfn ce es dst infos off s s'. _`
    (drule_at (Pat `compile_concat _ _ _ _ _ _ _ = _`)) >>
  asm_rewrite_tac[] >> strip_tac >>
  qpat_assum `emit_op MLOAD _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op_result) >> simp[] >> strip_tac >>
  qpat_assum `emit_void MSTORE [_; final_offset] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void_result) >>
  simp[runtime_sym_value_def, base_ptr_def]
QED

Theorem runtime_sym_builtin_slice_address[local]:
  runtime_sym_generator_contracts tops /\
  (!e t. expr_size e < list_size expr_size args ==>
     runtime_sym_expr_contract tops cfn ce t e) /\
  runtime_sym_env tops ce /\
  supported_pure_expr tops src /\ ~supported_expr_exists is_self_code src /\
  MEM src args /\ is_extcode src /\ EVERY runtime_sym_inst (state_insts s) /\
  lower_value cfn ce ty (extcode_addr_expr src) s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  strip_tac >>
  `runtime_sym_expr_contract tops cfn ce ty (extcode_addr_expr src)` by
    (first_x_assum irule >> irule extcode_child_bound >> simp[]) >>
  fs[is_extcode_characterization] >> gvs[extcode_addr_expr_def] >>
  drule runtime_sym_generators_lower_value >>
  pure_rewrite_tac[runtime_sym_lower_value_clause_def] >>
  disch_then (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  fs[supported_expr_def, supported_pure_expr_def, supported_expr_exists_def]
QED

fun runtime_sym_lower_slice_arg_tac expr =
  qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac o
     Q.SPECL [expr, `ty`]) >> simp[] >> strip_tac;

Theorem runtime_sym_builtin_slice:
  runtime_sym_generator_contracts tops /\
  (!e t. expr_size e < list_size expr_size args ==>
    runtime_sym_expr_contract tops cfn ce t e) ==>
  runtime_sym_builtin_contract tops (compile_builtin_dispatch_body cfn) ce rt ty (Slice n) args
Proof
  strip_tac >> pure_rewrite_tac[runtime_sym_builtin_contract_def] >>
  rpt gen_tac >> strip_tac >>
  `EVERY (supported_pure_expr tops) args /\
   ~supported_exprs_exists is_self_code args` by
    gvs[runtime_sym_builtin_domain, supported_expr_exists_def] >>
  runtime_sym_assume_lower_value_tac >>
  `?src start len. args = [src;start;len]` by
    (namedCases_on `args` ["", "first tail"] >>
     TRY (namedCases_on `tail` ["", "second tail2"]) >>
     TRY (namedCases_on `tail2` ["", "third rest"]) >>
     gvs[runtime_sym_builtin_domain, supported_builtin_form_def,
         builtin_args_length_ok_def] >>
     Cases_on `rest` >> gvs[]) >>
  gvs[] >>
  rename1 `Builtin rt (Slice n) [src;start;len]` >>
  `~is_self_code src` by
    (fs[supported_expr_exists_def] >> metis_tac[supported_expr_exists_root]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_builtin_dispatch_body_def] >> simp[] >>
  Cases_on `is_extcode src` >> simp[]
  >- (ntac 3 (pairarg_tac >> simp[]) >>
      runtime_sym_result_tac as_ptr_val_def `as_ptr_val _ LocMemory output` >>
      runtime_sym_lower_slice_arg_tac `start` >>
      runtime_sym_lower_slice_arg_tac `len` >>
      `EVERY runtime_sym_inst (state_insts st3) /\ ~is_label_operand addr_op` by
        (irule runtime_sym_builtin_slice_address >>
         goal_assum (drule_at (Pat `lower_value _ _ _ (extcode_addr_expr _) _ = _`)) >>
         qexistsl [`[src;start;len]`, `tops`] >> fs[supported_expr_exists_def]) >>
      drule_all runtime_sym_slice_extcode >> simp[runtime_sym_value_def, mk_ptr_def]) >>
  pairarg_tac >> simp[] >>
  runtime_sym_lower_slice_arg_tac `src` >>
  Cases_on `is_bytestring_type (expr_type src)` >> simp[]
  >- (rpt (pairarg_tac >> simp[]) >>
      runtime_sym_result_tac as_ptr_val_def `as_ptr_val _ LocMemory output` >>
      drule_all runtime_sym_bytestring_src >> strip_tac >>
      runtime_sym_lower_slice_arg_tac `start` >>
      runtime_sym_lower_slice_arg_tac `len` >>
      drule_all runtime_sym_slice_data >> simp[runtime_sym_value_def, mk_ptr_def]) >>
  rpt (pairarg_tac >> simp[]) >>
  runtime_sym_result_tac as_ptr_val_def `as_ptr_val _ LocMemory output` >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  qpat_assum `emit_void MSTORE _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void_result) >> simp[] >> strip_tac >>
  runtime_sym_lower_slice_arg_tac `start` >>
  runtime_sym_lower_slice_arg_tac `len` >>
  drule_at (Pat `compile_slice_data _ _ _ _ _ _ = _`) runtime_sym_slice_data >>
  simp[runtime_sym_value_def, mk_ptr_def, is_label_operand_def]
QED

Theorem runtime_sym_bytestring_hash[local]:
  ~is_label_operand p /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_bytestring_hash p s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_bytestring_hash_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  qpat_assum `emit_op ADD _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op_result) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_op MLOAD _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op_result) >> simp[] >> strip_tac >>
  qpat_assum `emit_op SHA3 _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op_result) >> simp[]
QED

Theorem runtime_sym_bytestring_hash_arg[local]:
  (case bytestring_literal_hash e of
     SOME h => (Lit h,s)
   | NONE => (\(p,st). compile_bytestring_hash p st)
               (lower_value cfn ce (ety:type) e s)) = (v,s') ==>
  (!st op st'. EVERY runtime_sym_inst (state_insts st) /\
    lower_value cfn ce ety e st = (op,st') ==>
    EVERY runtime_sym_inst (state_insts st') /\ ~is_label_operand op) /\
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `bytestring_literal_hash e` >> simp[]
  >- (Cases_on `lower_value cfn ce ety e s` >> simp[] >> ntac 2 strip_tac >>
      first_x_assum (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
      simp[] >> strip_tac >> drule_all runtime_sym_bytestring_hash >> simp[]) >>
  ntac 2 strip_tac >> gvs[is_label_operand_def]
QED

Theorem runtime_sym_bytestring_compare[local]:
  (!e t st op st'. MEM e [a;b] /\ EVERY runtime_sym_inst (state_insts st) /\
    lower_value cfn ce t e st = (op,st') ==>
    EVERY runtime_sym_inst (state_insts st') /\ ~is_label_operand op) /\
  is_bytestring_type (expr_type a) /\ (bop = Eq \/ bop = NotEq) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_builtin_dispatch_body cfn ce rt ty (Bop bop) [a;b] s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `EVERY runtime_sym_inst (state_insts st2) /\ ~is_label_operand h1` by
    (irule (SRULE [] runtime_sym_bytestring_hash_arg) >>
     qexistsl [`ce`, `cfn`, `a`, `expr_type a`, `s`] >>
     simp[] >> rpt gen_tac >>
     qpat_assum `!e t st op st'. _ ==> _`
       (mp_tac o Q.SPECL [`a`, `expr_type a`, `st`, `op`, `st'`]) >>
     simp[]) >>
  `EVERY runtime_sym_inst (state_insts st4) /\ ~is_label_operand h2` by
    (irule (SRULE [] runtime_sym_bytestring_hash_arg) >>
     qexistsl [`ce`, `cfn`, `b`, `expr_type a`, `st2`] >>
     simp[] >> rpt gen_tac >>
     qpat_assum `!e t st op st'. _ ==> _`
       (mp_tac o Q.SPECL [`b`, `expr_type a`, `st`, `op`, `st'`]) >>
     simp[])
  >- (runtime_sym_stack_result_tac >>
      qpat_assum `emit_op EQ _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op_result) >>
      simp[runtime_sym_value_def]) >>
  pairarg_tac >> simp[] >> runtime_sym_stack_result_tac >>
  qpat_assum `emit_op EQ _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op_result) >>
  simp[] >> strip_tac >>
  qpat_assum `emit_op ISZERO _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op_result) >>
  simp[runtime_sym_value_def]
QED

Theorem runtime_sym_membership_eqs[local]:
  !elems s cs s'. ~is_label_operand needle /\ EVERY (\op. ~is_label_operand op) elems /\
    EVERY runtime_sym_inst (state_insts s) /\ emit_membership_eqs needle elems s = (cs,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ EVERY (\op. ~is_label_operand op) cs
Proof
  Induct >> simp[emit_membership_eqs_def, comp_return_def, comp_bind_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  qpat_assum `emit_op EQ _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op_result) >>
  simp[] >> strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem runtime_sym_membership_or[local]:
  !cs acc s v s'. ~is_label_operand acc /\ EVERY (\op. ~is_label_operand op) cs /\
    EVERY runtime_sym_inst (state_insts s) /\ fold_membership_or acc cs s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Induct >> simp[fold_membership_or_def, comp_return_def, comp_bind_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac >>
  qpat_assum `emit_op OR _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op_result) >>
  simp[] >> strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem runtime_sym_membership_and[local]:
  !cs acc s v s'. ~is_label_operand acc /\ EVERY (\op. ~is_label_operand op) cs /\
    EVERY runtime_sym_inst (state_insts s) /\ fold_membership_and acc cs s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Induct >> simp[fold_membership_and_def, comp_return_def, comp_bind_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> simp[]) >> strip_tac >>
  qpat_assum `emit_op ISZERO _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op_result) >>
  simp[] >> strip_tac >>
  qpat_assum `emit_op AND _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op_result) >>
  simp[] >> strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem runtime_sym_list_membership[local]:
  ~is_label_operand needle /\ EVERY (\op. ~is_label_operand op) elems /\
  EVERY runtime_sym_inst (state_insts s) /\
  (if is_in then compile_list_membership_in needle elems
   else compile_list_membership_notin needle elems) s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `is_in` >>
  simp[compile_list_membership_in_def, compile_list_membership_notin_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule_all runtime_sym_membership_eqs >> strip_tac >>
  rename1 `emit_membership_eqs needle elems s = (cs,st)` >>
  Cases_on `cs` >> gvs[comp_return_def, is_label_operand_def, comp_bind_def]
  >- (drule_all runtime_sym_membership_or >> simp[]) >>
  qpat_x_assum `_ (emit_op ISZERO _ _) = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_assum `emit_op ISZERO _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op_result) >>
  simp[] >> strip_tac >> drule_all runtime_sym_membership_and >> simp[]
QED

fun runtime_sym_membership_step_tac pat theorem =
  qpat_assum pat (mp_then Any mp_tac theorem) >>
  simp[is_label_operand_def] >> strip_tac;

Theorem runtime_sym_membership_bound[local]:
  ~is_label_operand len /\ EVERY runtime_sym_inst (state_insts s) /\
  (case bound of
     SOME cap => do inv <- emit_op GT [len; Lit (n2w cap)];
                    valid <- emit_op ISZERO [inv];
                    emit_inst ASSERT [valid] []
                 od
   | NONE => return ()) s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `bound` >> simp[comp_return_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  runtime_sym_membership_step_tac `emit_op GT _ _ = _` runtime_sym_emit_op_result >>
  runtime_sym_membership_step_tac `emit_op ISZERO _ _ = _` runtime_sym_emit_op_result >>
  irule runtime_sym_emit_inst >> goal_assum (drule_at Any) >>
  qexistsl [`0`, `ASSERT`, `[valid]`, `[]`] >> simp[] >>
  irule runtime_sym_labeled_inst >> simp[]
QED

Theorem runtime_sym_membership_offset[local]:
  ~is_label_operand idx_offset /\ EVERY runtime_sym_inst (state_insts s) /\
  (if offset_base > 0 then emit_op ADD [Lit (n2w offset_base); idx_offset]
   else return idx_offset) s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `offset_base > 0` >> simp[comp_return_def] >> strip_tac >> gvs[is_label_operand_def] >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op_result) >>
  simp[is_label_operand_def]
QED

Theorem runtime_sym_membership_result[local]:
  EVERY runtime_sym_inst (state_insts s) /\
  (if is_in then return (Var result_var)
   else emit_op ISZERO [Var result_var]) s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `is_in` >> simp[comp_return_def, is_label_operand_def] >> strip_tac >> gvs[is_label_operand_def] >>
  qpat_assum `emit_op ISZERO _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op_result) >>
  simp[is_label_operand_def]
QED

Theorem runtime_sym_array_membership_loop[local]:
  (!p st u st'. ~is_label_operand p /\ EVERY runtime_sym_inst (state_insts st) /\
     loader p st = (u,st') ==>
     EVERY runtime_sym_inst (state_insts st') /\ ~is_label_operand u) /\
  ~is_label_operand needle /\ ~is_label_operand arr /\ ~is_label_operand len /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_array_membership_loop needle arr len stride offset loader bound is_in s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  simp[compile_array_membership_loop_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  ntac 6 (qpat_x_assum `fresh_label _ _ = _`
    (mp_then Any strip_assume_tac runtime_sym_fresh_label)) >>
  ntac 2 (qpat_x_assum `fresh_var _ = _`
    (mp_then Any strip_assume_tac runtime_sym_fresh_var)) >>
  gvs[] >>
  runtime_sym_membership_step_tac `emit_inst JMP [Label entry_lbl] _ _ = _` runtime_sym_jump >>
  runtime_sym_membership_step_tac `new_block entry_lbl _ = _` runtime_sym_new_block_result >>
  runtime_sym_membership_step_tac `emit_inst ASSIGN [Lit 0w] [idx_var] _ = _` runtime_sym_assign >>
  runtime_sym_membership_step_tac `emit_inst ASSIGN [Lit 0w] [result_var] _ = _` runtime_sym_assign >>
  runtime_sym_membership_step_tac `(case bound of NONE => _ | SOME _ => _) _ = _` runtime_sym_membership_bound >>
  qpat_assum `(case bound of NONE => _ | SOME _ => _) _ = _` (fn th =>
    let val (_,next) = pairSyntax.dest_pair (boolSyntax.rhs (concl th))
    in runtime_sym_membership_step_tac `emit_inst JMP [Label cond_lbl] [] ^next = _`
         runtime_sym_jump
    end) >>
  runtime_sym_membership_step_tac `new_block cond_lbl _ = _` runtime_sym_new_block_result >>
  runtime_sym_membership_step_tac `emit_op EQ [Var idx_var;len] _ = _` runtime_sym_emit_op_result >>
  runtime_sym_membership_step_tac `emit_inst JNZ [done_op;_;_] _ _ = _` runtime_sym_jnz >>
  runtime_sym_membership_step_tac `new_block body_lbl _ = _` runtime_sym_new_block_result >>
  runtime_sym_membership_step_tac `emit_op MUL _ _ = _` runtime_sym_emit_op_result >>
  runtime_sym_membership_step_tac `(if _ then emit_op ADD _ else _) _ = _` runtime_sym_membership_offset >>
  runtime_sym_membership_step_tac `emit_op ADD [arr;total_offset] _ = _` runtime_sym_emit_op_result >>
  qpat_x_assum `!p st u st'. _` (drule_at_then (Pat `loader _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  runtime_sym_membership_step_tac `emit_op EQ [elem_val;needle] _ = _` runtime_sym_emit_op_result >>
  runtime_sym_membership_step_tac `emit_inst JNZ [match_op;_;_] _ _ = _` runtime_sym_jnz >>
  runtime_sym_membership_step_tac `new_block found_lbl _ = _` runtime_sym_new_block_result >>
  runtime_sym_membership_step_tac `emit_inst ASSIGN [Lit 1w] _ _ = _` runtime_sym_assign >>
  runtime_sym_membership_step_tac `emit_inst JMP [Label exit_lbl] _ _ = _` runtime_sym_jump >>
  runtime_sym_membership_step_tac `new_block incr_lbl _ = _` runtime_sym_new_block_result >>
  runtime_sym_membership_step_tac `emit_op ADD [Var idx_var;Lit 1w] _ = _` runtime_sym_emit_op_result >>
  runtime_sym_membership_step_tac `emit_inst ASSIGN [new_idx] _ _ = _` runtime_sym_assign >>
  runtime_sym_membership_step_tac `emit_inst JMP [Label cond_lbl] _ _ = _` runtime_sym_jump >>
  runtime_sym_membership_step_tac `new_block exit_lbl _ = _` runtime_sym_new_block_result >>
  qpat_assum `(if is_in then _ else _) _ = _`
    (mp_then Any mp_tac runtime_sym_membership_result) >> simp[]
QED

Theorem runtime_sym_var_array_membership[local]:
  (!op. ce.ce_imm_alloca = SOME op ==> ~is_label_operand op) /\
  ~is_label_operand needle /\ runtime_sym_value av /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_var_array_membership ce needle av rhs_ty is_in s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  strip_tac >>
  `~is_label_operand (vv_operand av)` by fs[runtime_sym_value_operand] >>
  qpat_x_assum `compile_var_array_membership _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_var_array_membership_def, comp_bind_def] >>
  namedCases_on `rhs_ty` ["base", "tys", "element bnd", "sid", "fid", ""] >>
  TRY (Cases_on `bnd`) >> simp[comp_return_def, is_label_operand_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  TRY (qpat_assum `compile_ptr_load _ _ _ _ _ = _`
         (mp_then Any mp_tac runtime_sym_ptr_load) >> simp[] >> strip_tac) >>
  qpat_assum `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_array_membership_loop) >>
  simp[is_label_operand_def] >>
  (impl_tac >-
   (rpt gen_tac >> strip_tac >>
    irule runtime_sym_ptr_load >> simp[] >> metis_tac[])) >>
  simp[]
QED

Theorem runtime_sym_literal_array_membership[local]:
  runtime_sym_generator_contracts tops /\ runtime_sym_env tops ce /\
  (!e t. expr_size e <
     list_size expr_size [a; Builtin ann (MakeArray elem bnd) elems] ==>
     runtime_sym_expr_contract tops cfn ce t e) /\
  supported_pure_expr tops a /\ ~supported_expr_exists is_self_code a /\
  supported_pure_expr tops (Builtin ann (MakeArray elem bnd) elems) /\
  ~supported_exprs_exists is_self_code elems /\
  is_ArrayT ann /\ (bop = In \/ bop = NotIn) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_builtin_dispatch_body cfn ce rt ty (Bop bop)
    [a; Builtin ann (MakeArray elem bnd) elems] s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >>
  `EVERY (supported_pure_expr tops) elems` by
    fs[supported_pure_expr_def, supported_pure_exprs_every, SF ETA_ss] >>
  `!e t. MEM e elems ==> runtime_sym_expr_contract tops cfn ce t e` by
    (rpt strip_tac >> first_x_assum irule >>
     irule nested_array_child_bound >>
     qexistsl [`ann`, `bnd`, `elem`, `elems`] >> simp[]) >>
  `runtime_sym_expr_contract tops cfn ce (expr_type a) a` by
    (qpat_assum `!e t. expr_size e < _ ==> _` irule >>
     irule expr_list_member_bound >> simp[]) >>
  `supported_expr tops a` by fs[supported_expr_def] >>
  drule runtime_sym_generators_lower_value >>
  pure_rewrite_tac[runtime_sym_lower_value_clause_def] >> strip_tac >>
  drule runtime_sym_generators_multi_exprs >>
  pure_rewrite_tac[runtime_sym_multi_exprs_clause_def] >> strip_tac >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def, expr_type_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  qpat_x_assum `!cfn ce ty e s op s'. _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!cfn ce es s ops s'. _`
    (drule_at_then (Pat `compile_multi_exprs _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  runtime_sym_stack_result_tac
  >- (qpat_assum `compile_list_membership_in _ _ _ = _`
        (mp_then Any mp_tac (SRULE [] (Q.INST [`is_in` |-> `T`] runtime_sym_list_membership))) >>
      simp[runtime_sym_value_def]) >>
  qpat_assum `compile_list_membership_notin _ _ _ = _`
    (mp_then Any mp_tac (SRULE [] (Q.INST [`is_in` |-> `F`] runtime_sym_list_membership))) >>
  simp[runtime_sym_value_def]
QED

Theorem runtime_sym_nonliteral_array_membership[local]:
  (!t st op st'. EVERY runtime_sym_inst (state_insts st) /\
     lower_value cfn ce t a st = (op,st') ==>
     EVERY runtime_sym_inst (state_insts st') /\ ~is_label_operand op) /\
  (!st av st'. EVERY runtime_sym_inst (state_insts st) /\
     cfn ce (expr_type b) b st = (av,st') ==>
     EVERY runtime_sym_inst (state_insts st') /\ runtime_sym_value av) /\
  (!ann elem bnd elems. b <> Builtin ann (MakeArray elem bnd) elems) /\
  (!op. ce.ce_imm_alloca = SOME op ==> ~is_label_operand op) /\
  is_ArrayT (expr_type b) /\ (bop = In \/ bop = NotIn) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_builtin_dispatch_body cfn ce rt ty (Bop bop) [a;b] s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >>
  qpat_x_assum `!t st op st'. _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  namedCases_on `b` ["rtb n", "rtb ns", "rtb ns fld", "rtb c a1 a2",
    "rtb lit", "rtb sid fs", "rtb base key", "rtb base fld", "rtb bi es",
    "rtb tb tgt es", "rtb ptr", "rtb target es df"] >> fs[] >>
  TRY (Cases_on `bi` >> fs[]) >>
  pairarg_tac >> simp[] >> runtime_sym_stack_result_tac >>
  qpat_x_assum `!st av st'. _`
    (drule_at_then (Pat `cfn _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  drule_all runtime_sym_var_array_membership >> simp[runtime_sym_value_def]
QED

Theorem runtime_sym_array_membership[local]:
  runtime_sym_generator_contracts tops /\ runtime_sym_env tops ce /\
  (!e t. expr_size e < list_size expr_size [a;b] ==>
     runtime_sym_expr_contract tops cfn ce t e) /\
  EVERY (supported_pure_expr tops) [a;b] /\
  ~supported_exprs_exists is_self_code [a;b] /\
  is_ArrayT (expr_type b) /\ (bop = In \/ bop = NotIn) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_builtin_dispatch_body cfn ce rt ty (Bop bop) [a;b] s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  Cases_on `?ann elem bnd elems. b = Builtin ann (MakeArray elem bnd) elems`
  >- (gvs[supported_expr_exists_def, expr_type_def] >>
      irule runtime_sym_literal_array_membership >>
      goal_assum (drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)) >>
      qexists `tops` >> simp[]) >>
  `!t st op st'. EVERY runtime_sym_inst (state_insts st) /\
     lower_value cfn ce t a st = (op,st') ==>
     EVERY runtime_sym_inst (state_insts st') /\ ~is_label_operand op` by
    (rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`args` |-> `[a;b]`] runtime_sym_builtin_lower_value) >>
     simp[] >> metis_tac[]) >>
  `!st av st'. EVERY runtime_sym_inst (state_insts st) /\
     cfn ce (expr_type b) b st = (av,st') ==>
     EVERY runtime_sym_inst (state_insts st') /\ runtime_sym_value av` by
    (rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`args` |-> `[a;b]`] runtime_sym_builtin_callback) >>
     simp[] >> metis_tac[]) >>
  irule runtime_sym_nonliteral_array_membership >>
  goal_assum (drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)) >>
  fs[runtime_sym_env_def, NOT_EXISTS_THM] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem runtime_sym_builtin_body:
  runtime_sym_generator_contracts tops /\
  (!e t. expr_size e < list_size expr_size args ==>
     runtime_sym_expr_contract tops cfn ce t e) ==>
  runtime_sym_builtin_contract tops (compile_builtin_dispatch_body cfn) ce rt ty bi args
Proof
  strip_tac >> pure_rewrite_tac[runtime_sym_builtin_contract_def] >>
  rpt gen_tac >> strip_tac >>
  `EVERY (supported_pure_expr tops) args /\
   ~supported_exprs_exists is_self_code args` by
    gvs[runtime_sym_builtin_domain, supported_expr_exists_def] >>
  `!e t s op s'. MEM e args /\ EVERY runtime_sym_inst (state_insts s) /\
     lower_value cfn ce t e s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op` by
    (rpt gen_tac >> strip_tac >>
     drule_all runtime_sym_builtin_lower_value >> simp[]) >>
  Cases_on `bi`
  >~ [`Keccak256`] >-
    (irule (runtime_sym_builtin_keccak |> SRULE [runtime_sym_builtin_contract_def]) >>
     simp[] >> metis_tac[])
  >~ [`Floor`] >-
    (irule (runtime_sym_builtin_floor |> SRULE [runtime_sym_builtin_contract_def]) >>
     simp[] >> metis_tac[])
  >~ [`Concat n`] >-
    (irule (runtime_sym_builtin_concat |> SRULE [runtime_sym_builtin_contract_def]) >>
     simp[] >> metis_tac[])
  >~ [`Slice n`] >-
    (irule (runtime_sym_builtin_slice |> SRULE [runtime_sym_builtin_contract_def]) >>
     simp[] >> metis_tac[])
  >~ [`NamedConst`] >-
    (runtime_sym_unary_args_tac >>
     qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
     simp[NoAsms, compile_builtin_dispatch_body_def] >>
     pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
     rename1 `lower_value _ _ _ _ _ = (op0,st1)` >>
     qpat_x_assum `!t s op s'. _ /\ lower_value _ _ _ _ _ = _ ==> _`
       drule_all >> strip_tac >>
     Cases_on `is_word_type rt` >> Cases_on `op0` >>
     gvs[as_stack_val_def, as_ptr_val_def, runtime_sym_value_def,
         mk_ptr_def, is_label_operand_def])
  >~ [`BoolChain is_and n`] >-
    (runtime_sym_unary_args_tac >>
     qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
     simp[NoAsms, compile_builtin_dispatch_body_def] >>
     rpt (pairarg_tac >> simp[]) >>
     strip_tac >> gvs[] >>
     `~supported_expr_exists is_self_code a` by
       (qpat_x_assum `~supported_exprs_exists is_self_code [a]` mp_tac >>
        simp[supported_expr_exists_def]) >>
     `EVERY (\e. supported_pure_expr tops e /\
                    ~supported_expr_exists is_self_code e /\
                    expr_size e < list_size expr_size [a])
        (bool_chain_operands is_and (n - 1) a)` by
       (irule (Q.INST [`P` |-> `\e. supported_pure_expr tops e /\
                              ~supported_expr_exists is_self_code e /\
                              expr_size e < list_size expr_size [a]`,
                         `Q` |-> `EVERY (\e. supported_pure_expr tops e /\
                              ~supported_expr_exists is_self_code e /\
                              expr_size e < list_size expr_size [a])`,
                         `G` |-> `\c. T`] bool_chain_operands_guarded) >>
        conj_tac
        >- gvs[supported_expr_exists_def, expr_size_def]
        >- (conj_tac >>
            simp[supported_pure_expr_def, supported_expr_exists_def,
                 expr_size_def])) >>
     `!e ss vv ss'. MEM e (bool_chain_operands is_and (n - 1) a) /\
        EVERY runtime_sym_inst (state_insts ss) /\
        lower_value cfn ce (BaseT BoolT) e ss = (vv,ss') ==>
        EVERY runtime_sym_inst (state_insts ss') /\ ~is_label_operand vv` by
       (rpt gen_tac >> strip_tac >>
        qpat_x_assum `EVERY (\z. supported_pure_expr tops z /\
          ~supported_expr_exists is_self_code z /\
          expr_size z < list_size expr_size [a])
          (bool_chain_operands is_and (n - 1) a)` mp_tac >>
        simp[EVERY_MEM] >> disch_then drule >> strip_tac >>
        drule runtime_sym_generators_lower_value >>
        pure_rewrite_tac[runtime_sym_lower_value_clause_def] >> disch_tac >>
        pure_rewrite_tac[runtime_sym_expr_contract_def] >>
        first_x_assum (qspecl_then
          [`cfn`,`ce`,`BaseT BoolT`,`e`,`ss`,`vv`,`ss'`] mp_tac) >>
        disch_tac >>
        `supported_expr tops e` by
          simp[supported_expr_def, supported_pure_expr_def] >>
        qpat_x_assum `runtime_sym_expr_contract _ _ _ _ _ /\ _ ==> _` mp_tac >>
        disch_tac >>
        gvs[EVERY_MEM] ) >>
     imp_res_tac runtime_sym_fresh_var >>
     imp_res_tac runtime_sym_fresh_label >>
     `EVERY runtime_sym_inst (state_insts st3)` by
       (drule_at (Pat `compile_bool_chain_ops _ _ _ _ _ _ _ = _`)
          runtime_sym_compile_bool_chain_ops >>
        simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
     imp_res_tac runtime_sym_new_block_result >>
     gvs[runtime_sym_value_def] )
  >~ [`Bop bop`] >- suspend "bop"
  >~ [`Env item`] >- (irule (runtime_sym_builtin_env |> SRULE [runtime_sym_builtin_contract_def]) >> simp[] >> metis_tac[])
  >~ [`Neg`] >- suspend "neg"
  >~ [`Abs`] >- suspend "abs"
  >~ [`Not`] >- suspend "not"
  >~ [`Acc item`] >- suspend "acc"
  >~ [`MakeArray elem bound`] >- suspend "array"
  >~ [`AsWeiValue d`] >- suspend "wei"
  >~ [`AddMod`] >- suspend "addmod"
  >~ [`MulMod`] >- suspend "mulmod"
  >~ [`PowMod256`] >- suspend "powmod"
  >~ [`Sha256`] >- suspend "sha"
  >~ [`BlockHash`] >- suspend "blockhash"
  >~ [`BlobHash`] >- suspend "blobhash"
  >~ [`ECRecover`] >- suspend "ecrecover"
  >~ [`ECAdd`] >- suspend "ecadd"
  >~ [`ECMul`] >- suspend "ecmul"
  >~ [`Uint2Str n`] >- suspend "uint2str"
  >~ [`CalldataLen`] >- suspend "calldatalen"
  >~ [`Len`] >- suspend "len"
  >~ [`MethodId`] >- suspend "method_id"
  >~ [`CalldataSlice n`] >- suspend "calldataslice"
  >~ [`Ceil`] >- suspend "ceil"
  >> gvs[supported_expr_def, supported_pure_expr_def,
         supported_effect_expr_def, supported_builtin_form_def, builtin_args_length_ok_def]
QED
Resume runtime_sym_builtin_body[bop]:
  drule runtime_sym_bop_selections >> strip_tac >>
  namedCases_on `args` ["", "a tail"] >> gnvs[] >>
  namedCases_on `tail` ["", "b rest"] >> gnvs[] >>
  Cases_on `(bop = In \/ bop = NotIn) /\ is_ArrayT (expr_type b)`
  >- suspend "array_membership" >>
  Cases_on `is_bytestring_type (expr_type a) /\ (bop = Eq \/ bop = NotEq)`
  >- (irule runtime_sym_bytestring_compare >>
      goal_assum (drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)) >>
      simp[] >> first_assum ACCEPT_TAC) >>
  RULE_ASSUM_TAC (SRULE [DE_MORGAN_THM]) >> fs[] >>
  drule runtime_sym_generators_expr_primitive >>
  disch_then (assume_tac o cj 3 o SRULE [runtime_sym_expr_primitive_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `compile_binop bop v1 v2 (expr_type a)
    (if bop = Exp then expr_int_literal a else NONE)
    (if bop = Exp then expr_int_literal b else NONE) st2` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  `EVERY runtime_sym_inst (state_insts st1) /\ ~is_label_operand v1` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st2) /\ ~is_label_operand v2` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  simp[runtime_sym_value_def] >>
  qpat_x_assum `!bop x y ty bl el s op s'. _` (drule_at_then (Pat `compile_binop _ _ _ _ _ _ _ = _`) mp_tac) >>
  simp[]
QED
Resume runtime_sym_builtin_body[neg]:
  `LENGTH args = 1` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def, builtin_args_length_ok_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[]) >>
  namedCases_on `args` ["", "a rest"] >> gnvs[] >>
  drule runtime_sym_generators_expr_primitive >>
  disch_then (assume_tac o cj 5 o SRULE [runtime_sym_expr_primitive_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >> pairarg_tac >> simp[] >>
  Cases_on `compile_neg v' (expr_type a) st1` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  qpat_assum `!t s op s'. _ /\ lower_value _ _ _ _ _ = _ ==> _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!v ty s op s'. _` (drule_at_then (Pat `compile_neg _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[abs]:
  `LENGTH args = 1` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def, builtin_args_length_ok_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[]) >>
  namedCases_on `args` ["", "a rest"] >> gnvs[] >>
  drule runtime_sym_generators_simple >>
  disch_then (assume_tac o cj 1 o SRULE [runtime_sym_simple_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >> pairarg_tac >> simp[] >>
  Cases_on `compile_builtin_abs v' st1` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  qpat_assum `!t s op s'. _ /\ lower_value _ _ _ _ _ = _ ==> _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!v s op s'. _` (drule_at_then (Pat `compile_builtin_abs _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[not]:
  `LENGTH args = 1` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def, builtin_args_length_ok_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[]) >>
  namedCases_on `args` ["", "a rest"] >> gnvs[] >>
  drule runtime_sym_generators_expr_primitive >>
  disch_then (assume_tac o cj 4 o SRULE [runtime_sym_expr_primitive_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >> pairarg_tac >> simp[] >>
  qpat_assum `!t s op s'. _ /\ lower_value _ _ _ _ _ = _ ==> _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `expr_type a = BaseT BoolT` >> simp[]
  >- (Cases_on `emit_op ISZERO [v'] st1` >>
      simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
      drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
      simp[runtime_sym_value_def]) >>
  Cases_on `compile_invert v' (expr_type a) ce st1` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  qpat_assum `!ce v ty s op s'. _`
    (drule_at_then (Pat `compile_invert _ _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[acc]:
  `LENGTH args = 1` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def, builtin_args_length_ok_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[]) >>
  namedCases_on `args` ["", "a rest"] >> gnvs[] >>
  drule runtime_sym_generators_acc >>
  pure_rewrite_tac[runtime_sym_acc_clause_def] >> strip_tac >>
  `runtime_sym_expr_contract tops cfn ce (BaseT AddressT) a` by
    (first_x_assum irule >> simp[]) >>
  `supported_expr tops a /\ ~supported_expr_exists is_self_code a` by
    (conj_tac >- (irule runtime_sym_supported_argument >> qexists `[a]` >> simp[]) >>
     qpat_x_assum `~supported_exprs_exists _ _` mp_tac >>
     simp[supported_exprs_exists_every]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  Cases_on `compile_acc cfn ce a item s` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  qpat_x_assum `!cfn ce e item s op s'. _`
    (drule_at_then (Pat `compile_acc _ _ _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[array]:
  `!e t. MEM e args ==> runtime_sym_expr_contract tops cfn ce t e` by
    (rpt strip_tac >> first_x_assum irule >> metis_tac[expr_list_member_bound]) >>
  qpat_x_assum `!e t. expr_size e < _ ==> _` kall_tac >>
  qpat_x_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` kall_tac >>
  drule runtime_sym_generators_context >>
  disch_then (assume_tac o cj 3 o SRULE [runtime_sym_context_clauses_def]) >>
  drule runtime_sym_generators_make_tuple >>
  pure_rewrite_tac[runtime_sym_make_tuple_clause_def] >> strip_tac >>
  drule runtime_sym_generators_make_array >>
  pure_rewrite_tac[runtime_sym_make_array_clause_def] >> strip_tac >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `elem` >> simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >>
  qpat_assum `!n s b s'. _` (drule_at_then (Pat `compile_alloc_buffer _ _ = _`) mp_tac) >>
  simp[] >> strip_tac
  >~ [`compile_make_tuple _ _ _ _ _ _`]
  >- (Cases_on `compile_make_tuple cfn ce args (tuple_literal_types rt args) buf_op_alloc.buf_operand 0 st2` >>
      simp[as_ptr_val_def] >> strip_tac >> gnvs[] >>
      qpat_x_assum `!cfn ce es tys buf off s op s'. _`
        (drule_at_then (Pat `compile_make_tuple _ _ _ _ _ _ _ = _`) mp_tac) >>
      simp[runtime_sym_value_def, mk_ptr_def]) >>
  Cases_on `compile_make_array cfn ce args x (type_memory_bytes ce x)
    (case bound of Fixed v2 => F | Dynamic v3 => T) buf_op_alloc.buf_operand st2` >>
  simp[as_ptr_val_def] >> strip_tac >> gnvs[] >>
  qpat_x_assum `!cfn ce es ety stride lw buf s op s'. _`
    (drule_at_then (Pat `compile_make_array _ _ _ _ _ _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def, mk_ptr_def]
QED
Resume runtime_sym_builtin_body[wei]:
  `LENGTH args = 1` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def, builtin_args_length_ok_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[]) >>
  namedCases_on `args` ["", "a rest"] >> gnvs[] >>
  drule runtime_sym_generators_misc >>
  disch_then (fn th => map_every assume_tac
    [cj 6 (SRULE [runtime_sym_misc_clauses_def] th),
     cj 7 (SRULE [runtime_sym_misc_clauses_def] th)]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >> pairarg_tac >> simp[] >>
  qpat_assum `!t s op s'. _ /\ lower_value _ _ _ _ _ = _ ==> _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `is_decimal_type (expr_type a)` >> simp[]
  >- (Cases_on `compile_as_wei_value_decimal v' (denomination_multiplier d)
        (decimal_divisor (expr_type a)) st1` >>
      simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
      qpat_assum `!v scale divisor s op s'. _`
        (drule_at_then (Pat `compile_as_wei_value_decimal _ _ _ _ = _`) mp_tac) >>
      simp[runtime_sym_value_def]) >>
  Cases_on `compile_as_wei_value_int v' (denomination_multiplier d)
    (is_signed_type (expr_type a)) st1` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  qpat_assum `!v scale signed s op s'. _`
    (drule_at_then (Pat `compile_as_wei_value_int _ _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[addmod]:
  `LENGTH args = 3` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def, builtin_args_length_ok_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[] >>
     namedCases_on `ys` ["", "c zs"] >> simp[] >>
     namedCases_on `zs` ["", "d rest"] >> simp[]) >>
  namedCases_on `args` ["", "a xs"] >> gnvs[] >>
  namedCases_on `xs` ["", "b ys"] >> gnvs[] >>
  namedCases_on `ys` ["", "c zs"] >> gnvs[] >>
  `LENGTH zs = 0` by decide_tac >> gnvs[] >>
  drule runtime_sym_generators_math >>
  disch_then (assume_tac o cj 1 o SRULE [runtime_sym_math_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `compile_addmod va vb vc st3` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  `EVERY runtime_sym_inst (state_insts st1) /\ ~is_label_operand va` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st2) /\ ~is_label_operand vb` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st3) /\ ~is_label_operand vc` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  qpat_assum `!a b m s op s'. _` (drule_at_then (Pat `compile_addmod _ _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[mulmod]:
  `LENGTH args = 3` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def, builtin_args_length_ok_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[] >>
     namedCases_on `ys` ["", "c zs"] >> simp[] >>
     namedCases_on `zs` ["", "d rest"] >> simp[]) >>
  namedCases_on `args` ["", "a xs"] >> gnvs[] >>
  namedCases_on `xs` ["", "b ys"] >> gnvs[] >>
  namedCases_on `ys` ["", "c zs"] >> gnvs[] >>
  `LENGTH zs = 0` by decide_tac >> gnvs[] >>
  drule runtime_sym_generators_math >>
  disch_then (assume_tac o cj 2 o SRULE [runtime_sym_math_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `compile_mulmod va vb vc st3` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  `EVERY runtime_sym_inst (state_insts st1) /\ ~is_label_operand va` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st2) /\ ~is_label_operand vb` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st3) /\ ~is_label_operand vc` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  qpat_assum `!a b m s op s'. _` (drule_at_then (Pat `compile_mulmod _ _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[powmod]:
  `LENGTH args = 2` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def, builtin_args_length_ok_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[] >>
     namedCases_on `ys` ["", "c zs"] >> simp[]) >>
  namedCases_on `args` ["", "a xs"] >> gnvs[] >>
  namedCases_on `xs` ["", "b ys"] >> gnvs[] >>
  drule runtime_sym_generators_math >>
  disch_then (assume_tac o cj 3 o SRULE [runtime_sym_math_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `compile_pow_mod256 v1 v2 st2` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  `EVERY runtime_sym_inst (state_insts st1) /\ ~is_label_operand v1` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st2) /\ ~is_label_operand v2` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  qpat_assum `!a b s op s'. _` (drule_at_then (Pat `compile_pow_mod256 _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[blockhash]:
  `LENGTH args = 1` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def, builtin_args_length_ok_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[]) >>
  namedCases_on `args` ["", "a rest"] >> gnvs[] >>
  drule runtime_sym_generators_misc >>
  disch_then (assume_tac o cj 1 o SRULE [runtime_sym_misc_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >> pairarg_tac >> simp[] >>
  Cases_on `compile_blockhash v' st1` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  qpat_assum `!t s op s'. _ /\ lower_value _ _ _ _ _ = _ ==> _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!v s op s'. _` (drule_at_then (Pat `compile_blockhash _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[blobhash]:
  `LENGTH args = 1` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def, builtin_args_length_ok_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[]) >>
  namedCases_on `args` ["", "a rest"] >> gnvs[] >>
  drule runtime_sym_generators_misc >>
  disch_then (assume_tac o cj 2 o SRULE [runtime_sym_misc_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >> pairarg_tac >> simp[] >>
  Cases_on `compile_blobhash v' st1` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  qpat_assum `!t s op s'. _ /\ lower_value _ _ _ _ _ = _ ==> _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!v s op s'. _` (drule_at_then (Pat `compile_blobhash _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[ecrecover]:
  `LENGTH args = 4` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def, builtin_args_length_ok_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[] >>
     namedCases_on `ys` ["", "c zs"] >> simp[] >>
     namedCases_on `zs` ["", "d ws"] >> simp[] >>
     namedCases_on `ws` ["", "e rest"] >> simp[]) >>
  namedCases_on `args` ["", "a xs"] >> gnvs[] >>
  namedCases_on `xs` ["", "b ys"] >> gnvs[] >>
  namedCases_on `ys` ["", "c zs"] >> gnvs[] >>
  namedCases_on `zs` ["", "d ws"] >> gnvs[] >>
  `LENGTH ws = 0` by decide_tac >> gnvs[] >>
  drule runtime_sym_generators_misc >>
  disch_then (assume_tac o cj 3 o SRULE [runtime_sym_misc_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `compile_ecrecover vh vv vr vs' st4` >>
  simp[as_stack_val_def] >> strip_tac >>
  qpat_x_assum `StackValue _ _ = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `r = s'` (SUBST_ALL_TAC o SYM) >>
  `EVERY runtime_sym_inst (state_insts st1) /\ ~is_label_operand vh` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st2) /\ ~is_label_operand vv` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st3) /\ ~is_label_operand vr` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st4) /\ ~is_label_operand vs'` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `!e t. expr_size e < _ ==> _` kall_tac >>
  qpat_x_assum `!h v r x s op s'. _` (drule_at_then (Pat `compile_ecrecover _ _ _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[ecadd]:
  drule runtime_sym_builtin_callback >> simp[] >> strip_tac >>
  `LENGTH args = 2` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def, builtin_args_length_ok_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[] >>
     namedCases_on `ys` ["", "c zs"] >> simp[]) >>
  namedCases_on `args` ["", "a xs"] >> gnvs[] >>
  namedCases_on `xs` ["", "b ys"] >> gnvs[] >>
  drule runtime_sym_generators_context >>
  disch_then (assume_tac o cj 1 o SRULE [runtime_sym_context_clauses_def]) >>
  drule runtime_sym_generators_misc >>
  disch_then (assume_tac o cj 4 o SRULE [runtime_sym_misc_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `compile_ecadd_points p1 p2 st2a` >>
  simp[as_stack_val_def] >> strip_tac >>
  qpat_x_assum `StackValue _ _ = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `r = s'` (SUBST_ALL_TAC o SYM) >>
  `EVERY runtime_sym_inst (state_insts st1) /\ runtime_sym_value p1_vv` by
    (qpat_assum `!e t s v s'. _ /\ _ /\ cfn _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st1a) /\ ~is_label_operand p1` by
    (qpat_assum `!ce v s op s'. runtime_sym_env tops ce /\ _ ==> _` (mp_tac o Q.SPECL [`ce`, `p1_vv`]) >>
     disch_then (drule_at_then (Pat `unwrap_value _ _ _ = _`) mp_tac) >>
     disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `EVERY runtime_sym_inst (state_insts st2) /\ runtime_sym_value p2_vv` by
    (qpat_assum `!e t s v s'. _ /\ _ /\ cfn _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st2a) /\ ~is_label_operand p2` by
    (qpat_assum `!ce v s op s'. _` (drule_at_then (Pat `unwrap_value _ _ _ = _`) mp_tac) >>
     disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!e t s v s'. _ /\ _ /\ cfn _ _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `!e t. expr_size e < _ ==> _` kall_tac >>
  qpat_assum `!p q s op s'. _` (drule_at_then (Pat `compile_ecadd_points _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[ecmul]:
  drule runtime_sym_builtin_callback >> simp[] >> strip_tac >>
  `LENGTH args = 2` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def, builtin_args_length_ok_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[] >>
     namedCases_on `ys` ["", "c zs"] >> simp[]) >>
  namedCases_on `args` ["", "a xs"] >> gnvs[] >>
  namedCases_on `xs` ["", "b ys"] >> gnvs[] >>
  drule runtime_sym_generators_context >>
  disch_then (assume_tac o cj 1 o SRULE [runtime_sym_context_clauses_def]) >>
  drule runtime_sym_generators_misc >>
  disch_then (assume_tac o cj 5 o SRULE [runtime_sym_misc_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `compile_ecmul_point p s'' st2` >>
  simp[as_stack_val_def] >> strip_tac >>
  qpat_x_assum `StackValue _ _ = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `r = s'` (SUBST_ALL_TAC o SYM) >>
  `EVERY runtime_sym_inst (state_insts st1) /\ runtime_sym_value p_vv` by
    (qpat_assum `!e t s v s'. _ /\ _ /\ cfn _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st1a) /\ ~is_label_operand p` by
    (qpat_assum `!ce v s op s'. _` (drule_at_then (Pat `unwrap_value _ _ _ = _`) mp_tac) >>
     disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `EVERY runtime_sym_inst (state_insts st2) /\ ~is_label_operand s''` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!e t s v s'. _ /\ _ /\ cfn _ _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `!e t. expr_size e < _ ==> _` kall_tac >>
  qpat_assum `!p q s op s'. _` (drule_at_then (Pat `compile_ecmul_point _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[uint2str]:
  `LENGTH args = 1` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def, builtin_args_length_ok_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[]) >>
  namedCases_on `args` ["", "a rest"] >> gnvs[] >>
  drule runtime_sym_generators_simple >>
  disch_then (assume_tac o cj 4 o SRULE [runtime_sym_simple_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >> pairarg_tac >> simp[] >>
  Cases_on `compile_uint2str v' n (type_memory_bytes ce rt) st1` >>
  simp[as_ptr_val_def] >> strip_tac >> gnvs[] >>
  qpat_assum `!t s op s'. _ /\ lower_value _ _ _ _ _ = _ ==> _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!v digits size s op s'. _`
    (drule_at_then (Pat `compile_uint2str _ _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def, mk_ptr_def]
QED
Resume runtime_sym_builtin_body[calldataslice]:
  `LENGTH args = 1` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def, builtin_args_length_ok_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[]) >>
  namedCases_on `args` ["", "a rest"] >> gnvs[] >>
  drule runtime_sym_generators_simple >>
  disch_then (assume_tac o cj 3 o SRULE [runtime_sym_simple_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >> pairarg_tac >> simp[] >>
  Cases_on `compile_slice_calldata start_op (Lit (n2w n)) (type_memory_bytes ce rt) st1` >>
  simp[as_ptr_val_def] >> strip_tac >> gnvs[] >>
  qpat_assum `!t s op s'. _ /\ lower_value _ _ _ _ _ = _ ==> _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!start len n s op s'. _`
    (drule_at_then (Pat `compile_slice_calldata _ _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def, mk_ptr_def, stackPlanTypesTheory.is_label_operand_def]
QED
Resume runtime_sym_builtin_body[method_id]:
  runtime_sym_unary_args_tac >>
  drule runtime_sym_generators_expr_primitive >>
  disch_then (assume_tac o cj 1 o SRULE [runtime_sym_expr_primitive_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_builtin_dispatch_body_def] >>
  Cases_on `method_id_literal a` >> simp[NoAsms] >>
  Cases_on `lower_value cfn ce (expr_type a) a s` >>
  Cases_on `rt = BaseT (BytesT (Fixed 4))` >> simp[] >>
  TRY (runtime_sym_finish_unary_tac runtime_sym_stack_result_tac
    runtime_sym_method_id_runtime) >>
  TRY (runtime_sym_finish_unary_tac
    (runtime_sym_result_tac as_ptr_val_def `as_ptr_val _ LocMemory output`)
    runtime_sym_method_id_runtime) >>
  disch_tac >>
  qpat_assum `!ty lit s v s'. EVERY runtime_sym_inst (state_insts s) /\
       compile_literal_vv ty lit s = (v,s') ==> _`
    (drule_at_then (Pat `compile_literal_vv _ _ _ = _`) mp_tac) >>
  simp[]
QED

Resume runtime_sym_builtin_body[len]:
  runtime_sym_unary_args_tac >>
  drule runtime_sym_builtin_callback >> simp[] >> strip_tac >>
  `!op. ce.ce_imm_alloca = SOME op ==> ~is_label_operand op` by
    fs[runtime_sym_env_def] >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> runtime_sym_stack_result_tac >>
  qpat_assum `!t s v s'. _ /\ cfn _ _ _ _ = _ ==> _`
    (drule_at_then (Pat `cfn _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  imp_res_tac runtime_sym_value_operand >>
  drule_all runtime_sym_builtin_len >> simp[runtime_sym_value_def]
QED

Resume runtime_sym_builtin_body[calldatalen]:
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_builtin_dispatch_body_def] >>
  runtime_sym_stack_result_tac >>
  drule_all runtime_sym_builtin_calldatasize >> simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[ceil]:
  runtime_sym_round_tac runtime_sym_ceil
QED
Resume runtime_sym_builtin_body[sha]:
  runtime_sym_unary_args_tac >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_builtin_dispatch_body_def] >>
  IF_CASES_TAC >> simp[NoAsms] >>
  rpt (CASE_TAC >> simp[NoAsms]) >>
  FIRST [runtime_sym_unary_stack_tac runtime_sym_sha256_bytes,
         runtime_sym_unary_stack_tac runtime_sym_sha256_bytesm,
         runtime_sym_unary_stack_tac runtime_sym_sha256_word]
QED
Resume runtime_sym_builtin_body[array_membership]:
  irule runtime_sym_array_membership >>
  goal_assum (drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)) >>
  qexists `tops` >> gvs[]
QED
Finalise runtime_sym_builtin_body
