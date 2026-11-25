(* Terminal opcodes emitted by the checked runtime-default grammar. *)
Theory runtimeDefaultRejectExpr
Ancestors
  runtimeDefaultRejectCode runtimeDefaultCompile ctorCallFreeCallbacks ctorCallFreeOps ctorCallFreeRules
  ctorCallFreeValues ctorCallFreeMemory exprLoweringEquations exprLowering
  exprCallBounds compileEnv vyperAST vyperTypeContract vyperTypeSystem
  whitelistCheckerConsts supportedExprTraverse context loweringShapeDefs
  emitHelper venomInst list pair words exprBopLowering builtinHashing
  ctorCallFreeMembership moduleLowering loweringFunctionOpcodes ctorCallFreeABIDecode
  deploySymSrcGeneratorFrame deploySymSrcBlockFrame deploySymSrcFrameContext
  deploySymSrcFrameExprHelpers deploySymSrcFrameABI exprSimAbiGasBridge fragObserverCodeProps exprLoweringProps fragExec rich_list
  constSubst constSubstMods constSubstCorrect vyperTypeBuiltins vyperInterpreter alist
  compileVyper immutableLocationProps checkedCopyAcyclic whitelistCheckerDecls
  runtimeConstantSubstitutionProps
  vyperTypeExternalDefaults publicGetterProps loweringShapeProps loweringShapeSource
  ctorCallFreeBoolChain boolChainOperandsSupported runtimeConstBoolChainOperands

Libs runtimeDefaultRejectSyntaxLib

val _ = Parse.hide "tops";
val _ = Parse.hide "body";

val default_code = ``\st. EVERY (\i. ^default_opcode i.inst_opcode) (state_insts st)``;

fun default_ops th =
  SIMP_RULE (srw_ss()) [DISJ_IMP_THM, FORALL_AND_THM]
    (Q.INST [`P` |-> `^default_opcode`] (SPEC_ALL th));

fun default_insts th =
  SIMP_RULE (srw_ss()) []
    (Q.INST [`P` |-> `\i. ^default_opcode i.inst_opcode`] (SPEC_ALL th));

fun default_emit opc =
  SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> opc] (default_ops opcode_every_emit_inst));

Theorem runtime_default_ifexp_opcodes[local]:
  (!st. ^default_code st ==>
    ^default_code (SND (lower_value cfn ce (BaseT BoolT) test st))) /\
  (!e st. MEM e [yes;no] /\ ^default_code st ==>
    ^default_code (SND (cfn ce ty e st))) /\
  acyclic_struct_metadata ce.ce_struct_fields /\ ^default_code s ==>
  ^default_code (SND (compile_expr_body cfn bfn tfn ce ty (IfExp t test yes no) s))
Proof
  strip_tac >> simp[Once compile_expr_body_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[COND_RAND] >>
  `^default_code st1` by (gvs[] >> metis_tac[SND]) >>
  `^default_code st2` by (gvs[] >> metis_tac[default_insts every_state_insts_fresh_var, SND]) >>
  `^default_code st3` by (gvs[] >> metis_tac[default_insts every_state_insts_fresh_label, SND]) >>
  `^default_code st4` by (gvs[] >> metis_tac[default_insts every_state_insts_fresh_label, SND]) >>
  `^default_code st5` by (gvs[] >> metis_tac[default_insts every_state_insts_fresh_label, SND]) >>
  `^default_code st6` by (gvs[] >> metis_tac[default_emit `JNZ`, SND]) >>
  `^default_code st7` by (gvs[] >> metis_tac[default_insts every_state_insts_new_block, SND]) >>
  `^default_code st7a` by (gvs[] >> metis_tac[SND]) >>
  `^default_code st8` by
    (gvs[] >> metis_tac[default_ops runtime_default_ifexp_arm_opcodes, SND]) >>
  `^default_code st9` by (gvs[] >> metis_tac[default_emit `ASSIGN`, SND]) >>
  `^default_code st10` by (gvs[] >> metis_tac[default_emit `JMP`, SND]) >>
  `^default_code st11` by (gvs[] >> metis_tac[default_insts every_state_insts_new_block, SND]) >>
  `^default_code st11a` by (gvs[] >> metis_tac[SND]) >>
  `^default_code st12` by
    (gvs[] >> metis_tac[default_ops runtime_default_ifexp_arm_opcodes, SND]) >>
  `^default_code st13` by (gvs[] >> metis_tac[default_emit `ASSIGN`, SND]) >>
  `^default_code st14` by (gvs[] >> metis_tac[default_emit `JMP`, SND]) >>
  gvs[] >> metis_tac[default_insts every_state_insts_new_block, SND]
QED

Theorem runtime_default_lower_value_opcodes[local]:
  acyclic_struct_metadata ce.ce_struct_fields /\
  (!st. ^default_code st ==> ^default_code (SND (cfn ce ty e st))) /\
  ^default_code s ==> ^default_code (SND (lower_value cfn ce ty e s))
Proof
  simp[lower_value_def] >> strip_tac >>
  irule every_state_insts_bind >> simp[] >> rpt strip_tac >>
  irule (default_ops runtime_default_unwrap_opcodes) >> gvs[]
QED

Theorem runtime_default_builtin_body[local]:
  EVERY (runtime_constant_expr mods) es ==>
  compile_expr_body cfn bfn tfn ce ty (Builtin ann bi es) =
  bfn ce ann ty bi es
Proof
  strip_tac >> irule compile_expr_body_builtin_default >>
  rpt conj_tac >> rpt strip_tac >> gvs[runtime_constant_expr_def]
QED

Theorem runtime_default_multi_exprs_opcodes[local]:
  !es s.
    (!e st. MEM e es /\ ^default_code st ==>
      ^default_code (SND (lower_value cfn ce (expr_type e) e st))) /\
    ^default_code s ==>
    ^default_code (SND (compile_multi_exprs cfn ce es s))
Proof
  Induct >> simp[compile_multi_exprs_def, every_state_insts_return] >>
  rpt strip_tac >>
  Cases_on `lower_value cfn ce (expr_type h) h s` >>
  `^default_code r` by (gvs[] >> metis_tac[SND]) >>
  `^default_code (SND (compile_multi_exprs cfn ce es r))` by
    (gvs[] >> first_assum irule >> simp[]) >>
  simp[comp_bind_def,comp_return_def] >>
  Cases_on `compile_multi_exprs cfn ce es r` >> gvs[]
QED

Theorem runtime_default_literal_items[local]:
  runtime_constant_expr mods (Builtin ty (MakeArray elem cap) es) /\
  ~supported_expr_exists p (Builtin ty (MakeArray elem cap) es) /\ MEM e es ==>
  runtime_constant_expr mods e /\ ~supported_expr_exists p e
Proof
  simp[runtime_constant_expr_def, supported_expr_exists_def,
       supported_exprs_exists_every, EXISTS_MEM] >>
  metis_tac[EVERY_MEM, constant_expr_runtime_constant]
QED

Theorem runtime_default_expr_terminal_opcodes:
  (!ce ty e s.
    runtime_constant_expr mods e /\ ~supported_expr_exists (^checked_default_expr ce) e /\
    acyclic_struct_metadata ce.ce_struct_fields /\ ^default_code s ==>
    ^default_code (SND (compile_expr ce ty e s))) /\
  (!ce rt ty bi es s.
    (runtime_constant_builtin bi \/ constant_builtin bi) /\
    bi <> Sha256 /\ builtin_args_length_ok bi (LENGTH es) /\
    EVERY (runtime_constant_expr mods) es /\ ~supported_exprs_exists (^checked_default_expr ce) es /\
    acyclic_struct_metadata ce.ce_struct_fields /\ ^default_code s ==>
    ^default_code (SND (compile_builtin_dispatch ce rt ty bi es s))) /\
  (!ce vt ty tb rt es s.
    constant_type_builtin tb /\ type_builtin_args_length_ok tb (LENGTH es) /\
    EVERY (runtime_constant_expr mods) es /\ ~supported_exprs_exists (^checked_default_expr ce) es /\
    acyclic_struct_metadata ce.ce_struct_fields /\ ^default_code s ==>
    ^default_code (SND (compile_type_builtin_dispatch ce vt ty tb rt es s)))
Proof
  ho_match_mp_tac compile_expr_raw_ind >> rpt conj_tac >> rpt gen_tac >>
  DISCH_TAC >> once_rewrite_tac[compile_expr_raw_def] >>
  rpt (disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))
  >~ [`compile_expr_body`] >- suspend "expr"
  >~ [`compile_builtin_dispatch_body`] >- suspend "builtin"
  >> suspend "type_builtin"
QED

Resume runtime_default_expr_terminal_opcodes[type_builtin]:
  simp[] >> irule (default_ops runtime_default_type_builtin_opcodes) >> gvs[]
QED

Resume runtime_default_expr_terminal_opcodes[expr]:
  Cases_on `e` >> gvs[runtime_constant_expr_def]
  >~ [`compile_expr_body _ _ _ _ _ (TopLevelName _ _) _`] >-
    (gvs[supported_expr_exists_def] >> simp[Once compile_expr_body_def] >> gvs[])
  >~ [`compile_expr_body _ _ _ _ _ (Literal _ _) _`] >-
    (simp[Once compile_expr_body_def] >>
     irule (default_ops outcomes_free_literal_vv) >> gvs[])
  >~ [`compile_expr_body _ _ _ _ _ (Builtin _ _ _) _`] >-
    suspend "expr_builtin"
  >~ [`compile_expr_body _ _ _ _ _ (Builtin _ _ _) _`] >-
    suspend "expr_builtin_constant"
  >~ [`compile_expr_body _ _ _ _ _ (TypeBuiltin _ _ _ _) _`] >-
    (simp[Once compile_expr_body_def, type_child_callback_def, expr_size_def] >>
     gvs[supported_expr_exists_def] >> first_assum irule >> simp[])
  >> fs[supported_expr_exists_def]
  >~ [`compile_expr_body _ _ _ _ _ (IfExp _ _ _ _) _`] >- suspend "expr_if"
  >~ [`compile_expr_body _ _ _ _ _ (IfExp _ _ _ _) _`] >- suspend "expr_if_alt"
  >~ [`compile_expr_body _ _ _ _ _ (StructLit _ _ _) _`] >- suspend "expr_struct"
  >~ [`compile_expr_body _ _ _ _ _ (Subscript _ _ _) _`] >- suspend "expr_subscript"
  >> suspend "expr_attribute"
QED

val default_child_tac =
  gvs[] >>
  qpat_assum `!child env ty st. _ ==> _ ==> EVERY _ (state_insts (SND (compile_expr env ty child st)))` irule >>
  simp[];

val default_ifexp_tac =
  irule (SRULE [] runtime_default_ifexp_opcodes) >>
  gvs[Excl "expr_child_callback_def"] >> rpt conj_tac
  >- (rpt strip_tac >> irule (SRULE [] runtime_default_lower_value_opcodes) >>
      gvs[Excl "expr_child_callback_def"] >> rpt strip_tac >> default_child_tac)
  >> rpt strip_tac >> default_child_tac;

Resume runtime_default_expr_terminal_opcodes[expr_if]:
  default_ifexp_tac
QED

Resume runtime_default_expr_terminal_opcodes[expr_if_alt]:
  default_ifexp_tac
QED

Resume runtime_default_expr_terminal_opcodes[expr_attribute]:
  simp[Once compile_expr_body_def] >>
  irule (default_ops outcomes_free_attribute) >> gvs[Excl "expr_child_callback_def"] >>
  rpt strip_tac >> default_child_tac
QED

Resume runtime_default_expr_terminal_opcodes[expr_builtin]:
  qpat_assum `EVERY (runtime_constant_expr mods) _`
    (fn th => rewrite_tac [MATCH_MP runtime_default_builtin_body th]) >>
  gvs[builtin_child_callback_def, supported_expr_exists_def, expr_size_def] >>
  qpat_assum `!args env rt ty bi st. _ ==> _ ==>
    EVERY _ (state_insts (SND (compile_builtin_dispatch env rt ty bi args st)))` irule >>
  simp[]
QED

Resume runtime_default_expr_terminal_opcodes[expr_builtin_constant]:
  rename1 `Builtin ann bi args` >>
  `EVERY (runtime_constant_expr mods) args` by
    (irule EVERY_MONOTONIC >> goal_assum (drule_at Any) >>
     simp[constant_expr_runtime_constant]) >>
  qpat_assum `EVERY (runtime_constant_expr mods) _`
    (fn th => rewrite_tac [MATCH_MP runtime_default_builtin_body th]) >>
  gvs[builtin_child_callback_def, supported_expr_exists_def, expr_size_def] >>
  qpat_assum `!args env rt ty bi st. _ ==> _ ==>
    EVERY _ (state_insts (SND (compile_builtin_dispatch env rt ty bi args st)))` irule >>
  simp[]
QED

Resume runtime_default_expr_terminal_opcodes[expr_struct]:
  rename1 `StructLit t ns fields` >>
  `!name e ty st. MEM (name,e) fields /\ ^default_code st ==>
    ^default_code (SND (expr_child_callback
      (expr_size (StructLit t ns fields) + cenv_defaults_size ce)
      compile_expr ce ty e st))` by
    (rpt strip_tac >>
     `expr_size e < expr_size (StructLit t ns fields)` by
       metis_tac[expr_struct_field_bound] >>
     simp[expr_child_callback_def] >>
     qpat_assum `!child env ty st. _ ==> _ ==>
       EVERY _ (state_insts (SND (compile_expr env ty child st)))` irule >>
     conj_tac >- fs[expr_size_def] >>
     qpat_assum `EVERY (runtime_constant_expr mods) _`
       (mp_tac o REWRITE_RULE [EVERY_MEM, MEM_MAP]) >>
     qpat_assum `~supported_fields_exists _ _`
       (mp_tac o REWRITE_RULE [supported_fields_exists_every, EXISTS_MEM]) >>
     gvs[] >> metis_tac[SND]) >>
  simp[Once compile_expr_body_def, LET_THM, ETA_AX, Excl "expr_child_callback_def"] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  `^default_code st2` by
    (gvs[] >> metis_tac[default_ops outcomes_free_alloc_buffer, SND]) >>
  gvs[Excl "expr_child_callback_def", ETA_AX] >>
  qpat_assum `compile_struct_lit _ _ _ _ _ _ _ = (_,st3)`
    (fn th => once_rewrite_tac[GSYM (SRULE [] (Q.AP_TERM `SND` th))]) >>
  irule (default_ops runtime_default_struct_lit_opcodes) >>
  simp[Excl "expr_child_callback_def"] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  first_assum ACCEPT_TAC
QED

Resume runtime_default_expr_terminal_opcodes[expr_subscript]:
  simp[Once compile_expr_body_def] >>
  irule every_state_insts_subscript >>
  simp[default_ops outcomes_free_keccak256_key,
       default_ops outcomes_free_mapping_subscript,
       default_ops outcomes_free_tuple_subscript,
       default_ops outcomes_free_array_subscript,
       default_ops outcomes_free_ptr_load] >>
  gvs[Excl "expr_child_callback_def"] >> rpt conj_tac
  >- (rpt strip_tac >> irule (SRULE [] runtime_default_lower_value_opcodes) >>
      gvs[Excl "expr_child_callback_def"] >> rpt strip_tac >> default_child_tac)
  >> rpt strip_tac >>
  simp[compile_snapshot_vv_def, compile_materialize_vv_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >>
  IF_CASES_TAC >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  metis_tac[default_ops runtime_default_unwrap_opcodes,
    default_ops outcomes_free_alloc_buffer, default_ops runtime_default_store_memory_opcodes, SND]
QED

Resume runtime_default_expr_terminal_opcodes[builtin]:
  simp[Excl "expr_child_callback_def"] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qabbrev_tac `lim = list_size expr_size es + cenv_defaults_size ce` >>
  `!e ty st. MEM e es /\ ^default_code st ==>
    ^default_code (SND (expr_child_callback lim compile_expr ce ty e st))` by
    (rpt strip_tac >>
     drule expr_list_member_bound >> strip_tac >>
     `runtime_constant_expr mods e` by
       (qpat_assum `EVERY (runtime_constant_expr mods) _`
         (qspec_then `e` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        simp[]) >>
     `~supported_expr_exists (^checked_default_expr ce) e` by
       (strip_tac >> qpat_assum `~supported_exprs_exists _ es` mp_tac >>
        PURE_REWRITE_TAC [supported_exprs_exists_every, EXISTS_MEM, IMP_CLAUSES, NOT_CLAUSES] >>
        qexists_tac `e` >> BETA_TAC >> conj_tac >> first_assum (ACCEPT_TAC o BETA_RULE)) >>
     gvs[Abbr `lim`, expr_child_callback_def] >>
     qpat_assum `!child env ty st. _ ==> _ ==> _`
       (qspecl_then [`e`,`ce`,`ty`,`st`] mp_tac) >>
     simp[]) >>
  `!e ty st. MEM e es /\ ^default_code st ==>
    ^default_code (SND (lower_value (expr_child_callback lim compile_expr) ce ty e st))` by
    (rpt strip_tac >> gvs[Excl "expr_child_callback_def"] >>
     irule (SRULE [] runtime_default_lower_value_opcodes) >>
     simp[Excl "expr_child_callback_def"] >> rpt strip_tac >>
     first_assum irule >> simp[]) >>
  qpat_x_assum `bi <> Sha256` mp_tac >>
  qpat_x_assum `builtin_args_length_ok bi (LENGTH es)` mp_tac >>
  qpat_x_assum `runtime_constant_builtin bi \/ constant_builtin bi` mp_tac >>
  Cases_on `bi` >>
  simp[runtime_constant_builtin_def, constant_builtin_def, vyperContextTheory.builtin_args_length_ok_def,
       DECIDE ``(p /\ q) \/ p <=> p``, Excl "expr_child_callback_def"] >>
  rpt strip_tac >>
  FIRST
    [qmatch_goalsub_abbrev_tac `compile_builtin_dispatch_body _ _ _ _ (Bop _) _ _` >>
      suspend "bop",
     qmatch_goalsub_abbrev_tac `compile_builtin_dispatch_body _ _ _ _ (MakeArray _ _) _ _` >>
      suspend "make_array",
     qmatch_goalsub_rename_tac `compile_builtin_dispatch_body _ _ _ _ NamedConst _ _` >>
      suspend "named_const",
     qmatch_goalsub_rename_tac `compile_builtin_dispatch_body _ _ _ _ (BoolChain d n) _ _` >>
      suspend "bool_chain",
     suspend "simple_builtins"]
QED

Resume runtime_default_expr_terminal_opcodes[named_const]:
  gvs[LENGTH_EQ_NUM_compute, Excl "expr_child_callback_def"] >>
  simp[compile_builtin_dispatch_body_def, Excl "expr_child_callback_def"] >>
  pairarg_tac >>
  simp[exprBopLoweringTheory.as_stack_val_pair, exprBopLoweringTheory.as_ptr_val_pair,
       COND_RAND, COND_RATOR, Excl "expr_child_callback_def"] >>
  metis_tac[SND]
QED

Resume runtime_default_expr_terminal_opcodes[bool_chain]:
  gvs[LENGTH_EQ_NUM_compute, Excl "expr_child_callback_def"] >>
  rename1 `compile_builtin_dispatch_body _ _ _ _ (BoolChain d n) [arg] _` >>
  `~supported_expr_exists (^checked_default_expr ce) arg` by
    fs[supported_exprs_exists_every] >>
  `EVERY (runtime_constant_expr mods) (bool_chain_operands d (n - 1) arg)` by
    simp[runtime_constant_bool_chain_operands] >>
  `EVERY (\e. ~supported_expr_exists (^checked_default_expr ce) e)
     (bool_chain_operands d (n - 1) arg)` by simp[bool_chain_operands_supported] >>
  `!r exit_lbl st. ^default_code st ==>
     ^default_code (SND (compile_bool_chain_ops (expr_child_callback lim compile_expr)
       ce d r exit_lbl (bool_chain_operands d (n - 1) arg) st))` by
    (rpt gen_tac >> simp[Excl "expr_child_callback_def"] >> strip_tac >>
     irule (default_ops opcode_every_bool_chain_ops) >>
     simp[Excl "expr_child_callback_def"] >>
     once_rewrite_tac[EVERY_MEM] >> qx_gen_tac `e` >> strip_tac >> BETA_TAC >>
     qx_gen_tac `st'` >> strip_tac >>
     `expr_size e <= expr_size arg` by metis_tac[bool_chain_operand_size] >>
     `cenv_defaults_size ce + expr_size e < lim` by (simp[Abbr `lim`] >> decide_tac) >>
     `expr_size e + cenv_defaults_size ce < lim` by decide_tac >>
     `runtime_constant_expr mods e /\ ~supported_expr_exists (^checked_default_expr ce) e` by
       (conj_tac
        >- (qpat_assum `EVERY (runtime_constant_expr mods) (bool_chain_operands _ _ _)`
              (qspec_then `e` mp_tac o REWRITE_RULE [EVERY_MEM]) >> simp[])
        >> qpat_assum `EVERY (\x. ~supported_expr_exists _ x) (bool_chain_operands _ _ _)`
             (qspec_then `e` mp_tac o REWRITE_RULE [EVERY_MEM]) >> simp[]) >>
     qpat_x_assum `~supported_expr_exists _ e` (assume_tac o SRULE []) >>
     irule (SRULE [] runtime_default_lower_value_opcodes) >>
     simp[Excl "expr_child_callback_def"] >> qx_gen_tac `cs` >> strip_tac >>
     simp[expr_child_callback_def] >>
     qpat_assum `!child env ty st. _ ==> _ ==> _`
       (qspecl_then [`e`, `ce`, `BaseT BoolT`, `cs`] mp_tac) >> simp[]) >>
  simp[compile_builtin_dispatch_body_def, pairTheory.ELIM_UNCURRY,
       Excl "expr_child_callback_def"] >>
  irule (default_insts every_state_insts_new_block) >>
  first_assum (irule o SRULE []) >>
  irule (default_insts every_state_insts_fresh_label) >>
  irule (default_insts every_state_insts_fresh_var) >> simp[]
QED

val default_builtin_step =
  FIRST [CHANGED_TAC (BasicProvers.TOP_CASE_TAC >> simp[Excl "expr_child_callback_def"]),
         CHANGED_TAC (IF_CASES_TAC >> simp[Excl "expr_child_callback_def"]),
         CHANGED_TAC (pairarg_tac >> simp[Excl "expr_child_callback_def"])];

Resume runtime_default_expr_terminal_opcodes[simple_builtins]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `!child env ty st. _ ==> _ ==> _` kall_tac >>
  gvs[LENGTH_EQ_NUM_compute, Excl "expr_child_callback_def"] >>
  simp[compile_builtin_dispatch_body_def, exprBopLoweringTheory.as_stack_val_pair,
       exprBopLoweringTheory.as_ptr_val_pair, Excl "expr_child_callback_def"] >>
  ntac 5 (TRY default_builtin_step) >>
  FIRST
    [irule (default_ops outcomes_free_compile_builtin_len),
     irule (default_ops outcomes_free_compile_invert),
     irule (default_ops outcomes_free_compile_neg),
     irule (default_ops outcomes_free_compile_builtin_abs),
     irule (default_ops outcomes_free_compile_env_var),
     irule (default_ops runtime_default_acc_opcodes),
     irule (default_ops outcomes_free_compile_keccak256_word),
     irule (default_ops outcomes_free_compile_keccak256_bytes),
     irule (default_ops outcomes_free_compile_keccak256_bytesm),
     irule (default_ops outcomes_free_compile_addmod),
     irule (default_ops outcomes_free_compile_mulmod),
     irule (default_ops outcomes_free_compile_pow_mod256),
     irule (default_ops outcomes_free_compile_ceil),
     irule (default_ops outcomes_free_compile_floor),
     irule (default_ops outcomes_free_compile_uint2str),
     irule (default_ops outcomes_free_compile_as_wei_value_int),
     irule (default_ops outcomes_free_compile_as_wei_value_decimal),
     irule (default_ops outcomes_free_compile_method_id_runtime),
     irule (default_ops outcomes_free_literal_vv),
     irule (SRULE [] (Q.INST [`opc` |-> `ISZERO`] (default_ops opcode_every_emit_op)))] >>
  gvs[Excl "expr_child_callback_def"] >> metis_tac[SND]
QED

Resume runtime_default_expr_terminal_opcodes[bop]:
  markerLib.RESUME_TAC >>
  gvs[LENGTH_EQ_NUM_compute, Excl "expr_child_callback_def"] >>
  rename1 `constant_binop bop` >>
  qmatch_goalsub_abbrev_tac
    `compile_builtin_dispatch_body cfn ce rt ty (Bop bop) [a;b] s` >>
  simp[compile_builtin_dispatch_body_def, exprBopLoweringTheory.as_stack_val_pair, Excl "expr_child_callback_def"] >>
  IF_CASES_TAC >- suspend "bop_membership" >>
  IF_CASES_TAC >- suspend "bop_bytes" >>
  ntac 2 (pairarg_tac >> simp[Excl "expr_child_callback_def"]) >>
  irule (default_ops runtime_default_binop_opcodes) >>
  gvs[Excl "expr_child_callback_def"] >> metis_tac[SND]
QED

Resume runtime_default_expr_terminal_opcodes[bop_bytes]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `!child env ty st. _ ==> _ ==> _` kall_tac >>
  qmatch_goalsub_rename_tac `bytestring_literal_hash a` >>
  Cases_on `bytestring_literal_hash a` >> simp[Excl "expr_child_callback_def"] >>
  qmatch_goalsub_rename_tac `bytestring_literal_hash b` >>
  Cases_on `bytestring_literal_hash b` >> simp[Excl "expr_child_callback_def"] >>
  ntac 4 (TRY default_builtin_step) >>
  FIRST [irule (SRULE [] (Q.INST [`opc` |-> `EQ`] (default_ops opcode_every_emit_op))),
         irule (SRULE [] (Q.INST [`opc` |-> `ISZERO`] (default_ops opcode_every_emit_op)))] >>
  rpt (qpat_x_assum `(\(x,y). z) arg = rhs` mp_tac >>
    pairarg_tac >> simp[Excl "expr_child_callback_def"] >> strip_tac) >>
  gvs[Excl "expr_child_callback_def"] >>
  metis_tac[default_ops outcomes_free_compile_bytestring_hash,
    SRULE [] (Q.INST [`opc` |-> `EQ`] (default_ops opcode_every_emit_op)), SND]
QED

Resume runtime_default_expr_terminal_opcodes[bop_membership]:
  markerLib.RESUME_TAC >>
  pairarg_tac >> simp[Excl "expr_child_callback_def"] >>
  rename1 `lower_value cfn ce (expr_type a) a s = (needle,st1)` >>
  `^default_code st1` by (gvs[Excl "expr_child_callback_def"] >> metis_tac[SND]) >>
  Cases_on `b` >> simp[exprBopLoweringTheory.as_stack_val_pair,
    Excl "expr_child_callback_def"] >>
  TRY (rename1 `runtime_constant_expr mods (Builtin _ builtin _)` >>
    Cases_on `builtin` >> simp[exprBopLoweringTheory.as_stack_val_pair,
      Excl "expr_child_callback_def"]) >>
  pairarg_tac >> simp[Excl "expr_child_callback_def"] >>
  TRY (qmatch_goalsub_rename_tac `compile_list_membership_in _ _ _` >>
    suspend "bop_member_literal") >>
  irule (default_ops outcomes_free_compile_var_array_membership) >>
  qpat_assum `cfn ce _ _ st1 = (_, _)` (fn eq =>
    qpat_assum `!e ty st. _ ==> EVERY _ (state_insts (SND (cfn ce ty e st)))`
      (fn callback =>
        let
          val [_,ty,e,st] = snd (strip_comb (lhs (concl eq)))
        in
          mp_tac (REWRITE_RULE [eq,SND] (SPECL [e,ty,st] callback))
        end)) >>
  qpat_assum `^default_code st1`
    (fn th => simp[SRULE [] th, Excl "expr_child_callback_def"])
QED

Resume runtime_default_expr_terminal_opcodes[make_array]:
  markerLib.RESUME_TAC >>
  qmatch_goalsub_rename_tac
    `compile_builtin_dispatch_body _ _ _ _ (MakeArray element_type _) _ _` >>
  qpat_x_assum `!child env ty st. _ ==> _ ==> _` kall_tac >>
  Cases_on `element_type` >>
  simp[compile_builtin_dispatch_body_def, exprBopLoweringTheory.as_ptr_val_pair,
       Excl "expr_child_callback_def"] >>
  pairarg_tac >> gvs[Excl "expr_child_callback_def"] >>
  FIRST [irule (default_ops runtime_default_make_tuple_opcodes),
         irule (default_ops runtime_default_make_array_opcodes)] >>
  gvs[] >> rpt strip_tac >>
  metis_tac[default_ops outcomes_free_alloc_buffer, SND]
QED

Resume runtime_default_expr_terminal_opcodes[bop_member_literal]:
  markerLib.RESUME_TAC >>
  rename1 `compile_multi_exprs cfn ce items st1 = (ops,st2)` >>
  rename1 `runtime_constant_expr mods (Builtin ann (MakeArray ety cap) items)` >>
  `^default_code (SND (compile_multi_exprs cfn ce items st1))` by
    (simp[NoAsms, Excl "expr_child_callback_def"] >>
     irule (SRULE [] runtime_default_multi_exprs_opcodes) >>
     qpat_assum `^default_code st1` (fn th => simp[SRULE [] th]) >>
     rpt strip_tac >> irule (SRULE [] runtime_default_lower_value_opcodes) >>
     asm_rewrite_tac[] >> rpt strip_tac >>
     `runtime_constant_expr mods e /\ ~supported_expr_exists (^checked_default_expr ce) e` by
       (irule runtime_default_literal_items >>
        qexistsl_tac [`cap`,`ety`,`items`,`ann`] >>
        simp[] >> metis_tac[supported_exprs_exists_every, EXISTS_MEM, MEM]) >>
     `expr_size e < list_size expr_size items` by metis_tac[expr_list_member_bound] >>
     `list_size expr_size items < expr_size (Builtin ann (MakeArray ety cap) items)` by
       simp[expr_builtin_dispatch_bound] >>
     `expr_size e + cenv_defaults_size ce < lim` by (simp[Abbr `lim`] >> decide_tac) >>
     qpat_assum `Abbrev (cfn = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     gvs[expr_child_callback_def] >>
     qpat_assum `!child env ty st. _ ==> _ ==> _`
       (qspecl_then [`e`,`ce`,`expr_type e`,`st`] mp_tac) >>
     simp[]) >>
  IF_CASES_TAC >> simp[exprBopLoweringTheory.as_stack_val_pair,
    default_ops outcomes_free_compile_list_membership_in,
    default_ops outcomes_free_compile_list_membership_notin] >>
  gvs[default_ops outcomes_free_compile_list_membership_in,
      default_ops outcomes_free_compile_list_membership_notin]
QED

Finalise runtime_default_expr_terminal_opcodes

Theorem runtime_default_omitted_init_opcodes:
  !vars off hi s.
    EVERY (\(_,_,_,e).
      runtime_constant_expr mods e /\ ~supported_expr_exists (^checked_default_expr ce) e) vars /\
    acyclic_struct_metadata ce.ce_struct_fields /\ ^default_code s ==>
    ^default_code (SND (compile_init_kwargs ce vars off 0 hi s))
Proof
  Induct >- simp[compile_init_kwargs_def, every_state_insts_return] >>
  gen_tac >> PairCases_on `h` >> simp[compile_init_kwargs_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  irule every_state_insts_bind >> rpt conj_tac
  >~ [`lower_value compile_expr`] >-
    (rpt strip_tac >> irule (SRULE [] runtime_default_lower_value_opcodes) >>
     simp[] >> rpt strip_tac >>
     irule (SRULE [] (cj 1 runtime_default_expr_terminal_opcodes)) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     qexists_tac `mods` >> simp[])
  >~ [`comp_ignore_bind`] >-
    (rpt strip_tac >> simp[] >> irule every_state_insts_ignore_bind >> rpt conj_tac
     >~ [`emit_void MSTORE`] >-
       (rpt strip_tac >> IF_CASES_TAC >>
        simp[default_ops opcode_every_emit_void] >>
        IF_CASES_TAC >>
        simp[default_ops opcode_every_emit_void,
             DISCH_ALL (cj 2 (UNDISCH (default_ops outcomes_free_bytestring_copy)))])
     >> rpt strip_tac >> first_assum (irule o SRULE []) >> simp[])
  >> simp[]
QED

Theorem runtime_default_init_opcodes[local]:
  !vars off k hi s.
    EVERY (\(_,_,_,e).
      runtime_constant_expr mods e /\ ~supported_expr_exists (^checked_default_expr ce) e) vars /\
    acyclic_struct_metadata ce.ce_struct_fields /\ ^default_code s ==>
    ^default_code (SND (compile_init_kwargs ce vars off k hi s))
Proof
  Induct >- simp[compile_init_kwargs_def, every_state_insts_return] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> Cases_on `k`
  >- metis_tac[runtime_default_omitted_init_opcodes] >>
  simp[compile_init_kwargs_def] >> strip_tac >>
  rpt (FIRST [irule every_state_insts_bind >> rpt conj_tac,
              irule every_state_insts_ignore_bind >> rpt conj_tac,
              gen_tac, strip_tac, IF_CASES_TAC,
              CHANGED_TAC (simp[default_ops opcode_every_emit_op,
                default_ops outcomes_free_abi_arg_ptr_guard, every_state_insts_return,
                cj 1 (default_ops outcomes_free_abi_decode)])]) >>
  first_assum (irule o SRULE []) >> simp[]
QED

Theorem runtime_default_init_blocks_frame[local]:
  !vars off k hi. deploy_blocks_frame (compile_init_kwargs ce vars off k hi)
Proof
  Induct >- simp[compile_init_kwargs_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> simp[compile_init_kwargs_def] >>
  rpt (FIRST [match_mp_tac deploy_blocks_frame_bind >> conj_tac,
              match_mp_tac deploy_blocks_frame_ignore_bind >> conj_tac,
              gen_tac, IF_CASES_TAC,
              CHANGED_TAC (simp[deploy_blocks_frame_emit_op,
                deploy_blocks_frame_emit_void, deploy_blocks_frame_lower_value,
                deploy_blocks_frame_unwrap_value, deploy_blocks_frame_store_bytestring,
                deploy_blocks_frame_abi_decode_to_buf, compile_abi_arg_ptr_guard_def])])
QED

Theorem runtime_default_init_fragment_opcodes:
  EVERY (\(_,_,_,e).
    runtime_constant_expr mods e /\ ~supported_expr_exists (^checked_default_expr ce) e) vars /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  EVERY (\i. ^default_opcode i.inst_opcode) sa.cs_current_insts /\
  compile_init_kwargs ce vars off k hi sa = ((),sb) ==>
  EVERY (\i. ^default_opcode i.inst_opcode) (frag_code sa sb)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `s0 = sa with cs_blocks := []` >>
  Cases_on `compile_init_kwargs ce vars off k hi s0` >> Cases_on `q` >>
  `s0 with cs_blocks := s0.cs_blocks ++ sa.cs_blocks = sa` by simp[Abbr `s0`] >>
  mp_tac (REWRITE_RULE [deploy_blocks_frame_def]
    (Q.SPECL [`vars`,`off`,`k`,`hi`] runtime_default_init_blocks_frame)) >>
  disch_then (qspecl_then [`s0`,`sa.cs_blocks`,`()`,`r`] mp_tac) >>
  simp[] >> strip_tac >>
  `emitted_blocks sa sb = r.cs_blocks /\ emitted_blocks s0 r = r.cs_blocks` by
    (rpt conj_tac >> irule emitted_blocks_append >> simp[Abbr `s0`]) >>
  `frag_code s0 r = frag_code sa sb` by
    simp[frag_code_def, emitted_insts_def, Abbr `s0`] >>
  `^default_code s0` by fs[state_insts_def, all_blocks_def, Abbr `s0`] >>
  `^default_code r` by
    (mp_tac (Q.SPECL [`vars`,`off`,`k`,`hi`,`s0`] runtime_default_init_opcodes) >>
     asm_rewrite_tac[]) >>
  fs[EVERY_MEM] >> metis_tac[frag_code_in_state_insts]
QED

val sha256_root = ``\e. case e of Builtin _ Sha256 _ => T | _ => F``;

Theorem runtime_default_sha256_roots[local]:
  (!e. no_sha256_expr e <=> ~supported_expr_exists ^sha256_root e) /\
  (!bt. no_sha256_btarget bt <=> ~supported_target_exists ^sha256_root bt) /\
  (!es. no_sha256_exprs es <=> ~supported_exprs_exists ^sha256_root es) /\
  (!opt. no_sha256_opt opt <=> ~supported_opt_exists ^sha256_root opt) /\
  (!fs. no_sha256_fields fs <=> ~supported_fields_exists ^sha256_root fs)
Proof
  ho_match_mp_tac no_sha256_expr_ind >>
  simp[no_sha256_expr_def, supported_expr_exists_def] >>
  rpt gen_tac >> CASE_TAC >> simp[]
QED

val bad_arity_root = ``\e. case e of
    Builtin _ bi args => ~builtin_args_length_ok bi (LENGTH args)
  | TypeBuiltin _ tb _ args => ~type_builtin_args_length_ok tb (LENGTH args)
  | _ => F``;

val bad_immutable_root = ``\ce e. case e of
    TopLevelName _ id => ~(?offset. FLOOKUP ce.ce_module_vars id = SOME (ImmutableLoc offset))
  | _ => F``;

Theorem runtime_default_replacement_no_global[local]:
  (!e. constant_expr [(NONE,tops)] e /\ const_local_refs e = [] ==>
    ~supported_expr_exists (^bad_immutable_root ce) e) /\
  (!es. EVERY (constant_expr [(NONE,tops)]) es /\ const_local_exprs es = [] ==>
    ~supported_exprs_exists (^bad_immutable_root ce) es) /\
  (!fs. EVERY (constant_expr [(NONE,tops)]) (MAP SND fs) /\ const_local_fields fs = [] ==>
    ~supported_fields_exists (^bad_immutable_root ce) fs)
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[constant_expr_def, const_local_refs_def, supported_expr_exists_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  PairCases_on `ns` >> Cases_on `ns0` >>
  gvs[constant_expr_def, declared_constant_def, const_local_refs_def]
QED
val default_replacements = ``\tops ce E.
  (!id e. ALOOKUP E id = SOME e ==>
    constant_expr [(NONE,tops)] e /\ const_local_refs e = []) /\
  (!id. declared_constant [((NONE:num option),tops)] NONE id ==> IS_SOME (ALOOKUP E id)) /\
  (!id. declared_immutable [((NONE:num option),tops)] NONE id ==>
    ?off. FLOOKUP ce.ce_module_vars (NONE,id) = SOME (ImmutableLoc off))``;

Theorem runtime_default_substitution_locations[local]:
  ^default_replacements tops ce E0 ==>
  (!E e. E = E0 /\ runtime_constant_expr [(NONE,tops)] e ==>
    ~supported_expr_exists (^bad_immutable_root ce) (subst_consts_expr E e)) /\
  (!E bt. subst_consts_btarget E bt = subst_consts_btarget E bt) /\
  (!E es. E = E0 /\ EVERY (runtime_constant_expr [(NONE,tops)]) es ==>
    ~supported_exprs_exists (^bad_immutable_root ce) (subst_consts_exprs E es)) /\
  (!E opt. subst_consts_opt E opt = subst_consts_opt E opt) /\
  (!E fs. E = E0 /\ EVERY (runtime_constant_expr [(NONE,tops)]) (MAP SND fs) ==>
    ~supported_fields_exists (^bad_immutable_root ce) (subst_consts_fields E fs))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  ho_match_mp_tac subst_consts_expr_ind >>
  simp[runtime_constant_expr_def, subst_consts_expr_def, supported_expr_exists_def] >>
  (let
     val top_level_name =
       Cases_on `ns` >> gvs[declared_constant_def, declared_immutable_def] >>
       Cases_on `ALOOKUP E0 id` >> gvs[supported_expr_exists_def]
       >- (qpat_assum `!n. _ ==> IS_SOME (ALOOKUP E0 n)` (qspec_then `id` mp_tac) >>
           qpat_assum `!n. _ ==> ?off. FLOOKUP _ (NONE,n) = SOME _` (qspec_then `id` mp_tac) >>
           simp[] >> metis_tac[]) >>
       `constant_expr [(NONE,tops)] x /\ const_local_refs x = []` by
         (qpat_assum `!id e. ALOOKUP E0 id = SOME e ==> _` drule >> simp[]) >>
       mp_tac (Q.SPEC `x` (cj 1 runtime_default_replacement_no_global)) >> simp[]
   in
     (rpt strip_tac >> gvs[])
     >- top_level_name
     >- top_level_name
   end) >>
  TRY (`EVERY (runtime_constant_expr [(NONE,tops)]) es` by
    (irule EVERY_MONOTONIC >> qexists_tac `constant_expr [(NONE,tops)]` >>
     simp[constant_expr_runtime_constant])) >>
  res_tac >> gvs[] >>
  `~EVERY (runtime_constant_expr [(NONE,tops)]) es` by
    (PURE_REWRITE_TAC [NOT_EVERY] >> first_assum ACCEPT_TAC) >>
  metis_tac[]
QED

Theorem runtime_default_checked_replacements[local]:
  check_contract F layouts addr [(NONE,tops)] = SOME art ==>
  ((!id e. ALOOKUP (module_consts_env tops []) id = SOME e ==>
      constant_expr [(NONE,tops)] e /\ const_local_refs e = []) /\
   (!id. declared_constant [((NONE:num option),tops)] NONE id ==>
     IS_SOME (ALOOKUP (module_consts_env tops []) id)))
Proof
  strip_tac >>
  `contract_constants_ok [(NONE,tops)]` by
    (qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
     simp[check_contract_def, AllCaseEqs()]) >>
  `?imms A. constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME A` by
    (qpat_x_assum `contract_constants_ok _` mp_tac >>
     simp[contract_constants_ok_def, constants_order_def, constants_fold_def] >>
     Cases_on `initial_immutables (type_env_all_modules [(NONE,tops)]) [(NONE,tops)]` >>
     simp[optionTheory.IS_SOME_EXISTS] >>
     Cases_on `constants_fold_module [(NONE,tops)] x NONE tops FEMPTY` >> simp[] >>
     metis_tac[]) >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`,`mode` |-> `F`,
    `artifact` |-> `art`] checked_module_consts_env_agrees) >>
  asm_simp_tac std_ss [ALOOKUP_def] >> simp[] >>
  strip_tac >> fs[const_acc_agrees_def, const_prefix_syntax_def] >>
  conj_tac >- metis_tac[] >>
  simp[declared_constant_def] >> rpt strip_tac >>
  `MEM id (const_decl_names tops)` by metis_tac[const_decl_names_MEM] >>
  Cases_on `ALOOKUP (module_consts_env tops []) id` >>
  gvs[ALOOKUP_NONE] >> metis_tac[]
QED

Theorem runtime_default_combine_syntax[local]:
  !p q r e. ~supported_expr_exists p e /\ ~supported_expr_exists q e /\
    ~supported_expr_exists r e ==>
    ~supported_expr_exists (\x. p x \/ q x \/ r x) e
Proof
  simp[supported_expr_exists_disj]
QED

Theorem runtime_default_checked_syntax[local]:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  runtime_constant_expr [(NONE,tops)] e /\
  well_typed_expr (artifact_env art [(NONE,tops)] NONE)
    (subst_consts_expr (module_consts_env tops []) e) /\
  no_sha256_expr (subst_consts_expr (module_consts_env tops []) e) /\
  (!id. declared_immutable [((NONE:num option),tops)] NONE id ==>
    ?off. FLOOKUP ce.ce_module_vars (NONE,id) = SOME (ImmutableLoc off)) ==>
  ~supported_expr_exists (^checked_default_expr ce) (subst_consts_expr (module_consts_env tops []) e)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `^default_replacements tops ce (module_consts_env tops [])` by
    (simp[] >> drule runtime_default_checked_replacements >>
     disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `~supported_expr_exists (^bad_immutable_root ce)
      (subst_consts_expr (module_consts_env tops []) e)` by
    (mp_tac (Q.INST [`E0` |-> `module_consts_env tops []`] runtime_default_substitution_locations) >>
     asm_rewrite_tac[] >>
     disch_then (qspecl_then [`module_consts_env tops []`,`e`] mp_tac o cj 1) >>
     asm_rewrite_tac[]) >>
  `~supported_expr_exists ^bad_arity_root
      (subst_consts_expr (module_consts_env tops []) e)` by
    metis_tac[cj 1 well_typed_expr_builtin_args_length] >>
  `~supported_expr_exists ^sha256_root
      (subst_consts_expr (module_consts_env tops []) e)` by
    metis_tac[cj 1 runtime_default_sha256_roots] >>
  `^checked_default_expr ce = (\e. ^bad_immutable_root ce e \/ ^bad_arity_root e \/ ^sha256_root e)` by
    (simp[FUN_EQ_THM] >> Cases >> simp[] >> Cases_on `b` >> simp[]) >>
  qpat_x_assum `^checked_default_expr ce = _` SUBST1_TAC >>
  BETA_TAC >> RULE_ASSUM_TAC BETA_RULE >>
  MATCH_MP_TAC (BETA_RULE (Q.SPECL
    [`^bad_immutable_root ce`,`^bad_arity_root`,`^sha256_root`,
     `subst_consts_expr (module_consts_env tops []) e`]
    runtime_default_combine_syntax)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem runtime_default_entry_checks_opcodes:
  compile_entry_checks minimum payable sa = ((),sb) /\
  EVERY (\i. ^default_opcode i.inst_opcode) sa.cs_current_insts ==>
  EVERY (\i. ^default_opcode i.inst_opcode) sb.cs_current_insts
Proof
  Cases_on `payable` >> Cases_on `4 < minimum` >>
  simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[EVERY_APPEND, mk_inst_def]
QED

Theorem runtime_default_package_fields[local]:
  package_external_group tops target tr keys (mut,nr,rr,name,args,defaults,ret,body) =
    ExternalDefaults common entries specs off ==>
  common.ec_env.ce_struct_fields = make_struct_fields_map tops /\
  (!id. declared_immutable [((NONE:num option),tops)] NONE id ==>
    ?offset. FLOOKUP common.ec_env.ce_module_vars (NONE,id) = SOME (ImmutableLoc offset)) /\
  specs = MAP (\((name,ty),e). (name,ty,e)) (ZIP (DROP (LENGTH args - LENGTH defaults) args, defaults))
Proof
  simp[package_external_group_def, package_external_fn_def, set_external_package_target_def,
     LET_THM, update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
  rpt CASE_TAC >> strip_tac >>
  gvs[build_compile_env_ce_struct_fields, declared_immutable_def] >> rpt strip_tac >> metis_tac[immutable_build_compile_env_declared]
QED

Theorem runtime_default_checked_external_syntax[local]:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  MEM (mut,nr,rr,name,args,defaults,ret,body) (FST (classify_functions tops)) /\
  no_sha256_exprs defaults /\
  (!id. declared_immutable [((NONE:num option),tops)] NONE id ==>
    ?off. FLOOKUP ce.ce_module_vars (NONE,id) = SOME (ImmutableLoc off)) ==>
  LENGTH defaults <= LENGTH args /\
  EVERY (\e. runtime_constant_expr [(NONE,tops)] e /\
    ~supported_expr_exists (^checked_default_expr ce) e) defaults
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule classify_functions_external_source >> strip_tac >>
  gvs[subst_consts_fn_def]
  >- (`External <> Deploy` by simp[] >>
      drule_all check_contract_single_body >>
      simp[check_function_body_def, defaults_env_function_entry_env,
        consts_env_mods_singleton, subst_consts_mods_singleton] >> strip_tac >>
      `LENGTH rawdefaults <= LENGTH args` by
        (qpat_assum `MAP expr_type rawdefaults = _`
          (mp_tac o AP_TERM (Term `LENGTH : type list -> num`)) >>
         simp[LENGTH_DROP] >> decide_tac) >>
      asm_simp_tac (srw_ss()) [subst_consts_exprs_map, EVERY_MAP, combinTheory.o_DEF] >>
      `!id r. ALOOKUP (module_consts_env tops []) id = SOME r ==>
         constant_expr [(NONE,tops)] r` by
        (rpt strip_tac >> irule checked_module_consts_env_replacement_constant >>
         simp[] >> conj_tac
         >- (qexistsl_tac [`addr`,`art`,`layouts`,`F`] >> simp[]) >>
         qexists_tac `id` >> simp[]) >>
      fs[cj 1 no_sha256_collections, subst_consts_exprs_map, frame_well_typed_exprs_every, EVERY_MAP, combinTheory.o_DEF] >>
      simp[EVERY_MEM] >> qx_gen_tac `e` >> strip_tac >>
      `runtime_constant_expr [(NONE,tops)] e` by metis_tac[EVERY_MEM] >>
      `runtime_constant_expr [(NONE,tops)] (subst_consts_expr (module_consts_env tops []) e)` by
        (irule subst_const_runtime_constant >> simp[] >> first_assum ACCEPT_TAC) >>
      `well_typed_expr (artifact_env art [(NONE,tops)] NONE)
          (subst_consts_expr (module_consts_env tops []) e)` by
        (qpat_assum `EVERY (\x. well_typed_expr _ _) rawdefaults`
           (qspec_then `e` mp_tac o REWRITE_RULE [EVERY_MEM]) >> simp[]) >>
      `no_sha256_expr (subst_consts_expr (module_consts_env tops []) e)` by
        (qpat_assum `EVERY (\x. no_sha256_expr _) rawdefaults`
           (qspec_then `e` mp_tac o REWRITE_RULE [EVERY_MEM]) >> simp[]) >>
      mp_tac (Q.INST [`e` |-> `e`] runtime_default_checked_syntax) >>
      simp[]) >>
  drule public_getter_defaults >> simp[subst_consts_exprs_map]
QED

Theorem runtime_default_checked_package:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  MEM (mut,nr,rr,name,args,defaults,ret,body) (FST (classify_functions tops)) /\
  no_sha256_exprs defaults /\
  package_external_group tops target tr keys (mut,nr,rr,name,args,defaults,ret,body) =
    ExternalDefaults common entries specs off ==>
  EVERY (\(_,_,e). runtime_constant_expr [(NONE,tops)] e /\
    ~supported_expr_exists (^checked_default_expr common.ec_env) e) specs /\
  acyclic_struct_metadata common.ec_env.ce_struct_fields
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule runtime_default_package_fields >> strip_tac >>
  mp_tac (Q.INST [`ce` |-> `common.ec_env`]
    runtime_default_checked_external_syntax) >>
  asm_rewrite_tac[] >> strip_tac >>
  conj_tac >-
    (simp[EVERY_MEM, MEM_MAP] >> rpt strip_tac >>
     gvs[] >> rename1 `MEM x (ZIP _)` >> PairCases_on `x` >> gvs[] >>
     `LENGTH (DROP (LENGTH args - LENGTH defaults) args) = LENGTH defaults` by
       (simp[LENGTH_DROP] >> decide_tac) >>
     imp_res_tac MEM_ZIP >>
     `MEM x2 defaults` by
       (qpat_assum `((x0,x1),x2) = (EL n _, EL n defaults)`
          (mp_tac o AP_TERM (Term `SND : argument # expr -> expr`)) >>
        simp[] >> disch_then SUBST1_TAC >> irule EL_MEM >> decide_tac) >>
     qpat_assum `EVERY _ defaults` (qspec_then `x2` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     simp[]) >>
  qpat_assum `common.ec_env.ce_struct_fields = _` SUBST1_TAC >>
  drule_all checked_struct_metadata_acyclic >> simp[]
QED
