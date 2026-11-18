Theory deployOutcomesFreeBody
Ancestors
  ctorCallFreeRules ctorCallFreeExpr ctorCallFreeStmt ctorCallFreeSource
  deployOutcomesFreeConstructorTyping ctorDeployDefs e2eDeployDefs compileVyper
  supportedStmtTraverse

(* The constructor's statements are an instance of the precise statement
   lemma: the excluded opcodes are the six call and create opcodes, and every
   call or precompile root is ruled out by constructor_call_root. *)
val outcomes_free_instance =
  SRULE [constructor_call_root_def] o
  Q.INST [`P` |-> `\opc. ~MEM opc
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]`,
    `R` |-> `constructor_call_root`]

(* Source typing belongs to the selected constructor, independently of the
   compiler environment and return convention used for its lowering. *)
Theorem outcomes_free_constructor_body:
  !tops am tx ctor target use_trans nkeys cenv args pay nr key ut fbody ret
    ce lc ty s.
  deploy_source_ok tops am tx /\
  SND (SND (SND (classify_functions tops))) = ctor /\
  ctor_named_init ctor /\
  set_constructor_package_target target
    (case ctor of
       SOME cf => package_constructor tops use_trans nkeys cf
     | NONE => (ARB, ([] : (string # bool # bool # num # abi_dec_info) list),
                F, F, 0n, F, ([] : stmt list), NoneT)) =
    (cenv,args,pay,nr,key,ut,fbody,ret) /\
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
    bb.bb_instructions) (all_blocks s) ==>
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
    bb.bb_instructions) (all_blocks (SND (compile_stmts ce lc ty fbody s)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all outcomes_free_constructor_package_source >> strip_tac >>
  `~supported_stmts_expr_exists expr_shape_root fbody` by
    (Cases_on `ctor`
     >- gvs[set_constructor_package_target_def, supported_stmt_expr_exists_def] >>
     rename1 `ctor_named_init (SOME cf)` >> PairCases_on `cf` >>
     gvs[set_constructor_package_target_def, package_constructor_def,
         ctor_named_init_def, deploy_source_ok_def] >>
     drule_all (cj 2 named_constructor_call_free_source) >> simp[]) >>
  gvs[GSYM ctorCallFreeRulesTheory.every_state_insts_blocks] >>
  mp_tac (outcomes_free_instance outcomes_free_compile_stmt_stmts_from_expr) >>
  simp[] >> impl_tac
  >- (rpt strip_tac >>
      irule (outcomes_free_instance outcomes_free_compile_expr) >> simp[]) >>
  strip_tac >> first_x_assum irule >> simp[]
QED
