Theory deployOutcomesFreeBody
Ancestors
  deployOutcomesFreeExpressions deployOutcomesFreeStatements
  deployOutcomesFreeConstructorTyping deployOutcomesFreeGenerators
  deployOutcomesFreeExprGenerators deployOutcomesFreeStmtLog
  deployOutcomesFreeStmtValues deployOutcomesFreeAbiGenerators
  supportedStmtTraverse deployOutcomesFreeBodyGenerators
  exprLowering deployOutcomesFreeLowering

val safe_generators = map
  (SRULE [DISJ_IMP_THM, FORALL_AND_THM] o
   Q.INST [`P` |-> `\opc. ~MEM opc
     [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]`])
  [outcomes_free_unwrap_value, outcomes_free_alloc_buffer,
   outcomes_free_store_memory, cj 1 outcomes_free_typed_copy,
   outcomes_free_copy_memory, outcomes_free_dynarray_to_storage,
   outcomes_free_slot_copies, outcomes_free_imm_store,
   outcomes_free_store_immutable_bytestring, outcomes_free_imm_store_words,
   outcomes_free_load_memory, outcomes_free_binop, outcomes_free_bytelike_literal,
   outcomes_free_nonreentrant, outcomes_free_ptr_load,
   outcomes_free_slot_to_memory, outcomes_free_imm_copy,
   outcomes_free_compile_log_save_arg, outcomes_free_compile_log_topic_ops,
   outcomes_free_compile_log_store_data,
   outcomes_free_compile_revert_with_reason, outcomes_free_compile_external_return,
   outcomes_free_snapshot, outcomes_free_dynarray_append,
   cj 1 outcomes_free_word_copy, cj 2 outcomes_free_abi_encode,
   outcomes_free_encode_log_topic];

Theorem outcomes_free_compile_stmts:
  !ce lc ty sts env ret out s.
    type_stmts env ret sts = SOME out /\
    ~supported_stmts_expr_exists constructor_call_root sts /\
    EVERY (\i. ~MEM i.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (state_insts s) ==>
    EVERY (\i. ~MEM i.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
      (state_insts (SND (compile_stmts ce lc ty sts s)))
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (SRULE [] (Q.INST [`P` |-> `\opc. ~MEM opc
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]`]
    outcomes_free_compile_stmts_conditional)) >>
  impl_tac >- (simp safe_generators >>
    conj_tac >- metis_tac[SRULE [] outcomes_free_compile_expr] >>
    conj_tac >- metis_tac[SRULE [] outcomes_free_compile_get_target_ptr] >>
    conj_tac >- (rpt gen_tac >> strip_tac >>
      irule (List.nth (safe_generators, 23)) >> simp safe_generators >>
      gvs[] ) >>
    rpt gen_tac >> strip_tac >>
    irule (List.nth (safe_generators, 17)) >> simp[] >>
    rpt gen_tac >> strip_tac >>
    simp[compile_materialize_vv_def] >>
    irule outcomes_free_bind >> simp safe_generators >>
    rpt gen_tac >> strip_tac >> BETA_TAC >>
    irule outcomes_free_bind >> simp safe_generators >>
    rpt gen_tac >> strip_tac >> BETA_TAC >>
    irule outcomes_free_ignore_bind >> simp (outcomes_free_return :: safe_generators)) >>
  gvs[] >> metis_tac[]
QED

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
  gvs[GSYM outcomes_free_all_blocks] >>
  irule (SRULE [] outcomes_free_compile_stmts) >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED
