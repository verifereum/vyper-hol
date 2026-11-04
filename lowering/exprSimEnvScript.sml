(* Counted simulation for gas-independent environment reads. *)
Theory exprSimEnv
Ancestors
  exprSimProps
  exprSimDefs exprSimStack exprSimValues
  loweringPosts
  list rich_list finite_map pred_set
  fragExec varsExt loweringSlice localPtrsProps venomMemDefs
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperValueOperation vyperContext
  valueEncoding valueEncodingProofs vyperTypeSystem
  venomExecSemantics venomInst venomState
  vyperLookupStorage vyperStorageBackend

Theorem compile_env_sim:
  !ctx func cenv cx ty ann item es.
    item <> PrevHash /\ item <> MsgGas /\ ann = env_item_type item ==>
    expr_sim ctx func cenv cx ty (Builtin ann (Env item) []) es
Proof
  rpt strip_tac >> irule expr_sim_values >>
  conj_tac >~ [`expr_res_ok _`]
  >- (rpt strip_tac >> drule_all eval_expr_env >> strip_tac >> simp[]) >>
  rpt strip_tac >>
  `expr_res_ok (INL v : value + exception)` by
    simp[expr_res_ok_def] >>
  drule_all eval_expr_env >> strip_tac >> gvs[] >>
  `is_word_type (env_item_type item) /\
   !tv. evaluate_type (get_tenv cx) (env_item_type item) = SOME tv ==>
        typed_val_to_w256 tv v = val_to_w256 v` by
    (Cases_on `item` >>
     gvs[evaluate_builtin_def, env_item_type_def, is_word_type_def,
         vyperValueTheory.evaluate_type_def, typed_val_to_w256_def,
         val_to_w256_def] >>
     simp_tac (srw_ss() ++ wordsLib.SIZES_ss) []) >>
  drule lower_value_env >> strip_tac >>
  irule frag_exec_conseq >>
  qexistsl_tac [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s`,
                `\s. stmt_state_rel ctx func cenv cx es s /\
                     eval_operand op s = SOME (val_to_w256 v) /\
                     (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                            lookup_var x s = SOME w) /\
                     (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                              FLOOKUP s.vs_allocas aid = SOME b) /\
                     s.vs_memory = s0.vs_memory`,
                `\r. F`] >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, locals_kept_mem] >>
  Cases_on `item` >>
  gvs[compile_env_var_def, evaluate_builtin_def] >>
  drule emit_op_frag >> disch_then irule >>
  simp[is_terminator_def] >> rpt strip_tac >>
  simp[step_inst_base_opcode_eqs, exec_read0_def, exec_gas_def, venomInstTheory.mk_inst_def] >>
  fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
     val_to_w256_address, val_to_w256_def, integer_wordTheory.i2w_def]
QED
