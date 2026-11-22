Theory ctorCallFreeBoolChain
Ancestors
  list pair arithmetic vyperAST compileEnv context emitHelper venomInst
  exprLowering loweringShapeDefs ctorCallFreeRules vyperCompiler
  boolChainOperandsGuarded boolChainOperandsSupported exprCallBounds
  supportedExprTraverse ctorCallFreeCallbacks

Theorem bool_chain_operand_size:
  MEM child (bool_chain_operands d k e) ==> expr_size child <= expr_size e
Proof
  `!b k e. expr_size e <= b ==>
    EVERY (\child. expr_size child <= b) (bool_chain_operands d k e)` by
    (gen_tac >> ho_match_mp_tac (Q.INST [`G` |-> `\c:expr. T`] bool_chain_operands_guarded) >>
     simp[expr_size_def] >> decide_tac) >>
  gvs[EVERY_MEM] >> metis_tac[LESS_EQ_REFL]
QED

(* A fixed memory array emits each of the three BoolChain control opcodes.
   The existing uniform membership-frame hypothesis therefore supplies them. *)
Theorem array_membership_frame_chain_opcodes:
  (!v vv t isin st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts
      (SND (compile_var_array_membership ce v vv t isin st)))) ==>
  P ASSIGN /\ P JMP /\ P JNZ
Proof
  disch_then (qspecl_then
    [`Lit 0w`, `StackValue (BaseT BoolT) (Lit 0w)`,
     `ArrayT (BaseT BoolT) (Fixed 1)`, `T`, `initial_compile_state ""`] mp_tac) >>
  simp[compile_var_array_membership_def, compile_array_membership_loop_def,
       vv_operand_def, vv_location_def, compile_ptr_load_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, initial_compile_state_def,
       fresh_var_def, fresh_label_def, fresh_id_def, new_block_def, emit_def,
       emit_inst_def, emit_op_def, state_insts_def, all_blocks_def, mk_inst_def]
QED

Theorem opcode_every_bool_chain_ops:
  P ASSIGN /\ P JMP /\ P JNZ ==>
  !es. EVERY (\e. !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts
      (SND (lower_value cfn cenv (BaseT BoolT) e st)))) es ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts
      (SND (compile_bool_chain_ops cfn cenv is_and result exit es st)))
Proof
  strip_tac >> Induct_on `es`
  >- simp[compile_bool_chain_ops_def, every_state_insts_return] >>
  gen_tac >> simp[EVERY_DEF] >> strip_tac >>
  rename1 `compile_bool_chain_ops _ _ _ _ _ (e::es)` >>
  Cases_on `es` >> Cases_on `is_and` >>
  once_rewrite_tac[compile_bool_chain_ops_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    CHANGED_TAC (simp[every_state_insts_return, every_state_insts_fresh_label,
      every_state_insts_new_block, opcode_every_emit_inst]), gen_tac])
QED

Theorem opcode_every_bool_chain_children:
  (!e ety st. expr_size e < list_size expr_size args /\
      ~supported_expr_exists R e /\ ~supported_expr_exists Q e ==>
    EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (cfn cenv ety e st)))) /\
  (!vv st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (unwrap_value cenv vv st)))) /\
  ~supported_exprs_exists R args /\ ~supported_exprs_exists Q args /\
  MEM arg args ==>
  EVERY (\e. !st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (lower_value cfn cenv (BaseT BoolT) e st))))
    (bool_chain_operands d k arg)
Proof
  strip_tac >>
  `expr_size arg < list_size expr_size args` by simp[expr_list_member_bound] >>
  `~supported_expr_exists R arg /\ ~supported_expr_exists Q arg` by
    (fs[supported_exprs_exists_every, EXISTS_MEM] >> metis_tac[]) >>
  `EVERY (\e. ~supported_expr_exists R e) (bool_chain_operands d k arg) /\
   EVERY (\e. ~supported_expr_exists Q e) (bool_chain_operands d k arg)` by
    simp[bool_chain_operands_supported] >>
  once_rewrite_tac[EVERY_MEM] >> qx_gen_tac `child` >> strip_tac >>
  `expr_size child <= expr_size arg` by metis_tac[bool_chain_operand_size] >>
  `expr_size child < list_size expr_size args` by decide_tac >>
  BETA_TAC >> ho_match_mp_tac every_state_insts_lower_value >> simp[] >>
  rpt strip_tac >>
  qpat_assum `!e ety st. expr_size e < _ /\ _ ==> _` irule >>
  fs[EVERY_MEM]
QED
