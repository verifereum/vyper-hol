Theory bodyIntCallExprFrame
Ancestors
  exprSim bodyIntCallSemanticFrame loweringSlice fragExec exprLowering
  compileEnv localPtrsProps stmtSim valueEncoding valueEncodingProps
  vyperAST vyperInterpreter vyperValue venomInst venomState finite_map
  loweringPosts vyperValueOperation emitHelper exprSimUnwrap emitHelperProps vyperState

Theorem compile_name_word_storage_frame_frag:
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  is_word_type ann /\ lookup_scopes id es.scopes = SOME entry /\
  word_value entry.value /\
  lower_value compile_expr cenv ty (Name ann id) sa = (op,sb) /\
  local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. expr_post ctx func cenv cx (Name ann id) es sa sb s0 es entry.value op s /\
         contract_storage s = contract_storage s0 /\
         contract_transient s = contract_transient s0) (\r. F)
Proof
  strip_tac >> drule_all lower_value_name_word >> strip_tac >>
  irule frag_exec_conseq >>
  irule_at Any emit_op_storage_frame_frag >>
  goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  qexistsl_tac [`val_to_w256 entry.value`, `s0`, `func`, `es`, `cx`] >>
  qexists_tac `\r. F` >> simp[is_terminator_def] >>
  conj_tac >- (rpt strip_tac >> drule_all step_name_word >> simp[]) >>
  rpt strip_tac >>
  gvs[expr_post_def, expr_val_rel_def, expr_val_at_def,
      vyperASTTheory.expr_type_def,
      typed_val_to_w256_word_value, locals_kept_mem]
QED

val literal_storage_frame_tac =
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      compile_literal_vv_def, unwrap_value_def, evaluate_literal_def,
      vyperASTTheory.expr_type_def] >>
  irule frag_exec_refl >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, eval_operand_def,
       typed_val_to_w256_word_value, word_value_def, val_to_w256_def];

Theorem compile_literal_word_storage_frame_frag:
  is_word_type ann /\
  ((?b. l = BoolL b) \/ (?i. l = IntL i) \/ (?i. l = DecimalL i)) /\
  lower_value compile_expr cenv ty (Literal ann l) sa = (op,sb) ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. expr_post ctx func cenv cx (Literal ann l) es sa sb s0 es
           (evaluate_literal l) op s /\
         contract_storage s = contract_storage s0 /\
         contract_transient s = contract_transient s0) (\r. F)
Proof
  rpt strip_tac
  >~ [`BoolL b`] >- (Cases_on `b` >> literal_storage_frame_tac) >>
  literal_storage_frame_tac
QED

Theorem unwrap_memory_word_storage_frame_frag:
  emit_op MLOAD [p.ptr_operand] sm = (op,sb) /\
  p.ptr_location = LocMemory /\ is_word_type t /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
  frag_exec ctx sm sb
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
           (LocatedValue t p) s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  strip_tac >> irule frag_exec_pointwise >> rw[] >>
  rename1 `vv_post ctx _ _ _ _ _ _ _ _ _ _ _ s1` >>
  `t = expr_type e /\
   ?w. eval_operand p.ptr_operand s1 = SOME w /\
       !tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
             mem_word_at (w2n w) s1.vs_memory = typed_val_to_w256 tvt v` by
    (gvs[vv_post_def, vv_holds_def, read_result_def, return_def] >>
     metis_tac[]) >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  irule frag_exec_conseq >>
  irule_at Any emit_op_storage_frame_frag >>
  goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  qexistsl_tac [`mload (w2n w) s1`, `s1`, `func`, `es'`, `cx`] >>
  qexists_tac `R` >> simp[is_terminator_def] >>
  conj_tac >- (rpt strip_tac >> irule step_MLOAD >> simp[]) >>
  rpt strip_tac
  >~ [`expr_post`]
  >- (irule expr_post_of_vv_post_load >>
      simp[] >> conj_tac
      >- (rpt strip_tac >> gvs[GSYM mem_word_at_eq_mload]) >>
      goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[]) >>
  gvs[vv_post_def]
QED

Theorem unwrap_memory_stack_storage_frame_frag:
  unwrap_value cenv vv sm = (op,sb) /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (case vv of StackValue t operand => T
            | LocatedValue t p => p.ptr_location = LocMemory) ==>
  frag_exec ctx sm sb
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  Cases_on `vv` >> simp[] >> strip_tac
  >- (gvs[unwrap_value_def, comp_return_def] >> irule frag_exec_refl >>
      rw[] >> metis_tac[expr_post_of_vv_post_stack]) >>
  rename1 `LocatedValue t p` >> Cases_on `is_word_type t`
  >- (irule unwrap_memory_word_storage_frame_frag >>
      gvs[unwrap_value_def, contextTheory.compile_ptr_load_def]) >>
  gvs[unwrap_value_def, comp_return_def] >> irule frag_exec_refl >>
  rw[] >> metis_tac[expr_post_of_vv_post_memory]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Expression storage frame has unproved dependencies"
  end) [compile_name_word_storage_frame_frag,
        compile_literal_word_storage_frame_frag,
        unwrap_memory_word_storage_frame_frag,
        unwrap_memory_stack_storage_frame_frag];
