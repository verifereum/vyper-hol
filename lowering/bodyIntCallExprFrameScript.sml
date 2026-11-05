Theory bodyIntCallExprFrame
Ancestors
  exprSim bodyIntCallSemanticFrame loweringSlice fragExec exprLowering
  compileEnv localPtrsProps stmtSim valueEncoding valueEncodingProps
  vyperAST vyperInterpreter vyperValue venomInst venomState finite_map
  loweringPosts vyperValueOperation emitHelper exprSimUnwrap emitHelperProps vyperState
  exprSimHyps vyperTypeEnv vyperTypeInvariants vyperTyping valueEncodingProofs
  vyperTypeSystem exprLoweringProps venomExecSemantics exprSimUnop builtinSimple
  words integer_word arithmeticProps builtinProps vyperContext exprOperandVar
  exprSimOps exprBopLowering exprSimCompare freshWrites rich_list exprSimArith
  exprSimOperators bodyIntCallSourceFrame
Libs
  intLib

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

Theorem framed_vv_memory_stack_lower_value_frag:
  compile_expr cenv ty e sa = (vv,sm) /\
  unwrap_value cenv vv sm = (op,sb) /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (case vv of StackValue t operand => T
            | LocatedValue t p => p.ptr_location = LocMemory) /\
  frag_exec ctx sa sm P
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s /\
         contract_storage s = contract_storage s0 /\
         contract_transient s = contract_transient s0) R ==>
  frag_exec ctx sa sb P
    (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         contract_storage s = contract_storage s0 /\
         contract_transient s = contract_transient s0) R
Proof
  strip_tac >> irule frag_exec_seq >>
  goal_assum (drule_at (Pat `frag_exec _ _ _ _ _ _`)) >>
  rpt conj_tac
  >~ [`cs_extends sa sm`] >- metis_tac[compile_expr_extends]
  >~ [`cs_extends sm sb`] >- metis_tac[unwrap_value_extends] >>
  irule unwrap_memory_stack_storage_frame_frag >> simp[]
QED

Theorem compile_name_vv_storage_frame_frag:
  expr_sim_pre cenv cx env (Name ann id) es /\
  compile_expr cenv ty (Name ann id) sa = (vv,sb) /\
  eval_expr cx (Name ann id) es = (res,es') /\ expr_vv_res_ok res /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. (?raw. res = INL raw /\
          vv_post ctx func cenv cx (Name ann id) es sa sb s0 es' raw vv s) /\
         contract_storage s = contract_storage s0 /\
         contract_transient s = contract_transient s0) (expr_exit res)
Proof
  strip_tac >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\
           evaluate_type (get_tenv cx) ann = SOME entry.type /\
           value_has_type entry.type entry.value` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     drule_all well_typed_Name_lookup >> strip_tac >>
     gvs[env_consistent_def, env_context_consistent_def]) >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  `cenv.ce_var_type id = SOME ann` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  drule_then (qspecl_then [`cx`, `ann`] assume_tac) eval_name_word >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       type_check_def, assert_def, check_def, ignore_bind_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       type_check_def, assert_def, check_def, ignore_bind_def,
       read_result_def] >> strip_tac >>
  gvs[compile_expr_def, compile_name_vv_def, comp_return_def,
      contextTheory.mk_ptr_def, vyperASTTheory.expr_type_def] >>
  irule frag_exec_refl >> rpt strip_tac >> gvs[] >>
  rename1 `stmt_state_rel ctx func cenv cx es s1` >>
  `?w. lookup_var p s1 = SOME w /\ type_memory_size entry.type <= sz /\
       val_wf entry.type entry.value /\
       val_in_memory entry.type entry.value (w2n w) s1.vs_memory` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  simp[vv_post_def, vv_holds_def, vv_at_def, read_result_def, return_def,
       vyperASTTheory.expr_type_def, eval_operand_def] >>
  rpt conj_tac
  >- metis_tac[val_in_memory_word_type]
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`id`, `w2n w`, `sz`] >>
      asm_simp_tac (srw_ss()) [local_region_def, dynarray_local_def] >>
      drule val_footprint_le >> decide_tac) >>
  rpt strip_tac >> gvs[]
QED

val literal_vv_storage_frame_tac =
  `is_word_type ann` by
    (gvs[expr_sim_pre_def, well_typed_expr_def] >>
     Cases_on `ann` >> gvs[well_typed_literal_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[well_typed_literal_def, is_word_type_def]) >>
  gvs[compile_expr_def, compile_literal_vv_def, comp_return_def,
      evaluate_literal_def] >>
  irule frag_exec_refl >>
  simp[vv_post_def, vv_holds_def, vv_at_def, read_result_def, return_def,
       expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, eval_operand_def,
       typed_val_to_w256_word_value, word_value_def, val_to_w256_def];

Theorem compile_literal_vv_storage_frame_frag:
  expr_sim_pre cenv cx env (Literal ann l) es /\
  compile_expr cenv ty (Literal ann l) sa = (vv,sb) /\
  eval_expr cx (Literal ann l) es = (res,es') /\ expr_vv_res_ok res /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  ((?b. l = BoolL b) \/ (?i. l = IntL i) \/ (?i. l = DecimalL i)) ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. (?raw. res = INL raw /\
          vv_post ctx func cenv cx (Literal ann l) es sa sb s0 es' raw vv s) /\
         contract_storage s = contract_storage s0 /\
         contract_transient s = contract_transient s0) (expr_exit res)
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, return_def]
  >~ [`BoolL b`] >- (Cases_on `b` >> literal_vv_storage_frame_tac) >>
  literal_vv_storage_frame_tac
QED

Theorem unwrap_storage_word_storage_frame_frag:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  is_word_type t /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var ==>
  frag_exec ctx sm sb
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
           (LocatedValue t p) s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  rpt strip_tac >>
  gvs[unwrap_value_def, contextTheory.compile_ptr_load_def] >> (
  irule frag_exec_pointwise >> rw[] >>
  rename1 `vv_post ctx _ _ _ _ _ _ _ _ _ _ _ s1` >>
  `t = expr_type e /\
   ?w. eval_operand p.ptr_operand s1 = SOME w /\
       storage_holds cx (p.ptr_location = LocTransient) (expr_type e)
         (Value v) w es' s1 /\
       stmt_state_rel ctx func cenv cx es' s1` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  `!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
         (if p.ptr_location = LocTransient then tload w s1 else sload w s1) =
         typed_val_to_w256 tvt v` by
    (rpt strip_tac >> drule_all storage_holds_load >> simp[]) >>
  irule frag_exec_conseq >> irule_at Any emit_op_storage_frame_frag >>
  goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  qexistsl_tac [`if p.ptr_location = LocTransient then tload w s1 else sload w s1`,
               `s1`, `func`, `es'`, `cx`] >>
  qexists_tac `R` >> simp[is_terminator_def] >>
  conj_tac >- (rpt strip_tac >> gvs[step_inst_base_def, exec_read1_def]) >>
  rpt strip_tac
  >~ [`expr_post`]
  >- (irule expr_post_of_vv_post_load >> simp[] >> conj_tac
      >- (rpt strip_tac >> gvs[]) >>
      goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[]) >>
  gvs[])
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
        unwrap_memory_stack_storage_frame_frag,
        framed_vv_memory_stack_lower_value_frag,
        compile_name_vv_storage_frame_frag,
        compile_literal_vv_storage_frame_frag,
        unwrap_storage_word_storage_frame_frag];

(* The Not instruction and its source encoding share one execution endpoint. *)
Theorem not_storage_frame_step:
  (is_bool_type ann \/ is_uint256_type ann \/ is_bytes32_type ann \/
   is_flag_type ann) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v1 /\
  (!nsid m. ann = FlagT nsid /\ tv = FlagTV m ==>
    cenv.ce_flag_n_members (nsid_to_string nsid) = m) /\
  unop_result cx ann Not tys v1 es = INL v /\
  (if ann = BaseT BoolT then emit_op ISZERO [x]
   else compile_invert x ann cenv) sa = (op,sb) ==>
  ?opc operands w.
    emit_op opc operands sa = (op,sb) /\
    opc <> INVOKE /\ ~is_terminator opc /\
    (!tv'. evaluate_type (get_tenv cx) ann = SOME tv' ==>
       w = typed_val_to_w256 tv' v) /\
    !s out. eval_operand x s = SOME (typed_val_to_w256 tv v1) ==>
      step_inst_base (mk_inst sa.cs_next_id opc operands [out]) s =
        OK (update_var out w s)
Proof
  disch_then (CONJUNCTS_THEN2 (strip_assume_tac o MATCH_MP not_type_cases)
                              strip_assume_tac) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v1` >>
  gvs[value_has_type_def, unop_result_def, evaluate_builtin_def,
      vyperASTTheory.type_to_int_bound_def, typed_val_to_w256_def,
      val_to_w256_def, compile_invert_def,
      vyperValueTheory.evaluate_type_def]
  >~ [`emit_op ISZERO`]
  >- (qexistsl_tac [`ISZERO`, `[x]`] >> simp[is_terminator_def] >>
      Cases_on `b` >> simp[typed_val_to_w256_def, val_to_w256_def,
        bool_to_word_def] >> rpt strip_tac >>
      drule step_ISZERO >> simp[bool_to_word_def])
  >~ [`i2w _`]
  >- (rename1 `Num i` >> qexistsl_tac [`NOT`, `[x]`] >>
      simp[is_terminator_def] >>
      `~(i < 0)` by intLib.ARITH_TAC >>
      simp[integer_wordTheory.i2w_pos, integer_wordTheory.i2w_def] >>
      metis_tac[step_NOT])
  >~ [`PAD_RIGHT`]
  >- (rename1 `LENGTH bs = 32` >>
      qexistsl_tac [`NOT`, `[x]`] >>
      simp[is_terminator_def, listTheory.PAD_RIGHT,
        length_word_to_bytes_be, word_of_bytes_be_to_bytes] >>
      metis_tac[step_NOT]) >>
  rename1 `k < 2 ** m` >>
  qexistsl_tac [`XOR`, `[x; Lit (n2w (2 ** m - 1))]`] >>
  simp[is_terminator_def] >>
  simp[GSYM flag_not_xor] >> rpt strip_tac >>
  irule step_XOR >> simp[eval_operand_def]
QED

Theorem not_storage_frame_tail:
  ann = expr_type e1 /\
  (is_bool_type ann \/ is_uint256_type ann \/ is_bytes32_type ann \/
   is_flag_type ann) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v1 /\
  (!nsid m. ann = FlagT nsid /\ tv = FlagTV m ==>
    cenv.ce_flag_n_members (nsid_to_string nsid) = m) /\
  unop_result cx ann Not [expr_type e1] v1 es' = INL v /\
  (if ann = BaseT BoolT then emit_op ISZERO [x]
   else compile_invert x ann cenv) sm = (op,sb) /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
  frag_exec ctx sm sb
    (\s. expr_post ctx func cenv cx e1 es sa sm s0 es' v1 x s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann Not [e1]) es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all not_storage_frame_step >> strip_tac >>
  `is_word_type ann` by
    (qpat_x_assum `ann = expr_type e1` kall_tac >>
     drule not_type_cases >> strip_tac >> gvs[is_word_type_def]) >>
  irule frag_exec_pointwise >> gen_tac >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `expr_post ctx _ _ _ _ _ _ _ _ _ _ _ s1` >>
  `stmt_state_rel ctx func cenv cx es' s1 /\
   eval_operand x s1 = SOME (typed_val_to_w256 tv v1)` by
    gvs[expr_post_def, expr_val_rel_def] >>
  irule frag_exec_conseq >> irule_at Any emit_op_storage_frame_frag >>
  goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  qexistsl_tac [`w`, `s1`, `func`, `es'`, `cx`, `R`] >> simp[] >>
  rpt strip_tac
  >~ [`expr_post`]
  >- (qpat_x_assum `ann = expr_type e1` (SUBST_ALL_TAC o SYM) >>
      irule expr_post_unop >> simp[expr_val_rel_def] >>
      goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  gvs[expr_post_def]
QED

Theorem compile_not_storage_frame_frag:
  ann = expr_type e1 /\
  (is_bool_type ann \/ is_uint256_type ann \/ is_bytes32_type ann \/
   is_flag_type ann) /\
  (!v1 es1.
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es1) ==>
    ?tv. evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v1 /\
      (!nsid m. ann = FlagT nsid /\ tv = FlagTV m ==>
        cenv.ce_flag_n_members (nsid_to_string nsid) = m)) /\
  (!a b operand es0 es1 value start saved savedT R.
    lower_value compile_expr cenv (expr_type e1) e1 a = (operand,b) /\
    (do r <- eval_expr cx e1; read_result cx r od) es0 = (INL value,es1) /\
    fn_has_code a b func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv a ==>
    frag_exec ctx a b
      (\s. s = start /\ stmt_state_rel ctx func cenv cx es0 s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\s. expr_post ctx func cenv cx e1 es0 a b start es1 value operand s /\
           contract_storage s = saved /\ contract_transient s = savedT) R) /\
  lower_value compile_expr cenv ty (Builtin ann Not [e1]) sa = (op,sb) /\
  (do r <- eval_expr cx (Builtin ann Not [e1]); read_result cx r od) es = (INL v,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann Not [e1]) es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule lower_value_not >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  qspec_then `expr_type e1` (qspec_then `cenv` (qspec_then `x` mp_tac))
    straight_fresh_not >>
  disch_tac >> drule_all straight_fresh_cs_extends >> strip_tac >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `?v1. (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es') /\
         unop_result cx ann Not [expr_type e1] v1 es' = INL v` by
    (drule eval_expr_unop_cases >>
     simp[precompile_builtin_def, builtin_args_length_ok_def] >>
     metis_tac[]) >>
  qpat_x_assum `!v1 es1. bind _ _ es = _ ==> _` drule >> strip_tac >>
  irule frag_exec_seq >>
  qpat_x_assum `!a b operand es0 es1 value start saved savedT R. _`
    (irule_at (Pat `frag_exec _ sa _ _ _ _`)) >>
  simp[] >> irule not_storage_frame_tail >>
  qpat_x_assum `ann = expr_type e1` (SUBST_ALL_TAC o SYM) >>
  simp[] >> qexists_tac `tv` >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Not storage frame has unproved dependencies"
  end) [not_storage_frame_step, not_storage_frame_tail,
        compile_not_storage_frame_frag];

Theorem abs_storage_frame_run:
  value_has_type (BaseTV (IntT 256)) v1 /\
  unop_result cx (BaseT (IntT 256)) Abs tys v1 es = INL v /\
  compile_builtin_abs x sa = (op,sb) /\
  eval_operand x s = SOME (typed_val_to_w256 (BaseTV (IntT 256)) v1) /\
  fresh_vars_wrt sa s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (typed_val_to_w256 (BaseTV (IntT 256)) v)
Proof
  strip_tac >> Cases_on `v1` >> gvs[value_has_type_def] >>
  rename1 `within_int_bound _ i` >>
  drule int256_abs_bound >> strip_tac >>
  drule_all abs_i2w >> strip_tac >>
  gvs[unop_result_def, evaluate_builtin_def,
      vyperASTTheory.type_to_int_bound_def, bounded_int_op_def,
      typed_val_to_w256_def, val_to_w256_def, AllCaseEqs()] >>
  `i2w i <> (INT_MINw : bytes32)` by metis_tac[] >>
  drule_all compile_builtin_abs_run >>
  disch_then (drule o CONJUNCT1) >> simp[]
QED

Theorem abs_storage_frame_tail:
  expr_type e1 = BaseT (IntT 256) /\
  value_has_type (BaseTV (IntT 256)) v1 /\
  unop_result cx (BaseT (IntT 256)) Abs [expr_type e1] v1 es' = INL v /\
  compile_builtin_abs x sm = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
  frag_exec ctx sm sb
    (\s. expr_post ctx func cenv cx e1 es sa sm s0 es' v1 x s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin (BaseT (IntT 256)) Abs [e1])
           es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  strip_tac >> irule frag_exec_pointwise >> gen_tac >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `expr_post ctx _ _ _ _ _ _ _ _ _ _ _ s1` >>
  `stmt_state_rel ctx func cenv cx es' s1 /\
   eval_operand x s1 = SOME (typed_val_to_w256 (BaseTV (IntT 256)) v1)` by
    gvs[expr_post_def, expr_val_rel_def, vyperValueTheory.evaluate_type_def,
        is_word_type_def] >>
  irule frag_exec_conseq >>
  irule_at Any frag_exec_straight_fresh_storage_frame_success >>
  qexistsl_tac [`typed_val_to_w256 (BaseTV (IntT 256)) v`, `s1`, `op`,
                 `compile_builtin_abs x`, `func`, `es'`, `cx`, `cenv`, `R`] >>
  qexists_tac `\s. eval_operand x s = SOME (typed_val_to_w256 (BaseTV (IntT 256)) v1)` >>
  simp[straight_fresh_abs, freshWritesTheory.eval_operand_drop_fresh] >>
  rpt conj_tac
  >- (rpt strip_tac >> irule abs_storage_frame_run >> simp[] >>
      goal_assum (drule_at (Pat `unop_result _ _ _ _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `compile_builtin_abs _ _ = _`)) >> simp[]) >>
  rpt strip_tac
  >~ [`expr_post`]
  >- (irule expr_post_unop >>
      simp[expr_val_rel_def, vyperValueTheory.evaluate_type_def, is_word_type_def] >>
      goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  gvs[expr_post_def]
QED

Theorem compile_abs_storage_frame_frag:
  ann = expr_type e1 /\ ann = BaseT (IntT 256) /\
  (!v1 es1.
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es1) ==>
    value_has_type (BaseTV (IntT 256)) v1) /\
  (!a b operand es0 es1 value start saved savedT R.
    lower_value compile_expr cenv ty e1 a = (operand,b) /\
    (do r <- eval_expr cx e1; read_result cx r od) es0 = (INL value,es1) /\
    fn_has_code a b func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv a ==>
    frag_exec ctx a b
      (\s. s = start /\ stmt_state_rel ctx func cenv cx es0 s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\s. expr_post ctx func cenv cx e1 es0 a b start es1 value operand s /\
           contract_storage s = saved /\ contract_transient s = savedT) R) /\
  lower_value compile_expr cenv ty (Builtin ann Abs [e1]) sa = (op,sb) /\
  (do r <- eval_expr cx (Builtin ann Abs [e1]); read_result cx r od) es = (INL v,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann Abs [e1]) es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule lower_value_abs >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  qspec_then `x` assume_tac straight_fresh_abs >>
  drule_all straight_fresh_cs_extends >> strip_tac >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `?v1. (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es') /\
         unop_result cx ann Abs [expr_type e1] v1 es' = INL v` by
    (drule eval_expr_unop_cases >>
     simp[precompile_builtin_def, builtin_args_length_ok_def] >> metis_tac[]) >>
  qpat_x_assum `!v1 es1. bind _ _ es = _ ==> _` drule >> strip_tac >>
  irule frag_exec_seq >>
  qpat_x_assum `!a b operand es0 es1 value start saved savedT R. _`
    (irule_at (Pat `frag_exec _ sa _ _ _ _`)) >>
  simp[] >> irule abs_storage_frame_tail >> gvs[] >>
  metis_tac[compile_lower_value_var]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Abs storage frame has unproved dependencies"
  end) [abs_storage_frame_run, abs_storage_frame_tail,
        compile_abs_storage_frame_frag];

Theorem neg_storage_frame_run:
  is_numeric_type t /\ ~is_uint_type t /\
  evaluate_type (get_tenv cx) t = SOME tv /\ value_has_type tv v1 /\
  unop_result cx t Neg [t] v1 es = INL v /\
  compile_neg x t sa = (op,sb) /\
  eval_operand x s = SOME (typed_val_to_w256 tv v1) /\ fresh_vars_wrt sa s ==>
  ?s'. run_inst_seq (emitted_insts sa sb) s = OK s' /\
       eval_operand op s' = SOME (typed_val_to_w256 tv v)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all neg_typed_source >> disch_then (qspec_then `es` mp_tac) >>
  Cases_on `w2i (FST (type_bounds t)) < w2i (typed_val_to_w256 tv v1)` >>
  simp[] >> strip_tac >> gvs[] >>
  drule_all compile_neg_run >> simp[]
QED

Theorem neg_storage_frame_tail:
  ann = expr_type e1 /\ is_numeric_type ann /\ ~is_uint_type ann /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v1 /\
  unop_result cx ann Neg [ann] v1 es' = INL v /\
  compile_neg x ann sm = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
  frag_exec ctx sm sb
    (\s. expr_post ctx func cenv cx e1 es sa sm s0 es' v1 x s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann Neg [e1])
           es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `is_word_type ann` by
    (qpat_x_assum `ann = expr_type e1` kall_tac >>
     Cases_on `ann` >> gvs[is_numeric_type_def, is_int_type_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_word_type_def]) >>
  irule frag_exec_pointwise >> gen_tac >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `expr_post ctx _ _ _ _ _ _ _ _ _ _ _ s1` >>
  `stmt_state_rel ctx func cenv cx es' s1 /\
   eval_operand x s1 = SOME (typed_val_to_w256 tv v1)` by
    gvs[expr_post_def, expr_val_rel_def] >>
  irule frag_exec_conseq >>
  irule_at Any frag_exec_straight_fresh_storage_frame_success >>
  qexistsl_tac [`typed_val_to_w256 tv v`, `s1`, `op`,
                 `compile_neg x ann`, `func`, `es'`, `cx`, `cenv`, `R`] >>
  qexists_tac `\s. eval_operand x s = SOME (typed_val_to_w256 tv v1)` >>
  simp[CONV_RULE (DEPTH_CONV ETA_CONV) straight_fresh_neg,
       freshWritesTheory.eval_operand_drop_fresh] >>
  rpt conj_tac
  >- (rpt strip_tac >> irule neg_storage_frame_run >> simp[] >>
      goal_assum (drule_at (Pat `unop_result _ _ _ _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `compile_neg _ _ _ = _`)) >> gvs[]) >>
  rpt strip_tac
  >~ [`expr_post`]
  >- (qpat_x_assum `ann = expr_type e1` (SUBST_ALL_TAC o SYM) >>
      irule expr_post_unop >> simp[expr_val_rel_def] >>
      goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  gvs[expr_post_def]
QED

Theorem compile_neg_storage_frame_frag:
  ann = expr_type e1 /\ is_numeric_type ann /\ ~is_uint_type ann /\
  (!v1 es1.
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es1) ==>
    ?tv. evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v1) /\
  (!a b operand es0 es1 value start saved savedT R.
    lower_value compile_expr cenv (expr_type e1) e1 a = (operand,b) /\
    (do r <- eval_expr cx e1; read_result cx r od) es0 = (INL value,es1) /\
    fn_has_code a b func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv a ==>
    frag_exec ctx a b
      (\s. s = start /\ stmt_state_rel ctx func cenv cx es0 s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\s. expr_post ctx func cenv cx e1 es0 a b start es1 value operand s /\
           contract_storage s = saved /\ contract_transient s = savedT) R) /\
  lower_value compile_expr cenv ty (Builtin ann Neg [e1]) sa = (op,sb) /\
  (do r <- eval_expr cx (Builtin ann Neg [e1]); read_result cx r od) es = (INL v,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann Neg [e1]) es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule lower_value_neg >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  qspecl_then [`x`, `expr_type e1`] assume_tac
    (CONV_RULE (DEPTH_CONV ETA_CONV) straight_fresh_neg) >>
  drule_all straight_fresh_cs_extends >> strip_tac >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `?v1. (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es') /\
         unop_result cx ann Neg [expr_type e1] v1 es' = INL v` by
    (drule eval_expr_unop_cases >>
     simp[precompile_builtin_def, builtin_args_length_ok_def] >> metis_tac[]) >>
  qpat_x_assum `!v1 es1. bind _ _ es = _ ==> _` drule >> strip_tac >>
  irule frag_exec_seq >>
  qpat_x_assum `!a b operand es0 es1 value start saved savedT R. _`
    (irule_at (Pat `frag_exec _ sa _ _ _ _`)) >>
  simp[] >> irule neg_storage_frame_tail >>
  gvs[] >> metis_tac[compile_lower_value_var]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Neg storage frame has unproved dependencies"
  end) [neg_storage_frame_run, neg_storage_frame_tail,
        compile_neg_storage_frame_frag];

Theorem bitwise_storage_frame_op:
  (bop = And \/ bop = Or \/ bop = XOr) /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  eval_operand x s0 = SOME a /\ eval_operand y s0 = SOME b /\
  local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. stmt_state_rel ctx func cenv cx es s /\
         eval_operand op s = SOME
           ((if bop = And then word_and else if bop = Or then word_or else word_xor) a b) /\
         (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z s = SOME w) /\
         (!aid base. FLOOKUP s0.vs_allocas aid = SOME base ==> FLOOKUP s.vs_allocas aid = SOME base) /\
         s.vs_memory = s0.vs_memory /\
         contract_storage s = contract_storage s0 /\
         contract_transient s = contract_transient s0) R
Proof
  strip_tac >> gvs[compile_binop_def] >>
  irule emit_op_storage_frame_frag >> simp[] >>
  goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
  simp[step_AND, step_OR, step_XOR, is_terminator_def]
QED

Theorem bitwise_storage_frame_tail:
  (bop = And \/ bop = Or \/ bop = XOr) /\
  bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 es' = INL v /\
  (!i1 i2. v1 = IntV i1 /\ v2 = IntV i2 ==>
    within_int_bound (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i1 /\
    within_int_bound (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i2) /\
  word_value v1 /\ word_value v2 /\
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e1)) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e2)) /\
  compile_binop bop x y (expr_type e1) bl el s2 = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s2 /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  stmt_state_rel ctx func cenv cx es s0 /\
  expr_post ctx func cenv cx e1 es sa s1 s0 es1 v1 x t ==>
  frag_exec ctx s2 sb
    (\s. expr_post ctx func cenv cx e2 es1 s1 s2 t es' v2 y s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
           es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_res_ok (bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 es')` by
    simp[expr_res_ok_def] >>
  drule_all bop_result_bitwise >> strip_tac >> gnvs[] >>
  irule frag_exec_pointwise >> gen_tac >> BETA_TAC >> strip_tac >>
  rename1 `expr_post ctx _ _ _ _ _ _ _ _ _ _ _ u` >>
  `stmt_state_rel ctx func cenv cx es' u /\
   eval_operand x u = SOME (val_to_w256 v1) /\
   eval_operand y u = SOME (val_to_w256 v2)` by
    (fs[expr_post_def] >>
     `eval_operand x t = SOME (val_to_w256 v1) /\
      eval_operand y u = SOME (val_to_w256 v2)` by
       (conj_tac >> irule expr_val_rel_word >> simp[] >> metis_tac[]) >>
     simp[] >> irule eval_operand_frame >> metis_tac[]) >>
  irule frag_exec_conseq >> irule_at Any bitwise_storage_frame_op >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`u`, `func`, `es'`, `cx`, `cenv`, `val_to_w256 v2`, `val_to_w256 v1`, `R`] >>
  simp[] >> rpt strip_tac
  >~ [`expr_post`]
  >- (irule expr_post_bop >> simp[] >>
      goal_assum (drule_at (Pat `expr_post _ _ _ _ e1 _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `expr_post _ _ _ _ e2 _ _ _ _ _ _ _ _`)) >> simp[]) >>
  gvs[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Bitwise storage frame has unproved dependencies"
  end) [bitwise_storage_frame_op, bitwise_storage_frame_tail];

Theorem successful_bop_operands[local]:
  (do r <- eval_expr cx (Builtin ann (Bop bop) [e1;e2]); read_result cx r od) es = (INL v,es') ==>
  ?v1 es1 v2.
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es1) /\
    (do r <- eval_expr cx e2; read_result cx r od) es1 = (INL v2,es') /\
    bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 es' = INL v
Proof
  strip_tac >> drule eval_expr_bop_cases >> simp[] >> metis_tac[]
QED

Theorem compile_bop_storage_frame_reachable_frag:
  ~((bop = In \/ bop = NotIn) /\ is_ArrayT (expr_type e2)) /\
  ~(is_bytestring_type (expr_type e1) /\ (bop = Eq \/ bop = NotEq)) /\
  (!v1 es1 v2 es2.
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es1) /\
    (do r <- eval_expr cx e2; read_result cx r od) es1 = (INL v2,es2) ==>
    MAP FDOM es.scopes = MAP FDOM es1.scopes) /\
  (!a b operand.
    lower_value compile_expr cenv (expr_type e1) e1 a = (operand,b) ==>
    !l. operand <> Label l) /\
  (!e a b operand es0 es1 value start saved savedT R.
    ((e = e1 /\ es0 = es) \/
     (e = e2 /\ ?vfirst.
       (do r <- eval_expr cx e1; read_result cx r od) es = (INL vfirst,es0))) /\
    lower_value compile_expr cenv (expr_type e1) e a = (operand,b) /\
    (do r <- eval_expr cx e; read_result cx r od) es0 = (INL value,es1) /\
    fn_has_code a b func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv a ==>
    frag_exec ctx a b
      (\s. s = start /\ stmt_state_rel ctx func cenv cx es0 s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\s. expr_post ctx func cenv cx e es0 a b start es1 value operand s /\
           contract_storage s = saved /\ contract_transient s = savedT) R) /\
  (!a a1 a2 b start mid es1 es2 v1 v2 value x y operand saved savedT R.
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es1) /\
    (do r <- eval_expr cx e2; read_result cx r od) es1 = (INL v2,es2) /\
    bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 es2 = INL value /\
    compile_binop bop x y (expr_type e1)
      (if bop = Exp then expr_int_literal e1 else NONE)
      (if bop = Exp then expr_int_literal e2 else NONE) a2 = (operand,b) /\
    (!z. x = Var z ==> not_fresh_at a1 z) /\
    (!z. y = Var z ==> not_fresh_at a2 z) /\ (!l. x <> Label l) /\
    local_ptrs_reserved cenv a /\ local_ptrs_reserved cenv a2 /\
    a.cs_next_var <= a1.cs_next_var /\ a1.cs_next_var <= a2.cs_next_var /\
    a.cs_next_id <= a1.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    stmt_state_rel ctx func cenv cx es start /\
    expr_post ctx func cenv cx e1 es a a1 start es1 v1 x mid ==>
    frag_exec ctx a2 b
      (\s. expr_post ctx func cenv cx e2 es1 a1 a2 mid es2 v2 y s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\s. expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
             es a b start es2 value operand s /\
           contract_storage s = saved /\ contract_transient s = savedT) R) /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  (do r <- eval_expr cx (Builtin ann (Bop bop) [e1;e2]); read_result cx r od) es = (INL v,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2]) es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all lower_value_bop >> strip_tac >>
  qpat_assum `lower_value _ _ _ e1 sa = _`
    (mp_then Any strip_assume_tac (cj 2 compile_expr_grows)) >>
  qpat_assum `lower_value _ _ _ e2 s1 = _`
    (mp_then Any strip_assume_tac (cj 2 compile_expr_grows)) >>
  drule compile_binop_grows >> strip_tac >>
  `cs_extends sa s2 /\ cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  drule successful_bop_operands >> strip_tac >>
  qpat_x_assum `!v1 es1 v2 es2. _` (drule_all_then assume_tac) >>
  irule frag_exec_pointwise >> gen_tac >> BETA_TAC >> strip_tac >> gnvs[] >>
  `frag_exec ctx sa s1 (\s. s = s0)
    (\s. expr_post ctx func cenv cx e1 es sa s1 s0 es1 v1 x s /\
         contract_storage s = contract_storage s0 /\
         contract_transient s = contract_transient s0) R` by
    (irule frag_exec_pre_exit >>
     qpat_assum `!e a b operand es0 es1 value start saved savedT R. _`
       (irule_at (Pat `frag_exec _ _ _ _ _ _`)) >> simp[] >>
     qexists_tac `R` >> simp[]) >>
  drule frag_exec_then >> disch_then irule >> simp[] >> rpt strip_tac >>
  rename1 `expr_post ctx _ _ _ e1 _ _ _ _ _ _ _ t` >>
  `stmt_state_rel ctx func cenv cx es1 t` by fs[expr_post_def] >>
  `frag_exec ctx s1 s2 (\s. s = t)
    (\s. expr_post ctx func cenv cx e2 es1 s1 s2 t es' v2 y s /\
         contract_storage s = contract_storage s0 /\
         contract_transient s = contract_transient s0) R` by
    (irule frag_exec_pre_exit >>
     qpat_assum `!e a b operand es0 es1 value start saved savedT R. _`
       (irule_at (Pat `frag_exec _ _ _ _ _ _`)) >> simp[] >>
     qexists_tac `R` >> simp[]) >>
  qpat_x_assum `frag_exec ctx s1 s2 _ _ _`
    (mp_then Any mp_tac frag_exec_then) >> disch_then irule >> simp[] >>
  rpt strip_tac >>
  irule frag_exec_conseq >>
  qpat_x_assum `!a a1 a2 b start mid x y operand saved savedT R. _`
    (irule_at Any) >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> qexists_tac `R` >> simp[] >>
  qpat_assum `lower_value _ _ _ e1 sa = _`
    (mp_then Any mp_tac compile_lower_value_var) >> simp[] >> strip_tac >>
  qpat_assum `lower_value _ _ _ e2 s1 = _`
    (mp_then Any mp_tac compile_lower_value_var) >> simp[] >> strip_tac >>
  qpat_x_assum `!a b operand. _` (drule_then assume_tac) >> simp[]
QED

(* Compatibility boundary: unconditional operand simulations imply the
   reachable-source callback, but typed recursive callers use the latter. *)
Theorem compile_bop_storage_frame_frag:
  ~((bop = In \/ bop = NotIn) /\ is_ArrayT (expr_type e2)) /\
  ~(is_bytestring_type (expr_type e1) /\ (bop = Eq \/ bop = NotEq)) /\
  (!v1 es1 v2 es2.
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es1) /\
    (do r <- eval_expr cx e2; read_result cx r od) es1 = (INL v2,es2) ==>
    MAP FDOM es.scopes = MAP FDOM es1.scopes) /\
  (!a b operand.
    lower_value compile_expr cenv (expr_type e1) e1 a = (operand,b) ==>
    !l. operand <> Label l) /\
  (!e a b operand es0 es1 value start saved savedT R.
    (e = e1 \/ e = e2) /\
    lower_value compile_expr cenv (expr_type e1) e a = (operand,b) /\
    (do r <- eval_expr cx e; read_result cx r od) es0 = (INL value,es1) /\
    fn_has_code a b func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv a ==>
    frag_exec ctx a b
      (\s. s = start /\ stmt_state_rel ctx func cenv cx es0 s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\s. expr_post ctx func cenv cx e es0 a b start es1 value operand s /\
           contract_storage s = saved /\ contract_transient s = savedT) R) /\
  (!a a1 a2 b start mid es1 es2 v1 v2 value x y operand saved savedT R.
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es1) /\
    (do r <- eval_expr cx e2; read_result cx r od) es1 = (INL v2,es2) /\
    bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 es2 = INL value /\
    compile_binop bop x y (expr_type e1)
      (if bop = Exp then expr_int_literal e1 else NONE)
      (if bop = Exp then expr_int_literal e2 else NONE) a2 = (operand,b) /\
    (!z. x = Var z ==> not_fresh_at a1 z) /\
    (!z. y = Var z ==> not_fresh_at a2 z) /\ (!l. x <> Label l) /\
    local_ptrs_reserved cenv a /\ local_ptrs_reserved cenv a2 /\
    a.cs_next_var <= a1.cs_next_var /\ a1.cs_next_var <= a2.cs_next_var /\
    a.cs_next_id <= a1.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    stmt_state_rel ctx func cenv cx es start /\
    expr_post ctx func cenv cx e1 es a a1 start es1 v1 x mid ==>
    frag_exec ctx a2 b
      (\s. expr_post ctx func cenv cx e2 es1 a1 a2 mid es2 v2 y s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\s. expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
             es a b start es2 value operand s /\
           contract_storage s = saved /\ contract_transient s = savedT) R) /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  (do r <- eval_expr cx (Builtin ann (Bop bop) [e1;e2]); read_result cx r od) es = (INL v,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2]) es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  strip_tac >> irule compile_bop_storage_frame_reachable_frag >>
  simp[] >> metis_tac[]
QED

Theorem compile_bitwise_storage_frame_frag:
  (bop = And \/ bop = Or \/ bop = XOr) /\
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e1)) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e2)) /\
  (!v1 es1 v2 es2.
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es1) /\
    (do r <- eval_expr cx e2; read_result cx r od) es1 = (INL v2,es2) ==>
    word_value v1 /\ word_value v2 /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    (!i1 i2. v1 = IntV i1 /\ v2 = IntV i2 ==>
      within_int_bound (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i1 /\
      within_int_bound (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i2)) /\
  (!a b operand.
    lower_value compile_expr cenv (expr_type e1) e1 a = (operand,b) ==>
    !l. operand <> Label l) /\
  (!e a b operand es0 es1 value start saved savedT R.
    (e = e1 \/ e = e2) /\
    lower_value compile_expr cenv (expr_type e1) e a = (operand,b) /\
    (do r <- eval_expr cx e; read_result cx r od) es0 = (INL value,es1) /\
    fn_has_code a b func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv a ==>
    frag_exec ctx a b
      (\s. s = start /\ stmt_state_rel ctx func cenv cx es0 s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\s. expr_post ctx func cenv cx e es0 a b start es1 value operand s /\
           contract_storage s = saved /\ contract_transient s = savedT) R) /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  (do r <- eval_expr cx (Builtin ann (Bop bop) [e1;e2]); read_result cx r od) es = (INL v,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2]) es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~((bop = In \/ bop = NotIn) /\ is_ArrayT (expr_type e2)) /\
   ~(is_bytestring_type (expr_type e1) /\ (bop = Eq \/ bop = NotEq))` by
    (qpat_x_assum `bop = And \/ _` mp_tac >> rpt strip_tac >> gvs[]) >>
  drule_all lower_value_bop >> strip_tac >>
  qpat_assum `lower_value _ _ _ e1 sa = _`
    (mp_then Any strip_assume_tac (cj 2 compile_expr_grows)) >>
  qpat_assum `lower_value _ _ _ e2 s1 = _`
    (mp_then Any strip_assume_tac (cj 2 compile_expr_grows)) >>
  drule compile_binop_grows >> strip_tac >>
  `cs_extends sa s2 /\ cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  drule successful_bop_operands >> strip_tac >>
  qpat_x_assum `!v1 es1 v2 es2. _` (drule_all_then strip_assume_tac) >>
  irule frag_exec_pointwise >> gen_tac >> BETA_TAC >> strip_tac >> gnvs[] >>
  `frag_exec ctx sa s1 (\s. s = s0)
    (\s. expr_post ctx func cenv cx e1 es sa s1 s0 es1 v1 x s /\
         contract_storage s = contract_storage s0 /\
         contract_transient s = contract_transient s0) R` by
    (irule frag_exec_pre_exit >>
     qpat_assum `!e a b operand es0 es1 value start saved savedT R. _`
       (irule_at (Pat `frag_exec _ _ _ _ _ _`)) >> simp[] >>
     qexists_tac `R` >> simp[]) >>
  drule frag_exec_then >> disch_then irule >> simp[] >> rpt strip_tac >>
  rename1 `expr_post ctx _ _ _ e1 _ _ _ _ _ _ _ t` >>
  `stmt_state_rel ctx func cenv cx es1 t` by fs[expr_post_def] >>
  `frag_exec ctx s1 s2 (\s. s = t)
    (\s. expr_post ctx func cenv cx e2 es1 s1 s2 t es' v2 y s /\
         contract_storage s = contract_storage s0 /\
         contract_transient s = contract_transient s0) R` by
    (irule frag_exec_pre_exit >>
     qpat_assum `!e a b operand es0 es1 value start saved savedT R. _`
       (irule_at (Pat `frag_exec _ _ _ _ _ _`)) >> simp[] >>
     qexists_tac `R` >> simp[]) >>
  qpat_x_assum `frag_exec ctx s1 s2 _ _ _`
    (mp_then Any mp_tac frag_exec_then) >> disch_then irule >> simp[] >>
  rpt strip_tac >>
  irule frag_exec_conseq >> irule_at Any bitwise_storage_frame_tail >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `bop_result _ _ _ _ _ _ _ = _`)) >>
  simp[] >> qexists_tac `R` >> simp[] >>
  qpat_assum `lower_value _ _ _ e1 sa = _`
    (mp_then Any mp_tac compile_lower_value_var) >> simp[] >>
  strip_tac >>
  qpat_x_assum `!a b operand. _` (drule_then assume_tac) >> simp[]
QED

(* The no-label contract is discharged at typed callers by
   lower_compile_expr_not_label, using well_typed_expr and the compiler's
   PtrVar (Var p) environment mapping. It is independent of value semantics. *)
val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Bitwise constructor has unproved dependencies"
  end) [compile_bitwise_storage_frame_frag];

Theorem bitwise_generic_tail_test[local]:
  (bop = And \/ bop = Or \/ bop = XOr) /\
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e1)) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e2)) /\
  (!v1 es1 v2 es2.
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es1) /\
    (do r <- eval_expr cx e2; read_result cx r od) es1 = (INL v2,es2) ==>
    word_value v1 /\ word_value v2 /\
    (!i1 i2. v1 = IntV i1 /\ v2 = IntV i2 ==>
      within_int_bound (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i1 /\
      within_int_bound (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i2)) ==>
  !a a1 a2 b start mid es1 es2 v1 v2 value x y operand saved savedT R.
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es1) /\
    (do r <- eval_expr cx e2; read_result cx r od) es1 = (INL v2,es2) /\
    bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 es2 = INL value /\
    compile_binop bop x y (expr_type e1)
      (if bop = Exp then expr_int_literal e1 else NONE)
      (if bop = Exp then expr_int_literal e2 else NONE) a2 = (operand,b) /\
    (!z. x = Var z ==> not_fresh_at a1 z) /\
    (!z. y = Var z ==> not_fresh_at a2 z) /\ (!l. x <> Label l) /\
    local_ptrs_reserved cenv a /\ local_ptrs_reserved cenv a2 /\
    a.cs_next_var <= a1.cs_next_var /\ a1.cs_next_var <= a2.cs_next_var /\
    a.cs_next_id <= a1.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    stmt_state_rel ctx func cenv cx es start /\
    expr_post ctx func cenv cx e1 es a a1 start es1 v1 x mid ==>
    frag_exec ctx a2 b
      (\s. expr_post ctx func cenv cx e2 es1 a1 a2 mid es2 v2 y s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\s. expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
             es a b start es2 value operand s /\
           contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!v1 es1 v2 es2. _` (drule_all_then strip_assume_tac) >>
  `bop <> Exp` by (qpat_x_assum `bop = And \/ _` mp_tac >> rpt strip_tac >> gvs[]) >>
  irule bitwise_storage_frame_tail >> simp[] >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Generic binary framing has unproved dependencies"
  end) [compile_bop_storage_frame_frag, bitwise_generic_tail_test];

Theorem shift_storage_frame_op:
  (bop = ShL \/ bop = ShR) /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  eval_operand x s0 = SOME a /\ eval_operand y s0 = SOME b /\
  local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. stmt_state_rel ctx func cenv cx es s /\
         eval_operand op s = SOME
           (if bop = ShL then word_lsl a (w2n b)
            else if is_signed_type ty then word_asr a (w2n b) else word_lsr a (w2n b)) /\
         (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z s = SOME w) /\
         (!aid base. FLOOKUP s0.vs_allocas aid = SOME base ==> FLOOKUP s.vs_allocas aid = SOME base) /\
         s.vs_memory = s0.vs_memory /\
         contract_storage s = contract_storage s0 /\
         contract_transient s = contract_transient s0) R
Proof
  strip_tac >> gvs[compile_binop_def] >> Cases_on `is_signed_type ty` >> gvs[] >>
  irule emit_op_storage_frame_frag >> simp[] >>
  goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
  simp[step_SHL, step_SHR, step_SAR, is_terminator_def]
QED

Theorem shift_result_words[local]:
  (bop = ShL \/ bop = ShR) /\
  v1 = IntV i1 /\ v2 = IntV i2 /\ within_int_bound (Unsigned 256) i2 /\
  ((type_to_int_bound ann = SOME (if is_signed_type ty then Signed 256 else Unsigned 256) /\
    within_int_bound (if is_signed_type ty then Signed 256 else Unsigned 256) i1) \/
   (bop = ShR /\ ?n. 0 < n /\ n <= 256 /\
    type_to_int_bound ann = SOME (if is_signed_type ty then Signed n else Unsigned n) /\
    within_int_bound (if is_signed_type ty then Signed n else Unsigned n) i1)) /\
  bop_result cx ann bop tys v1 v2 es = INL v ==>
  word_value v1 /\ word_value v2 /\ word_value v /\
  val_to_w256 v =
    (if bop = ShL then word_lsl (val_to_w256 v1) (w2n (val_to_w256 v2))
     else if is_signed_type ty then word_asr (val_to_w256 v1) (w2n (val_to_w256 v2))
     else word_lsr (val_to_w256 v1) (w2n (val_to_w256 v2)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `(_ /\ _) \/ _` strip_assume_tac
  >- (drule_all bop_result_shift >>
      disch_then (qspecl_then [`tys`, `cx`, `es`] strip_assume_tac) >>
      gvs[word_value_def]) >>
  drule_all bop_result_shr >>
  disch_then (qspecl_then [`tys`, `cx`, `es`] strip_assume_tac) >> gvs[word_value_def]
QED

Theorem shift_storage_frame_tail:
  (bop = ShL \/ bop = ShR) /\
  bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 es' = INL v /\
  v1 = IntV i1 /\ v2 = IntV i2 /\ within_int_bound (Unsigned 256) i2 /\
  ((type_to_int_bound ann = SOME (if is_signed_type (expr_type e1) then Signed 256 else Unsigned 256) /\
    within_int_bound (if is_signed_type (expr_type e1) then Signed 256 else Unsigned 256) i1) \/
   (bop = ShR /\ ?n. 0 < n /\ n <= 256 /\
    type_to_int_bound ann = SOME (if is_signed_type (expr_type e1) then Signed n else Unsigned n) /\
    within_int_bound (if is_signed_type (expr_type e1) then Signed n else Unsigned n) i1)) /\
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e1)) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e2)) /\
  compile_binop bop x y (expr_type e1) bl el s2 = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s2 /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  stmt_state_rel ctx func cenv cx es s0 /\
  expr_post ctx func cenv cx e1 es sa s1 s0 es1 v1 x t ==>
  frag_exec ctx s2 sb
    (\s. expr_post ctx func cenv cx e2 es1 s1 s2 t es' v2 y s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
           es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `word_value v1 /\ word_value v2 /\ word_value v /\
   val_to_w256 v =
     (if bop = ShL then word_lsl (val_to_w256 v1) (w2n (val_to_w256 v2))
      else if is_signed_type (expr_type e1)
      then word_asr (val_to_w256 v1) (w2n (val_to_w256 v2))
      else word_lsr (val_to_w256 v1) (w2n (val_to_w256 v2)))` by
    (irule shift_result_words >> simp[] >> metis_tac[]) >>
  irule frag_exec_pointwise >> gen_tac >> BETA_TAC >> strip_tac >>
  rename1 `expr_post ctx _ _ _ _ _ _ _ _ _ _ _ u` >>
  `stmt_state_rel ctx func cenv cx es' u /\
   eval_operand x u = SOME (val_to_w256 v1) /\
   eval_operand y u = SOME (val_to_w256 v2)` by
    (fs[expr_post_def] >>
     `eval_operand x t = SOME (val_to_w256 v1) /\
      eval_operand y u = SOME (val_to_w256 v2)` by
       (conj_tac >> irule expr_val_rel_word >> simp[] >> metis_tac[]) >>
     simp[] >> irule eval_operand_frame >> simp[] >> qexistsl_tac [`s1`, `t`] >> simp[]) >>
  irule frag_exec_conseq >> irule_at Any shift_storage_frame_op >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`u`, `func`, `es'`, `cx`, `cenv`, `val_to_w256 v2`, `val_to_w256 v1`, `R`] >>
  simp[] >> rpt strip_tac
  >~ [`expr_post`]
  >- (irule expr_post_bop >> simp[] >>
      goal_assum (drule_at (Pat `expr_post _ _ _ _ e1 _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `expr_post _ _ _ _ e2 _ _ _ _ _ _ _ _`)) >> simp[]) >>
  gvs[]
QED

Theorem compile_shift_storage_frame_frag:
  (bop = ShL \/ bop = ShR) /\
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e1)) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e2)) /\
  (!v1 es1 v2 es2.
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es1) /\
    (do r <- eval_expr cx e2; read_result cx r od) es1 = (INL v2,es2) ==>
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    ?i1 i2. v1 = IntV i1 /\ v2 = IntV i2 /\ within_int_bound (Unsigned 256) i2 /\
      ((type_to_int_bound ann = SOME (if is_signed_type (expr_type e1) then Signed 256 else Unsigned 256) /\
        within_int_bound (if is_signed_type (expr_type e1) then Signed 256 else Unsigned 256) i1) \/
       (bop = ShR /\ ?n. 0 < n /\ n <= 256 /\
        type_to_int_bound ann = SOME (if is_signed_type (expr_type e1) then Signed n else Unsigned n) /\
        within_int_bound (if is_signed_type (expr_type e1) then Signed n else Unsigned n) i1))) /\
  (!a b operand.
    lower_value compile_expr cenv (expr_type e1) e1 a = (operand,b) ==> !l. operand <> Label l) /\
  (!e a b operand es0 es1 value start saved savedT R.
    (e = e1 \/ e = e2) /\
    lower_value compile_expr cenv (expr_type e1) e a = (operand,b) /\
    (do r <- eval_expr cx e; read_result cx r od) es0 = (INL value,es1) /\
    fn_has_code a b func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv a ==>
    frag_exec ctx a b
      (\s. s = start /\ stmt_state_rel ctx func cenv cx es0 s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\s. expr_post ctx func cenv cx e es0 a b start es1 value operand s /\
           contract_storage s = saved /\ contract_transient s = savedT) R) /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  (do r <- eval_expr cx (Builtin ann (Bop bop) [e1;e2]); read_result cx r od) es = (INL v,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2]) es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bop <> In /\ bop <> NotIn /\ bop <> Eq /\ bop <> NotEq /\ bop <> Exp` by
    (qpat_x_assum `bop = ShL \/ _` mp_tac >> rpt strip_tac >> gvs[]) >>
  irule compile_bop_storage_frame_frag >> simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!v1 es1 v2 es2. _` (drule_all_then strip_assume_tac) >>
      irule shift_storage_frame_tail >> simp[] >>
      qexistsl_tac [`NONE`, `NONE`, `i1`, `x`] >> simp[] >> metis_tac[]) >>
  conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> first_assum irule >> simp[]) >>
  qexists_tac `ty` >> simp[]
QED

(* The combined shift constructor covers both 256-bit shifts and ShR at
   any 0 < n <= 256, avoiding a duplicate right-shift constructor theorem. *)
val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Shift framing has unproved dependencies"
  end) [shift_storage_frame_op, shift_result_words,
        shift_storage_frame_tail, compile_shift_storage_frame_frag];

Theorem compare_straight_fresh[local]:
  MEM bop [Lt;Gt;Eq;NotEq;LtE;GtE] ==>
  straight_fresh (compile_compare bop x y ty)
Proof
  strip_tac >> rw[straight_fresh_def] >>
  drule_all compile_compare_shape >> strip_tac >>
  `compile_binop bop x y ty NONE NONE st = (x',st')` by
    (gvs[compile_binop_def]) >>
  drule compile_binop_grows >> strip_tac >>
  gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]
QED

Theorem compare_storage_frame_op:
  MEM bop [Lt;Gt;Eq;NotEq;LtE;GtE] /\
  compile_compare bop x y ty sa = (op,sb) /\
  eval_operand x s0 = SOME a /\ eval_operand y s0 = SOME b /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. stmt_state_rel ctx func cenv cx es s /\
         eval_operand op s = SOME (bool_to_word (eval_compare bop ty a b)) /\
         (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z s = SOME w) /\
         (!aid base. FLOOKUP s0.vs_allocas aid = SOME base ==> FLOOKUP s.vs_allocas aid = SOME base) /\
         s.vs_memory = s0.vs_memory /\
         contract_storage s = contract_storage s0 /\
         contract_transient s = contract_transient s0) R
Proof
  strip_tac >> irule frag_exec_pre_exit >>
  irule_at (Pat `frag_exec _ _ _ _ _ _`) frag_exec_straight_fresh_storage_frame_success >>
  qexistsl_tac [`compile_compare bop x y ty`, `R`] >>
  qexists_tac `\s. eval_operand x s = SOME a /\ eval_operand y s = SOME b` >>
  simp[compare_straight_fresh, eval_operand_drop_fresh] >>
  rpt strip_tac >> irule compile_compare_correct >> simp[] >>
  goal_assum (drule_at (Pat `compile_compare _ _ _ _ _ = _`)) >> simp[]
QED

Theorem compare_typed_word_second[local]:
  word_value v1 /\ value_has_type tv v1 /\ value_has_type tv v2 ==> word_value v2
Proof
  strip_tac >> fs[word_value_def] >> Cases_on `tv` >> gvs[value_has_type_def] >>
  Cases_on `v2` >> gvs[value_has_type_def, word_value_def] >>
  rename1 `value_has_type (BaseTV bt) _` >> Cases_on `bt` >> gvs[value_has_type_def]
QED

Theorem compile_compare_storage_frame_tail:
  MEM bop [Lt;Gt;Eq;NotEq;LtE;GtE] /\
  bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 es' = INL v /\
  word_value v1 /\ value_has_type tv v1 /\ value_has_type tv v2 /\
  (is_uint256 (expr_type e1) <=> tv = BaseTV (UintT 256)) /\
  (!m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==> m <= 256) /\
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e1)) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e2)) /\
  compile_binop bop x y (expr_type e1) bl el s2 = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  (!z. y = Var z ==> not_fresh_at s2 z) /\ (!l. x <> Label l) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s2 /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  stmt_state_rel ctx func cenv cx es s0 /\
  expr_post ctx func cenv cx e1 es sa s1 s0 es1 v1 x t ==>
  frag_exec ctx s2 sb
    (\s. expr_post ctx func cenv cx e2 es1 s1 s2 t es' v2 y s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
           es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_res_ok (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 es')` by
    simp[expr_res_ok_def] >>
  drule_all bop_result_compare >>
  disch_then assume_tac >>
  `v = BoolV (eval_compare bop (expr_type e1) (val_to_w256 v1) (val_to_w256 v2))` by metis_tac[sumTheory.INL_11] >>
  `word_value v /\ val_to_w256 v = bool_to_word (eval_compare bop (expr_type e1) (val_to_w256 v1) (val_to_w256 v2))` by
    (Cases_on `eval_compare bop (expr_type e1) (val_to_w256 v1) (val_to_w256 v2)` >>
     simp[word_value_def, val_to_w256_def, bool_to_word_def]) >>
  `word_value v2` by metis_tac[compare_typed_word_second] >>
  `compile_compare bop x y (expr_type e1) s2 = (op,sb)` by gvs[compile_binop_def] >>
  irule frag_exec_pointwise >> gen_tac >> BETA_TAC >> strip_tac >>
  rename1 `expr_post ctx _ _ _ _ _ _ _ _ _ _ _ u` >>
  `stmt_state_rel ctx func cenv cx es' u /\
   eval_operand x u = SOME (val_to_w256 v1) /\
   eval_operand y u = SOME (val_to_w256 v2)` by
    (fs[expr_post_def] >>
     `eval_operand x t = SOME (val_to_w256 v1) /\
      eval_operand y u = SOME (val_to_w256 v2)` by
       (conj_tac >> irule expr_val_rel_word >> simp[] >> metis_tac[]) >>
     simp[] >> irule eval_operand_frame >> simp[] >> qexistsl_tac [`s1`, `t`] >> simp[]) >>
  irule frag_exec_conseq >> irule_at Any compare_storage_frame_op >>
  goal_assum (drule_at (Pat `compile_compare _ _ _ _ _ = _`)) >>
  qexistsl_tac [`u`, `func`, `es'`, `cx`, `cenv`, `val_to_w256 v2`, `val_to_w256 v1`, `R`] >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `s1` >> simp[])
  >> rpt strip_tac
  >~ [`expr_post`]
  >- (qpat_x_assum `v = BoolV _` SUBST_ALL_TAC >>
      irule expr_post_bop >> simp[] >>
      goal_assum (drule_at (Pat `expr_post _ _ _ _ e1 _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `expr_post _ _ _ _ e2 _ _ _ _ _ _ _ _`)) >> simp[]) >> gvs[]
QED

Theorem compile_compare_storage_frame_frag:
  MEM bop [Lt;Gt;Eq;NotEq;LtE;GtE] /\
  ~is_bytestring_type (expr_type e1) /\
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e1)) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e2)) /\
  (!v1 es1 v2 es2.
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es1) /\
    (do r <- eval_expr cx e2; read_result cx r od) es1 = (INL v2,es2) ==>
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    ?tv. word_value v1 /\ value_has_type tv v1 /\ value_has_type tv v2 /\
      (is_uint256 (expr_type e1) <=> tv = BaseTV (UintT 256)) /\
      (!m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==> m <= 256)) /\
  (!a b operand.
    lower_value compile_expr cenv (expr_type e1) e1 a = (operand,b) ==> !l. operand <> Label l) /\
  (!e a b operand es0 es1 value start saved savedT R.
    (e = e1 \/ e = e2) /\
    lower_value compile_expr cenv (expr_type e1) e a = (operand,b) /\
    (do r <- eval_expr cx e; read_result cx r od) es0 = (INL value,es1) /\
    fn_has_code a b func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv a ==>
    frag_exec ctx a b
      (\s. s = start /\ stmt_state_rel ctx func cenv cx es0 s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\s. expr_post ctx func cenv cx e es0 a b start es1 value operand s /\
           contract_storage s = saved /\ contract_transient s = savedT) R) /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  (do r <- eval_expr cx (Builtin ann (Bop bop) [e1;e2]); read_result cx r od) es = (INL v,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2]) es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bop <> In /\ bop <> NotIn /\ bop <> Exp` by
    (qpat_x_assum `MEM bop _` mp_tac >> simp[] >> rpt strip_tac >> gvs[]) >>
  irule compile_bop_storage_frame_frag >> simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!v1 es1 v2 es2. _` (drule_all_then strip_assume_tac) >>
      irule compile_compare_storage_frame_tail >> simp[] >>
      qexistsl_tac [`NONE`, `NONE`, `tv`, `v1`, `x`] >> simp[] >> metis_tac[]) >>
  conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> first_assum irule >> simp[]) >>
  qexists_tac `ty` >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Comparison framing has unproved dependencies"
  end) [compare_straight_fresh, compare_storage_frame_op, compare_typed_word_second,
        compile_compare_storage_frame_tail, compile_compare_storage_frame_frag];

Theorem checked_storage_frame_run:
  MEM bop [Add;Sub;Mul] /\
  type_to_int_bound ty = SOME u /\ type_to_int_bound ann = SOME u /\
  0 < type_bits ty /\ type_bits ty <= 256 /\
  within_int_bound u i1 /\ within_int_bound u i2 /\
  bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  fresh_vars_wrt sa s /\ eval_operand x s = SOME (i2w i1) /\
  eval_operand y s = SOME (i2w i2) ==>
  word_value v /\ ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)
Proof
  strip_tac >>
  `bop_result cx ann bop tys (IntV i1) (IntV i2) es =
    if within_int_bound u (if bop = Add then i1 + i2 else if bop = Sub then i1 - i2 else i1 * i2)
    then INL (IntV (if bop = Add then i1 + i2 else if bop = Sub then i1 - i2 else i1 * i2))
    else INR (Error (RuntimeError "bounded_int_op bound"))` by
    (irule (SRULE [LET_THM] bop_result_checked) >> simp[] >> fs[]) >>
  gvs[AllCaseEqs(), word_value_def, val_to_w256_def, compile_binop_def]
  >- (drule_all compile_safe_add_run >> simp[])
  >- (drule_all compile_safe_sub_run >> simp[]) >>
  drule_all compile_safe_mul_run >> simp[]
QED

Theorem checked_result_word[local]:
  MEM bop [Add;Sub;Mul] /\ type_to_int_bound ann = SOME u /\
  bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v ==> word_value v
Proof
  strip_tac >>
  `bop_result cx ann bop tys (IntV i1) (IntV i2) es =
    if within_int_bound u (if bop = Add then i1 + i2 else if bop = Sub then i1 - i2 else i1 * i2)
    then INL (IntV (if bop = Add then i1 + i2 else if bop = Sub then i1 - i2 else i1 * i2))
    else INR (Error (RuntimeError "bounded_int_op bound"))` by
    (irule (SRULE [LET_THM] bop_result_checked) >> simp[] >> fs[]) >>
  gvs[AllCaseEqs(), word_value_def]
QED

Theorem compile_checked_storage_frame_tail:
  MEM bop [Add;Sub;Mul] /\
  bop_result cx ann bop [expr_type e1;expr_type e2] (IntV i1) (IntV i2) es' = INL v /\
  type_to_int_bound (expr_type e1) = SOME u /\ type_to_int_bound ann = SOME u /\
  0 < type_bits (expr_type e1) /\ type_bits (expr_type e1) <= 256 /\
  within_int_bound u i1 /\ within_int_bound u i2 /\
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e1)) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e2)) /\
  compile_binop bop x y (expr_type e1) bl el s2 = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  (!z. y = Var z ==> not_fresh_at s2 z) /\ (!l. x <> Label l) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s2 /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  stmt_state_rel ctx func cenv cx es s0 /\
  expr_post ctx func cenv cx e1 es sa s1 s0 es1 (IntV i1) x t ==>
  frag_exec ctx s2 sb
    (\s. expr_post ctx func cenv cx e2 es1 s1 s2 t es' (IntV i2) y s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
           es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all checked_result_word >> strip_tac >>
  `straight_fresh (compile_binop bop x y (expr_type e1) bl el)` by
    (fs[] >> simp[compile_binop_def, straight_fresh_checked]) >>
  `!z. x = Var z ==> not_fresh_at s2 z` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `s1` >> simp[]) >>
  irule frag_exec_pointwise >> gen_tac >> BETA_TAC >> strip_tac >>
  rename1 `expr_post ctx _ _ _ _ _ _ _ _ _ _ _ w` >>
  `stmt_state_rel ctx func cenv cx es' w /\
   eval_operand x w = SOME (i2w i1) /\ eval_operand y w = SOME (i2w i2)` by
    (fs[expr_post_def] >>
     `eval_operand x t = SOME (i2w i1) /\ eval_operand y w = SOME (i2w i2)` by
       (conj_tac >> metis_tac[expr_val_rel_word, word_value_def, val_to_w256_def]) >>
     simp[] >> irule eval_operand_frame >> simp[] >> qexistsl_tac [`s1`, `t`] >> simp[]) >>
  irule frag_exec_conseq >> irule_at Any frag_exec_straight_fresh_storage_frame_success >>
  qexistsl_tac [`val_to_w256 v`, `w`, `op`,
    `compile_binop bop x y (expr_type e1) bl el`, `func`, `es'`, `cx`, `cenv`, `R`] >>
  qexists_tac `\s. eval_operand x s = SOME (i2w i1) /\ eval_operand y s = SOME (i2w i2)` >>
  simp[eval_operand_drop_fresh] >> rpt conj_tac
  >- (rpt strip_tac >> drule_all checked_storage_frame_run >> metis_tac[]) >>
  rpt strip_tac
  >~ [`expr_post`]
  >- (irule expr_post_bop >> simp[] >>
      goal_assum (drule_at (Pat `expr_post _ _ _ _ e1 _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `expr_post _ _ _ _ e2 _ _ _ _ _ _ _ _`)) >> simp[]) >> gvs[]
QED

Theorem compile_checked_storage_frame_frag:
  MEM bop [Add;Sub;Mul] /\
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e1)) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e2)) /\
  (!v1 es1 v2 es2.
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es1) /\
    (do r <- eval_expr cx e2; read_result cx r od) es1 = (INL v2,es2) ==>
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    ?i1 i2 u. v1 = IntV i1 /\ v2 = IntV i2 /\
      type_to_int_bound (expr_type e1) = SOME u /\ type_to_int_bound ann = SOME u /\
      0 < type_bits (expr_type e1) /\ type_bits (expr_type e1) <= 256 /\
      within_int_bound u i1 /\ within_int_bound u i2) /\
  (!a b operand.
    lower_value compile_expr cenv (expr_type e1) e1 a = (operand,b) ==> !l. operand <> Label l) /\
  (!e a b operand es0 es1 value start saved savedT R.
    (e = e1 \/ e = e2) /\
    lower_value compile_expr cenv (expr_type e1) e a = (operand,b) /\
    (do r <- eval_expr cx e; read_result cx r od) es0 = (INL value,es1) /\
    fn_has_code a b func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv a ==>
    frag_exec ctx a b
      (\s. s = start /\ stmt_state_rel ctx func cenv cx es0 s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\s. expr_post ctx func cenv cx e es0 a b start es1 value operand s /\
           contract_storage s = saved /\ contract_transient s = savedT) R) /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  (do r <- eval_expr cx (Builtin ann (Bop bop) [e1;e2]); read_result cx r od) es = (INL v,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2]) es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bop <> In /\ bop <> NotIn /\ bop <> Exp` by
    (qpat_x_assum `MEM bop _` mp_tac >> simp[] >> rpt strip_tac >> gvs[]) >>
  irule compile_bop_storage_frame_frag >> simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!v1 es1 v2 es2. _` (drule_all_then strip_assume_tac) >>
      gvs[] >> irule compile_checked_storage_frame_tail >> simp[] >>
      qexistsl_tac [`NONE`, `NONE`, `i1`, `x`] >> simp[] >> metis_tac[]) >>
  conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> first_assum irule >> simp[]) >>
  conj_tac >- (disj2_tac >> fs[]) >>
  qexists_tac `ty` >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Checked arithmetic framing has unproved dependencies"
  end) [checked_storage_frame_run, checked_result_word,
        compile_checked_storage_frame_tail, compile_checked_storage_frame_frag];

Theorem compile_checked_storage_frame_reachable_frag:
  MEM bop [Add;Sub;Mul] /\
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e1)) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e2)) /\
  (!v1 es1 v2 es2.
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es1) /\
    (do r <- eval_expr cx e2; read_result cx r od) es1 = (INL v2,es2) ==>
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    ?i1 i2 u. v1 = IntV i1 /\ v2 = IntV i2 /\
      type_to_int_bound (expr_type e1) = SOME u /\ type_to_int_bound ann = SOME u /\
      0 < type_bits (expr_type e1) /\ type_bits (expr_type e1) <= 256 /\
      within_int_bound u i1 /\ within_int_bound u i2) /\
  (!a b operand.
    lower_value compile_expr cenv (expr_type e1) e1 a = (operand,b) ==> !l. operand <> Label l) /\
  (!e a b operand es0 es1 value start saved savedT R.
    ((e = e1 /\ es0 = es) \/
     (e = e2 /\ ?vfirst.
       (do r <- eval_expr cx e1; read_result cx r od) es = (INL vfirst,es0))) /\
    lower_value compile_expr cenv (expr_type e1) e a = (operand,b) /\
    (do r <- eval_expr cx e; read_result cx r od) es0 = (INL value,es1) /\
    fn_has_code a b func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv a ==>
    frag_exec ctx a b
      (\s. s = start /\ stmt_state_rel ctx func cenv cx es0 s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\s. expr_post ctx func cenv cx e es0 a b start es1 value operand s /\
           contract_storage s = saved /\ contract_transient s = savedT) R) /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  (do r <- eval_expr cx (Builtin ann (Bop bop) [e1;e2]); read_result cx r od) es = (INL v,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2]) es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bop <> In /\ bop <> NotIn /\ bop <> Exp` by
    (qpat_x_assum `MEM bop _` mp_tac >> simp[] >> rpt strip_tac >> gvs[]) >>
  irule compile_bop_storage_frame_reachable_frag >> simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!v1 es1 v2 es2. _` (drule_all_then strip_assume_tac) >>
      gvs[] >> irule compile_checked_storage_frame_tail >> simp[] >>
      qexistsl_tac [`NONE`, `NONE`, `i1`, `x`] >> simp[] >> metis_tac[]) >>
  conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> first_assum irule >> simp[]) >>
  conj_tac >- (disj2_tac >> fs[]) >>
  qexists_tac `ty` >> simp[]
QED

Theorem compile_shift_storage_frame_reachable_frag:
  (bop = ShL \/ bop = ShR) /\
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e1)) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e2)) /\
  (!v1 es1 v2 es2.
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es1) /\
    (do r <- eval_expr cx e2; read_result cx r od) es1 = (INL v2,es2) ==>
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    ?i1 i2. v1 = IntV i1 /\ v2 = IntV i2 /\ within_int_bound (Unsigned 256) i2 /\
      ((type_to_int_bound ann = SOME (if is_signed_type (expr_type e1) then Signed 256 else Unsigned 256) /\
        within_int_bound (if is_signed_type (expr_type e1) then Signed 256 else Unsigned 256) i1) \/
       (bop = ShR /\ ?n. 0 < n /\ n <= 256 /\
        type_to_int_bound ann = SOME (if is_signed_type (expr_type e1) then Signed n else Unsigned n) /\
        within_int_bound (if is_signed_type (expr_type e1) then Signed n else Unsigned n) i1))) /\
  (!a b operand.
    lower_value compile_expr cenv (expr_type e1) e1 a = (operand,b) ==> !l. operand <> Label l) /\
  (!e a b operand es0 es1 value start saved savedT R.
    ((e = e1 /\ es0 = es) \/
     (e = e2 /\ ?vfirst.
       (do r <- eval_expr cx e1; read_result cx r od) es = (INL vfirst,es0))) /\
    lower_value compile_expr cenv (expr_type e1) e a = (operand,b) /\
    (do r <- eval_expr cx e; read_result cx r od) es0 = (INL value,es1) /\
    fn_has_code a b func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv a ==>
    frag_exec ctx a b
      (\s. s = start /\ stmt_state_rel ctx func cenv cx es0 s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\s. expr_post ctx func cenv cx e es0 a b start es1 value operand s /\
           contract_storage s = saved /\ contract_transient s = savedT) R) /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  (do r <- eval_expr cx (Builtin ann (Bop bop) [e1;e2]); read_result cx r od) es = (INL v,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2]) es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bop <> In /\ bop <> NotIn /\ bop <> Eq /\ bop <> NotEq /\ bop <> Exp` by
    (qpat_x_assum `bop = ShL \/ _` mp_tac >> rpt strip_tac >> gvs[]) >>
  irule compile_bop_storage_frame_reachable_frag >> simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!v1 es1 v2 es2. _` (drule_all_then strip_assume_tac) >>
      irule shift_storage_frame_tail >> simp[] >>
      qexistsl_tac [`NONE`, `NONE`, `i1`, `x`] >> simp[] >> metis_tac[]) >>
  conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> first_assum irule >> simp[]) >>
  qexists_tac `ty` >> simp[]
QED

Theorem compile_compare_storage_frame_reachable_frag:
  MEM bop [Lt;Gt;Eq;NotEq;LtE;GtE] /\
  ~is_bytestring_type (expr_type e1) /\
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e1)) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e2)) /\
  (!v1 es1 v2 es2.
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es1) /\
    (do r <- eval_expr cx e2; read_result cx r od) es1 = (INL v2,es2) ==>
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    ?tv. word_value v1 /\ value_has_type tv v1 /\ value_has_type tv v2 /\
      (is_uint256 (expr_type e1) <=> tv = BaseTV (UintT 256)) /\
      (!m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==> m <= 256)) /\
  (!a b operand.
    lower_value compile_expr cenv (expr_type e1) e1 a = (operand,b) ==> !l. operand <> Label l) /\
  (!e a b operand es0 es1 value start saved savedT R.
    ((e = e1 /\ es0 = es) \/
     (e = e2 /\ ?vfirst.
       (do r <- eval_expr cx e1; read_result cx r od) es = (INL vfirst,es0))) /\
    lower_value compile_expr cenv (expr_type e1) e a = (operand,b) /\
    (do r <- eval_expr cx e; read_result cx r od) es0 = (INL value,es1) /\
    fn_has_code a b func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv a ==>
    frag_exec ctx a b
      (\s. s = start /\ stmt_state_rel ctx func cenv cx es0 s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\s. expr_post ctx func cenv cx e es0 a b start es1 value operand s /\
           contract_storage s = saved /\ contract_transient s = savedT) R) /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  (do r <- eval_expr cx (Builtin ann (Bop bop) [e1;e2]); read_result cx r od) es = (INL v,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2]) es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bop <> In /\ bop <> NotIn /\ bop <> Exp` by
    (qpat_x_assum `MEM bop _` mp_tac >> simp[] >> rpt strip_tac >> gvs[]) >>
  irule compile_bop_storage_frame_reachable_frag >> simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!v1 es1 v2 es2. _` (drule_all_then strip_assume_tac) >>
      irule compile_compare_storage_frame_tail >> simp[] >>
      qexistsl_tac [`NONE`, `NONE`, `tv`, `v1`, `x`] >> simp[] >> metis_tac[]) >>
  conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> first_assum irule >> simp[]) >>
  qexists_tac `ty` >> simp[]
QED

Theorem compile_bitwise_storage_frame_reachable_frag:
  (bop = And \/ bop = Or \/ bop = XOr) /\
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e1)) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e2)) /\
  (!v1 es1 v2 es2.
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es1) /\
    (do r <- eval_expr cx e2; read_result cx r od) es1 = (INL v2,es2) ==>
    word_value v1 /\ word_value v2 /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    (!i1 i2. v1 = IntV i1 /\ v2 = IntV i2 ==>
      within_int_bound (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i1 /\
      within_int_bound (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i2)) /\
  (!a b operand.
    lower_value compile_expr cenv (expr_type e1) e1 a = (operand,b) ==>
    !l. operand <> Label l) /\
  (!e a b operand es0 es1 value start saved savedT R.
    ((e = e1 /\ es0 = es) \/
     (e = e2 /\ ?vfirst.
       (do r <- eval_expr cx e1; read_result cx r od) es = (INL vfirst,es0))) /\
    lower_value compile_expr cenv (expr_type e1) e a = (operand,b) /\
    (do r <- eval_expr cx e; read_result cx r od) es0 = (INL value,es1) /\
    fn_has_code a b func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv a ==>
    frag_exec ctx a b
      (\s. s = start /\ stmt_state_rel ctx func cenv cx es0 s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\s. expr_post ctx func cenv cx e es0 a b start es1 value operand s /\
           contract_storage s = saved /\ contract_transient s = savedT) R) /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  (do r <- eval_expr cx (Builtin ann (Bop bop) [e1;e2]); read_result cx r od) es = (INL v,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2]) es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bop <> In /\ bop <> NotIn /\ bop <> Eq /\ bop <> NotEq` by
    (qpat_x_assum `bop = And \/ _` mp_tac >> rpt strip_tac >> gvs[]) >>
  irule compile_bop_storage_frame_reachable_frag >> simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!v1 es1 v2 es2. _` (drule_all_then strip_assume_tac) >>
      `bop <> Exp` by
        (qpat_x_assum `bop = And \/ _` mp_tac >> rpt strip_tac >> gvs[]) >>
      irule bitwise_storage_frame_tail >> simp[] >>
      goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> first_assum irule >> simp[]) >>
  qexists_tac `ty` >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Reachable binary framing has unproved dependencies"
  end) [compile_bop_storage_frame_reachable_frag,
        compile_checked_storage_frame_reachable_frag,
        compile_shift_storage_frame_reachable_frag,
        compile_compare_storage_frame_reachable_frag,
        compile_bitwise_storage_frame_reachable_frag];

Theorem integer_typed_value_bound:
  is_int_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
  ?i u. v = IntV i /\ type_to_int_bound ty = SOME u /\
    within_int_bound u i /\ 0 < type_bits ty /\ type_bits ty <= 256
Proof
  strip_tac >> Cases_on `ty` >> gvs[is_int_type_def] >>
  rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[is_int_type_def, evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[value_has_type_def, type_to_int_bound_def, type_bits_def] >>
  simp[within_int_bound_def]
QED

Theorem integer_bop_operand_types[local]:
  well_typed_binop ann bop t1 t2 /\ MEM bop [Add;Sub;Mul] /\ is_int_type ann ==>
  t1 = ann /\ t2 = ann /\ is_word_type ann /\ word_value_type ann
Proof
  strip_tac >> fs[] >> gvs[well_typed_binop_def] >>
  Cases_on `ann` >> gvs[is_int_type_def] >>
  rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[is_int_type_def, is_word_type_def, word_value_type_def, is_numeric_type_def]
QED

Theorem integer_bop_success_types[local]:
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  MEM bop [Add;Sub;Mul] /\ is_int_type ann /\
  (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1,es1) /\
  (do r <- eval_expr cx e2; read_result cx r od) es1 = (INL v2,es2) ==>
  expr_type e1 = ann /\ expr_type e2 = ann /\
  is_word_type ann /\ IS_SOME (evaluate_type (get_tenv cx) ann) /\
  expr_body_pre cenv cx env e1 es /\ expr_body_pre cenv cx env e2 es1 /\
  ?i1 i2 u. v1 = IntV i1 /\ v2 = IntV i2 /\ type_to_int_bound ann = SOME u /\
    0 < type_bits ann /\ type_bits ann <= 256 /\
    within_int_bound u i1 /\ within_int_bound u i2
Proof
  strip_tac >> drule expr_body_pre_bop >> strip_tac >>
  drule_all integer_bop_operand_types >> strip_tac >>
  `word_value_type (expr_type e1)` by simp[] >>
  drule_all expr_body_pre_word_result >> strip_tac >>
  `expr_body_pre cenv cx env e2 es1` by metis_tac[] >>
  `word_value_type (expr_type e2)` by simp[] >>
  qpat_assum `expr_body_pre _ _ _ e2 es1`
    (mp_then Any mp_tac expr_body_pre_word_result) >>
  simp[] >> strip_tac >>
  gvs[] >>
  `?i u. v1 = IntV i /\ type_to_int_bound (expr_type e1) = SOME u /\
    within_int_bound u i /\ 0 < type_bits (expr_type e1) /\ type_bits (expr_type e1) <= 256` by
    (irule integer_typed_value_bound >> metis_tac[]) >>
  qpat_assum `value_has_type _ v2`
    (mp_then Any (qspecl_then [`expr_type e1`, `get_tenv cx`] mp_tac)
      integer_typed_value_bound) >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem supported_word_eval_scopes[local]:
  supported_pure_expr tops e /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
  es'.scopes = es.scopes
Proof
  simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
  drule_all supported_eval_expr_outcomes >> strip_tac >>
  drule read_result_state >> strip_tac >> gvs[] >>
  qpat_x_assum `es' = _` (mp_tac o Q.AP_TERM `\s. s.scopes`) >> simp[]
QED

Theorem compile_checked_storage_frame_typed:
  MEM bop [Add;Sub;Mul] /\ is_int_type ann /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  supported_pure_expr tops e1 /\ supported_pure_expr tops e2 /\
  (!e env0 a b operand es0 es1 value start saved savedT R.
    (e = e1 \/ e = e2) /\ expr_body_pre cenv cx env0 e es0 /\
    lower_value compile_expr cenv (expr_type e1) e a = (operand,b) /\
    (do r <- eval_expr cx e; read_result cx r od) es0 = (INL value,es1) /\
    fn_has_code a b func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv a ==>
    frag_exec ctx a b
      (\s. s = start /\ stmt_state_rel ctx func cenv cx es0 s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\s. expr_post ctx func cenv cx e es0 a b start es1 value operand s /\
           contract_storage s = saved /\ contract_transient s = savedT) R) /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  (do r <- eval_expr cx (Builtin ann (Bop bop) [e1;e2]); read_result cx r od) es = (INL v,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2]) es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule successful_bop_operands >> strip_tac >>
  drule_all integer_bop_success_types >> strip_tac >>
  irule compile_checked_storage_frame_reachable_frag >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule expr_body_pre_lower_value_word_shape >>
      disch_then (qspecl_then [`cx`, `env`, `es`] mp_tac) >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!e env0 a b operand es0 es1 value start saved savedT R. _`
        irule >> gvs[] >> qexists_tac `env` >> simp[]) >>
  conj_tac
  >- (`es1.scopes = es.scopes` by
        (irule supported_word_eval_scopes >> metis_tac[]) >> simp[]) >>
  qexists_tac `ty` >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Typed integer framing has unproved dependencies"
  end) [integer_typed_value_bound, integer_bop_operand_types,
        integer_bop_success_types, supported_word_eval_scopes,
        compile_checked_storage_frame_typed];

(* Mapping roots produce addresses, not readable values.  The metadata lookup
   is explicit: source typing/metadata transport is a separate obligation. *)
Theorem compile_toplevel_slot_vv_shape:
  FLOOKUP cenv.ce_module_vars nsid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) ==>
  compile_expr cenv ty (TopLevelName ann nsid) sa =
    (LocatedValue ann (mk_ptr (Lit slot) (slot_loc tr)),sa)
Proof
  Cases_on `tr` >>
  simp[Once compile_expr_raw_def, compile_expr_body_def,
       expr_type_def, slot_loc_def]
QED

Theorem hashmap_root_place_ptr_rel:
  place_ptr_rel cenv cx s (HashMapRef tr slot kt vt)
    slot (SOME (slot_loc tr)) (HashMapT kt vt)
Proof
  simp[place_ptr_rel_def]
QED

Theorem compile_hashmap_root_storage_frame_frag:
  FLOOKUP cenv.ce_module_vars nsid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  compile_expr cenv ty (TopLevelName ann nsid) sa = (vv,sb) ==>
  frag_exec ctx sa sb (\s. s = s0 /\ P s)
    (\s. s = s0 /\ P s /\
      (?w. eval_operand (vv_operand vv) s = SOME w /\
           place_ptr_rel cenv cx s (HashMapRef tr slot kt vt)
             w (vv_location vv) (HashMapT kt vt)) /\
      contract_storage s = contract_storage s0 /\
      contract_transient s = contract_transient s0) R
Proof
  strip_tac >> drule compile_toplevel_slot_vv_shape >> strip_tac >> gvs[] >>
  irule frag_exec_refl >>
  simp[contextTheory.vv_operand_def, contextTheory.vv_location_def,
       contextTheory.mk_ptr_def, eval_operand_def, hashmap_root_place_ptr_rel]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Mapping root frame has unproved dependencies"
  end)
  [compile_toplevel_slot_vv_shape, hashmap_root_place_ptr_rel,
   compile_hashmap_root_storage_frame_frag];

Theorem mapping_place_root_type_lookup:
  type_place_expr env (TopLevelName ann nsid) = SOME (HashMapT kt vt) ==>
  FLOOKUP env.toplevel_vtypes nsid = SOME (HashMapT kt vt)
Proof
  PairCases_on `nsid` >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem mapping_place_defined_table:
  place_map_tables_agree_on_defined cenv env /\
  FLOOKUP env.toplevel_vtypes nsid = SOME (HashMapT kt vt) ==>
  ?tr. cenv.ce_hashmap_info nsid = SOME (tr,kt,vt)
Proof
  strip_tac >>
  qpat_x_assum `place_map_tables_agree_on_defined _ _` mp_tac >>
  simp[placeTypingPropsTheory.place_map_tables_agree_on_defined_def] >>
  disch_then (qspecl_then [`nsid`, `HashMapT kt vt`] mp_tac) >> simp[] >>
  Cases_on `cenv.ce_hashmap_info nsid` >> simp[] >>
  rename1 `SOME info` >> PairCases_on `info` >> simp[]
QED

Theorem mapping_place_subscript_types:
  type_place_expr env (Subscript ann obj key) = SOME (HashMapT kt vt) ==>
  ?keyty. type_place_expr env obj = SOME (HashMapT keyty (HashMapT kt vt)) /\
    well_typed_expr env key /\ expr_type key = keyty /\ hashmap_key_type keyty
Proof
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
  rename1 `subscript_vtype base_ty _ = SOME _` >>
  Cases_on `base_ty` >> gvs[subscript_vtype_def, AllCaseEqs()] >>
  rename1 `subscript_vtype (Type t) _ = SOME _` >>
  Cases_on `t` >> gvs[subscript_vtype_def, AllCaseEqs()]
QED

Theorem mapping_place_constructor:
  type_place_expr env e = SOME (HashMapT kt vt) ==>
  (?ann nsid. e = TopLevelName ann nsid) \/
  (?ann obj key. e = Subscript ann obj key)
Proof
  Cases_on `e` >> simp[Once well_typed_expr_def]
QED

Theorem mapping_subscript_syntactic_limits:
  byte_widths_expr (Subscript ann obj key) /\
  alloc_limits_expr cenv (Subscript ann obj key) ==>
  byte_widths_expr obj /\ byte_widths_expr key /\
  alloc_limits_expr cenv obj /\ alloc_limits_expr cenv key
Proof
  simp[byte_widths_expr_def, allocLimitsTheory.alloc_limits_expr_def]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Mapping place typing has unproved dependencies"
  end)
  [mapping_place_root_type_lookup, mapping_place_defined_table,
   mapping_place_subscript_types, mapping_place_constructor,
   mapping_subscript_syntactic_limits];

Theorem lookup_global_hashmap_module_vars:
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  lookup_global cx src name es = (INL (HashMapRef tr slot kt vt),es') ==>
  es' = es /\
  FLOOKUP cenv.ce_module_vars (src,name) =
    SOME (if tr then TransientLoc slot else StorageLoc slot)
Proof
  simp[lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
      var_decl_info_CASE_rator, bind_def, lift_option_type_def,
      return_def, raise_def, AllCaseEqs()] >>
  gvs[storage_vars_rel_def, transient_vars_rel_def] >>
  Cases_on `tr` >> gvs[var_decl_transient_def] >> metis_tac[]
QED

Theorem eval_hashmap_root_module_vars:
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  eval_expr cx (TopLevelName ann (src,name)) es =
    (INL (HashMapRef tr slot kt vt),es') ==>
  es' = es /\
  FLOOKUP cenv.ce_module_vars (src,name) =
    SOME (if tr then TransientLoc slot else StorageLoc slot)
Proof
  simp[Once evaluate_def] >> metis_tac[lookup_global_hashmap_module_vars]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Mapping root metadata has unproved dependencies"
  end)
  [lookup_global_hashmap_module_vars, eval_hashmap_root_module_vars];

Theorem eval_hashmap_root_storage_frame_frag:
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  eval_expr cx (TopLevelName ann (src,name)) es =
    (INL (HashMapRef tr slot kt vt),es') /\
  compile_expr cenv ty (TopLevelName ann (src,name)) sa = (vv,sb) ==>
  frag_exec ctx sa sb (\s. s = s0 /\ P s)
    (\s. s = s0 /\ P s /\
      (?w. eval_operand (vv_operand vv) s = SOME w /\
           place_ptr_rel cenv cx s (HashMapRef tr slot kt vt)
             w (vv_location vv) (HashMapT kt vt)) /\
      contract_storage s = contract_storage s0 /\
      contract_transient s = contract_transient s0) R
Proof
  strip_tac >> drule_all eval_hashmap_root_module_vars >> strip_tac >>
  irule compile_hashmap_root_storage_frame_frag >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any)
QED

val () =
  let val th = eval_hashmap_root_storage_frame_frag
      val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Mapping root source frame has unproved dependencies"
  end;
