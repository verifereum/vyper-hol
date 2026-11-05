Theory bodyIntCallExprFrame
Ancestors
  exprSim bodyIntCallSemanticFrame loweringSlice fragExec exprLowering
  compileEnv localPtrsProps stmtSim valueEncoding valueEncodingProps
  vyperAST vyperInterpreter vyperValue venomInst venomState finite_map
  loweringPosts vyperValueOperation emitHelper exprSimUnwrap emitHelperProps vyperState
  exprSimHyps vyperTypeEnv vyperTypeInvariants vyperTyping valueEncodingProofs
  vyperTypeSystem exprLoweringProps venomExecSemantics exprSimUnop builtinSimple
  words integer_word arithmeticProps builtinProps vyperContext exprOperandVar
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
