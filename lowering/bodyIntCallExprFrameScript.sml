Theory bodyIntCallExprFrame
Ancestors
  exprSimDefs exprSimProps bodyIntCallSemanticFrame loweringSlice fragExec exprLowering
  compileEnv localPtrsProps stmtSimDefs stmtSimProps valueEncoding valueEncodingProps
  vyperAST vyperInterpreter vyperValue venomInst venomState finite_map
  loweringPosts vyperValueOperation emitHelper exprSimUnwrap emitHelperProps vyperState
  exprSimHyps vyperTypeEnv vyperTypeInvariants vyperTyping valueEncodingProofs
  vyperTypeSystem exprLoweringProps venomExecSemantics exprSimUnop builtinSimple
  words integer_word arithmeticProps builtinProps vyperContext exprOperandVar
  bodyIntCallForceTransfer bodyIntCallAggregateCopy
  exprSimOps exprBopLowering exprSimCompare freshWrites rich_list exprSimArith
  vyperHashMapStorage
  exprSimOperators bodyIntCallSourceFrame bodyIntCallMappingFrame
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

Theorem unwrap_runtime_immutable_word_storage_frame_frag:
  emit_op DLOAD [p.ptr_operand] sm = (op,sb) /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ is_word_type t /\
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
       immutable_holds cenv cx (expr_type e) (Value v) w es' /\
       stmt_state_rel ctx func cenv cx es' s1` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  drule_all immutable_holds_dload >> strip_tac >>
  irule frag_exec_conseq >> irule_at Any emit_op_storage_frame_frag >>
  goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  qexistsl [`word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP (w2n w) s1.vs_data_section ++ REPLICATE 32 0w))`,
       `s1`, `func`, `es'`, `cx`] >>
  qexists `R` >> simp[is_terminator_def] >>
  conj_tac >- (rpt strip_tac >> gvs[step_inst_base_def, exec_read1_def]) >>
  rpt strip_tac
  >~ [`expr_post`]
  >- (irule expr_post_of_vv_post_load >> simp[] >>
      goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[]) >>
  gvs[]
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
Theorem unwrap_noncopy_runtime_storage_frame_frag:
  unwrap_value cenv vv sm = (op,sb) /\ ~cenv.ce_is_ctor /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (case vv of StackValue t operand => T
    | LocatedValue t p => p.ptr_location = LocMemory \/ is_word_type t) ==>
  frag_exec ctx sm sb
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  strip_tac >> Cases_on `vv`
  >- (irule unwrap_memory_stack_storage_frame_frag >> gvs[]) >>
  rename1 `LocatedValue t p` >>
  Cases_on `p.ptr_location = LocMemory`
  >- (irule unwrap_memory_stack_storage_frame_frag >> gvs[]) >>
  gvs[] >> Cases_on `p.ptr_location = LocCalldata`
  >- (irule frag_exec_conseq >> qexistsl [`\s. F`, `\s. F`, `R`] >>
      gvs[frag_exec_false_pre, vv_post_calldata]) >>
  Cases_on `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient`
  >- (irule unwrap_storage_word_storage_frame_frag >> simp[]) >>
  `p.ptr_location = LocCode` by (Cases_on `p.ptr_location` >> gvs[]) >>
  irule unwrap_runtime_immutable_word_storage_frame_frag >>
  gvs[unwrap_value_def, contextTheory.compile_ptr_load_def,
      contextTheory.compile_imm_load_word_def]
QED

(* This boundary excludes aggregate copies from storage, transient storage
   and code. Exceptions and failed reads are handled by the transfer. *)
Theorem raw_to_forced_noncopy_runtime_storage_frame_frag:
  compile_expr cenv ty e sa = (vv,sm) /\
  unwrap_value cenv vv sm = (op,sb) /\
  eval_expr cx e es = (rawres,est) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (res,es') /\
  expr_res_ok res /\ ~cenv.ce_is_ctor /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (case vv of StackValue t operand => T
    | LocatedValue t p => p.ptr_location = LocMemory \/ is_word_type t) /\
  frag_exec ctx sa sm P
    (\s. ?raw. rawres = INL raw /\
         vv_post ctx func cenv cx e es sa sm s0 est raw vv s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (expr_exit rawres) ==>
  frag_exec ctx sa sb P
    (\s. ?v. res = INL v /\
         expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (expr_exit res)
Proof
  strip_tac >> irule raw_to_forced_storage_frame_frag >> simp[] >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  simp[] >> rpt strip_tac >>
  irule unwrap_noncopy_runtime_storage_frame_frag >> simp[]
QED

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

(* Typed consumer boundary: this starts AFTER a successful forced child;
   it does not assert that all reachable keys have a framed producer. *)
Theorem mapping_dynamic_key_post_hash_frag:
  expr_post ctx func cenv cx e es sa sm s0 es' (BytesV bs) key mid /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  compile_keccak256_key key F sm = (out,sb) /\
  (!x. key = Var x ==> not_fresh_at sm x) /\
  local_ptrs_reserved cenv sm ==>
  frag_exec ctx sm sb (\s. s = mid)
    (\t. eval_operand out t = SOME
          (encode_hashmap_key (BaseT (BytesT (Dynamic cap))) (BytesV bs)) /\
      stmt_state_rel ctx func cenv cx es' t /\
      t.vs_memory = mid.vs_memory /\ t.vs_allocas = mid.vs_allocas /\
      contract_storage t = contract_storage mid /\
      contract_transient t = contract_transient mid /\
      (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x mid)) R
Proof
  strip_tac >>
  drule_all exprSimHashTheory.hash_dynamic_post_view >> strip_tac >>
  simp[vyperStorageTheory.encode_hashmap_key_def, byteTheory.word_of_bytes_be_def] >>
  irule compile_keccak256_key_bytes_frame_frag >>
  goal_assum (drule_at Any) >>
  reverse conj_tac >- gvs[expr_post_def] >>
  qexistsl [`key`, `n2w b`] >>
  simp[GSYM mem_word_at_eq_mload, abiDecodeStaticPropsTheory.w2n_add_n2w_lt]
QED

(* The scalar MapPT branch uses typed encoding, never the untyped
   length-20 heuristic. These equations also test fixed bytes20. *)
Theorem mapping_scalar_key_encoding:
  (!bt i. typed_val_to_w256 (BaseTV bt) (IntV i) =
     encode_hashmap_key (BaseT bt) (IntV i)) /\
  (!tv kt n. typed_val_to_w256 tv (FlagV n) =
     encode_hashmap_key kt (FlagV n)) /\
  (!bt b. typed_val_to_w256 (BaseTV bt) (BoolV b) =
     encode_hashmap_key (BaseT bt) (BoolV b)) /\
  (!bs. typed_val_to_w256 (BaseTV AddressT) (BytesV bs) =
     encode_hashmap_key (BaseT AddressT) (BytesV bs)) /\
  (!n bs. typed_val_to_w256 (BaseTV (BytesT (Fixed n))) (BytesV bs) =
     encode_hashmap_key (BaseT (BytesT (Fixed n))) (BytesV bs))
Proof
  simp[typed_val_to_w256_def, val_to_w256_def,
       vyperStorageTheory.encode_hashmap_key_def] >>
  Cases >> simp[typed_val_to_w256_def, val_to_w256_def] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >>
  simp[typed_val_to_w256_def, val_to_w256_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[typed_val_to_w256_def, val_to_w256_def]
QED

(* MapPT key handoff audit (expression dispatch only).

   Child success/exception interface: expr_sim_def quantifies over
     lower_value compile_expr cenv ty key sa = (op,sb),
     (do r <- eval_expr cx key; read_result cx r od) es = (res,es'),
     expr_res_ok res, fn_has_code sa sb func, fn_inst_ids_distinct func,
     local_ptrs_reserved cenv sa.
   It supplies frag_exec with entry s=s0 /\ stmt_state_rel ... es s,
   post ?v. res=INL v /\ expr_post ... es' v op s, and expr_exit res.
   expr_res_ok includes runtime/revert errors and assertions, not type
   errors; expr_exit_def specifies the corresponding Abort outcomes.
   This is NOT yet the needed same-execution storage/transient frame.
   framed_vv_memory_stack_lower_value_frag only handles successful Value v
   with StackValue or LocMemory, and takes the framed raw child as input.
   Missing: total reachable FORCED producer (including exceptional reads,
   storage/transient/immutable locations), not another success wrapper.

   Encoding: mapping_scalar_key_encoding checks IntV, FlagV, BoolV,
   AddressT/PAD_LEFT and Fixed bytes/PAD_RIGHT (including bytes20).
   Decimal is not a hashmap_key_type. Dynamic bytes and strings use F in
   compile_keccak256_key, never the fixed-bytes hashing branch.
   hash_dynamic_post_view/hash_string_post_view require expr_post, the
   exact expr_type and successful evaluate_type. They supply a pointer b,
   length word, data at b+32, b+32<dimword and length<dimword. The checked
   mapping_dynamic_key_post_hash_frag adapts precisely these facts via
   mem_word_at_eq_mload and w2n_add_n2w_lt. evaluate_type is an explicit
   input: support alone does not give its capacity/slot-size bounds.

   Base operand lifetime: expr_post_def preserves every existing SOME
   lookup at not_fresh_at sa variables. Together with safe_operand and
   its known evaluation, safe_operand_value_preserved keeps the mapping
   slot operand across lower_value. No absent-lookup equality is needed;
   HashMapRef has no target memory payload. The suffix preserves old
   lookups exactly. A reachable PLACE producer still must provide the
   base slot and freshness, not ordinary expr_vv_res_ok for a mapping.

   Scratch entry: local_ptrs_reserved_next_var transports reservation
   given the compiler next-var inequality. fn_has_code_split transports
   code given both cs_extends facts; compile_expr_extends,
   unwrap_value_extends and suffix extension supply those boundaries.
   stmt_state_rel is part of the actual expr_post and is retained by
   compile_keccak256_key_bytes_frame_frag; it must not be transported
   across arbitrary source outcomes by assumption.

   Caller memory: expr_post_def keeps allocation entries and old regions
   with aid<sa.cs_next_id disjoint from ALL local_region entries at the
   child start, plus locals_kept. It does NOT frame arbitrary caller
   bytes. The hashing suffix keeps memory and allocas exactly.
   compile_mapping_subscript_frame_frag keeps old allocation entries,
   every old allocation region (aid below scratch entry next_id), and
   local regions. Composition therefore needs the original caller
   region's initial disjointness and surviving entry, then id monotonicity;
   it cannot remove the child's local-disjointness premise. Missing total
   RAW/FORCED/PLACE producers must carry these same-endpoint posts and
   storage projections. No unconditional nested producer follows here.
*)

(* Runtime suffix dispatch retains the copy layout obligations explicitly. *)
Theorem unwrap_runtime_storage_frame_frag:
  unwrap_value cenv vv sm = (op,sb) /\ ~cenv.ce_is_ctor /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (case vv of StackValue t operand => T | LocatedValue t p =>
    ~is_word_type t /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
     p.ptr_location = LocCode) ==>
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
      type_memory_bytes cenv t = type_memory_size tvt /\
      ((p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
       type_memory_size tvt < 2 ** 64))) ==>
  frag_exec ctx sm sb
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  Cases_on `vv`
  >- (irule unwrap_noncopy_runtime_storage_frame_frag >> gvs[]) >>
  rename1 `LocatedValue t p` >>
  Cases_on `p.ptr_location = LocMemory \/ is_word_type t`
  >- (irule unwrap_noncopy_runtime_storage_frame_frag >> gvs[]) >>
  Cases_on `p.ptr_location = LocCalldata`
  >- (irule frag_exec_conseq >> qexistsl [`\s. F`, `\s. F`, `R`] >>
      gvs[frag_exec_false_pre, vv_post_calldata]) >>
  Cases_on `p.ptr_location = LocCode`
  >- (gvs[] >> irule frag_exec_pointwise >> gen_tac >> simp[] >> strip_tac >>
      drule_all unwrap_runtime_code_copy_storage_frame_frag >>
      disch_then (qspec_then `R` mp_tac) >>
      disch_then (mp_then Any mp_tac frag_exec_conseq) >>
      disch_then irule >> simp[]) >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by
    (Cases_on `p.ptr_location` >> gvs[]) >>
  gvs[] >> irule frag_exec_pointwise >> gen_tac >> simp[] >> strip_tac >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) unwrap_storage_copy_storage_frame_frag >>
  disch_then (qspecl_then [`sb`, `op`, `R`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (mp_then Any mp_tac frag_exec_conseq) >>
  disch_then irule >> simp[]
QED

Theorem raw_to_forced_runtime_storage_frame_frag:
  compile_expr cenv ty e sa = (vv,sm) /\
  unwrap_value cenv vv sm = (op,sb) /\
  eval_expr cx e es = (rawres,est) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (res,es') /\
  expr_res_ok res /\ ~cenv.ce_is_ctor /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM est.scopes /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (case vv of StackValue t operand => T | LocatedValue t p =>
    ~is_word_type t /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
     p.ptr_location = LocCode) ==>
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
      type_memory_bytes cenv t = type_memory_size tvt /\
      ((p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
       type_memory_size tvt < 2 ** 64))) /\
  frag_exec ctx sa sm P
    (\s. ?raw. rawres = INL raw /\
         vv_post ctx func cenv cx e es sa sm s0 est raw vv s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (expr_exit rawres) ==>
  frag_exec ctx sa sb P
    (\s. ?v. res = INL v /\
         expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (expr_exit res)
Proof
  strip_tac >> irule raw_to_forced_storage_frame_frag >> simp[] >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  simp[] >> rpt strip_tac >>
  irule unwrap_runtime_storage_frame_frag >> simp[]
QED

Theorem unwrap_typed_runtime_storage_frame_frag:
  unwrap_value cenv vv sm = (op,sb) /\ ~cenv.ce_is_ctor /\
  expr_body_pre cenv cx env e es /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (case vv of StackValue t operand => T | LocatedValue t p =>
    ~is_word_type t /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
     p.ptr_location = LocCode) ==>
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x)) ==>
  frag_exec ctx sm sb
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT) R
Proof
  strip_tac >> irule frag_exec_pointwise >> gen_tac >> simp[] >> strip_tac >>
  Cases_on `vv`
  >- (irule frag_exec_conseq >>
      irule_at (Pos last) unwrap_runtime_storage_frame_frag >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  rename1 `LocatedValue t p` >>
  `t = expr_type e` by gvs[vv_post_def, vv_holds_def] >>
  `!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
     type_memory_bytes cenv t = type_memory_size tvt /\
     type_memory_size tvt < 2 ** 64` by
    (rpt strip_tac >> gvs[] >> drule_all expr_body_pre_copy_ok >> simp[]) >>
  irule frag_exec_conseq >>
  irule_at (Pos last) unwrap_runtime_storage_frame_frag >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> gvs[] >> metis_tac[]
QED

Theorem raw_to_forced_typed_runtime_storage_frame_frag:
  compile_expr cenv ty e sa = (vv,sm) /\
  unwrap_value cenv vv sm = (op,sb) /\
  eval_expr cx e es = (rawres,est) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (res,es') /\
  expr_res_ok res /\ ~cenv.ce_is_ctor /\ expr_body_pre cenv cx env e es /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM est.scopes /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (case vv of StackValue t operand => T | LocatedValue t p =>
    ~is_word_type t /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
     p.ptr_location = LocCode) ==>
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x)) /\
  frag_exec ctx sa sm P
    (\s. ?raw. rawres = INL raw /\
         vv_post ctx func cenv cx e es sa sm s0 est raw vv s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (expr_exit rawres) ==>
  frag_exec ctx sa sb P
    (\s. ?v. res = INL v /\
         expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (expr_exit res)
Proof
  strip_tac >> irule raw_to_forced_storage_frame_frag >> simp[] >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  simp[] >> rpt strip_tac >>
  irule unwrap_typed_runtime_storage_frame_frag >> simp[] >> metis_tac[]
QED

Theorem mapping_string_key_post_hash_frag:
  expr_post ctx func cenv cx e es sa sm s0 es' (StringV str) key mid /\
  expr_type e = BaseT (StringT cap) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (StringT cap)) /\
  compile_keccak256_key key F sm = (out,sb) /\
  (!x. key = Var x ==> not_fresh_at sm x) /\
  local_ptrs_reserved cenv sm ==>
  frag_exec ctx sm sb (\s. s = mid)
    (\t. eval_operand out t = SOME
          (encode_hashmap_key (BaseT (StringT cap)) (StringV str)) /\
      stmt_state_rel ctx func cenv cx es' t /\
      t.vs_memory = mid.vs_memory /\ t.vs_allocas = mid.vs_allocas /\
      contract_storage t = contract_storage mid /\
      contract_transient t = contract_transient mid /\
      (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x mid)) R
Proof
  strip_tac >>
  drule_all exprSimHashTheory.hash_string_post_view >> strip_tac >>
  `n2w_o_ORD = (n2w o ORD):char -> word8` by
    simp[FUN_EQ_THM, vyperMiscTheory.n2w_o_ORD_def] >>
  simp[vyperStorageTheory.encode_hashmap_key_def, byteTheory.word_of_bytes_be_def] >>
  irule compile_keccak256_key_bytes_frame_frag >> simp[] >>
  reverse conj_tac >- gvs[expr_post_def] >>
  qexistsl [`key`, `n2w b`] >>
  simp[GSYM mem_word_at_eq_mload, abiDecodeStaticPropsTheory.w2n_add_n2w_lt]
QED

(* Task-local PLACE interface: mapping references have no expr_val_rel or
   expr_val_at.  The caller-owned allocation/local frame is the same one
   carried by expr_post, so constructor callbacks share one boundary. *)
Definition mapping_place_post_def:
  mapping_place_post ctx func cenv cx kt vt es sa sb s0 es' r vv s <=>
    stmt_state_rel ctx func cenv cx es' s /\
    (?w. eval_operand (vv_operand vv) s = SOME w /\
         place_ptr_rel cenv cx s r w (vv_location vv) (HashMapT kt vt)) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
    locals_kept cenv es s0 s /\
    contract_storage s = contract_storage s0 /\
    contract_transient s = contract_transient s0
End

Theorem mapping_place_post_refl:
  stmt_state_rel ctx func cenv cx es s /\
  (?w. eval_operand (vv_operand vv) s = SOME w /\
       place_ptr_rel cenv cx s r w (vv_location vv) (HashMapT kt vt)) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sb x) ==>
  mapping_place_post ctx func cenv cx kt vt es sa sb s es r vv s
Proof
  simp[mapping_place_post_def, locals_kept_def]
QED

Theorem compile_hashmap_root_place_frag:
  FLOOKUP cenv.ce_module_vars nsid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  compile_expr cenv ty (TopLevelName ann nsid) sa = (vv,sb) ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (mapping_place_post ctx func cenv cx kt vt es sa sb s0 es
      (HashMapRef tr slot kt vt) vv) R
Proof
  strip_tac >> drule compile_toplevel_slot_vv_shape >> strip_tac >> gvs[] >>
  irule frag_exec_refl >> rpt strip_tac >> gvs[] >>
  irule mapping_place_post_refl >>
  simp[contextTheory.vv_operand_def, contextTheory.vv_location_def,
       contextTheory.mk_ptr_def, eval_operand_def, hashmap_root_place_ptr_rel]
QED

(* Conditional rebase: locality transport is an obligation of the reachable
   producer, not a consequence of either child postcondition alone. *)
Theorem mapping_place_post_compose:
  mapping_place_post ctx func cenv cx kt0 vt0 es sa sm s0 esm r0 vv0 mid /\
  mapping_place_post ctx func cenv cx kt vt esm sm sb mid es' r vv s /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!n b sz. local_region cenv es.scopes s0 n b sz <=>
            local_region cenv esm.scopes mid n b sz) ==>
  mapping_place_post ctx func cenv cx kt vt es sa sb s0 es' r vv s
Proof
  rewrite_tac[mapping_place_post_def] >> strip_tac >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- metis_tac[]
  >- metis_tac[]
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by
        (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      metis_tac[])
  >- metis_tac[]
  >- (rpt strip_tac >>
      `aid < sm.cs_next_id` by decide_tac >>
      metis_tac[])
  >- (gvs[locals_kept_def] >> metis_tac[])
  >- metis_tac[] >>
  metis_tac[]
QED

Theorem mapping_key_post_keeps_place:
  expr_post ctx func cenv cx e esm sm sn mid es' v key s /\
  safe_operand sm (vv_operand bvv) /\
  (?w. eval_operand (vv_operand bvv) mid = SOME w /\
       place_ptr_rel cenv cx mid (HashMapRef tr slot kt vt)
         w (vv_location bvv) (HashMapT kt vt)) /\
  (!x. vv_operand bvv = Var x ==> not_fresh_at sm x) /\
  sm.cs_next_var <= sn.cs_next_var /\
  contract_storage s = contract_storage mid /\
  contract_transient s = contract_transient mid ==>
  mapping_place_post ctx func cenv cx kt vt esm sm sn mid es'
    (HashMapRef tr slot kt vt) bvv s
Proof
  rewrite_tac[expr_post_def, mapping_place_post_def, place_ptr_rel_def] >>
  strip_tac >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (simp[] >> Cases_on `vv_operand bvv` >>
      gvs[eval_operand_def, exprSafeOperandTheory.safe_operand_def] >>
      first_x_assum irule >> simp[])
  >- (rpt strip_tac >> gvs[not_fresh_at_def] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >>
  first_assum ACCEPT_TAC
QED

Theorem compile_mapping_subscript_place_frag:
  compile_mapping_subscript bop key sa = (out,sb) /\
  fn_has_code sa sb func /\
  eval_operand bop s0 = SOME slot /\ eval_operand key s0 = SOME kw /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb (\s. s = s0)
    (mapping_place_post ctx func cenv cx kt vt es sa sb s0 es
      (HashMapRef tr (hashmap_slot slot kw) kt vt)
      (LocatedValue ann (mk_ptr out (slot_loc tr)))) R
Proof
  strip_tac >>
  `!x. out = Var x ==> not_fresh_at sb x` by
    metis_tac[compiler_subscript_ops_var] >>
  irule frag_exec_conseq >>
  irule_at Any compile_mapping_subscript_frame_frag >>
  goal_assum (drule_at (Pat `compile_mapping_subscript _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `eval_operand bop _ = _`)) >>
  goal_assum (drule_at (Pat `eval_operand key _ = _`)) >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  qexists `R` >> simp[] >> rpt strip_tac >>
  simp[mapping_place_post_def, contextTheory.vv_operand_def,
       contextTheory.vv_location_def, contextTheory.mk_ptr_def,
       place_ptr_rel_def] >>
  conj_tac >- metis_tac[] >>
  irule locals_kept_regions >> metis_tac[]
QED

(* Hashing changes only fresh variables.  Lift that same endpoint to the
   mapping PLACE boundary before composing the scratch allocation. *)
Theorem mapping_place_post_readonly:
  mapping_place_post ctx func cenv cx kt vt es sa sm s0 es'
    (HashMapRef tr slot kt vt) vv mid /\
  safe_operand sm (vv_operand vv) /\ sa.cs_next_var <= sm.cs_next_var /\
  sm.cs_next_var <= sb.cs_next_var /\
  stmt_state_rel ctx func cenv cx es' s /\
  s.vs_memory = mid.vs_memory /\ s.vs_allocas = mid.vs_allocas /\
  contract_storage s = contract_storage mid /\
  contract_transient s = contract_transient mid /\
  (!x. not_fresh_at sm x ==> lookup_var x s = lookup_var x mid) ==>
  mapping_place_post ctx func cenv cx kt vt es sa sb s0 es'
    (HashMapRef tr slot kt vt) vv s
Proof
  rewrite_tac[mapping_place_post_def, place_ptr_rel_def] >>
  strip_tac >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (simp[] >>
      Cases_on `vv_operand vv` >>
      gvs[eval_operand_def, exprSafeOperandTheory.safe_operand_def] >>
      metis_tac[])
  >- (rpt strip_tac >> gvs[not_fresh_at_def] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS])
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by
        (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      metis_tac[])
  >- metis_tac[]
  >- metis_tac[]
  >- (gvs[locals_kept_def] >> metis_tac[])
  >- metis_tac[] >> metis_tac[]
QED

Theorem mapping_scalar_typed_encoding:
  hashmap_key_type kt /\ ~is_bytestring_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv v ==>
  is_word_type kt /\ typed_val_to_w256 tv v = encode_hashmap_key kt v
Proof
  Cases_on `kt` >> simp[hashmap_key_type_def] >> strip_tac
  >- (rename1 `BaseT bt` >> Cases_on `bt` >>
      gvs[hashmap_key_type_def, is_bytestring_type_def, evaluate_type_def,
          is_word_type_def] >>
      TRY (rename1 `BytesT bd` >> Cases_on `bd` >>
           gvs[is_bytestring_type_def, evaluate_type_def, is_word_type_def]) >>
      Cases_on `v` >> gvs[value_has_type_def] >>
      simp[mapping_scalar_key_encoding])
  >- (gvs[evaluate_type_def, AllCaseEqs(), is_word_type_def] >>
      Cases_on `v` >> gvs[value_has_type_def] >>
      simp[typed_val_to_w256_def, val_to_w256_def])
QED

(* Dispatch the actual MapPT conditional, including the no-hash scalar
   branch.  The forced key's source type and evaluated type stay explicit. *)
Theorem mapping_typed_key_post_hash_frag:
  expr_post ctx func cenv cx e es sa sm s0 es' v key mid /\
  expr_type e = kt /\ hashmap_key_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv v /\
  (if is_bytestring_type kt then compile_keccak256_key key F
   else comp_return key) sm = (out,sb) /\
  (!x. key = Var x ==> not_fresh_at sm x) /\
  local_ptrs_reserved cenv sm ==>
  frag_exec ctx sm sb (\s. s = mid)
    (\t. eval_operand out t = SOME (encode_hashmap_key kt v) /\
      stmt_state_rel ctx func cenv cx es' t /\
      t.vs_memory = mid.vs_memory /\ t.vs_allocas = mid.vs_allocas /\
      contract_storage t = contract_storage mid /\
      contract_transient t = contract_transient mid /\
      (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x mid)) R
Proof
  strip_tac >> Cases_on `is_bytestring_type kt`
  >- (gvs[] >> Cases_on `expr_type e` >> gvs[is_bytestring_type_def] >>
      rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def]
      >- (rename1 `StringT cap` >>
          `tv = BaseTV (StringT cap)` by gvs[evaluate_type_def] >>
          gvs[] >> Cases_on `v` >> gvs[value_has_type_def] >>
          irule mapping_string_key_post_hash_frag >>
          conj_tac >- first_assum ACCEPT_TAC >>
          goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
          simp[])
      >- (rename1 `BytesT bd` >> Cases_on `bd` >> gvs[is_bytestring_type_def] >>
          rename1 `Dynamic cap` >>
          `tv = BaseTV (BytesT (Dynamic cap))` by gvs[evaluate_type_def] >>
          gvs[] >> Cases_on `v` >> gvs[value_has_type_def] >>
          irule mapping_dynamic_key_post_hash_frag >>
          conj_tac >- first_assum ACCEPT_TAC >>
          goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
          simp[])) >>
  drule_all mapping_scalar_typed_encoding >> strip_tac >>
  gvs[comp_return_def] >> irule frag_exec_refl >> simp[] >>
  gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]
QED

Theorem mapping_typed_key_place_hash_frag:
  mapping_place_post ctx func cenv cx kt vt es sa sm s0 es'
    (HashMapRef tr slot kt vt) bvv mid /\
  expr_post ctx func cenv cx e esk sk sm key_start es' v key mid /\
  expr_type e = kt /\ hashmap_key_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv v /\
  (if is_bytestring_type kt then compile_keccak256_key key F
   else comp_return key) sm = (out,sb) /\
  (!x. key = Var x ==> not_fresh_at sm x) /\
  safe_operand sm (vv_operand bvv) /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sb.cs_next_var /\
  local_ptrs_reserved cenv sm ==>
  frag_exec ctx sm sb (\s. s = mid)
    (\s. mapping_place_post ctx func cenv cx kt vt es sa sb s0 es'
           (HashMapRef tr slot kt vt) bvv s /\
         eval_operand out s = SOME (encode_hashmap_key kt v)) R
Proof
  strip_tac >> irule frag_exec_conseq >>
  irule_at Any mapping_typed_key_post_hash_frag >>
  goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexistsl [`tv`, `out`, `kt`, `R`] >> simp[] >> rpt strip_tac >>
  irule mapping_place_post_readonly >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `mapping_place_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[]
QED

Theorem mapping_place_scratch_tail:
  mapping_place_post ctx func cenv cx kt vt es sa sm s0 es'
    (HashMapRef tr slot kt vt) bvv mid /\
  compile_mapping_subscript (vv_operand bvv) key sm = (out,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  eval_operand key mid = SOME kw /\
  (!x. key = Var x ==> not_fresh_at sm x) /\
  local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!n b sz. local_region cenv es.scopes s0 n b sz <=>
            local_region cenv es'.scopes mid n b sz) ==>
  frag_exec ctx sm sb (\s. s = mid)
    (mapping_place_post ctx func cenv cx kt vt es sa sb s0 es'
      (HashMapRef tr (hashmap_slot slot kw) kt vt)
      (LocatedValue ann (mk_ptr out (slot_loc tr)))) R
Proof
  strip_tac >>
  `eval_operand (vv_operand bvv) mid = SOME slot /\
   (!x. vv_operand bvv = Var x ==> not_fresh_at sm x) /\
   stmt_state_rel ctx func cenv cx es' mid` by
    gvs[mapping_place_post_def, place_ptr_rel_def] >>
  irule frag_exec_conseq >>
  irule_at Any compile_mapping_subscript_place_frag >>
  goal_assum (drule_at (Pat `compile_mapping_subscript _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `eval_operand key _ = _`)) >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  qexistsl [`vt`, `tr`, `kw`, `kt`, `ann`, `R`] >> simp[] >> rpt strip_tac >>
  irule mapping_place_post_compose >>
  goal_assum (drule_at (Pat `mapping_place_post _ _ _ _ _ _ es sa sm _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

(* All compiler-extension and locality premises are explicit here; this is
   the operational suffix, not a reachable-program invariant. *)
Theorem mapping_typed_key_scratch_frag:
  mapping_place_post ctx func cenv cx kt vt es sa sm s0 es'
    (HashMapRef tr slot kt vt) bvv mid /\
  expr_post ctx func cenv cx e esk sk sm key_start es' v key mid /\
  expr_type e = kt /\ hashmap_key_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv v /\
  (if is_bytestring_type kt then compile_keccak256_key key F
   else comp_return key) sm = (hashed,sn) /\
  compile_mapping_subscript (vv_operand bvv) hashed sn = (out,sb) /\
  (!x. key = Var x ==> not_fresh_at sm x) /\
  (!x. hashed = Var x ==> not_fresh_at sn x) /\
  safe_operand sm (vv_operand bvv) /\
  cs_extends sm sn /\ cs_extends sn sb /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
  sa.cs_next_id <= sn.cs_next_id /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn /\
  (!s. mapping_place_post ctx func cenv cx kt vt es sa sn s0 es'
          (HashMapRef tr slot kt vt) bvv s ==>
       !n b sz. local_region cenv es.scopes s0 n b sz <=>
                local_region cenv es'.scopes s n b sz) ==>
  frag_exec ctx sm sb (\s. s = mid)
    (mapping_place_post ctx func cenv cx kt vt es sa sb s0 es'
      (HashMapRef tr (hashmap_slot slot (encode_hashmap_key kt v)) kt vt)
      (LocatedValue ann (mk_ptr out (slot_loc tr)))) R
Proof
  strip_tac >> irule frag_exec_seq >>
  irule_at (Pat `frag_exec _ sm _ _ _ _`) mapping_typed_key_place_hash_frag >>
  goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `mapping_place_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> irule frag_exec_pointwise >> gen_tac >> simp[] >> strip_tac >>
  irule mapping_place_scratch_tail >>
  rpt conj_tac
  >- metis_tac[]
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- metis_tac[arithmeticTheory.LESS_EQ_TRANS]
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >>
  qexistsl [`bvv`, `hashed`] >> simp[]
QED

Theorem mapping_key_post_rebase:
  mapping_place_post ctx func cenv cx kt vt es sa sm s0 esm
    (HashMapRef tr slot kt vt) bvv mid /\
  expr_post ctx func cenv cx e esm sm sn mid es' v key s /\
  safe_operand sm (vv_operand bvv) /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sn.cs_next_var /\
  contract_storage s = contract_storage mid /\
  contract_transient s = contract_transient mid /\
  (!n b sz. local_region cenv es.scopes s0 n b sz <=>
            local_region cenv esm.scopes mid n b sz) ==>
  mapping_place_post ctx func cenv cx kt vt es sa sn s0 es'
    (HashMapRef tr slot kt vt) bvv s
Proof
  strip_tac >> irule mapping_place_post_compose >>
  goal_assum (drule_at (Pat `mapping_place_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> irule mapping_key_post_keeps_place >>
  rpt conj_tac
  >- (gvs[mapping_place_post_def] >> metis_tac[])
  >- (gvs[mapping_place_post_def] >> metis_tac[])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at Any)
QED

(* Conditional constructor assembly.  Child fragments may abort through R;
   successful endpoints are always the SAME endpoints carrying the frames.
   Source evaluations and locality transport are deliberately explicit. *)
Theorem mapping_subscript_place_constructor:
  eval_expr cx base_e es = (INL (HashMapRef tr slot kt vt),esm) /\
  (do r <- eval_expr cx idx; read_result cx r od) esm = (INL v,es') /\
  place_type cenv base_e = MapPT kt vt /\
  compile_expr cenv ty base_e sa = (bvv,s1) /\
  lower_value compile_expr cenv (expr_type idx) idx s1 = (key,s2) /\
  (if is_bytestring_type kt then compile_keccak256_key key F
   else comp_return key) s2 = (hashed,s3) /\
  compile_mapping_subscript (vv_operand bvv) hashed s3 = (out,sb) /\
  expr_type idx = kt /\ hashmap_key_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv v /\
  cs_extends sa s1 /\ cs_extends s1 s2 /\
  cs_extends s2 s3 /\ cs_extends s3 sb /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  s1.cs_next_var <= s2.cs_next_var /\ s2.cs_next_var <= s3.cs_next_var /\
  sa.cs_next_id <= s3.cs_next_id /\
  (!x. key = Var x ==> not_fresh_at s2 x) /\
  (!x. hashed = Var x ==> not_fresh_at s3 x) /\
  safe_operand s1 (vv_operand bvv) /\ safe_operand s2 (vv_operand bvv) /\
  fn_has_code s3 sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv s2 /\ local_ptrs_reserved cenv s3 /\
  frag_exec ctx sa s1
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (mapping_place_post ctx func cenv cx kt vt es sa s1 s0 esm
      (HashMapRef tr slot kt vt) bvv) R /\
  (!mid. mapping_place_post ctx func cenv cx kt vt es sa s1 s0 esm
           (HashMapRef tr slot kt vt) bvv mid ==>
     frag_exec ctx s1 s2 (\s. s = mid)
       (\s. expr_post ctx func cenv cx idx esm s1 s2 mid es' v key s /\
            contract_storage s = contract_storage mid /\
            contract_transient s = contract_transient mid) R) /\
  (!mid. mapping_place_post ctx func cenv cx kt vt es sa s1 s0 esm
           (HashMapRef tr slot kt vt) bvv mid ==>
     !n b sz. local_region cenv es.scopes s0 n b sz <=>
              local_region cenv esm.scopes mid n b sz) /\
  (!s. mapping_place_post ctx func cenv cx kt vt es sa s3 s0 es'
          (HashMapRef tr slot kt vt) bvv s ==>
     !n b sz. local_region cenv es.scopes s0 n b sz <=>
              local_region cenv es'.scopes s n b sz) ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (mapping_place_post ctx func cenv cx kt vt es sa sb s0 es'
      (HashMapRef tr (hashmap_slot slot (encode_hashmap_key kt v)) kt vt)
      (LocatedValue ann (mk_ptr out
        (case vv_location bvv of SOME l => l | NONE => LocMemory)))) R
Proof
  strip_tac >> irule frag_exec_seq >>
  goal_assum (drule_at (Pat `frag_exec _ sa s1 _ _ _`)) >>
  simp[] >> conj_tac >- metis_tac[cs_extends_trans] >>
  irule frag_exec_pointwise >> gen_tac >> strip_tac >>
  `vv_location bvv = SOME (slot_loc tr)` by
    gvs[mapping_place_post_def, place_ptr_rel_def] >> simp[] >>
  irule frag_exec_seq >>
  first_x_assum (irule_at (Pat `frag_exec _ s1 s2 _ _ _`)) >>
  first_assum (irule_at Any) >> simp[] >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  qpat_x_assum `eval_expr cx base_e es = _` kall_tac >>
  qpat_x_assum `bind _ _ esm = _` kall_tac >>
  qpat_x_assum `place_type _ _ = _` kall_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` kall_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `frag_exec _ sa s1 _ _ _` kall_tac >>
  irule frag_exec_pointwise >> gen_tac >> simp[] >> strip_tac >>
  irule mapping_typed_key_scratch_frag >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- metis_tac[arithmeticTheory.LESS_EQ_TRANS]
  >- first_assum ACCEPT_TAC
  >- (qexists `tv` >> simp[]) >>
  goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `compile_mapping_subscript _ _ _ = _`)) >>
  simp[] >> irule mapping_key_post_rebase >>
  goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `mapping_place_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

Theorem compile_subscript_mapping_components:
  place_type cenv base_e = MapPT kt vt /\
  cfn cenv ty base_e sa = (bvv,s1) /\
  lower_value cfn cenv (expr_type idx) idx s1 = (key,s2) /\
  (if is_bytestring_type kt then compile_keccak256_key key F
   else comp_return key) s2 = (hashed,s3) /\
  compile_mapping_subscript (vv_operand bvv) hashed s3 = (out,sb) ==>
  compile_subscript cfn cenv ann ty base_e idx sa =
    (LocatedValue ann (mk_ptr out
      (case vv_location bvv of SOME l => l | NONE => LocMemory)),sb)
Proof
  simp[compile_subscript_def, comp_bind_def, comp_return_def, LET_THM]
QED

Theorem mapping_place_post_retag:
  mapping_place_post ctx func cenv cx kt vt es sa sb s0 es'
    (HashMapRef tr slot kt vt) vv s ==>
  mapping_place_post ctx func cenv cx kt' vt' es sa sb s0 es'
    (HashMapRef tr slot kt' vt') vv s
Proof
  simp[mapping_place_post_def, place_ptr_rel_def] >> metis_tac[]
QED

Theorem eval_subscript_result_split:
  eval_expr cx base_e es = (rb,esm) /\
  (do r <- eval_expr cx idx; read_result cx r od) esm = (rk,esk) ==>
  eval_expr cx (Subscript ann base_e idx) es =
    (case rb of INR ex => (INR ex,esm) | INL r =>
       case rk of INR ex => (INR ex,esk) | INL v =>
         select_result cx (expr_type base_e) r (ValueSubscript v) esk)
Proof
  strip_tac >> Cases_on `rb` >>
  gvs[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx idx esm` >>
  gvs[AllCaseEqs()] >> Cases_on `rk` >> gvs[]
QED

(* Conditional nested PLACE closure: the callbacks include both source exits.
   No total recursive producer is asserted by this boundary. *)
Theorem mapping_subscript_nested_place_frag:
  eval_expr cx base_e es = (rb,esm) /\
  (do r <- eval_expr cx idx; read_result cx r od) esm = (rk,esk) /\
  eval_expr cx (Subscript ann base_e idx) es = (res,es') /\
  place_type cenv base_e = MapPT kt (HashMapT kt' vt') /\
  compile_expr cenv ty base_e sa = (bvv,s1) /\
  lower_value compile_expr cenv (expr_type idx) idx s1 = (key,s2) /\
  (if is_bytestring_type kt then compile_keccak256_key key F
   else comp_return key) s2 = (hashed,s3) /\
  compile_mapping_subscript (vv_operand bvv) hashed s3 = (out,sb) /\
  cs_extends sa s1 /\ cs_extends s1 s2 /\
  cs_extends s2 s3 /\ cs_extends s3 sb /\
  (!r. rb = INL r ==> ?tr slot. r = HashMapRef tr slot kt (HashMapT kt' vt')) /\
  (!ex. rb = INR ex ==>
    frag_exec ctx sa s1
      (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. F) (expr_exit (INR ex : eval_result + exception))) /\
  (!tr slot. rb = INL (HashMapRef tr slot kt (HashMapT kt' vt')) ==>
    frag_exec ctx sa s1
      (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (mapping_place_post ctx func cenv cx kt (HashMapT kt' vt') es sa s1 s0 esm
        (HashMapRef tr slot kt (HashMapT kt' vt')) bvv) (expr_exit res) /\
    (!mid. mapping_place_post ctx func cenv cx kt (HashMapT kt' vt') es sa s1 s0 esm
        (HashMapRef tr slot kt (HashMapT kt' vt')) bvv mid ==>
      !ex. rk = INR ex ==>
        frag_exec ctx s1 s2 (\s. s = mid) (\s. F) (expr_exit (INR ex : eval_result + exception))) /\
    (!v. rk = INL v ==>
      expr_type idx = kt /\ hashmap_key_type kt /\
      (?tv. evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv v) /\
      sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
      s1.cs_next_var <= s2.cs_next_var /\ s2.cs_next_var <= s3.cs_next_var /\
      sa.cs_next_id <= s3.cs_next_id /\
      (!x. key = Var x ==> not_fresh_at s2 x) /\
      (!x. hashed = Var x ==> not_fresh_at s3 x) /\
      safe_operand s1 (vv_operand bvv) /\ safe_operand s2 (vv_operand bvv) /\
      fn_has_code s3 sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv s2 /\ local_ptrs_reserved cenv s3 /\
      (!mid. mapping_place_post ctx func cenv cx kt (HashMapT kt' vt') es sa s1 s0 esm
          (HashMapRef tr slot kt (HashMapT kt' vt')) bvv mid ==>
        frag_exec ctx s1 s2 (\s. s = mid)
          (\s. expr_post ctx func cenv cx idx esm s1 s2 mid esk v key s /\
            contract_storage s = contract_storage mid /\
            contract_transient s = contract_transient mid) (expr_exit res)) /\
      (!mid. mapping_place_post ctx func cenv cx kt (HashMapT kt' vt') es sa s1 s0 esm
          (HashMapRef tr slot kt (HashMapT kt' vt')) bvv mid ==>
        !n b sz. local_region cenv es.scopes s0 n b sz <=>
                 local_region cenv esm.scopes mid n b sz) /\
      (!s. mapping_place_post ctx func cenv cx kt (HashMapT kt' vt') es sa s3 s0 esk
          (HashMapRef tr slot kt (HashMapT kt' vt')) bvv s ==>
        !n b sz. local_region cenv es.scopes s0 n b sz <=>
                 local_region cenv esk.scopes s n b sz))) ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. ?r. res = INL r /\
      mapping_place_post ctx func cenv cx kt' vt' es sa sb s0 es' r
        (LocatedValue ann (mk_ptr out
          (case vv_location bvv of SOME l => l | NONE => LocMemory))) s)
    (expr_exit res)
Proof
  strip_tac >>
  `cs_extends s2 sb` by (irule cs_extends_trans >> qexists `s3` >> simp[]) >>
  `cs_extends s1 sb` by (irule cs_extends_trans >> qexists `s2` >> simp[]) >>
  drule_all eval_subscript_result_split >> strip_tac >>
  Cases_on `rb`
  >- (gvs[] >> Cases_on `rk`
      >- (gvs[select_result_hashmap_nested] >>
          drule_all (SRULE [] (Q.INST [`kt` |-> `expr_type idx`]
            mapping_subscript_place_constructor)) >> strip_tac >>
          qpat_x_assum `!a. frag_exec _ sa sb _ _ _`
            (qspec_then `ann` mp_tac) >>
          rpt (pop_assum kall_tac) >> strip_tac >>
          drule frag_exec_weaken >> disch_then irule >>
          simp[] >> metis_tac[mapping_place_post_retag]) >>
      gvs[] >> irule frag_exec_seq_pointwise >>
      goal_assum (drule_at (Pat `frag_exec _ sa s1 _ _ _`)) >>
      simp[] >> rpt strip_tac >>
      irule frag_exec_exit_prefix >> qexists `s2` >>
      simp[] >> first_x_assum drule >> disch_then ACCEPT_TAC) >>
  gvs[] >> irule frag_exec_exit_prefix >> qexists `s1` >> simp[]
QED
