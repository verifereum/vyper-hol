(* Typed Keccak continuation of the operand pointer simulation. *)
Theory bodyPtrHashBuiltinsKeccakUnary
Ancestors bodyPtrHashBuiltinsKeccakCase bodyPtrHashBuiltinsSummary
  bodyPtrHashBuiltinsGhostCompose bodyPtrHashBuiltinsWordSummary
  bodyPtrHashBuiltinsCursor exprSimVVFrame
  bodyPtrHashBuiltinsUnary exprSimHash exprSimHypsDefs vyperTypeSystem
  exprLoweringProps exprSimDefs exprLowering emitHelperProps
  bodyPtrDefs gasSummaryComposePtr vyperInterpreter vyperContext compileEnv loweringStateRelDefs list
  exprSimWordArgs fragExec exprSimSource exprSimHyps rich_list arithmetic vyperTyping

(* Private proof-code consumer of the shared semantic endpoint interface. *)
fun hash_keccak_word_summary_tac g = (
  drule_all hash_expr_post_ghost_kept_compose >> strip_tac >>
  qpat_x_assum `sb.cs_current_insts = _` (assume_tac o GSYM) >>
  asm_rewrite_tac[GSYM LENGTH_APPEND] >>
  simp[vyperASTTheory.expr_type_def, is_word_type_def] >>
  irule (SRULE [vyperASTTheory.expr_type_def, is_word_type_def]
    (Q.INST [`e` |-> `Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e]`]
      (SPEC_ALL hash_word_endpoint_summary))) >>
  first_assum (irule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >>
  qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def, same_blocks_def] >>
  `sm.cs_current_bb = sb.cs_current_bb` by fs[same_blocks_def] >>
  `LENGTH sb.cs_current_insts = LENGTH sm.cs_current_insts +
    LENGTH (emitted_insts sm sb)` by metis_tac[LENGTH_APPEND] >>
  simp[builtin_result_def, vyperContextTheory.evaluate_builtin_def] >>
  metis_tac[hash_fixed_keccak_emitted_length]) g;

Theorem hash_compile_typed_keccak256_unary_vv_sim_ptr:
  expr_body_pre cenv cx env (Builtin ann Keccak256 [e]) es /\
  expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (Builtin ann Keccak256 [e]) es
Proof
  strip_tac >>
  `well_typed_builtin_app ann Keccak256 [expr_type e]` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  drule_at Any hash_builtin_types >> simp[] >> strip_tac >>
  `?bty. expr_type e = BaseT bty` by
    (Cases_on `expr_type e` >> gvs[is_bytes_or_string_type_def]) >>
  irule hash_compile_typed_unary_builtin_vv_sim_ptr >>
  simp[precompile_builtin_def, builtin_args_length_ok_def] >>
  qexistsl_tac [`\x sm. as_stack_val ann
    (if is_bytestring_type (expr_type e) then compile_keccak256_bytes x sm
     else case expr_type e of
       BaseT (BytesT (Fixed m)) => compile_keccak256_bytesm x m sm
     | _ => compile_keccak256_word x sm)`, `env`] >>
  conj_tac >- suspend "suffix" >>
  conj_tac
  >- (simp[compile_hash_singleton] >> rpt gen_tac >> pairarg_tac >>
      strip_tac >> gvs[] >> goal_assum (drule_at Any) >> simp[]) >>
  reverse conj_tac >- gvs[] >>
  Cases_on `bty` >> gvs[is_bytes_or_string_type_def] >>
  TRY (rename1 `expr_type e = BaseT (BytesT bd)` >> Cases_on `bd`) >>
  simp[is_bytestring_type_def] >> gen_tac >>
  irule cs_appends_stack_value >> simp[hash_suffix_appends]
QED

Resume hash_compile_typed_keccak256_unary_vv_sim_ptr[suffix]:
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e ee` by
    (irule expr_body_pre_builtin_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >> simp[]) >>
  `evaluate_type (get_tenv cx) (BaseT bty) = SOME (BaseTV bty)` by
    (drule expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def] >>
     Cases_on `bty` >> gvs[AllCaseEqs()] >>
     rename1 `expr_type e = BaseT (BytesT bd)` >>
     Cases_on `bd` >> gvs[AllCaseEqs()]) >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `!z. not_fresh_at sa z ==> not_fresh_at sm z` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z)` by
    metis_tac[] >>
  drule (CONV_RULE (DEPTH_CONV ETA_CONV)
    forced_eval_expr_preserves_scopes_dom) >> simp[] >> strip_tac >>
  Cases_on `bty` >> gvs[is_bytes_or_string_type_def] >>
  TRY (rename1 `expr_type e = BaseT (BytesT bd)` >> Cases_on `bd`) >>
  gvs[is_bytestring_type_def] >>
  gvs[oneline as_stack_val_def, AllCaseEqs()] >>
  `same_blocks sm sb /\
   sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
    metis_tac[keccak_suffix_shape] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_NIL, GSYM APPEND_ASSOC])
  >- (Cases_on `v` >> gvs[value_has_type_def] >>
      drule_at (Pos hd) hash_string_keccak_ptr_post >> simp[] >>
      disch_then (drule_all_then
        (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac)) >>
      hash_keccak_word_summary_tac)
  >- (`n <= 32` by gvs[vyperValueTheory.evaluate_type_def] >>
      Cases_on `v` >> gvs[value_has_type_def] >>
      `op_taint tn x = {}` by
        gvs[ptr_val_ok_def, is_word_type_def] >>
      drule_at (Pos hd) hash_fixed_keccak_ptr_post >>
      simp[value_has_type_def] >>
      disch_then (drule_all_then
        (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac)) >>
      hash_keccak_word_summary_tac) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  drule_at (Pos hd) hash_dynamic_keccak_ptr_post >> simp[] >>
  disch_then (drule_all_then
    (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac)) >>
  hash_keccak_word_summary_tac
QED


Finalise hash_compile_typed_keccak256_unary_vv_sim_ptr
