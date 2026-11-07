Theory bodyPtrBytestringBuiltinsCalldataCase
Ancestors
  bodyPtrBytestringBuiltinsEval bodyPtrBytestringBuiltinsExternalSlice
  bodyPtrPreds exprPtrUnwrap vyperTypeSystem exprSimHypsDefs
  emitHelperProps compileEnv fragExec bodyPtrBytestringBuiltinsCalldataOutcome
  exprSimWordArgs loweringPosts bodyPtrDefs
  vyperContext exprSimSource exprLowering exprBopLowering list

(* Expose the actual lowered operand from the conditional body hypothesis.
   Typing, rather than an unconditional list membership rule, fixes arity. *)
Theorem calldata_slice_body_operand_ptr:
  (builtin_args_length_ok (CalldataSlice n) (LENGTH args) ==>
    body_exprs_ptr_ok cx args) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann (CalldataSlice n) args) es ==>
  ?e. args = [e] /\ expr_type e = BaseT (UintT 256) /\
    ann = BaseT (BytesT (Dynamic n)) /\ 0 < n /\ n < 2 ** 256 /\
    expr_body_pre cenv cx env e es /\
    expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es
Proof
  strip_tac >>
  `well_typed_expr env (Builtin ann (CalldataSlice n) args)` by
    fs[expr_body_pre_def] >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
  strip_tac >> Cases_on `args` >> gvs[] >>
  `body_expr_ptr_ok cx h` by
    fs[builtin_args_length_ok_def, body_exprs_ptr_ok_def] >>
  `expr_body_pre cenv cx env h es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then irule >> fs[expr_body_pre_def]) >>
  fs[body_expr_ptr_ok_def] >> metis_tac[]
QED

(* Consumer-facing equation: hide dispatch and expose only the operand and
   the already checked calldata fragment, without a let-bound statement. *)
Theorem calldata_slice_compile_cut:
  compile_expr cenv ty (Builtin ann (CalldataSlice n) [e]) sa = (vv,sb) ==>
  ?op sm. lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
    as_ptr_val ann LocMemory
      (compile_slice_calldata op (Lit (n2w n))
        (type_memory_bytes cenv ann) sm) = (vv,sb)
Proof
  `!bt args. names_builtin bt args ==> bt <> CalldataSlice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `~names_builtin (CalldataSlice n) [e]` by metis_tac[] >>
  simp[compile_expr_builtin_dispatch] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def] >>
  pairarg_tac >> simp[] >> strip_tac >> metis_tac[]
QED

Theorem calldata_slice_code_appends:
  cs_appends (\sm. as_ptr_val ann LocMemory
    (compile_slice_calldata x (Lit (n2w n)) N sm))
Proof
  rw[cs_appends_def] >>
  Cases_on `compile_slice_calldata x (Lit (n2w n)) N sm` >>
  gvs[as_ptr_val_def] >>
  drule compile_slice_calldata_stages >> strip_tac >>
  metis_tac[cs_extends_trans]
QED

