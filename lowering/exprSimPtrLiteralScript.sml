(*
 * The pointer twin of S1's Literal case (exprSimLiteralWord,
 * exprSimLiteralBytes, exprSimLiteralBuffer).  A literal of a word type
 * is a Lit, no code: the path is empty and the ghost stays.  A bytes or
 * string literal of a dynamic type is a fresh buffer the lowering
 * allocates and fills (literal_buffer_sim_ptr).
 *
 * TOP-LEVEL:
 *   literal_expr_sim_ptr
 *
 * Helpers: literal_word_compile, literal_word_sim_ptr,
 *   literal_buffer_sim_ptr
 *)
Theory exprSimPtrLiteral
Ancestors
  exprSimPtrProps bodyPtrDefs fragGasPathPtr ptrDiscipline exprSimHypsDefs
  exprSimLiteralWord exprSimProps exprSimDefs loweringPosts gasSummary
  loweringSlice exprLowering exprLoweringProps compileEnv vyperAST
  vyperInterpreter vyperState vyperValue vyperTypeSystem valueEncoding
  vyperValueOperation venomState list

(* As bodyLiteralMemory's: a word-typed literal is a stack value. *)
Theorem literal_word_compile:
  expr_sim_pre cenv cx env (Literal ann l) es /\ is_word_type ann ==>
  ?op. compile_expr cenv ty (Literal ann l) sa = (StackValue ann op,sa)
Proof
  strip_tac >>
  `~(?str. l = StringL str)` by
    (strip_tac >> gvs[expr_sim_pre_def, well_typed_expr_def] >>
     Cases_on `ann` >> gvs[well_typed_literal_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[well_typed_literal_def, is_word_type_def]) >>
  Cases_on `l` >> gvs[]
  >~ [`BytesL bs`]
  >- (`!n. ann <> BaseT (BytesT (Dynamic n))` by
        (rpt strip_tac >> gvs[is_word_type_def]) >>
      simp[compile_expr_def, vyperASTTheory.expr_type_def] >>
      irule compile_literal_bytes_stack >> simp[])
  >~ [`BoolL b`]
  >- (Cases_on `b` >>
      simp[compile_expr_def, compile_literal_vv_def,
           vyperASTTheory.expr_type_def, comp_return_def]) >>
  simp[compile_expr_def, compile_literal_vv_def,
       vyperASTTheory.expr_type_def, comp_return_def]
QED

Theorem ghost_inv_gas_obs[local]:
  ghost_inv d cenv cx es G tn s ==>
  ghost_inv d cenv cx (es with gas_obs := obs) G tn s
Proof
  simp[ghost_inv_def] >> metis_tac[]
QED

val literal_word_tac =
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      compile_literal_vv_def, unwrap_value_def, evaluate_literal_def,
      vyperASTTheory.expr_type_def] >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, eval_operand_def,
       typed_val_to_w256_word_value, word_value_def, val_to_w256_def,
       is_word_type_def, vyperValueTheory.evaluate_type_def,
       locals_kept_def, ptr_val_ok_def, op_taint_def, ghost_kept_def] >>
  fs[];

Theorem literal_word_sim_ptr[local]:
  expr_sim_pre cenv cx env (Literal ann l) es /\ is_word_type ann ==>
  expr_sim_ptr d ctx PG func cenv cx ty (Literal ann l) es
Proof
  rw[expr_sim_ptr_def] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`]
       mp_tac) >>
     qpat_x_assum `s0.vs_inst_idx = _` kall_tac >> simp[]) >>
  `ghost_inv d cenv cx (es with gas_obs := []) G0 tn0 s0` by
    simp[ghost_inv_gas_obs] >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (evaluate_literal l)`, `es`, `G0`, `tn0`, `OK s0`] >>
  simp[gas_explicit_def, gas_path_ptr_rules, literal_read_all_tails] >>
  gvs[expr_sim_pre_def, well_typed_expr_def] >>
  Cases_on `l` >> gvs[well_typed_literal_def]
  >~ [`BoolL b`] >- (Cases_on `b` >> literal_word_tac)
  >~ [`IntL i`] >- literal_word_tac
  >~ [`DecimalL i`] >- literal_word_tac >>
  Cases_on `ann` >> gvs[well_typed_literal_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[well_typed_literal_def, is_word_type_def]
  >~ [`BytesT bd`] >- (Cases_on `bd` >> gvs[is_word_type_def] >>
                       literal_word_tac) >>
  literal_word_tac
QED

(* A dynamic bytes or string literal: compile_bytelike_literal's ALLOCA, the
   length word and the padded chunks.  The new site starts tainted
   (mem_taint); the stores write all val_store_size bytes of the value with
   untainted data, so the buffer holds the value robustly. *)
Theorem literal_buffer_sim_ptr:
  !d PG ctx func cenv cx env ty ann l es.
    expr_sim_pre cenv cx env (Literal ann l) es /\ ~is_word_type ann ==>
    expr_sim_ptr d ctx PG func cenv cx ty (Literal ann l) es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Literal ann l) es
Proof
  cheat
QED

Theorem literal_expr_sim_ptr:
  !d PG ctx func cenv cx env ty ann l es.
    expr_sim_pre cenv cx env (Literal ann l) es ==>
    expr_sim_ptr d ctx PG func cenv cx ty (Literal ann l) es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Literal ann l) es
Proof
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `is_word_type ann`)
  >- metis_tac[literal_buffer_sim_ptr] >>
  `expr_sim_ptr d ctx PG func cenv cx ty (Literal ann l) es` by
    metis_tac[literal_word_sim_ptr] >>
  simp[] >> irule expr_vv_sim_ptr_stack >> simp[] >> conj_tac
  >~ [`compile_expr`] >- metis_tac[literal_word_compile] >>
  simp[Once evaluate_def, return_def]
QED
