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
  fragGasSeqPtr exprSimLiteralBuffer allocLimits exprSimPtrLiteralOps exprSimPtrLiteralBuffer exprSimPtrProps bodyPtrDefs fragGasPathPtr ptrDiscipline exprSimHypsDefs
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

Theorem literal_buffer_unwrap[local]:
  ~is_word_type ann /\
  compile_expr cenv ty (Literal ann l) sa =
    (LocatedValue ann (base_ptr buf),sb) ==>
  lower_value compile_expr cenv ty (Literal ann l) sa = (buf.buf_operand,sb)
Proof
  strip_tac >>
  simp[lower_value_def, comp_bind_def, unwrap_value_def, contextTheory.base_ptr_def,
       comp_return_def]
QED

Theorem literal_buffer_next_id[local]:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) ==>
  sa.cs_next_id < sb.cs_next_id
Proof
  strip_tac >> drule literal_ptr_bytelike_shape >> strip_tac >>
  `ci_mono sh sb` by metis_tac[ci_mono_compile_store_byte_chunks, pairTheory.SND] >>
  `ci_mono sm sh` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  gvs[ci_mono_def] >> decide_tac
QED

Theorem literal_buffer_ptr_path[local]:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >> drule_all literal_bytelike_gas_path >> strip_tac >>
  simp[] >> drule literal_bytelike_counted_shape >> strip_tac >>
  gvs[fragExecTheory.fn_has_code_def, exprLoweringPropsTheory.same_blocks_def,
      rich_listTheory.IS_PREFIX_APPEND] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[rich_listTheory.DROP_APPEND1] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem literal_memory_vv_expr_post[local]:
  ~is_word_type (expr_type e) /\
  vv_post ctx func cenv cx e es sa sb s0 ee (Value v)
    (LocatedValue (expr_type e) (base_ptr buf)) t ==>
  expr_post ctx func cenv cx e es sa sb s0 ee v buf.buf_operand t
Proof
  simp[vv_post_def, expr_post_def, vv_holds_def, vv_at_def,
       expr_val_rel_def, expr_val_at_def, contextTheory.base_ptr_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  metis_tac[]
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
  rpt gen_tac >> strip_tac >>
  drule_all literal_nonword_classify >> strip_tac >> gvs[]
  >- (conj_tac >- suspend "bytes_expr" >> suspend "bytes_vv") >>
  conj_tac >- suspend "string_expr" >> suspend "string_vv"
QED

Resume literal_buffer_sim_ptr[bytes_vv]:
  rw[expr_vv_sim_ptr_def] >>
  gvs[compile_expr_def, compile_literal_vv_def, is_word_type_def,
      vyperASTTheory.expr_type_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_literal_def,
      Once evaluate_def, return_def, evaluate_literal_def,
      alloc_limits_expr_def, literal_alloc_ok_def] >>
  `32+32*word_size (LENGTH bs) < dimword (:256)` by
    (simp[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all literal_bytelike_ptr_run >>
  disch_then (qspecl_then [`tn0`, `func`, `PG`, `G0`, `cx_dead cx`]
    strip_assume_tac) >>
  drule_all literal_buffer_ptr_path >> strip_tac >>
  drule_all literal_bytelike_ptr_nonmemory_frame >> strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `w2n (n2w b : 256 word) = b` by simp[wordsTheory.w2n_n2w] >>
  `LENGTH bs <= n` by gvs[vyperValueTheory.compatible_bound_def] >>
  drule_all literal_ptr_bytes_representation >> strip_tac >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (Value (BytesV bs))`, `es`, `G'`, `tn'`,
    `OK (t with vs_inst_idx := LENGTH cs'.cs_current_insts)`] >>
  simp[gas_explicit_def, Once evaluate_def, return_def, evaluate_literal_def] >>
  conj_tac
  >- (once_rewrite_tac[GSYM (Q.INST [`gs` |-> `[]`] vv_post_initial_gas)] >>
      irule (SRULE [vyperASTTheory.expr_type_def]
        (Q.INST [`n` |-> `32+32*word_size (LENGTH (bs:word8 list))`,
                 `e` |-> `Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)`]
          (SPEC_ALL literal_ptr_memory_vv_frame_post))) >>
      simp[is_word_type_def] >>
      conj_tac >- (drule literal_buffer_next_id >> simp[]) >>
      conj_tac
      >- (drule_all literal_ptr_bytelike_alloca_mem >> strip_tac >>
          qexists_tac `STRING #"%" (toString sa.cs_next_var)` >> gvs[]) >>
      qexistsl_tac [`sh`, `BaseTV (BytesT (Dynamic n))`, `u`, `n2w b`] >>
      drule_all literal_ptr_bytelike_alloca_mem >> strip_tac >>
      simp[vyperASTTheory.expr_type_def, is_word_type_def,
        vyperValueTheory.evaluate_type_def, eval_operand_def] >>
      gvs[well_formed_type_def, vyperValueTheory.evaluate_type_def,
          type_slot_size_def, type_memory_size_def, wordsTheory.dimword_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv d cenv cx es G' tn' t /\
   ghost_kept cenv es sa G0 tn0 s0 G' tn'` by
    (irule literal_ptr_ghost_frame >>
     simp[] >>
     qexistsl_tac [`b`, `ctx`, `func`, `32+32*word_size (LENGTH bs)`, `u`] >>
     gvs[] >> rpt conj_tac >> metis_tac[]) >>
  simp[literal_ptr_ghost_inv_normalize] >>
  `ptr_vv_ok cx (BaseT (BytesT (Dynamic n))) (Value (BytesV bs))
     (LocatedValue (BaseT (BytesT (Dynamic n))) (base_ptr buf))
     (es with gas_obs := []) G' tn' (t with vs_inst_idx := LENGTH cs'.cs_current_insts) /\
   ptr_val_ok cx (BaseT (BytesT (Dynamic n))) (BytesV bs) (Var p) G' tn'
     (t with vs_inst_idx := LENGTH cs'.cs_current_insts) /\
   ptr_buf_ok cenv (Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) (Var p) G'
     (t with vs_inst_idx := LENGTH cs'.cs_current_insts)` by
    (irule (SRULE [vyperASTTheory.expr_type_def]
      (Q.INST [`n` |-> `32+32*word_size (LENGTH (bs:word8 list))`,
               `e` |-> `Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)`]
       (SPEC_ALL literal_ptr_value_posts))) >>
     simp[] >>
     qexists_tac `BaseTV (BytesT (Dynamic n))` >>
     simp[vyperValueTheory.evaluate_type_def, lowered_value_type_def,
          type_memory_bytes_def, type_memory_size_def] >>
     gvs[well_formed_type_def, vyperValueTheory.evaluate_type_def,
         type_slot_size_def, vfmConstantsTheory.word_size_def,
         wordsTheory.dimword_def]) >>
  simp[contextTheory.base_ptr_def]
QED

Resume literal_buffer_sim_ptr[bytes_expr]:
  cheat
QED
Resume literal_buffer_sim_ptr[string_expr]:
  cheat
QED
Resume literal_buffer_sim_ptr[string_vv]:
  cheat
QED
Finalise literal_buffer_sim_ptr

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
