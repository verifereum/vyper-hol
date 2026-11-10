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
       locals_kept_def, ptr_val_ok_def, op_taint_def, op_prov_def,
       ghost_kept_def] >>
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

(* Shared proof phases: semantic parameters are supplied by each literal case. *)
fun literal_buffer_run_tac norm size =
  Q.SUBGOAL_THEN size ASSUME_TAC
    >- (simp[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all (norm literal_bytelike_ptr_run) >>
  disch_then (qspecl_then [`tn0`, `func`, `PG`, `G0`, `cx_dead cx`]
    strip_assume_tac) >>
  drule_all (norm literal_buffer_ptr_path) >> strip_tac >>
  drule_all (norm literal_bytelike_ptr_nonmemory_frame) >> strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `w2n (n2w b : 256 word) = b` by simp[wordsTheory.w2n_n2w];

fun literal_buffer_vv_post_tac norm e size tv =
  simp[] >>
  once_rewrite_tac[GSYM (Q.INST [`gs` |-> `[]`] vv_post_initial_gas)] >>
  irule (SRULE [vyperASTTheory.expr_type_def]
    (Q.INST [`n` |-> size, `e` |-> e]
      (SPEC_ALL literal_ptr_memory_vv_frame_post))) >>
  simp[is_word_type_def] >>
  conj_tac >- (drule (norm literal_buffer_next_id) >> simp[]) >>
  conj_tac
  >- (drule_all (norm literal_ptr_bytelike_alloca_mem) >> strip_tac >>
      qexists_tac `STRING #"%" (toString sa.cs_next_var)` >> gvs[]) >>
  qexistsl_tac [`sh`, tv, `u`, `n2w b`] >>
  drule_all (norm literal_ptr_bytelike_alloca_mem) >> strip_tac >>
  simp[vyperASTTheory.expr_type_def, is_word_type_def,
    vyperValueTheory.evaluate_type_def, eval_operand_def] >>
  gvs[well_formed_type_def, vyperValueTheory.evaluate_type_def,
      type_slot_size_def, type_memory_size_def, wordsTheory.dimword_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC;

fun literal_buffer_ghost_tac size =
  `ghost_inv d cenv cx es G' tn' t /\
   ghost_kept cenv es sa G0 tn0 s0 G' tn'` by
    (irule literal_ptr_ghost_frame >> simp[] >>
     qexistsl_tac [`b`, `ctx`, `func`, size, `u`] >>
     gvs[] >> rpt conj_tac >> metis_tac[]);

fun literal_buffer_value_tac e size tv value =
  mp_tac (Q.INST
    [`e` |-> e, `n` |-> size, `tv` |-> tv, `v` |-> value,
     `w` |-> `n2w b : 256 word`, `G` |-> `G'`, `tn` |-> `tn'`,
     `idx` |-> `LENGTH cs'.cs_current_insts`, `es` |-> `es with gas_obs := []`]
    (SPEC_ALL literal_ptr_value_posts)) >>
  (impl_tac
   >- (simp[vyperASTTheory.expr_type_def, vyperValueTheory.evaluate_type_def,
            is_word_type_def, lowered_value_type_def, type_memory_bytes_def, type_memory_size_def] >>
       gvs[well_formed_type_def, vyperValueTheory.evaluate_type_def,
           type_slot_size_def, vfmConstantsTheory.word_size_def,
           wordsTheory.dimword_def])) >>
  strip_tac;

fun literal_buffer_prepare_tac is_expr =
  rw[if is_expr then expr_sim_ptr_def else expr_vv_sim_ptr_def] >>
  gvs[lower_value_def, compile_expr_def, compile_literal_vv_def,
      is_word_type_def, vyperASTTheory.expr_type_def, comp_bind_def,
      comp_return_def] >>
  pairarg_tac >>
  gvs[unwrap_value_def, contextTheory.base_ptr_def, comp_return_def, is_word_type_def] >>
  (if is_expr then
     (pairarg_tac >>
      gvs[unwrap_value_def, contextTheory.base_ptr_def, comp_return_def, is_word_type_def] >>
      rename1 `compile_bytelike_literal _ _ sa = (buf,cs')`)
   else all_tac) >>
  gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_literal_def,
      Once evaluate_def, return_def, evaluate_literal_def,
      alloc_limits_expr_def, literal_alloc_ok_def];

(* The consumer proof as separate phases, so a caller can run each phase as
   its own proof step. *)
fun literal_buffer_consumer_parts is_expr norm bound_tac rep e size tv value vvpost =
  [literal_buffer_prepare_tac is_expr,
   literal_buffer_run_tac norm (size @ ` < dimword (:256)`) >>
   bound_tac >>
   drule_all rep >> strip_tac,
   Q.SUBGOAL_THEN vvpost ASSUME_TAC
     >- literal_buffer_vv_post_tac norm e size tv,
   literal_buffer_ghost_tac size >>
   (if is_expr then
      (drule (GEN_ALL (SRULE [vyperASTTheory.expr_type_def, is_word_type_def]
         (Q.INST [`e` |-> e] (SPEC_ALL literal_memory_vv_expr_post)))) >>
       simp[vyperASTTheory.expr_type_def, is_word_type_def] >> strip_tac)
    else all_tac),
   rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
   rewrite_tac[gas_summary_ptr_at_def] >>
   Q.EXISTS_TAC (if is_expr then `INL (` @ value @ `)`
                else `INL (Value (` @ value @ `))`) >>
   qexistsl_tac [`es`, `G'`, `tn'`,
     `OK (t with vs_inst_idx := LENGTH cs'.cs_current_insts)`],
   simp[gas_explicit_def, Once evaluate_def, return_def, evaluate_literal_def,
        vyperStateTheory.bind_def, vyperStateTheory.read_result_def] >>
   simp[literal_ptr_ghost_inv_normalize, vv_post_initial_gas],
   literal_buffer_value_tac e size tv value >>
   gvs[vyperASTTheory.expr_type_def, contextTheory.base_ptr_def,
       ptr_vv_ok_def, ptr_val_ok_def, vyperStateTheory.read_result_def]];

fun literal_buffer_consumer_tac is_expr norm bound_tac rep e size tv value vvpost =
  EVERY (literal_buffer_consumer_parts is_expr norm bound_tac rep e size tv value vvpost);

fun literal_bytes_consumer_parts is_expr =
  literal_buffer_consumer_parts is_expr I
    (`LENGTH (bs:word8 list) <= n` by gvs[vyperValueTheory.compatible_bound_def])
    literal_ptr_bytes_representation
    `Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)`
    `32+32*word_size (LENGTH (bs:word8 list))`
    `BaseTV (BytesT (Dynamic n))` `BytesV bs`
    `vv_post ctx func cenv cx
      (Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) es sa cs' s0 (es with gas_obs := [])
      (Value (BytesV bs)) (LocatedValue (BaseT (BytesT (Dynamic n))) (base_ptr buf))
      (t with vs_inst_idx := LENGTH cs'.cs_current_insts)`;

fun literal_bytes_consumer_tac is_expr = EVERY (literal_bytes_consumer_parts is_expr);

val literal_bytes_vv_parts = literal_bytes_consumer_parts false;

fun literal_string_norm th =
  GEN_ALL (SRULE [listTheory.LENGTH_MAP]
    (Q.INST [`bs` |-> `(MAP (n2w o ORD) str : word8 list)`] (SPEC_ALL th)));

fun literal_string_consumer_tac is_expr =
  literal_buffer_consumer_tac is_expr literal_string_norm all_tac literal_ptr_string_representation
    `Literal (BaseT (StringT n)) (StringL str)`
    `32+32*word_size (LENGTH (str:string))`
    `BaseTV (StringT n)` `StringV str`
    `vv_post ctx func cenv cx
      (Literal (BaseT (StringT n)) (StringL str)) es sa cs' s0 (es with gas_obs := [])
      (Value (StringV str)) (LocatedValue (BaseT (StringT n)) (base_ptr buf))
      (t with vs_inst_idx := LENGTH cs'.cs_current_insts)`;

(* Both judgments use the same allocation, stores and ghost witnesses. *)
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
  el 1 literal_bytes_vv_parts >> el 2 literal_bytes_vv_parts >>
  el 3 literal_bytes_vv_parts >> el 4 literal_bytes_vv_parts >>
  el 5 literal_bytes_vv_parts >> el 6 literal_bytes_vv_parts >>
  el 7 literal_bytes_vv_parts
QED
Resume literal_buffer_sim_ptr[bytes_expr]:
  literal_bytes_consumer_tac true
QED
Resume literal_buffer_sim_ptr[string_vv]:
  literal_string_consumer_tac false
QED
Resume literal_buffer_sim_ptr[string_expr]:
  literal_string_consumer_tac true
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
