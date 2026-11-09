(* Opcode boundaries for literal buffer construction. *)
Theory exprSimPtrLiteralOps
Ancestors
  allocationPtr typedCopyPtr exprSimLiteralBuffer exprSimHypsDefs
  exprLowering ptrDiscipline venomExecSemantics venomMemDefs finite_map
  vyperTypeSystem vyperValue vyperAST exprSimProps compileEnv venomState venomInst
  fragExecPtr ptrSafeRun codegenRel contextCodegenRel bodyPtrDefs words

Theorem literal_nonword_classify:
  expr_sim_pre cenv cx env (Literal ann l) es /\ ~is_word_type ann ==>
  (?bs n. l = BytesL bs /\ ann = BaseT (BytesT (Dynamic n))) \/
  (?str n. l = StringL str /\ ann = BaseT (StringT n))
Proof
  strip_tac >> gvs[expr_sim_pre_def, well_typed_expr_def] >>
  Cases_on `l` >> gvs[well_typed_literal_def, is_word_type_def] >>
  Cases_on `ann` >> gvs[well_typed_literal_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[well_typed_literal_def, is_word_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[well_typed_literal_def, is_word_type_def, well_formed_type_def,
      vyperValueTheory.evaluate_type_def]
QED

Theorem literal_mstore_ghost:
  lookup_var dst s = SOME a ==>
  step_prov PG G (mk_inst id MSTORE [Var dst; Lit w] [])
    (mstore (w2n a) w s) = G /\
  step_taint (mk_inst id MSTORE [Var dst; Lit w] []) s
    (mstore (w2n a) w s) tn =
    tn with t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}
Proof
  strip_tac >>
  drule mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `tn`, `id`, `Lit w`, `w`] mp_tac) >>
  simp[eval_operand_def, op_taint_def] >> strip_tac >>
  simp[taint_component_equality, step_taint_def, imm_taint_def, mk_inst_def]
QED

Theorem literal_add_ghost:
  FLOOKUP G src = SOME site ==>
  step_prov PG G (mk_inst id ADD [Var src; Lit off] [dst])
    (update_var dst v s) = G |+ (dst,site) /\
  step_taint (mk_inst id ADD [Var src; Lit off] [dst]) s
    (update_var dst v s) tn = tn with t_var := tn.t_var |+ (dst,{})
Proof
  strip_tac >>
  simp[step_prov_def, out_prov_def, set_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, step_taint_def, set_var_taint_def,
       out_taint_def, eval_operand_def, mem_taint_def, new_site_bytes_def,
       update_var_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def, range_bytes_def,
       written_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
       taint_component_equality, FLOOKUP_DEF, pred_setTheory.EXTENSION] >>
  Cases_on `lookup_var src s` >> simp[] >> metis_tac[]
QED

Theorem literal_empty_chunks:
  compile_store_byte_chunks op [] off sa = ((),sa)
Proof
  simp[compile_store_byte_chunks_def, comp_return_def]
QED

Theorem literal_short_chunk_shape:
  bs <> [] /\ LENGTH bs <= 32 ==>
  compile_store_byte_chunks op bs off =
    do dst <- emit_op ADD [op; Lit (n2w off)];
       emit_void MSTORE
         [dst; Lit (word_of_bytes T 0w (TAKE 32 (bs ++ REPLICATE 31 (0w:word8)) ))];
       return ()
    od
Proof
  strip_tac >> Cases_on `bs` >> gvs[] >>
  simp[Once compile_store_byte_chunks_def] >>
  `DROP 31 t = []` by (simp[listTheory.DROP_EQ_NIL] >> decide_tac) >>
  simp[compile_store_byte_chunks_def]
QED

Theorem literal_add_ptr_inst_ok:
  op_taint tn (Var src) = {} /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id ADD [Var src; Lit off] [dst]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, op_taint_def, step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds, opcode_case_def, combinTheory.K_THM] >>
  simp[exec_pure2_def, eval_operand_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[op_taint_def] >>
  Cases_on `FLOOKUP tn.t_var src` >> gvs[] >> metis_tac[]
QED

Theorem literal_mstore_ptr_inst_ok:
  ptr_covers G tn dst s 32 /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id MSTORE [Var dst; Lit w] []) s
Proof
  strip_tac >> irule ptr_inst_ok_mstore >> simp[op_taint_def]
QED

Theorem literal_alloca_ptr_inst_ok:
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id ALLOCA [Lit n] [dst]) s
Proof
  simp[ptr_inst_ok_alloca]
QED

Theorem literal_add_ptr_covers:
  lookup_var src s = SOME w /\ FLOOKUP G src = SOME (b,n) /\
  b <= w2n w /\ w2n w + off + sz <= b+n /\
  w2n w + off < dimword (:256) ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var src; Lit (n2w off)] [dst])
      (update_var dst (n2w (w2n w + off)) s))
    (step_taint (mk_inst id ADD [Var src; Lit (n2w off)] [dst]) s
      (update_var dst (n2w (w2n w + off)) s) tn)
    dst (update_var dst (n2w (w2n w + off)) s) sz
Proof
  strip_tac >> drule literal_add_ghost >> disch_then assume_tac >>
  simp[ptr_covers_def, op_taint_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, w2n_n2w] >> decide_tac
QED

Theorem literal_bytes_buffer_size:
  type_memory_bytes cenv
    (lowered_value_type cenv (Literal (BaseT (BytesT (Dynamic n))) (BytesL bs))) =
  32 + ((LENGTH bs + 31) DIV 32) * 32
Proof
  simp[lowered_value_type_def, type_memory_bytes_def]
QED

Theorem literal_string_buffer_size:
  type_memory_bytes cenv
    (lowered_value_type cenv (Literal (BaseT (StringT n)) (StringL str))) =
  32 + ((LENGTH str + 31) DIV 32) * 32
Proof
  simp[lowered_value_type_def, type_memory_bytes_def]
QED
