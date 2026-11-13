(* Pointer-checked constructor immutable reads at (D, lo): the twins of the
 * runtime DLOAD stages (exprPtrCodeCopySegments, exprPtrCodeCopyLoad,
 * exprPtrCodeCopyIteration, exprPtrCodeCopyInduction) for
 * compile_imm_load_word T, which adds the region base (zero in a
 * constructor) and ILOADs from memory below lo, and for
 * compile_imm_copy_to_memory T, which copies such words into a buffer
 * at or above lo.
 *
 * An ILOAD reads [a, a+32) with a + 32 <= lo through an address with no
 * provenance, so access_ok lo holds; the loaded word carries the taint of
 * the bytes it reads (mem_word_taint), which the copy stores into the
 * buffer.  Whether those bytes are tainted is the ghost invariant's
 * business, not these stages'.
 *
 * TOP-LEVEL:
 *   ptr_inst_ok_imm_load -- the ILOAD check
 *   ctor_base_add_segment, ctor_imm_load_segment -- the two stages
 *   code_copy_ctor_load -- compile_imm_load_word T
 *   code_copy_ctor_one_ptr, code_copy_ctor_range_ptr,
 *   code_copy_ctor_range_code_cursor -- compile_imm_copy_to_memory T
 *)
Theory exprPtrCtorCodeLoad
Ancestors
  exprPtrCodeCopyInduction exprPtrCodeCopyIteration exprPtrCodeCopyOffset
  exprPtrCodeCopySegments exprPtrUnwrapStoreSegment instSeqComposePtr
  emittedSeqComposePtr exprSimCopy immutableCopyExecution
  immutableWordExecution typedCopyPtr decoderGhostFramePtr
  exprPtrUnwrapCopyEdges exprPtrUnwrapScalarEdges fragGasSeqPtr ptrSafeRun
  ptrDiscipline bodyPtrDefs
  context compileEnv loweringStateRelDefs emitHelper emitHelperProps exprLoweringProps
  codegenRel contextCodegenRel memLocDefs
  venomExecSemantics venomInst venomState instIdxIndep fragExec
  entrySinkExtraction fragGasPathPtr
  finite_map pred_set list rich_list arithmetic words

(* ===== One instruction ===== *)

Theorem ptr_inst_ok_imm_load:
  eval_operand a s = SOME off /\ op_taint tn a = {} /\ op_prov G a = NONE /\
  w2n off + 32 <= lo /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id ILOAD [a] [out]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       mem_read_ops_def] >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_read1_def, update_var_def]
QED

Theorem load_word_output_taint:
  (opc = MLOAD \/ opc = ILOAD) /\ eval_operand a s = SOME off ==>
  op_taint (step_taint (mk_inst id opc [a] [out]) s u tn) (Var out) =
    mem_word_taint tn.t_mem (w2n off)
Proof
  strip_tac >>
  gvs[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
      mk_inst_def, FLOOKUP_UPDATE]
QED

Theorem load_word_taint_frame:
  (opc = MLOAD \/ opc = ILOAD) ==>
  (step_taint (mk_inst id opc [arg] [out]) s
    (update_var out value s) tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id opc [arg] [out]) s
    (update_var out value s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc [arg] [out]) s
    (update_var out value s) tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id opc [arg] [out]) s
    (update_var out value s) tn).t_imm = tn.t_imm
Proof
  strip_tac >> gvs[step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
    written_taint_def, source_memory_write_ranges_def, range_bytes_def,
    store_taint_def, imm_taint_def, adopt_reset_def, mk_inst_def, update_var_def,
    FLOOKUP_DEF, EXTENSION, SF CONJ_ss]
QED

(* ===== The two stages ===== *)

(* ADD [src; region]: the address plus the region base, both clean words. *)
Theorem ctor_base_add_segment:
  eval_operand src s = SOME a /\ eval_operand region s = SOME r /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  op_taint tn region = {} /\ op_prov G region = NONE /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  run_inst_seq [mk_inst id ADD [src; region] [out]] s = OK t /\
  (!p. P p ==> p <> out) ==>
  ?Gf tnf.
    (!k. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id ADD [src; region] [out]]
        (s with vs_inst_idx := k) Gf tnf) /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. P p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. P p /\ ptr_covers G tn p s n ==> ptr_covers Gf tnf p t n)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [src; region] [out]) s =
     OK (update_var out (a + r) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def] >>
  gvs[run_inst_seq_def] >>
  qexistsl [`step_prov PG G (mk_inst id ADD [src; region] [out])
      (update_var out (a + r) s)`,
    `step_taint (mk_inst id ADD [src; region] [out]) s
      (update_var out (a + r) s) tn`] >>
  simp[inst_seq_ptr_def, ptr_inst_ok_copy_arith,
       step_inst_inst_idx_indep, exec_result_map_def, mk_inst_def,
       is_terminator_def, copy_len_binop_ghost_frame, copy_mk_immutable_taint] >>
  rpt conj_tac
  >- (irule step_prov_out_none >> simp[mk_inst_def] >>
      irule out_prov_arith_none >> simp[mk_inst_def])
  >- (rpt strip_tac >> `p <> out` by metis_tac[] >>
      pure_rewrite_tac[GSYM mk_inst_def] >>
      simp[copy_len_binop_ghost_frame, step_taint_def, set_var_taint_def,
           mk_inst_def, FLOOKUP_UPDATE])
  >> rpt strip_tac >> `p <> out` by metis_tac[] >>
  irule ptr_covers_step_frame >>
  simp[mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* ILOAD [arg]: a word of the fixed region below lo, through an address
   with no provenance; the output carries the taint of the bytes read. *)
Theorem ctor_imm_load_segment:
  eval_operand arg s = SOME a /\ op_taint tn arg = {} /\
  op_prov G arg = NONE /\ w2n a + 32 <= lo /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  run_inst_seq [mk_inst id ILOAD [arg] [out]] s = OK t /\
  (!p. P p ==> p <> out) ==>
  ?Gf tnf.
    (!k. inst_seq_ptr D lo ctx fn PG G tn [mk_inst id ILOAD [arg] [out]]
      (s with vs_inst_idx := k) Gf tnf) /\
    op_taint tnf (Var out) = mem_word_taint tn.t_mem (w2n a) /\
    op_prov Gf (Var out) = NONE /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. P p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. P p /\ ptr_covers G tn p s n ==> ptr_covers Gf tnf p t n)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ILOAD [arg] [out]) s =
    OK (update_var out (mload (w2n a) s) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def] >>
  gvs[run_inst_seq_def] >>
  qexistsl [`step_prov PG G (mk_inst id ILOAD [arg] [out])
    (update_var out (mload (w2n a) s) s)`,
    `step_taint (mk_inst id ILOAD [arg] [out]) s
      (update_var out (mload (w2n a) s) s) tn`] >>
  simp[inst_seq_ptr_def, ptr_inst_ok_imm_load,
    step_inst_inst_idx_indep, exec_result_map_def, mk_inst_def,
    is_terminator_def, load_word_taint_frame] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[load_word_output_taint, load_word_taint_frame] >>
  rpt conj_tac
  >- (irule step_prov_out_none >> simp[mk_inst_def] >>
      irule out_prov_other_none >> simp[mk_inst_def])
  >- (rpt strip_tac >> `p <> out` by metis_tac[] >>
      simp[step_prov_other_output, step_taint_other_output, mk_inst_def])
  >> rpt strip_tac >> `p <> out` by metis_tac[] >>
  irule ptr_covers_step_frame >>
  simp[mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* ===== compile_imm_load_word T ===== *)

(* ADD [arg; region]; ILOAD: the region base is zero in a constructor. *)
Theorem ctor_word_load_seq:
  eval_operand arg s = SOME a /\ op_taint tn arg = {} /\ op_prov G arg = NONE /\
  eval_operand region s = SOME 0w /\ op_taint tn region = {} /\
  op_prov G region = NONE /\ w2n a + 32 <= lo /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  run_inst_seq [mk_inst id ADD [arg; region] [tmp];
                mk_inst (id + 1) ILOAD [Var tmp] [out]] s = OK t /\
  (!p. P p ==> p <> tmp /\ p <> out) ==>
  ?Gf tnf.
    (!k. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id ADD [arg; region] [tmp];
       mk_inst (id + 1) ILOAD [Var tmp] [out]]
      (s with vs_inst_idx := k) Gf tnf) /\
    op_taint tnf (Var out) = mem_word_taint tn.t_mem (w2n a) /\
    op_prov Gf (Var out) = NONE /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. P p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. P p /\ ptr_covers G tn p s n ==> ptr_covers Gf tnf p t n)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [arg; region] [tmp]) s =
     OK (update_var tmp a s)` by simp[immutable_word_add_zero] >>
  `run_inst_seq [mk_inst id ADD [arg; region] [tmp]] s =
     OK (update_var tmp a s)` by simp[run_inst_seq_def] >>
  `run_inst_seq [mk_inst (id + 1) ILOAD [Var tmp] [out]]
     (update_var tmp a s) = OK t` by
    (qpat_x_assum `run_inst_seq [_; _] _ = _`
       (mp_tac o ONCE_REWRITE_RULE [run_inst_seq_def]) >> simp[]) >>
  `!p. P p ==> p <> tmp` by metis_tac[] >>
  `!p. P p ==> p <> out` by metis_tac[] >>
  `?G1 tn1.
     (!k. inst_seq_ptr D lo ctx fn PG G tn [mk_inst id ADD [arg; region] [tmp]]
        (s with vs_inst_idx := k) G1 tn1) /\
     op_taint tn1 (Var tmp) = {} /\ op_prov G1 (Var tmp) = NONE /\
     tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
     tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
     (!p. P p ==> FLOOKUP G1 p = FLOOKUP G p /\
       op_taint tn1 (Var p) = op_taint tn (Var p)) /\
     allocas_from lo (update_var tmp a s) /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp (update_var tmp a s)) /\
     (!p n. P p /\ ptr_covers G tn p s n ==>
       ptr_covers G1 tn1 p (update_var tmp a s) n)` by
    (irule ctor_base_add_segment >> simp[] >> metis_tac[]) >>
  `eval_operand (Var tmp) (update_var tmp a s) = SOME a` by
    simp[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `?Gf tnf.
     (!k. inst_seq_ptr D lo ctx fn PG G1 tn1
        [mk_inst (id + 1) ILOAD [Var tmp] [out]]
        (update_var tmp a s with vs_inst_idx := k) Gf tnf) /\
     op_taint tnf (Var out) = mem_word_taint tn1.t_mem (w2n a) /\
     op_prov Gf (Var out) = NONE /\
     tnf.t_mem = tn1.t_mem /\ tnf.t_stor = tn1.t_stor /\
     tnf.t_trans = tn1.t_trans /\ tnf.t_imm = tn1.t_imm /\
     (!p. P p ==> FLOOKUP Gf p = FLOOKUP G1 p /\
       op_taint tnf (Var p) = op_taint tn1 (Var p)) /\
     allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
     (!p n. P p /\ ptr_covers G1 tn1 p (update_var tmp a s) n ==>
       ptr_covers Gf tnf p t n)` by
    (irule ctor_imm_load_segment >> simp[] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
     [mk_inst id ADD [arg; region] [tmp]]` by
    simp[mk_inst_def, is_terminator_def] >>
  qexistsl [`Gf`, `tnf`] >> simp[] >>
  `[mk_inst id ADD [arg; region] [tmp];
    mk_inst (id + 1) ILOAD [Var tmp] [out]] =
   [mk_inst id ADD [arg; region] [tmp]] ++
   [mk_inst (id + 1) ILOAD [Var tmp] [out]]` by simp[] >>
  pop_assum SUBST1_TAC >> irule inst_seq_ptr_uniform_append >>
  metis_tac[]
QED

Theorem ctor_load_word_nonterminators:
  compile_imm_load_word T imm arg sa = (op,sb) ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  Cases_on `imm`
  >- (simp[compile_imm_load_word_def] >> strip_tac >>
      drule emitted_op_nonterminators >> simp[is_terminator_def]) >>
  strip_tac >> drule compile_imm_load_word_ctor_result >> strip_tac >>
  simp[emitted_insts_def, DROP_APPEND, mk_inst_def, is_terminator_def]
QED

(* The ctor load at the copy's endpoint: the loaded word carries the taint
   of the section bytes it reads. *)
Theorem code_copy_ctor_load:
  compile_imm_load_word T imm arg sa = (op,sb) /\
  copy_old_operand sa arg /\ eval_operand arg s = SOME a /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\ w2n a + 32 <= lo /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
     copy_old_operand sa region /\ op_taint tn region = {} /\
     op_prov G region = NONE) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    copy_runtime_frame sa s sb t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    eval_operand op t = SOME (immutable_copy_read T a s) /\
    op_taint tnf op = mem_word_taint tn.t_mem (w2n a) /\
    op_prov Gf op = NONE /\
    copy_old_operand sb op /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tnf p t n)
Proof
  strip_tac >>
  drule copy_ctor_load >> disch_then (qspecl_then [`s`, `a`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  Cases_on `imm`
  >- (gvs[compile_imm_load_word_def] >>
      drule emitted_insts_emit_op >> strip_tac >>
      `!p. not_fresh_at sa p ==>
        p <> STRING #"%" (toString sa.cs_next_var)` by
        simp[not_fresh_at_def] >>
      gvs[copy_runtime_frame_def, immutable_copy_read_def] >>
      irule ctor_imm_load_segment >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  rename1 `compile_imm_load_word T (SOME region) arg sa = (op,sb)` >>
  drule compile_imm_load_word_ctor_result >> strip_tac >>
  `emitted_insts sa sb =
     [mk_inst sa.cs_next_id ADD [arg; region]
        ["%" ++ toString sa.cs_next_var];
      mk_inst (sa.cs_next_id + 1) ILOAD [Var ("%" ++ toString sa.cs_next_var)]
        ["%" ++ toString (sa.cs_next_var + 1)]]` by
    simp[emitted_insts_def, DROP_APPEND] >>
  `!p. not_fresh_at sa p ==> p <> "%" ++ toString sa.cs_next_var /\
      p <> "%" ++ toString (sa.cs_next_var + 1)` by
    simp[not_fresh_at_def] >>
  gvs[copy_runtime_frame_def, immutable_copy_read_def] >>
  irule ctor_word_load_seq >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

(* ===== compile_imm_copy_to_memory T: one word ===== *)

Theorem old_operand_prov_frame:
  (!x. not_fresh_at st x ==> FLOOKUP G' x = FLOOKUP G x) /\
  copy_old_operand st op ==>
  op_prov G' op = op_prov G op
Proof
  Cases_on `op` >> simp[op_prov_def, copy_old_operand_def]
QED

Theorem ctor_region_frame:
  copy_runtime_frame sa s sm t /\
  (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
     op_taint tnf (Var p) = op_taint tn (Var p)) /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
     copy_old_operand sa region /\ op_taint tn region = {} /\
     op_prov G region = NONE) ==>
  !region. imm = SOME region ==> eval_operand region t = SOME 0w /\
     copy_old_operand sm region /\ op_taint tnf region = {} /\
     op_prov Gf region = NONE
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >> rpt conj_tac
  >- metis_tac[copy_runtime_frame_operand]
  >- metis_tac[copy_old_operand_mono, copy_runtime_frame_def]
  >- metis_tac[old_operand_taint_frame, copy_old_operand_def]
  >> metis_tac[old_operand_prov_frame]
QED

(* Offsets of a source with no provenance have none. *)
Theorem code_copy_ctor_source_offset:
  compile_lit_byte_offset src off sa = (op,sb) /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\
  op_taint tn src = {} /\ op_prov G src = NONE /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    copy_runtime_frame sa s sb t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    eval_operand op t = SOME (a + n2w off) /\ op_taint tnf op = {} /\
    op_prov Gf op = NONE /\ copy_old_operand sb op /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tnf p t n)
Proof
  strip_tac >> drule_all copy_runtime_offset >> strip_tac >>
  Cases_on `off = 0`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def, emitted_insts_def,
          copy_runtime_frame_def, run_inst_seq_def] >>
      qexistsl [`G`, `tn`] >> simp[inst_seq_ptr_def]) >>
  Cases_on `src`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def, emitted_insts_def,
          copy_runtime_frame_def, run_inst_seq_def, eval_operand_def] >>
      qexistsl [`G`, `tn`] >> simp[inst_seq_ptr_def, op_taint_def, op_prov_def])
  >> (`eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
       op_taint tn (Lit (n2w off)) = {} /\ op_prov G (Lit (n2w off)) = NONE` by
        simp[eval_operand_def, op_taint_def, op_prov_def] >>
      gvs[compile_lit_byte_offset_def] >>
      drule emitted_insts_emit_op >> strip_tac >>
      `!p. not_fresh_at sa p ==>
        p <> STRING #"%" (toString sa.cs_next_var)` by
        simp[not_fresh_at_def] >>
      gvs[copy_runtime_frame_def] >>
      irule ctor_base_add_segment >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  gvs[eval_operand_def]
QED

Theorem code_copy_ctor_read_prefix:
  compile_lit_byte_offset src off sa = (arg,sm) /\
  compile_imm_load_word T imm arg sm = (op,sb) /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  w2n (a + n2w off) + 32 <= lo /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
     copy_old_operand sa region /\ op_taint tn region = {} /\
     op_prov G region = NONE) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    copy_runtime_frame sa s sb t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
    op_taint tnf op = mem_word_taint tn.t_mem (w2n (a + n2w off)) /\
    op_prov Gf op = NONE /\
    copy_old_operand sb op /\ (?v. eval_operand op t = SOME v) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tnf p t n)
Proof
  strip_tac >> drule_all code_copy_ctor_source_offset >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  rename1 `copy_runtime_frame sa s sm t1` >>
  drule_then (drule_then (drule_then assume_tac)) ctor_region_frame >>
  drule_all code_copy_ctor_load >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  rename1 `copy_runtime_frame sm t1 sb t2` >>
  qexistsl [`Gf'`, `tnf'`, `t2`] >> simp[] >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (fs[copy_runtime_frame_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm)` by
    (drule code_offset_insts >> simp[EVERY_MEM] >>
     metis_tac[is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    metis_tac[ctor_load_word_nonterminators] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> fs[copy_runtime_frame_def]) >>
  rpt conj_tac
  >- metis_tac[copy_runtime_frame_trans]
  >- (irule emitted_inst_seq_ptr_uniform_compose >>
      qexistsl [`Gf`, `sm`, `t1`, `tnf`] >>
      fs[copy_runtime_frame_def, inst_extends_def])
  >- simp[EVERY_APPEND]
  >> metis_tac[]
QED

(* A store of a possibly tainted word moves the word's taint into the
   destination bytes. *)
Theorem code_copy_ctor_store:
  emit_void MSTORE [Var root;v] sa = ((),sb) /\
  copy_old_operand sa (Var root) /\ copy_old_operand sa v /\
  eval_operand (Var root) s = SOME addr /\ eval_operand v s = SOME value /\
  ptr_covers G tn root s 32 /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    copy_runtime_frame sa s sb t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    tnf.t_mem =
      (tn.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr + 32}) UNION
        {w2n addr + k | k IN op_taint tn v} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. ptr_covers G tn p s n ==> ptr_covers Gf tnf p t n)
Proof
  strip_tac >> drule_all copy_runtime_store >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule_all copy_store_segment >>
  disch_then (qspecl_then [`sa.cs_next_id`, `fn`, `PG`, `D`] strip_assume_tac) >>
  gvs[] >> qexistsl [`Gf`, `tnf`, `mstore (w2n addr) value s`] >> simp[] >>
  `step_inst_base (mk_inst sa.cs_next_id MSTORE [Var root;v] []) s =
    OK (mstore (w2n addr) value s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def] >>
  gvs[inst_seq_ptr_def] >> gen_tac >>
  simp[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
       mk_inst_def, is_terminator_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  irule ptr_inst_ok_mstore_tainted >> simp[]
QED

Theorem code_copy_ctor_write_suffix:
  compile_lit_byte_offset (Var root) off sa = (dst,sm) /\
  emit_void MSTORE [dst;v] sm = ((),sb) /\
  not_fresh_at sa root /\ copy_old_operand sa v /\
  lookup_var root s = SOME b /\ eval_operand v s = SOME value /\
  ptr_covers G tn root s capacity /\
  off < capacity /\ off + 32 <= capacity /\
  w2n b + off < dimword(:256) /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    copy_runtime_frame sa s sb t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    tnf.t_mem =
      (tn.t_mem DIFF
        {j | w2n (b + n2w off) <= j /\ j < w2n (b + n2w off) + 32}) UNION
      {w2n (b + n2w off) + k | k IN op_taint tn v} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tnf p t n)
Proof
  strip_tac >>
  `op_taint tn (Var root) = {}` by fs[ptr_covers_def] >>
  `copy_old_operand sa (Var root) /\ eval_operand (Var root) s = SOME b` by
    simp[copy_old_operand_def, eval_operand_def] >>
  drule_all code_copy_source_offset >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sm) s Gf tnf` by
    (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
      (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  drule_all code_copy_destination_coverage >> strip_tac >> gvs[] >>
  `copy_old_operand sm v` by
    metis_tac[copy_old_operand_mono, copy_runtime_frame_def] >>
  `eval_operand v t = SOME value` by metis_tac[copy_runtime_frame_operand] >>
  `op_taint tnf v = op_taint tn v` by
    metis_tac[old_operand_taint_frame, copy_old_operand_def] >>
  drule_all code_copy_ctor_store >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl [`Gf'`, `tnf'`, `t'`] >> simp[] >> rpt conj_tac
  >- metis_tac[copy_runtime_frame_trans]
  >- (irule emitted_inst_seq_ptr_uniform_compose >>
      qexistsl [`Gf`, `sm`, `t`, `tnf`] >>
      fs[copy_runtime_frame_def, inst_extends_def] >>
      drule code_offset_insts >> simp[EVERY_MEM] >>
      metis_tac[is_terminator_def])
  >> metis_tac[]
QED

(* The destination word's bytes take the taint of the source word's. *)
Theorem store_word_taint_pointwise:
  x IN (M DIFF {j | c <= j /\ j < c + 32}) UNION
       {c + k | k IN mem_word_taint M d} <=>
  if c <= x /\ x < c + 32 then d + (x - c) IN M else x IN M
Proof
  simp[mem_word_taint_def, PULL_EXISTS] >> rw[] >> eq_tac >> rw[] >>
  gvs[] >> qexists_tac `x - c` >> simp[]
QED

Theorem code_copy_ctor_one_ptr:
  immutable_copy_one T imm src (Var root) off sa = ((),sb) /\
  copy_old_operand sa src /\ not_fresh_at sa root /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  w2n (a + n2w off) + 32 <= lo /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
     copy_old_operand sa region /\ op_taint tn region = {} /\
     op_prov G region = NONE) /\
  ptr_covers G tn root s capacity /\
  off < capacity /\ off + 32 <= capacity /\
  w2n b + off < dimword(:256) /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    copy_runtime_frame sa s sb t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    (!x. x IN tnf.t_mem <=>
       if w2n (b + n2w off) <= x /\ x < w2n (b + n2w off) + 32
       then w2n (a + n2w off) + (x - w2n (b + n2w off)) IN tn.t_mem
       else x IN tn.t_mem) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tnf p t n)
Proof
  simp[immutable_copy_one_def, immutable_comp_bind_cases] >> strip_tac >>
  drule_all code_copy_ctor_read_prefix >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  rename1 `copy_runtime_frame sa s sm t` >>
  `not_fresh_at sm root` by
    (fs[copy_runtime_frame_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `lookup_var root t = SOME b` by fs[copy_runtime_frame_def] >>
  `ptr_covers Gf tnf root t capacity` by metis_tac[] >>
  `w2n b + off < dimword(:256)` by simp[] >>
  drule_all code_copy_ctor_write_suffix >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl [`Gf'`, `tnf'`, `t'`] >> simp[] >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (fs[copy_runtime_frame_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  rpt conj_tac
  >- metis_tac[copy_runtime_frame_trans]
  >- (irule emitted_inst_seq_ptr_uniform_compose >>
      qexistsl [`Gf`, `sm`, `t`, `tnf`] >>
      fs[copy_runtime_frame_def, inst_extends_def])
  >- (gen_tac >>
      mp_tac (Q.INST [`M` |-> `tn.t_mem`, `c` |-> `w2n (b + n2w off : bytes32)`,
                      `d` |-> `w2n (a + n2w off : bytes32)`] store_word_taint_pointwise) >>
      simp[])
  >> metis_tac[]
QED

(* ===== compile_imm_copy_to_memory T: the whole copy ===== *)

Theorem copy_word_taint_compose:
  !a b off n M M1 M2.
  (a + off + 32 * SUC n <= b \/ b + off + 32 * SUC n <= a) /\
  (!x. x IN M1 <=>
     if b + off <= x /\ x < b + off + 32
     then a + off + (x - (b + off)) IN M else x IN M) /\
  (!x. x IN M2 <=>
     if b + (off + 32) <= x /\ x < b + (off + 32) + 32 * n
     then a + (x - b) IN M1 else x IN M1) ==>
  !x. x IN M2 <=>
     if b + off <= x /\ x < b + off + 32 * SUC n
     then a + (x - b) IN M else x IN M
Proof
  rpt strip_tac >> fs[MULT_SUC] >>
  (Cases_on `b + off <= x /\ x < b + off + 32`
  >- (`~(b + (off + 32) <= x)` by decide_tac >>
      `x < b + off + (32 * n + 32)` by decide_tac >>
      `a + off + (x - (b + off)) = a + (x - b)` by decide_tac >>
      fs[]) >>
  Cases_on `b + (off + 32) <= x /\ x < b + (off + 32) + 32 * n`
  >- (`~(b + off <= a + (x - b) /\ a + (x - b) < b + off + 32)` by
        decide_tac >>
      `b + off <= x /\ x < b + off + (32 * n + 32)` by decide_tac >>
      fs[]) >>
   `~(b + off <= x /\ x < b + off + (32 * n + 32))` by decide_tac >>
   fs[])
QED

Theorem ctor_copy_one_insts[local]:
  immutable_copy_one T imm src dst off sa = ((),sb) ==>
  EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; MSTORE]) (emitted_insts sa sb)
Proof
  strip_tac >>
  `compile_imm_copy_to_memory T imm src dst (SUC 0) off sa = ((),sb)` by
    simp[immutable_copy_suc, comp_ignore_bind_def,
         compile_imm_copy_to_memory_def, comp_return_def, comp_bind_def] >>
  drule code_ctor_copy_insts >> strip_tac >>
  fs[emitted_insts_def, DROP_APPEND]
QED

(* n words from the section below lo into a buffer at or above lo: each
   buffer byte takes the taint of the section byte it copies. *)
Theorem code_copy_ctor_range_ptr:
  !n off sa sb s G tn.
  compile_imm_copy_to_memory T imm src (Var root) n off sa = ((),sb) /\
  copy_old_operand sa src /\ not_fresh_at sa root /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
     copy_old_operand sa region /\ op_taint tn region = {} /\
     op_prov G region = NONE) /\
  w2n a + off + 32 * n <= lo /\ lo <= w2n b /\
  ptr_covers G tn root s capacity /\
  off + 32 * n <= capacity /\ w2n b + capacity < dimword(:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    copy_runtime_frame sa s sb t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    (!x. x IN tnf.t_mem <=>
       if w2n b + off <= x /\ x < w2n b + off + 32 * n
       then w2n a + (x - w2n b) IN tn.t_mem else x IN tn.t_mem) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
      ptr_covers Gf tnf p t sz)
Proof
  Induct >> rpt gen_tac
  >- (simp[compile_imm_copy_to_memory_def, comp_return_def] >> strip_tac >>
      gvs[] >> qexistsl [`G`, `tn`, `s`] >>
      simp[copy_runtime_frame_refl, emitted_insts_def, inst_seq_ptr_def]) >>
  simp[immutable_copy_suc, comp_ignore_bind_def, immutable_comp_bind_cases] >>
  strip_tac >>
  rename1 `immutable_copy_one T imm src (Var root) off sa = ((),sm)` >>
  `w2n a < dimword(:256)` by simp[w2n_lt] >>
  `w2n (a + n2w off) = w2n a + off /\ w2n (b + n2w off) = w2n b + off` by
    (Cases_on `a` >> Cases_on `b` >> fs[word_add_n2w, MULT_SUC]) >>
  `off < capacity /\ off + 32 <= capacity /\ w2n b + off < dimword(:256) /\
   w2n (a + n2w off) + 32 <= lo` by fs[MULT_SUC] >>
  drule_all code_copy_ctor_one_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (fs[copy_runtime_frame_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `copy_old_operand sm src /\ not_fresh_at sm root /\
    eval_operand src t = SOME a /\ lookup_var root t = SOME b /\
    op_taint tnf src = {} /\ op_prov Gf src = NONE /\
    ptr_covers Gf tnf root t capacity` by
    (rpt conj_tac
     >- (irule copy_old_operand_mono >> metis_tac[copy_runtime_frame_def])
     >- metis_tac[]
     >- metis_tac[copy_runtime_frame_operand]
     >- fs[copy_runtime_frame_def]
     >- metis_tac[old_operand_taint_frame, copy_old_operand_def]
     >- metis_tac[old_operand_prov_frame]
     >> metis_tac[]) >>
  drule_then (drule_then (drule_then assume_tac)) ctor_region_frame >>
  `w2n a + (off + 32) + 32 * n <= lo /\ (off + 32) + 32 * n <= capacity /\
   w2n b + capacity < dimword(:256)` by
    fs[MULT_SUC] >>
  qpat_x_assum `!off sa sb s G tn. _` drule_all >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qexistsl [`Gf'`, `tnf'`, `t'`] >>
  reverse (rpt conj_tac)
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (qspecl_then [`w2n a`, `w2n b`, `off`, `n`, `tn.t_mem`, `tnf.t_mem`,
                    `tnf'.t_mem`] mp_tac copy_word_taint_compose >>
      impl_tac
      >- (rpt conj_tac
          >- (disj1_tac >> fs[MULT_SUC])
          >- (gen_tac >> qpat_x_assum `!x. x IN tnf.t_mem <=> _`
                (qspec_then `x` mp_tac) >> simp[])
          >> first_assum ACCEPT_TAC) >>
      simp[])
  >- (irule emitted_inst_seq_ptr_uniform_compose >>
      qexistsl [`Gf`, `sm`, `t`, `tnf`] >>
      fs[copy_runtime_frame_def, inst_extends_def] >>
      drule ctor_copy_one_insts >> simp[EVERY_MEM] >>
      metis_tac[is_terminator_def]) >>
  metis_tac[copy_runtime_frame_trans]
QED

Theorem code_copy_ctor_range_counted:
  compile_imm_copy_to_memory T imm src dst n off sa = ((),sb) /\
  copy_runtime_frame sa s sb t /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := k) Gf tnf) ==>
  gas_path_ptr D lo ctx fn PG G tn s 0 Gf tnf
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)))
Proof
  strip_tac >> drule code_ctor_copy_insts >> strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; MSTORE]) (emitted_insts sa sb)` by
    fs[emitted_insts_def, DROP_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[is_terminator_def]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `EVERY (\i. MEM i.inst_opcode _) _`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then drule >> strip_tac >> gvs[]) >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tnf` by
    (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
      (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  fs[copy_runtime_frame_def] >> drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem code_copy_ctor_range_code_cursor:
  compile_imm_copy_to_memory T imm src dst n off sa = ((),sb) /\
  fn_has_code sa sb fn /\ copy_runtime_frame sa s sb t /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := k) Gf tnf) ==>
  gas_path_ptr D lo ctx fn PG G tn s 0 Gf tnf
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted
Proof
  strip_tac >> drule code_ctor_copy_insts >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by
    (fs[emitted_insts_def, DROP_APPEND, EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[is_terminator_def]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK t` by fs[copy_runtime_frame_def] >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    fs[copy_runtime_frame_def, same_blocks_def] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  drule_all code_copy_ctor_range_counted >> simp[]
QED
