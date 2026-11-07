(* Pointer-checked constructor immutable writes at (D, lo): compile_imm_store_word
 * (an ADD of the region base, zero in a constructor, then ISTORE) writes a
 * word of the fixed region below lo through an address with no provenance.
 *
 * The stored word may be tainted (a dead tail byte of the value).  ISTORE
 * moves its taint into the written memory bytes, exactly as MSTORE does,
 * and records it against the word's key in t_imm; t_imm is checked only at
 * a halt, against D.d_imm, which a constructor's dead_lo_ok makes UNIV.
 *
 * TOP-LEVEL:
 *   ptr_inst_ok_istore -- the ISTORE check
 *   ctor_istore_segment, ctor_word_store_seq -- the stages
 *   code_ctor_store_word -- compile_imm_store_word
 *   code_ctor_store_one_ptr, code_ctor_store_range_ptr,
 *   code_ctor_store_range_code_cursor -- compile_imm_store_words, which
 *     MLOADs each word of a value buffer at or above lo and stores it
 *     into the section below lo
 *
 * ISTORE changes vs_immutables, which copy_runtime_frame keeps fixed, so
 * these stages carry immutable_execution_frame instead.
 *)
Theory exprPtrCtorImmStore
Ancestors
  exprPtrCtorCodeLoad exprPtrUnwrapStoreSegment exprPtrUnwrapCopyEdges
  exprPtrCodeCopyOffset immutableCopyExecution fragGasSeqPtr
  entrySinkExtraction fragExec
  instSeqComposePtr emittedSeqComposePtr exprSimCopy immutableWordExecution
  decoderGhostFramePtr fragGasSeqPtr ptrSafeRun ptrDiscipline bodyPtrDefs
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  codegenRel contextCodegenRel memLocDefs
  venomExecSemantics venomInst venomState instIdxIndep
  finite_map pred_set list rich_list arithmetic words

(* ===== One instruction ===== *)

Theorem ptr_inst_ok_istore:
  eval_operand a s = SOME off /\ op_taint tn a = {} /\ op_prov G a = NONE /\
  w2n off + 32 <= lo /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id ISTORE [a; v] []) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       fixed_source_write_range_def, mem_write_ops_def] >>
  conj_tac
  >- (Cases_on `eval_operand v s` >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> gvs[]) >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[AllCaseEqs(), istore_def, mstore_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem istore_transferred_taint:
  eval_operand a s = SOME addr /\ eval_operand v s = SOME value ==>
  (step_taint (mk_inst id ISTORE [a;v] []) s
    (istore (w2n addr) value s) tn).t_mem =
  (tn.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr + 32}) UNION
    {w2n addr + k | k IN op_taint tn v} /\
  (step_taint (mk_inst id ISTORE [a;v] []) s
    (istore (w2n addr) value s) tn).t_imm =
  key_update tn.t_imm (w2n addr) (op_taint tn v) /\
  (step_taint (mk_inst id ISTORE [a;v] []) s
    (istore (w2n addr) value s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id ISTORE [a;v] []) s
    (istore (w2n addr) value s) tn).t_trans = tn.t_trans
Proof
  strip_tac >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
       written_taint_def, source_memory_write_ranges_def, range_bytes_def,
       fixed_source_write_range_def, mk_inst_def, istore_def, mstore_def,
       imm_taint_def, store_taint_def, adopt_reset_def,
       FLOOKUP_DEF, EXTENSION] >> metis_tac[]
QED

(* ===== The stages ===== *)

Theorem ctor_istore_segment:
  eval_operand arg s = SOME a /\ op_taint tn arg = {} /\
  op_prov G arg = NONE /\ w2n a + 32 <= lo /\
  eval_operand v s = SOME value /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq [mk_inst id ISTORE [arg;v] []] s = OK t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn [mk_inst id ISTORE [arg;v] []]
      (s with vs_inst_idx := k) Gf tnf) /\
    t = istore (w2n a) value s /\
    tnf.t_mem =
      (tn.t_mem DIFF {j | w2n a <= j /\ j < w2n a + 32}) UNION
        {w2n a + k | k IN op_taint tn v} /\
    tnf.t_imm = key_update tn.t_imm (w2n a) (op_taint tn v) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. FLOOKUP Gf p = FLOOKUP G p /\
         op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. ptr_covers G tn p s n ==> ptr_covers Gf tnf p t n)
Proof
  strip_tac >>
  qexistsl [`step_prov PG G (mk_inst id ISTORE [arg;v] [])
    (istore (w2n a) value s)`,
    `step_taint (mk_inst id ISTORE [arg;v] []) s
      (istore (w2n a) value s) tn`, `istore (w2n a) value s`] >>
  `step_inst_base (mk_inst id ISTORE [arg;v] []) s =
    OK (istore (w2n a) value s)` by
    simp[step_inst_base_def, mk_inst_def] >>
  drule_all istore_transferred_taint >>
  disch_then (qspecl_then [`tn`, `id`] strip_assume_tac) >>
  simp[run_inst_seq_def, inst_seq_ptr_def] >>
  conj_tac
  >- (gen_tac >>
      simp[step_inst_inst_idx_indep, exec_result_map_def] >>
      pure_rewrite_tac[GSYM mk_inst_def] >> irule ptr_inst_ok_istore >>
      fs[]) >>
  simp[step_prov_def, set_prov_def, step_taint_def, set_var_taint_def,
       mk_inst_def, FLOOKUP_DRESTRICT, allocas_from_def,
       allocas_below_fmp_def, ptr_covers_def, istore_def, mstore_def,
       lookup_var_def] >>
  fs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]
QED

(* ADD [region; dst]; ISTORE [addr; v]: the region base is zero. *)
Theorem ctor_word_store_seq:
  eval_operand region s = SOME 0w /\ op_taint tn region = {} /\
  op_prov G region = NONE /\
  eval_operand dst s = SOME a /\ op_taint tn dst = {} /\ op_prov G dst = NONE /\
  w2n a + 32 <= lo /\ eval_operand v s = SOME value /\
  (!x. v = Var x ==> x <> tmp) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!p. P p ==> p <> tmp) ==>
  ?Gf tnf t.
    run_inst_seq [mk_inst id ADD [region; dst] [tmp];
                  mk_inst (id + 1) ISTORE [Var tmp; v] []] s = OK t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id ADD [region; dst] [tmp];
       mk_inst (id + 1) ISTORE [Var tmp; v] []]
      (s with vs_inst_idx := k) Gf tnf) /\
    t = istore (w2n a) value (update_var tmp a s) /\
    tnf.t_mem =
      (tn.t_mem DIFF {j | w2n a <= j /\ j < w2n a + 32}) UNION
        {w2n a + k | k IN op_taint tn v} /\
    tnf.t_imm = key_update tn.t_imm (w2n a) (op_taint tn v) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. P p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. P p /\ ptr_covers G tn p s n ==> ptr_covers Gf tnf p t n)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [region; dst] [tmp]) s =
     OK (update_var tmp a s)` by
    (simp[mk_inst_def, step_inst_base_def, exec_pure2_def] >>
     simp[wordsTheory.WORD_ADD_0]) >>
  `run_inst_seq [mk_inst id ADD [region; dst] [tmp]] s =
     OK (update_var tmp a s)` by simp[run_inst_seq_def] >>
  `?G1 tn1.
     (!k. inst_seq_ptr D lo ctx fn PG G tn [mk_inst id ADD [region; dst] [tmp]]
        (s with vs_inst_idx := k) G1 tn1) /\
     op_taint tn1 (Var tmp) = {} /\ op_prov G1 (Var tmp) = NONE /\
     tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
     tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
     (!p. P p \/ v = Var p ==>
       FLOOKUP G1 p = FLOOKUP G p /\
       op_taint tn1 (Var p) = op_taint tn (Var p)) /\
     allocas_from lo (update_var tmp a s) /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp (update_var tmp a s)) /\
     (!p n. (P p \/ v = Var p) /\ ptr_covers G tn p s n ==>
       ptr_covers G1 tn1 p (update_var tmp a s) n)` by
    (irule ctor_base_add_segment >> simp[] >> metis_tac[]) >>
  `op_taint tn1 v = op_taint tn v` by
    (Cases_on `v` >> fs[op_taint_def] >> metis_tac[]) >>
  `eval_operand (Var tmp) (update_var tmp a s) = SOME a /\
   eval_operand v (update_var tmp a s) = SOME value` by
    (Cases_on `v` >>
     gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `?Gf tnf t.
     run_inst_seq [mk_inst (id + 1) ISTORE [Var tmp; v] []]
       (update_var tmp a s) = OK t /\
     (!k. inst_seq_ptr D lo ctx fn PG G1 tn1
        [mk_inst (id + 1) ISTORE [Var tmp; v] []]
        (update_var tmp a s with vs_inst_idx := k) Gf tnf) /\
     t = istore (w2n a) value (update_var tmp a s) /\
     tnf.t_mem =
       (tn1.t_mem DIFF {j | w2n a <= j /\ j < w2n a + 32}) UNION
         {w2n a + k | k IN op_taint tn1 v} /\
     tnf.t_imm = key_update tn1.t_imm (w2n a) (op_taint tn1 v) /\
     tnf.t_stor = tn1.t_stor /\ tnf.t_trans = tn1.t_trans /\
     (!p. FLOOKUP Gf p = FLOOKUP G1 p /\
          op_taint tnf (Var p) = op_taint tn1 (Var p)) /\
     allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
     (!p n. ptr_covers G1 tn1 p (update_var tmp a s) n ==>
        ptr_covers Gf tnf p t n)` by
    (irule ctor_istore_segment >> simp[]) >>
  qexistsl [`Gf`, `tnf`, `t`] >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
     [mk_inst id ADD [region; dst] [tmp]]` by
    simp[mk_inst_def, is_terminator_def] >>
  rpt conj_tac
  >- (ONCE_REWRITE_TAC[run_inst_seq_def] >> simp[])
  >- (`[mk_inst id ADD [region; dst] [tmp];
        mk_inst (id + 1) ISTORE [Var tmp; v] []] =
       [mk_inst id ADD [region; dst] [tmp]] ++
       [mk_inst (id + 1) ISTORE [Var tmp; v] []]` by simp[] >>
      pop_assum SUBST1_TAC >> irule inst_seq_ptr_uniform_append >>
      metis_tac[])
  >> gvs[] >> metis_tac[]
QED

(* ===== compile_imm_store_words: the value buffer's words ===== *)

Theorem ptr_inst_ok_mload_lo:
  ptr_covers G tn p s 32 /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id MLOAD [Var p] [out]) s
Proof
  strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       eval_operand_def] >>
  conj_tac
  >- (rpt strip_tac >> gvs[mem_read_ops_def] >> metis_tac[]) >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_read1_def, eval_operand_def, update_var_def]
QED

(* MLOAD [Var p]: a covered word; the output carries its bytes' taint. *)
Theorem ctor_mload_segment:
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME w /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  run_inst_seq [mk_inst id MLOAD [Var p] [out]] s = OK t /\
  (!q. P q ==> q <> out) ==>
  ?Gf tnf.
    (!k. inst_seq_ptr D lo ctx fn PG G tn [mk_inst id MLOAD [Var p] [out]]
      (s with vs_inst_idx := k) Gf tnf) /\
    op_taint tnf (Var out) = mem_word_taint tn.t_mem (w2n w) /\
    op_prov Gf (Var out) = NONE /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. P q ==> FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!q n. P q /\ ptr_covers G tn q s n ==> ptr_covers Gf tnf q t n)
Proof
  strip_tac >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  `step_inst_base (mk_inst id MLOAD [Var p] [out]) s =
    OK (update_var out (mload (w2n w) s) s)` by
    simp[step_inst_base_def, mk_inst_def, exec_read1_def] >>
  gvs[run_inst_seq_def] >>
  qexistsl [`step_prov PG G (mk_inst id MLOAD [Var p] [out])
    (update_var out (mload (w2n w) s) s)`,
    `step_taint (mk_inst id MLOAD [Var p] [out]) s
      (update_var out (mload (w2n w) s) s) tn`] >>
  simp[inst_seq_ptr_def, ptr_inst_ok_mload_lo,
    step_inst_inst_idx_indep, exec_result_map_def, mk_inst_def,
    is_terminator_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[load_word_output_taint, load_word_taint_frame] >>
  rpt conj_tac
  >- (irule step_prov_out_none >> simp[mk_inst_def] >>
      irule out_prov_other_none >> simp[mk_inst_def])
  >- (rpt strip_tac >> `q <> out` by metis_tac[] >>
      simp[step_prov_other_output, step_taint_other_output, mk_inst_def])
  >> rpt strip_tac >> `q <> out` by metis_tac[] >>
  irule ptr_covers_step_frame >>
  simp[mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem store_word_insts[local]:
  EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) l ==>
  EVERY (\i. ~is_terminator i.inst_opcode) l /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) l /\
  FILTER (\i. i.inst_opcode = GAS) l = []
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >> gvs[is_terminator_def]
QED

Theorem code_ctor_mload:
  emit_op MLOAD [Var p] sa = (op,sb) /\ fresh_vars_wrt sa s /\
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME w /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    immutable_execution_frame sa s sb t /\ sa.cs_next_var <= sb.cs_next_var /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sa sb) /\
    eval_operand op t = SOME (mload (w2n w) s) /\
    op_taint tnf op = mem_word_taint tn.t_mem (w2n w) /\
    op_prov Gf op = NONE /\ copy_old_operand sb op /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==> FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!q n. not_fresh_at sa q /\ ptr_covers G tn q s n ==>
      ptr_covers Gf tnf q t n)
Proof
  strip_tac >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `MLOAD`]
    (SPEC_ALL immutable_emit_read_frame))) >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `!q. not_fresh_at sa q ==>
     q <> STRING #"%" (toString sa.cs_next_var)` by simp[not_fresh_at_def] >>
  gvs[] >>
  drule_all (Q.INST [`P` |-> `not_fresh_at sa`] ctor_mload_segment) >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qexistsl [`Gf`, `tnf`, `s'`] >>
  simp[immutable_execution_frame_def, mk_inst_def] >>
  simp[copy_old_operand_def, not_fresh_at_def]
QED

(* The source word: an offset into the value buffer, then MLOAD. *)
Theorem code_ctor_store_read_prefix:
  compile_lit_byte_offset (Var root) off sa = (sop,sm) /\
  emit_op MLOAD [sop] sm = (v,sb) /\
  fresh_vars_wrt sa s /\ not_fresh_at sa root /\ lookup_var root s = SOME b /\
  ptr_covers G tn root s capacity /\
  off < capacity /\ off + 32 <= capacity /\ w2n b + off < dimword(:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    immutable_execution_frame sa s sb t /\ sa.cs_next_var <= sb.cs_next_var /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sa sb) /\
    op_taint tnf v = mem_word_taint tn.t_mem (w2n (b + n2w off)) /\
    copy_old_operand sb v /\ (?value. eval_operand v t = SOME value) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==> FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!q n. not_fresh_at sa q /\ ptr_covers G tn q s n ==>
      ptr_covers Gf tnf q t n)
Proof
  strip_tac >>
  `copy_old_operand sa (Var root) /\ eval_operand (Var root) s = SOME b /\
   op_taint tn (Var root) = {}` by
    fs[copy_old_operand_def, eval_operand_def, ptr_covers_def] >>
  drule_all code_copy_source_offset >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  rename1 `copy_runtime_frame sa s sm t1` >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sm) s Gf tnf` by
    (qpat_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
      (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  drule_all code_copy_destination_coverage >> strip_tac >> gvs[] >>
  drule_all immutable_offset_frame >> strip_tac >>
  `s' = t1` by fs[immutable_execution_frame_def, copy_runtime_frame_def] >>
  gvs[] >>
  `lookup_var p t1 = SOME (b + n2w off)` by fs[eval_operand_def] >>
  `fresh_vars_wrt sm t1` by
    fs[immutable_execution_frame_def, immutable_operand_frame_def] >>
  drule_all code_ctor_mload >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  rename1 `immutable_execution_frame sm t1 sb t2` >>
  qexistsl [`Gf'`, `tnf'`, `t2`] >>
  `!q. not_fresh_at sa q ==> not_fresh_at sm q` by
    (fs[copy_runtime_frame_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sa sm)` by
    (drule code_offset_insts >> simp[EVERY_MEM] >> rpt strip_tac >>
     res_tac >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> fs[immutable_execution_frame_def]) >>
  rpt conj_tac
  >- metis_tac[immutable_execution_frame_trans]
  >- fs[copy_runtime_frame_def]
  >- (irule emitted_inst_seq_ptr_uniform_compose >>
      qexistsl [`Gf`, `sm`, `t1`, `tnf`] >>
      fs[immutable_execution_frame_def, inst_extends_def, store_word_insts])
  >- simp[EVERY_APPEND]
  >> metis_tac[]
QED

(* compile_imm_store_word: ADD of the region base (zero), then ISTORE. *)
Theorem code_ctor_store_word:
  compile_imm_store_word imm dst v sa = ((),sb) /\ fresh_vars_wrt sa s /\
  copy_old_operand sa v /\ eval_operand v s = SOME value /\
  eval_operand dst s = SOME a /\ op_taint tn dst = {} /\ op_prov G dst = NONE /\
  w2n a + 32 <= lo /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
     op_taint tn region = {} /\ op_prov G region = NONE) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    immutable_execution_frame sa s sb t /\ sa.cs_next_var <= sb.cs_next_var /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sa sb) /\
    tnf.t_mem =
      (tn.t_mem DIFF {j | w2n a <= j /\ j < w2n a + 32}) UNION
        {w2n a + k | k IN op_taint tn v} /\
    tnf.t_imm = key_update tn.t_imm (w2n a) (op_taint tn v) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tnf p t n)
Proof
  strip_tac >>
  `!p. not_fresh_at sa p ==>
     p <> STRING #"%" (toString sa.cs_next_var)` by simp[not_fresh_at_def] >>
  `!x. v = Var x ==> x <> STRING #"%" (toString sa.cs_next_var)` by
    (rpt strip_tac >> gvs[copy_old_operand_def, not_fresh_at_def]) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qspecl_then [`imm`, `dst`, `v`, `sa`] mp_tac
       ci_mono_compile_imm_store_word >> simp[ci_mono_def]) >>
  Cases_on `imm`
  >- (gvs[compile_imm_store_word_def] >>
      drule_all (SRULE [] (Q.INST [`opc` |-> `ISTORE`]
        (SPEC_ALL immutable_emit_store_frame))) >> strip_tac >>
      drule emitted_insts_emit_void >> strip_tac >>
      drule_all (Q.INST [`id` |-> `sa.cs_next_id`] ctor_istore_segment) >>
      disch_then (strip_assume_tac o SPEC_ALL) >>
      qexistsl [`Gf`, `tnf`, `t`] >>
      gvs[immutable_execution_frame_def, mk_inst_def, istore_def, mstore_def] >>
      metis_tac[]) >>
  rename1 `compile_imm_store_word (SOME region) dst v sa` >>
  gvs[] >>
  drule_all immutable_ctor_store_frame >> strip_tac >>
  drule compile_imm_store_word_result >> strip_tac >>
  `emitted_insts sa sb =
     [mk_inst sa.cs_next_id ADD [region; dst]
        ["%" ++ toString sa.cs_next_var];
      mk_inst (sa.cs_next_id + 1) ISTORE
        [Var ("%" ++ toString sa.cs_next_var); v] []]` by
    simp[emitted_insts_def, DROP_APPEND] >>
  drule_all (Q.INST [`P` |-> `not_fresh_at sa`, `id` |-> `sa.cs_next_id`,
                     `tmp` |-> `STRING #"%" (toString sa.cs_next_var)`]
    ctor_word_store_seq) >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qexistsl [`Gf`, `tnf`, `s'`] >>
  gvs[immutable_execution_frame_def, mk_inst_def] >> metis_tac[]
QED

(* The destination word: an offset into the section, then the store. *)
Theorem code_ctor_store_write_suffix:
  compile_lit_byte_offset dst off sa = (dop,sm) /\
  compile_imm_store_word imm dop v sm = ((),sb) /\
  fresh_vars_wrt sa s /\ copy_old_operand sa dst /\ copy_old_operand sa v /\
  eval_operand v s = SOME value /\
  eval_operand dst s = SOME a /\ op_taint tn dst = {} /\ op_prov G dst = NONE /\
  w2n (a + n2w off) + 32 <= lo /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
     copy_old_operand sa region /\ op_taint tn region = {} /\
     op_prov G region = NONE) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    immutable_execution_frame sa s sb t /\ sa.cs_next_var <= sb.cs_next_var /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sa sb) /\
    tnf.t_mem =
      (tn.t_mem DIFF
        {j | w2n (a + n2w off) <= j /\ j < w2n (a + n2w off) + 32}) UNION
      {w2n (a + n2w off) + k | k IN op_taint tn v} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tnf p t n)
Proof
  strip_tac >>
  drule_all code_copy_ctor_source_offset >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  rename1 `copy_runtime_frame sa s sm t1` >>
  drule_all immutable_offset_frame >> strip_tac >>
  `s' = t1` by fs[immutable_execution_frame_def, copy_runtime_frame_def] >>
  gvs[] >>
  `fresh_vars_wrt sm t1` by
    fs[immutable_execution_frame_def, immutable_operand_frame_def] >>
  `copy_old_operand sm v /\ eval_operand v t1 = SOME value /\
   op_taint tnf v = op_taint tn v` by
    (rpt conj_tac
     >- metis_tac[copy_old_operand_mono, copy_runtime_frame_def]
     >- metis_tac[copy_runtime_frame_operand]
     >> metis_tac[old_operand_taint_frame, copy_old_operand_def]) >>
  drule_then (drule_then (drule_then assume_tac)) ctor_region_frame >>
  `!region. imm = SOME region ==> eval_operand region t1 = SOME 0w /\
     op_taint tnf region = {} /\ op_prov Gf region = NONE` by metis_tac[] >>
  drule_all code_ctor_store_word >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  rename1 `immutable_execution_frame sm t1 sb t2` >>
  qexistsl [`Gf'`, `tnf'`, `t2`] >>
  `!q. not_fresh_at sa q ==> not_fresh_at sm q` by
    (fs[copy_runtime_frame_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sa sm)` by
    (drule code_offset_insts >> simp[EVERY_MEM] >> rpt strip_tac >>
     res_tac >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> fs[immutable_execution_frame_def]) >>
  rpt conj_tac
  >- metis_tac[immutable_execution_frame_trans]
  >- fs[copy_runtime_frame_def]
  >- (irule emitted_inst_seq_ptr_uniform_compose >>
      qexistsl [`Gf`, `sm`, `t1`, `tnf`] >>
      fs[immutable_execution_frame_def, inst_extends_def, store_word_insts])
  >- simp[EVERY_APPEND]
  >> metis_tac[]
QED

Theorem code_ctor_store_one_ptr:
  immutable_store_one imm (Var root) dst off sa = ((),sb) /\
  fresh_vars_wrt sa s /\ not_fresh_at sa root /\ lookup_var root s = SOME b /\
  ptr_covers G tn root s capacity /\
  off < capacity /\ off + 32 <= capacity /\ w2n b + off < dimword(:256) /\
  copy_old_operand sa dst /\ eval_operand dst s = SOME a /\
  op_taint tn dst = {} /\ op_prov G dst = NONE /\
  w2n (a + n2w off) + 32 <= lo /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
     copy_old_operand sa region /\ op_taint tn region = {} /\
     op_prov G region = NONE) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    immutable_execution_frame sa s sb t /\ sa.cs_next_var <= sb.cs_next_var /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sa sb) /\
    (!x. x IN tnf.t_mem <=>
       if w2n (a + n2w off) <= x /\ x < w2n (a + n2w off) + 32
       then w2n (b + n2w off) + (x - w2n (a + n2w off)) IN tn.t_mem
       else x IN tn.t_mem) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tnf p t n)
Proof
  simp[immutable_store_one_def, immutable_comp_bind_cases] >> strip_tac >>
  rename1 `emit_op MLOAD [sop] sm = (v,sr)` >>
  drule_all code_ctor_store_read_prefix >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  rename1 `immutable_execution_frame sa s sr t1` >>
  `!q. not_fresh_at sa q ==> not_fresh_at sr q` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `copy_old_operand sr dst /\ eval_operand dst t1 = SOME a /\
   op_taint tnf dst = {} /\ op_prov Gf dst = NONE` by
    (rpt conj_tac
     >- (irule copy_old_operand_mono >> metis_tac[])
     >- fs[immutable_execution_frame_def, immutable_operand_frame_def]
     >- metis_tac[old_operand_taint_frame, copy_old_operand_def]
     >> metis_tac[old_operand_prov_frame]) >>
  `!region. imm = SOME region ==> eval_operand region t1 = SOME 0w /\
     copy_old_operand sr region /\ op_taint tnf region = {} /\
     op_prov Gf region = NONE` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >> rpt conj_tac
     >- fs[immutable_execution_frame_def, immutable_operand_frame_def]
     >- (irule copy_old_operand_mono >> metis_tac[])
     >- metis_tac[old_operand_taint_frame, copy_old_operand_def]
     >> metis_tac[old_operand_prov_frame]) >>
  drule_all code_ctor_store_write_suffix >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  rename1 `immutable_execution_frame sr t1 sb t2` >>
  qexistsl [`Gf'`, `tnf'`, `t2`] >>
  `emitted_insts sa sb = emitted_insts sa sr ++ emitted_insts sr sb` by
    (irule emitted_insts_append >> fs[immutable_execution_frame_def]) >>
  rpt conj_tac
  >- metis_tac[immutable_execution_frame_trans]
  >- decide_tac
  >- (irule emitted_inst_seq_ptr_uniform_compose >>
      qexistsl [`Gf`, `sr`, `t1`, `tnf`] >>
      fs[immutable_execution_frame_def, inst_extends_def, store_word_insts])
  >- simp[EVERY_APPEND]
  >- (gen_tac >>
      mp_tac (Q.INST [`M` |-> `tn.t_mem`, `c` |-> `w2n (a + n2w off : bytes32)`,
                      `d` |-> `w2n (b + n2w off : bytes32)`] store_word_taint_pointwise) >>
      simp[])
  >> metis_tac[]
QED

(* n words of a value buffer at or above lo into the section below lo:
   each section byte takes the taint of the buffer byte it copies. *)
Theorem code_ctor_store_range_ptr:
  !n off sa sb s G tn.
  compile_imm_store_words imm (Var root) dst n off sa = ((),sb) /\
  fresh_vars_wrt sa s /\ not_fresh_at sa root /\ lookup_var root s = SOME b /\
  copy_old_operand sa dst /\ eval_operand dst s = SOME a /\
  op_taint tn dst = {} /\ op_prov G dst = NONE /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
     copy_old_operand sa region /\ op_taint tn region = {} /\
     op_prov G region = NONE) /\
  w2n a + off + 32 * n <= lo /\ lo <= w2n b /\
  ptr_covers G tn root s capacity /\
  off + 32 * n <= capacity /\ w2n b + capacity < dimword(:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    immutable_execution_frame sa s sb t /\ sa.cs_next_var <= sb.cs_next_var /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sa sb) /\
    (!x. x IN tnf.t_mem <=>
       if w2n a + off <= x /\ x < w2n a + off + 32 * n
       then w2n b + (x - w2n a) IN tn.t_mem else x IN tn.t_mem) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
      ptr_covers Gf tnf p t sz)
Proof
  Induct >> rpt gen_tac
  >- (simp[compile_imm_store_words_def, comp_return_def] >> strip_tac >>
      gvs[] >> qexistsl [`G`, `tn`, `s`] >>
      simp[emitted_insts_def, inst_seq_ptr_def, immutable_execution_frame_def,
           run_inst_seq_def, same_blocks_def, immutable_operand_frame_def]) >>
  simp[immutable_store_suc, comp_ignore_bind_def, immutable_comp_bind_cases] >>
  strip_tac >>
  rename1 `immutable_store_one imm (Var root) dst off sa = ((),sm)` >>
  `w2n (a + n2w off) = w2n a + off /\ w2n (b + n2w off) = w2n b + off` by
    (Cases_on `a` >> Cases_on `b` >> fs[word_add_n2w, MULT_SUC]) >>
  `off < capacity /\ off + 32 <= capacity /\ w2n b + off < dimword(:256) /\
   w2n (a + n2w off) + 32 <= lo` by fs[MULT_SUC] >>
  drule_all code_ctor_store_one_ptr >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  rename1 `immutable_execution_frame sa s sm t1` >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `fresh_vars_wrt sm t1 /\ lookup_var root t1 = SOME b /\
   eval_operand dst t1 = SOME a` by
    (fs[immutable_execution_frame_def, immutable_operand_frame_def] >>
     first_x_assum (qspecl_then [`Var root`, `b`] mp_tac) >>
     simp[eval_operand_def]) >>
  `not_fresh_at sm root /\ copy_old_operand sm dst /\
   op_taint tnf dst = {} /\ op_prov Gf dst = NONE /\
   ptr_covers Gf tnf root t1 capacity` by
    (rpt conj_tac
     >- metis_tac[]
     >- (irule copy_old_operand_mono >> metis_tac[])
     >- metis_tac[old_operand_taint_frame, copy_old_operand_def]
     >- metis_tac[old_operand_prov_frame]
     >> metis_tac[]) >>
  `!region. imm = SOME region ==> eval_operand region t1 = SOME 0w /\
     copy_old_operand sm region /\ op_taint tnf region = {} /\
     op_prov Gf region = NONE` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >> rpt conj_tac
     >- fs[immutable_execution_frame_def, immutable_operand_frame_def]
     >- (irule copy_old_operand_mono >> metis_tac[])
     >- metis_tac[old_operand_taint_frame, copy_old_operand_def]
     >> metis_tac[old_operand_prov_frame]) >>
  `w2n a + (off + 32) + 32 * n <= lo /\ (off + 32) + 32 * n <= capacity /\
   w2n b + capacity < dimword(:256)` by
    fs[MULT_SUC] >>
  qpat_x_assum `!off sa sb s G tn. _` drule_all >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qexistsl [`Gf'`, `tnf'`, `t'`] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> fs[immutable_execution_frame_def]) >>
  rpt conj_tac
  >- metis_tac[immutable_execution_frame_trans]
  >- decide_tac
  >- (irule emitted_inst_seq_ptr_uniform_compose >>
      qexistsl [`Gf`, `sm`, `t1`, `tnf`] >>
      fs[immutable_execution_frame_def, inst_extends_def, store_word_insts])
  >- simp[EVERY_APPEND]
  >- (qspecl_then [`w2n b`, `w2n a`, `off`, `n`, `tn.t_mem`, `tnf.t_mem`,
                    `tnf'.t_mem`] mp_tac copy_word_taint_compose >>
      impl_tac
      >- (rpt conj_tac
          >- (disj2_tac >> fs[MULT_SUC])
          >- (gen_tac >> qpat_x_assum `!x. x IN tnf.t_mem <=> _`
                (qspec_then `x` mp_tac) >> simp[])
          >> first_assum ACCEPT_TAC) >>
      simp[])
  >> metis_tac[]
QED

Theorem code_ctor_store_range_code_cursor:
  compile_imm_store_words imm src dst n off sa = ((),sb) /\
  fn_has_code sa sb fn /\ immutable_execution_frame sa s sb t /\
  EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sa sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := k) Gf tnf) ==>
  gas_path_ptr D lo ctx fn PG G tn s 0 Gf tnf
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted
Proof
  strip_tac >> drule store_word_insts >> strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s = OK t /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   sb.cs_current_bb = sa.cs_current_bb` by
    fs[immutable_execution_frame_def, same_blocks_def] >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tnf` by
    (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
      (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED
