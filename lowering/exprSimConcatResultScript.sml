(*
 * Concat case: the whole builtin as counted execution.  The lowering
 * allocates the result buffer and a 64-byte offset word, zeroes the
 * offset, runs the operand loop (concat_args_sim), then loads the final
 * offset and stores it as the result's length word.
 *
 * TOP-LEVEL:
 *   concat_result_vv_sim — expr_vv_sim of concat(...) from its operands'
 *     case judgments
 *)
Theory exprSimConcatResult
Ancestors
  exprSimConcatArgs exprSimConcatSource exprSimConcatStep exprSimLiteralBuffer
  exprSimHash exprSimHyps exprSimSource exprSimAlloc exprSimWordArgs
  exprSimHypsDefs exprSimProps exprSimDefs exprBopSimProps exprBopLowering
  exprCallBounds stmtSimDeclCompose gasOutcome gasSummary gasSummaryCompose
  gasExemptCert fragGasSeq fragGasMode fragGasPath freshWrites fragExec
  abiDecoderReentryPointer loweringPosts exprLowering exprLoweringProps
  emitHelperProps emitHelper context compileEnv allocLimits valueEncoding
  valueEncodingProps venomState venomExecSemantics vyperValue
  vyperValueOperation vyperTyping vyperTypeConversions vyperTypeSystem
  vyperContext vyperEvalExprPreservesScopesDom vyperInterpreter vyperState
  vyperAST venomInst venomMemProps vyperTypeInvariants words arithmetic list rich_list finite_map
Libs
  monadsyntax

Overload concat_payload_bytes[local] =
  “\v. case v of BytesV bs => bs
               | StringV str => MAP ((n2w : num -> word8) o ORD) str
               | _ => []”

(* ===== Source side ===== *)

(* The typed operands concatenate to a located bytestring whose memory
   image is its length word followed by the operands' payloads. *)
Theorem concat_typed_result:
  !ann n ts vs tenv tvr.
    2 <= LENGTH ts /\ SUM (MAP bytelike_type_bound ts) <= n /\
    ((ann = BaseT (BytesT (Dynamic n)) /\
      EVERY (\t. ?bd. t = BaseT (BytesT bd)) ts) \/
     (ann = BaseT (StringT n) /\ EVERY (\t. ?m. t = BaseT (StringT m)) ts)) /\
    LIST_REL (\t v. ?tv. evaluate_type tenv t = SOME tv /\ value_has_type tv v)
      ts vs /\
    evaluate_type tenv ann = SOME tvr ==>
    ?v. evaluate_concat n vs = INL v /\ ~is_word_type ann /\
      LENGTH (FLAT (MAP concat_payload_bytes vs)) <=
        SUM (MAP concat_payload_capacity ts) /\
      val_wf tvr v /\
      val_footprint tvr v = 32 + LENGTH (FLAT (MAP concat_payload_bytes vs)) /\
      !off mem. val_in_memory tvr v off mem <=>
        mem_word_at off mem = n2w (LENGTH (FLAT (MAP concat_payload_bytes vs))) /\
        mem_bytes_at (off + 32) (LENGTH (FLAT (MAP concat_payload_bytes vs))) mem =
          FLAT (MAP concat_payload_bytes vs)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule evaluate_type_BaseT_SOME >> strip_tac >> gvs[]
  >- (drule_all typed_bytes_operands >> strip_tac >>
      drule_all evaluate_concat_typed_bytes >> strip_tac >>
      gvs[concat_map_ctor_11] >>
      `MAP bytelike_type_bound ts = MAP concat_payload_capacity ts` by
        (irule concat_payload_capacity_bound >> fs[EVERY_MEM]) >>
      gvs[MAP_MAP_o, combinTheory.o_DEF, is_word_type_def] >>
      simp[val_wf_def, val_footprint_def, val_in_memory_def,
           type_memory_size_def] >>
      assume_tac (Q.SPEC `n` le_word_size_mul) >> decide_tac) >>
  drule_all typed_string_operands >> strip_tac >>
  drule_all evaluate_concat_typed_string >> strip_tac >>
  gvs[concat_map_ctor_11] >>
  `MAP bytelike_type_bound ts = MAP concat_payload_capacity ts` by
    (irule concat_payload_capacity_bound >> fs[EVERY_MEM]) >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, is_word_type_def, GSYM MAP_FLAT] >>
  simp[val_wf_def, val_footprint_def, val_in_memory_def,
       type_memory_size_def, LET_THM] >>
  `FLAT (MAP (\x. MAP (\x. (n2w : num -> word8) (ORD x)) x) ss) =
   MAP (n2w o ORD) (FLAT ss)` by
    (simp[rich_listTheory.MAP_FLAT, combinTheory.o_DEF] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC) >>
  pop_assum SUBST_ALL_TAC >>
  assume_tac (Q.SPEC `n` le_word_size_mul) >> rw[] >> decide_tac
QED

(* ===== Lowering shape ===== *)

Theorem compile_concat_child_callback:
  !args m f cenv dp infos op.
    EVERY (\e. expr_size e + cenv_defaults_size cenv < m) args ==>
    compile_concat (expr_child_callback m f) cenv args dp infos op =
    compile_concat f cenv args dp infos op
Proof
  Induct >- simp[compile_concat_def] >>
  rpt strip_tac >> Cases_on `infos` >- simp[compile_concat_def] >>
  rename1 `compile_concat _ _ _ _ (inf::infs)` >> PairCases_on `inf` >>
  fs[compile_concat_def, lower_value_child_call]
QED

Theorem concat_compile_shape:
  !cenv ty ann n args sa vv sb.
    compile_expr cenv ty (Builtin ann (Concat n) args) sa = (vv, sb) ==>
    ?buf s1 d s2 ob s3 u s4 s5 fo s6 u'.
      context$compile_alloc_buffer (concat_alloc_size (MAP expr_type args)) sa =
        (buf, s1) /\
      emit_op ADD [buf.buf_operand; Lit 32w] s1 = (d, s2) /\
      context$compile_alloc_buffer 64 s2 = (ob, s3) /\
      emit_void MSTORE [ob.buf_operand; Lit 0w] s3 = (u, s4) /\
      compile_concat compile_expr cenv args d (MAP (\e. let ety = expr_type e in
                if is_bytestring_type ety then (T, 0:num)
                else case ety of
                       BaseT (BytesT (Fixed m)) => (F, m)
                     | _ => (F, 32:num)) args)
        ob.buf_operand s4 = ((), s5) /\
      emit_op MLOAD [ob.buf_operand] s5 = (fo, s6) /\
      emit_void MSTORE [buf.buf_operand; fo] s6 = (u', sb) /\
      vv = LocatedValue ann (base_ptr buf)
Proof
  rpt gen_tac >>
  `~names_builtin (Concat n) args` by
    (`!bt args. names_builtin bt args ==> !n. bt <> Concat n` suffices_by
       metis_tac[] >>
     ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `!f dp infos op.
     compile_concat
       (expr_child_callback (cenv_defaults_size cenv + list_size expr_size args) f)
       cenv args dp infos op = compile_concat f cenv args dp infos op` by
    (rpt gen_tac >> irule compile_concat_child_callback >>
     simp[EVERY_MEM, expr_list_member_bound]) >>
  simp[compile_expr_builtin_dispatch] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  qpat_x_assum `UNCURRY _ _ = _` mp_tac >>
  Cases_on `emit_void MSTORE [buf_op_alloc.buf_operand; final_offset] st4` >>
  rename1 `(uu, rr)` >> Cases_on `uu` >> simp[]
QED

Theorem concat_prefix_code:
  !bsz sa buf s1 d s2 ob s3 u s4.
    context$compile_alloc_buffer bsz sa = (buf,s1) /\
    emit_op ADD [buf.buf_operand; Lit 32w] s1 = (d,s2) /\
    context$compile_alloc_buffer 64 s2 = (ob,s3) /\
    emit_void MSTORE [ob.buf_operand; Lit 0w] s3 = (u,s4) ==>
    buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var)) /\
    d = Var (STRING #"%" (toString (sa.cs_next_var + 1))) /\
    ob.buf_operand = Var (STRING #"%" (toString (sa.cs_next_var + 2))) /\
    s1.cs_next_id = sa.cs_next_id + 1 /\ s1.cs_next_var = sa.cs_next_var + 1 /\
    s2.cs_next_id = sa.cs_next_id + 2 /\ s2.cs_next_var = sa.cs_next_var + 2 /\
    s3.cs_next_id = sa.cs_next_id + 3 /\ s3.cs_next_var = sa.cs_next_var + 3 /\
    s4.cs_next_id = sa.cs_next_id + 4 /\ s4.cs_next_var = sa.cs_next_var + 3 /\
    s4.cs_current_bb = sa.cs_current_bb /\ s4.cs_blocks = sa.cs_blocks /\
    emitted_insts sa s1 =
      [mk_inst sa.cs_next_id ALLOCA [Lit (n2w bsz)]
         [STRING #"%" (toString sa.cs_next_var)]] /\
    emitted_insts s1 s2 =
      [mk_inst (sa.cs_next_id + 1) ADD
         [Var (STRING #"%" (toString sa.cs_next_var)); Lit 32w]
         [STRING #"%" (toString (sa.cs_next_var + 1))]] /\
    emitted_insts s2 s3 =
      [mk_inst (sa.cs_next_id + 2) ALLOCA [Lit 64w]
         [STRING #"%" (toString (sa.cs_next_var + 2))]] /\
    emitted_insts s3 s4 =
      [mk_inst (sa.cs_next_id + 3) MSTORE
         [Var (STRING #"%" (toString (sa.cs_next_var + 2))); Lit 0w] []] /\
    emitted_insts sa s4 =
      emitted_insts sa s1 ++ (emitted_insts s1 s2 ++
        (emitted_insts s2 s3 ++ emitted_insts s3 s4)) /\
    s4.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa s4
Proof
  simp[contextTheory.compile_alloc_buffer_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem concat_suffix_code:
  !ov bv sa fo sm u sb.
    emit_op MLOAD [Var ov] sa = (fo, sm) /\
    emit_void MSTORE [Var bv; fo] sm = (u, sb) ==>
    fo = Var (STRING #"%" (toString sa.cs_next_var)) /\
    sb.cs_current_bb = sa.cs_current_bb /\ sb.cs_blocks = sa.cs_blocks /\
    sb.cs_next_var = sa.cs_next_var + 1 /\ sb.cs_next_id = sa.cs_next_id + 2 /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id MLOAD [Var ov] [STRING #"%" (toString sa.cs_next_var)];
       mk_inst (sa.cs_next_id + 1) MSTORE
         [Var bv; Var (STRING #"%" (toString sa.cs_next_var))] []] /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb
Proof
  simp[comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

(* ===== Straight-line runs ===== *)

Theorem concat_code_mem:
  !func sa sb i.
    fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    MEM i (emitted_insts sa sb) ==>
    MEM i (fn_insts func)
Proof
  rpt strip_tac >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX sb.cs_current_insts bb.bb_instructions` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  irule lookup_block_fn_insts >>
  qexistsl_tac [`bb`, `sa.cs_current_bb`] >> simp[] >>
  gvs[IS_PREFIX_APPEND]
QED

Theorem concat_straight_gas_path:
  !ctx func sa sb s t.
    fn_has_code sa sb func /\ ~s.vs_halted /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = [] /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    gas_path ctx func s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `fn_has_code _ _ _` mp_tac >>
     simp[fn_has_code_def, IS_PREFIX_APPEND] >> rpt strip_tac >>
     gvs[] >> simp[DROP_APPEND]) >>
  rpt conj_tac
  >- (drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
      disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
      impl_tac >- simp[] >> simp[])
  >- (irule (SRULE [] (Q.ISPEC `\s:venom_state. s.vs_current_bb`
       run_inst_seq_preserves_field)) >>
      qexists_tac `emitted_insts sa sb` >> simp[] >> rpt strip_tac >>
      fs[EVERY_MEM] >>
      metis_tac[venomInstProofsTheory.step_preserves_control_flow,
                venomExecSemanticsTheory.step_inst_non_invoke]) >>
  drule abi_decoder_sequence_halted >> simp[]
QED

Theorem concat_local_region_vars[local]:
  !cenv sa sc s t n b sz.
    local_ptrs_reserved cenv sa /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
    (local_region cenv sc t n b sz <=> local_region cenv sc s n b sz)
Proof
  rw[local_region_def] >> eq_tac >> strip_tac >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem concat_state_rws[local,simp]:
  (lookup_var x (mstore a w s) = lookup_var x s) /\
  ((mstore a w s).vs_allocas = s.vs_allocas) /\
  ((update_var y w s).vs_memory = s.vs_memory) /\
  ((update_var y w s).vs_allocas = s.vs_allocas) /\
  (local_region cenv sc (mstore a w s) n b z <=> local_region cenv sc s n b z)
Proof
  simp[mstore_def, update_var_def, lookup_var_def, local_region_def]
QED

Theorem concat_mstore_update_var_mem[local]:
  (mstore a w (update_var y v s)).vs_memory = (mstore a w s).vs_memory
Proof
  simp[mstore_def, update_var_def]
QED

Theorem concat_inst_idx_rws[local,simp]:
  (lookup_var x (s with vs_inst_idx := k) = lookup_var x s) /\
  (mload a (s with vs_inst_idx := k) = mload a s) /\
  (local_region cenv sc (s with vs_inst_idx := k) n b z <=>
   local_region cenv sc s n b z)
Proof
  simp[lookup_var_def, mload_def, local_region_def]
QED

(* The prefix: the result buffer, its data pointer, the offset word, and
   the offset zeroed. *)
Theorem concat_prefix_run:
  !ctx func cenv cx es bsz sa buf s1 d s2 ob s3 u s4 s0.
    context$compile_alloc_buffer bsz sa = (buf,s1) /\
    emit_op ADD [buf.buf_operand; Lit 32w] s1 = (d,s2) /\
    context$compile_alloc_buffer 64 s2 = (ob,s3) /\
    emit_void MSTORE [ob.buf_operand; Lit 0w] s3 = (u,s4) /\
    fn_has_code sa s4 func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ bsz < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t B ow binst oinst.
      gas_path ctx func s0 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es t /\ ~t.vs_halted /\
      t.vs_current_bb = s4.cs_current_bb /\
      t.vs_inst_idx = LENGTH s4.cs_current_insts /\
      lookup_var (STRING #"%" (toString sa.cs_next_var)) t = SOME (n2w B) /\
      lookup_var (STRING #"%" (toString (sa.cs_next_var + 1))) t =
        SOME (n2w (B + 32)) /\
      lookup_var (STRING #"%" (toString (sa.cs_next_var + 2))) t = SOME ow /\
      MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
      binst.inst_id = sa.cs_next_id /\ binst.inst_id < s4.cs_next_id /\
      MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
      oinst.inst_id < s4.cs_next_id /\
      FLOOKUP t.vs_allocas binst.inst_id = SOME (B, bsz) /\
      FLOOKUP t.vs_allocas oinst.inst_id = SOME (w2n ow, 64) /\
      (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
         (B + bsz <= lb \/ lb + lsz <= B) /\
         (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow)) /\
      (B + bsz <= w2n ow \/ w2n ow + 64 <= B) /\ B + bsz < dimword (:256) /\
      mload (w2n ow) t = n2w 0 /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
               FLOOKUP t.vs_allocas aid = SOME a) /\
      (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
         (B + bsz <= b \/ b + len <= B) /\
         (w2n ow + 64 <= b \/ b + len <= w2n ow)) /\
      (!p n. p + n <= w2n ow \/ w2n ow + 64 <= p ==>
         mem_bytes_at p n t.vs_memory = mem_bytes_at p n s0.vs_memory)
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qspecl_then [`bsz`, `sa`, `buf`, `s1`, `d`, `s2`, `ob`, `s3`, `u`, `s4`]
    mp_tac concat_prefix_code >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!i. MEM i (emitted_insts sa s4) ==> MEM i (fn_insts func)` by
    (rpt strip_tac >> irule concat_code_mem >>
     qexistsl_tac [`sa`, `s4`] >> simp[]) >>
  (* the result buffer *)
  qspecl_then [`func`, `cenv`, `cx`, `es`, `sa`, `s1`, `buf`, `bsz`, `s0`]
    mp_tac alloc_buffer_frame_run >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `FLOOKUP t1.vs_allocas sa.cs_next_id = SOME (w2n w1, bsz)` >>
  (* the data pointer *)
  qabbrev_tac `t2 = update_var (STRING #"%" (toString (sa.cs_next_var + 1)))
                      (w1 + 32w) t1` >>
  `step_inst_base (mk_inst (sa.cs_next_id + 1) ADD
     [Var (STRING #"%" (toString sa.cs_next_var)); Lit 32w]
     [STRING #"%" (toString (sa.cs_next_var + 1))]) t1 = OK t2` by
    (qunabbrev_tac `t2` >> irule step_ADD >> gvs[eval_operand_def]) >>
  `run_inst_seq (emitted_insts s1 s2) t1 = OK t2` by
    simp[run_inst_seq_def] >>
  `!x. not_fresh_at sa x ==> lookup_var x t2 = lookup_var x t1` by
    (rw[Abbr `t2`, lookup_var_update_var] >> fs[not_fresh_at_def]) >>
  `stmt_state_rel ctx func cenv cx es t2` by
    (qunabbrev_tac `t2` >> irule stmt_state_rel_update_var >> simp[] >>
     irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `t2.vs_allocas = t1.vs_allocas /\ t2.vs_memory = t1.vs_memory` by
    simp[Abbr `t2`, update_var_def] >>
  (* the offset word *)
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  qspecl_then [`func`, `cenv`, `cx`, `es`, `s2`, `s3`, `ob`, `64`, `t2`]
    mp_tac alloc_buffer_frame_run >>
  impl_tac >- (simp[dimword_def] >> first_assum irule >> simp[]) >>
  strip_tac >>
  rename1 `FLOOKUP t3.vs_allocas s2.cs_next_id = SOME (w2n w2, 64)` >>
  `eval_operand (Var (STRING #"%" (toString (sa.cs_next_var + 2)))) t3 = SOME w2` by
    gvs[] >>
  `step_inst_base (mk_inst (sa.cs_next_id + 3) MSTORE
     [Var (STRING #"%" (toString (sa.cs_next_var + 2))); Lit 0w] []) t3 =
   OK (mstore (w2n w2) 0w t3)` by
    (irule step_MSTORE >> simp[eval_operand_def]) >>
  `run_inst_seq (emitted_insts s3 s4) t3 = OK (mstore (w2n w2) 0w t3)` by
    simp[run_inst_seq_def] >>
  qabbrev_tac `t4 = mstore (w2n w2) 0w t3` >>
  `run_inst_seq (emitted_insts sa s4) s0 = OK t4` by
    (qpat_x_assum `emitted_insts sa s4 = _ ++ _` SUBST1_TAC >>
     qpat_assum `run_inst_seq (emitted_insts sa s1) s0 = OK t1`
       (fn th => REWRITE_TAC [MATCH_MP run_inst_seq_append th]) >>
     qpat_assum `run_inst_seq (emitted_insts s1 s2) t1 = OK t2`
       (fn th => REWRITE_TAC [MATCH_MP run_inst_seq_append th]) >>
     qpat_assum `run_inst_seq (emitted_insts s2 s3) t2 = OK t3`
       (fn th => REWRITE_TAC [MATCH_MP run_inst_seq_append th]) >>
     first_assum ACCEPT_TAC) >>
  `t4.vs_allocas = t3.vs_allocas /\ t4.vs_vars = t3.vs_vars` by
    simp[Abbr `t4`, mstore_def] >>
  (* facts of the alloca instructions *)
  qabbrev_tac `binst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w bsz)]
                         [STRING #"%" (toString sa.cs_next_var)]` >>
  qabbrev_tac `oinst = mk_inst (sa.cs_next_id + 2) ALLOCA [Lit 64w]
                         [STRING #"%" (toString (sa.cs_next_var + 2))]` >>
  `MEM binst (fn_insts func) /\ MEM oinst (fn_insts func)` by
    (conj_tac >> first_x_assum irule >> simp[Abbr `binst`, Abbr `oinst`]) >>
  `binst.inst_opcode = ALLOCA /\ binst.inst_id = sa.cs_next_id /\
   oinst.inst_opcode = ALLOCA /\ oinst.inst_id = sa.cs_next_id + 2` by
    simp[Abbr `binst`, Abbr `oinst`, mk_inst_def] >>
  `stmt_state_rel ctx func cenv cx es t4` by
    (qunabbrev_tac `t4` >>
     qspecl_then [`func`, `cenv`, `cx`, `es`, `t3`, `w2n w2`, `0w`, `oinst`,
                  `w2n w2`, `64`, `ctx`] mp_tac literal_mstore_state_rel >>
     impl_tac >- (
       qpat_assum `s2.cs_next_id = _` (fn th =>
         qpat_assum `FLOOKUP t3.vs_allocas s2.cs_next_id = _`
           (assume_tac o REWRITE_RULE [th])) >>
       fs[] >> rpt strip_tac >>
                  qpat_x_assum `!name b len. local_region cenv es.scopes t3 _ _ _ ==> _`
                    drule >>
                  simp[regions_disjoint_def]) >>
     simp[]) >>
  (* the whole prefix as a gas path *)
  qspecl_then [`ctx`, `func`, `sa`, `s4`, `s0`, `t4`] mp_tac
    concat_straight_gas_path >>
  impl_tac >- simp[mk_inst_def, is_terminator_def] >> strip_tac >>
  `!x. lookup_var x t4 = lookup_var x t3` by
    (qpat_assum `t4.vs_vars = t3.vs_vars` (fn th => simp[lookup_var_def, th])) >>
  `!x. not_fresh_at sa x ==> lookup_var x t3 = lookup_var x s0` by
    (rpt strip_tac >>
     `not_fresh_at s2 x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     metis_tac[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t4 = lookup_var x s0` by
    (rpt strip_tac >> res_tac >> asm_rewrite_tac[]) >>
  `!name lb lsz. local_region cenv es.scopes t4 name lb lsz <=>
                 local_region cenv es.scopes s0 name lb lsz` by
    (rpt gen_tac >> irule concat_local_region_vars >> qexists_tac `sa` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!name lb lsz. local_region cenv es.scopes t3 name lb lsz <=>
                 local_region cenv es.scopes s0 name lb lsz` by
    (rpt gen_tac >> irule concat_local_region_vars >> qexists_tac `sa` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!name lb lsz. local_region cenv es.scopes t1 name lb lsz <=>
                 local_region cenv es.scopes s0 name lb lsz` by
    (rpt gen_tac >> irule concat_local_region_vars >> qexists_tac `sa` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `lookup_var (STRING #"%" (toString sa.cs_next_var)) t1 = SOME w1` by
    (qpat_assum `eval_operand buf.buf_operand t1 = _` (fn th =>
       qpat_assum `buf.buf_operand = Var (STRING _ _)` (fn th2 =>
         mp_tac (REWRITE_RULE [th2, eval_operand_def] th))) >>
     rewrite_tac[]) >>
  `lookup_var (STRING #"%" (toString sa.cs_next_var)) t2 = SOME w1 /\ lookup_var (STRING #"%" (toString (sa.cs_next_var + 1))) t2 = SOME (w1 + 32w)` by
    (qpat_assum `lookup_var _ t1 = SOME w1`
       (fn th => simp[Abbr `t2`, lookup_var_update_var, th])) >>
  `not_fresh_at s2 (STRING #"%" (toString sa.cs_next_var)) /\ not_fresh_at s2 (STRING #"%" (toString (sa.cs_next_var + 1)))` by
    (qpat_assum `s2.cs_next_var = _` (fn th => simp[not_fresh_at_def, th])) >>
  `lookup_var (STRING #"%" (toString (sa.cs_next_var + 2))) t3 = SOME w2` by
    (qpat_assum `eval_operand (Var _) t3 = SOME w2`
       (fn th => ACCEPT_TAC (REWRITE_RULE [eval_operand_def] th))) >>
  `lookup_var (STRING #"%" (toString sa.cs_next_var)) t4 = SOME w1 /\ lookup_var (STRING #"%" (toString (sa.cs_next_var + 1))) t4 = SOME (w1 + 32w) /\
   lookup_var (STRING #"%" (toString (sa.cs_next_var + 2))) t4 = SOME w2` by
    (qpat_assum `!x. lookup_var x t4 = lookup_var x t3` (fn th => rewrite_tac[th]) >>
     qpat_assum `!x. not_fresh_at s2 x ==> lookup_var x t3 = _`
       (fn th => qpat_assum `not_fresh_at s2 (STRING #"%" (toString sa.cs_next_var))`
         (fn th2 => qpat_assum `not_fresh_at s2 (STRING #"%" (toString (sa.cs_next_var + 1)))`
           (fn th3 => rewrite_tac[MATCH_MP th th2, MATCH_MP th th3]))) >>
     qpat_assum `lookup_var (STRING #"%" (toString sa.cs_next_var)) t2 = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `lookup_var (STRING #"%" (toString (sa.cs_next_var + 1))) t2 = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `lookup_var _ t3 = SOME w2` (fn th => rewrite_tac[th])) >>
  `FLOOKUP t3.vs_allocas (sa.cs_next_id + 2) = SOME (w2n w2, 64)` by
    (qpat_assum `s2.cs_next_id = _` (fn th =>
       qpat_assum `FLOOKUP t3.vs_allocas s2.cs_next_id = _`
         (fn th2 => rewrite_tac[REWRITE_RULE [th] th2]))) >>
  `FLOOKUP t2.vs_allocas sa.cs_next_id = SOME (w2n w1, bsz)` by
    (qpat_assum `t2.vs_allocas = _` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `regions_disjoint (w2n w2) 64 (w2n w1) bsz` by
    (qpat_assum `!aid b len. aid < s2.cs_next_id /\ _ ==> _` irule >>
     qexists_tac `sa.cs_next_id` >> simp[]) >>
  `mload (w2n w2) t4 = 0w` by simp[Abbr `t4`, mload_mstore_same] >>
  `t3.vs_memory = s0.vs_memory` by
    (qpat_assum `t3.vs_memory = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `t2.vs_memory = _` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  qexistsl_tac [`t4 with vs_inst_idx := LENGTH s4.cs_current_insts`,
                `w2n w1`, `w2`, `binst`, `oinst`] >>
  simp[stmt_state_rel_inst_idx] >>
  rpt conj_tac
  >- simp[GSYM word_add_n2w]
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (`local_region cenv es.scopes t1 name lb lsz` by metis_tac[] >>
          res_tac >> fs[regions_disjoint_def])
      >> (`local_region cenv es.scopes t3 name lb lsz` by metis_tac[] >>
          res_tac >> fs[regions_disjoint_def]))
  >- fs[regions_disjoint_def]
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (res_tac >> fs[regions_disjoint_def])
      >> (`aid < s2.cs_next_id` by simp[] >>
          `FLOOKUP t2.vs_allocas aid = SOME (b,len)` by
            (qpat_assum `t2.vs_allocas = _` (fn th => rewrite_tac[th]) >>
             res_tac) >>
          res_tac >> fs[regions_disjoint_def])) >>
  rpt gen_tac >> strip_tac >>
  simp[Abbr `t4`] >>
  qpat_assum `t3.vs_memory = s0.vs_memory` (fn th => rewrite_tac[GSYM th]) >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Theorem concat_suffix_run:
  !ov bv sa fo sm u sb s ow bw.
    emit_op MLOAD [Var ov] sa = (fo, sm) /\
    emit_void MSTORE [Var bv; fo] sm = (u, sb) /\
    lookup_var ov s = SOME ow /\ lookup_var bv s = SOME bw /\
    not_fresh_at sa bv ==>
    run_inst_seq (emitted_insts sa sb) s =
      OK (mstore (w2n bw) (mload (w2n ow) s)
            (update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n ow) s) s))
Proof
  rpt strip_tac >>
  drule_all concat_suffix_code >> strip_tac >>
  qpat_x_assum `emitted_insts sa sb = _` SUBST1_TAC >>
  `bv <> (STRING #"%" (toString sa.cs_next_var))` by fs[not_fresh_at_def] >>
  `step_inst_base (mk_inst sa.cs_next_id MLOAD [Var ov] [(STRING #"%" (toString sa.cs_next_var))]) s =
   OK (update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n ow) s) s)` by
    (irule step_MLOAD >> simp[eval_operand_def]) >>
  qabbrev_tac `s' = update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n ow) s) s` >>
  `eval_operand (Var bv) s' = SOME bw /\
   eval_operand (Var (STRING #"%" (toString sa.cs_next_var))) s' = SOME (mload (w2n ow) s)` by
    simp[Abbr `s'`, eval_operand_def, lookup_var_update_var] >>
  `step_inst_base (mk_inst (sa.cs_next_id + 1) MSTORE [Var bv; Var (STRING #"%" (toString sa.cs_next_var))] []) s' =
   OK (mstore (w2n bw) (mload (w2n ow) s) s')` by
    (irule step_MSTORE >> conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `step_inst_base _ s = _` (fn th1 =>
    qpat_assum `step_inst_base _ s' = _` (fn th2 =>
      simp[run_inst_seq_def, th1, th2]))
QED

(* ===== Composition ===== *)

Theorem concat_values_then_outcome:
  !tops ctx func (a : evaluation_state -> value list evaluation_result) es s0 Q1.
    gas_outcome F tops (ctx,func) a (es,s0) Q1
      (\rr ee r. ?exc. rr = INR exc /\
         expr_exit (INR exc : eval_result + exception) r) ==>
    !k Q R.
      (!rr ee t. Q1 rr ee t ==> ?vs. rr = INL vs) /\
      (!vs ee t gs.
         Q1 (INL vs) ee t /\ ee.gas_obs = [] /\ ~t.vs_halted /\
         a (es with gas_obs := gs) = (INL vs, ee) ==>
         ?res ee' r.
           (!tail. k vs (ee with gas_obs := tail) =
                   (res, ee' with gas_obs := tail)) /\
           gas_marked_path F ctx func t 0 r /\
           ((?t'. r = OK t' /\ Q res (ee' with gas_obs := []) t') \/
            (exit_result r /\ R res (ee' with gas_obs := []) r))) /\
      (!ex ee r. expr_exit (INR ex : eval_result + exception) r ==>
                 R (INR ex) ee r) ==>
      gas_outcome F tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  simp[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      simp[gas_summary_at_def] >> strip_tac
      >- (qpat_x_assum `_ = OK _` SUBST_ALL_TAC >>
          rename1 `gas_marked_exec F (ctx,func) a (es,s0) marks rr mid (OK t)` >>
          `?vs. rr = INL vs` by (first_x_assum drule >> simp[]) >>
          pop_assum SUBST_ALL_TAC >>
          `a (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
             (INL vs, mid with gas_obs := [])` by
            (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o CONJUNCT1 o REWRITE_RULE [gas_marked_exec_def]) >>
             disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
          `~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          first_x_assum (qspecl_then [`vs`, `mid with gas_obs := []`, `t`,
            `gas_explicit marks s0.vs_gas_readings`] mp_tac) >>
          impl_tac >- simp[] >> strip_tac >>
          `gas_marked_exec F (ctx,func) (k vs) (mid with gas_obs := [], t)
             [] res ee' r` by fs[gas_marked_exec_def] >>
          `gas_marked_exec F (ctx,func) (bind a k) (es,s0)
             (marks ++ []) res ee' r` by
            (irule gas_marked_exec_bind_normal >> qexistsl_tac [`mid`, `t`, `vs`] >>
             simp[]) >>
          qexistsl_tac [`res`, `ee'`, `r`] >> fs[]) >>
      rename1 `gas_marked_exec F (ctx,func) a (es,s0) marks rr mid r` >>
      gvs[] >> qexistsl_tac [`INR exc`, `mid`, `r`] >> simp[] >>
      irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  qexists_tac `marks` >> disj2_tac >>
  `ignore_bind (bind a k) (return ()) =
   bind a (\v. ignore_bind (k v) (return ()))` by
    (simp[ignore_bind_def, FUN_EQ_THM, bind_def] >> gen_tac >>
     Cases_on `a x` >> Cases_on `q` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  metis_tac[gas_exempt_cert_error_values]
QED

fun on_concl pat tac (g as (_, c)) =
  if can (find_term (can (match_term pat))) c then tac g else NO_TAC g;

Theorem concat_result_vv_sim:
  !nocalls ctx func cenv cx env ty ann n args es.
    exprs_case nocalls ctx func cenv cx args /\
    expr_body_pre cenv cx env (Builtin ann (Concat n) args) es /\
    (nocalls ==> int_calls_expr (Builtin ann (Concat n) args) = []) ==>
    expr_vv_sim ctx func cenv cx ty (Builtin ann (Concat n) args) es
Proof
  rpt gen_tac >> strip_tac >>
  `!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
          expr_body_pre cenv cx env e st /\ (nocalls ==> int_calls_expr e = [])` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (qspecl_then [`cenv`, `cx`, `env`, `ann`, `Concat n`, `args`, `e`, `es`, `st`]
           mp_tac expr_body_pre_builtin_arg >> fs[])
     >> metis_tac[int_calls_builtin_arg]) >>
  `expr_sim_inv cenv cx env es /\ well_typed_expr env (Builtin ann (Concat n) args) /\
   alloc_limits_expr cenv (Builtin ann (Concat n) args)` by fs[expr_body_pre_def] >>
  `env.type_defs = get_tenv cx` by
    (qpat_x_assum `expr_sim_inv cenv cx env es` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[expr_sim_inv_def, env_consistent_def, env_context_consistent_def]) >>
  `2 <= LENGTH args /\ SUM (MAP bytelike_type_bound (MAP expr_type args)) <= n /\
   well_formed_type env.type_defs ann` by
    (qpat_x_assum `well_typed_expr _ _` mp_tac >>
     simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
     rpt strip_tac >> fs[]) >>
  Q.SUBGOAL_THEN
    `(ann = BaseT (BytesT (Dynamic n)) /\
      EVERY (\t. ?bd. t = BaseT (BytesT bd)) (MAP expr_type args)) \/
     (ann = BaseT (StringT n) /\
      EVERY (\t. ?m. t = BaseT (StringT m)) (MAP expr_type args))` assume_tac
  >- (qpat_x_assum `well_typed_expr _ _` mp_tac >>
      simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
      rpt strip_tac >> fs[]) >>
  `?tvr. evaluate_type (get_tenv cx) ann = SOME tvr` by
    (qpat_x_assum `well_formed_type _ _` mp_tac >>
     qpat_assum `env.type_defs = _`
       (fn th => simp[th, well_formed_type_def, optionTheory.IS_SOME_EXISTS])) >>
  `EVERY (\e. is_bytestring_type (expr_type e) \/
              ?m. expr_type e = BaseT (BytesT (Fixed m))) args` by
    (qpat_x_assum `(_ /\ _) \/ (_ /\ _)` strip_assume_tac >>
     fs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >> res_tac >>
     fs[is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_bytestring_type_def]) >>
  `concat_alloc_size (MAP expr_type args) < 2 ** 64` by
    (qpat_x_assum `alloc_limits_expr _ _` mp_tac >> simp[alloc_limits_expr_def]) >>
  simp[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  drule concat_compile_shape >> strip_tac >>
  qabbrev_tac `bsz = concat_alloc_size (MAP expr_type args)` >>
  `bsz < dimword (:256)` by
    (irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists_tac `2 ** 64` >>
     simp[dimword_def]) >>
  `32 + SUM (MAP concat_payload_capacity (MAP expr_type args)) <= bsz /\
   32 + concat_data_bound 0 (MAP expr_type args) <= bsz` by
    simp[Abbr `bsz`, concat_alloc_size_bounds] >>
  qspecl_then [`bsz`, `sa`, `buf`, `s1`, `d`, `s2`, `ob`, `s3`, `u`, `s4`]
    mp_tac concat_prefix_code >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `cs_extends sa s4` by
    (irule cs_extends_same_block >>
     qpat_assum `s4.cs_current_insts = _` (fn th => simp[th])) >>
  `ci_mono s4 s5` by
    (qpat_x_assum `compile_concat _ _ _ _ _ _ s4 = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     metis_tac[ci_mono_compile_concat_cfn, cj 1 compile_expr_ci_mono,
               pairTheory.SND]) >>
  `cs_extends s4 s5 /\ s4.cs_next_var <= s5.cs_next_var /\
   s4.cs_next_id <= s5.cs_next_id` by fs[ci_mono_def] >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `bsz`, `sa`, `buf`, `s1`,
               `d`, `s2`, `ob`, `s3`, `u`, `s4`, `s0`] mp_tac concat_prefix_run >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_x_assum `buf.buf_operand = _`
        (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
      qpat_x_assum `ob.buf_operand = _`
        (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
      qspecl_then [`(STRING #"%" (toString (sa.cs_next_var + 2)))`, `(STRING #"%" (toString sa.cs_next_var))`, `s5`, `fo`, `s6`, `u'`, `sb`] mp_tac
        concat_suffix_code >>
      impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      `cs_extends s5 sb` by
        (irule cs_extends_same_block >>
         qpat_assum `sb.cs_current_insts = _` (fn th => simp[th])) >>
      `cs_extends s4 sb` by metis_tac[cs_extends_trans] >>
      `fn_has_code sa s4 func /\ fn_has_code s4 sb func` by
        (irule fn_has_code_split >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`t`, `B`, `ow`, `binst`, `oinst`]
    (MAP_EVERY assume_tac o CONJUNCTS)) >>
  (* name the operands *)
  qpat_x_assum `buf.buf_operand = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  qpat_x_assum `ob.buf_operand = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  qpat_x_assum `d = _` SUBST_ALL_TAC >>
  qspecl_then [`(STRING #"%" (toString (sa.cs_next_var + 2)))`, `(STRING #"%" (toString sa.cs_next_var))`, `s5`, `fo`, `s6`, `u'`, `sb`] mp_tac
    concat_suffix_code >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `cs_extends s5 sb` by
    (irule cs_extends_same_block >>
     qpat_assum `sb.cs_current_insts = _` (fn th => simp[th])) >>
  `cs_extends s4 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s4 func /\ fn_has_code s4 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code s4 s5 func /\ fn_has_code s5 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv s4` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `not_fresh_at s4 (STRING #"%" (toString (sa.cs_next_var + 1))) /\ not_fresh_at s4 (STRING #"%" (toString (sa.cs_next_var + 2)))` by
    (qpat_assum `s4.cs_next_var = _` (fn th => simp[not_fresh_at_def, th])) >>
  `oinst.inst_id < s4.cs_next_id` by simp[] >>
  qspecl_then [`args`, `0`, `0`, `ctx`, `func`, `cenv`, `cx`, `env`, `nocalls`,
               `es`, `s4`, `s5`, `t`, `(STRING #"%" (toString (sa.cs_next_var + 1)))`, `(STRING #"%" (toString (sa.cs_next_var + 2)))`, `ow`, `binst`, `B`, `bsz`,
               `oinst`] mp_tac concat_args_sim >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[] >> NO_TAC) >>
  strip_tac >>
  qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  irule gas_outcome_zero_prefix >> qexists_tac `t` >>
  conj_tac >- (simp[gas_marked_path_def] >> first_assum ACCEPT_TAC) >>
  qspecl_then [`cx`, `ann`, `n`, `args`] mp_tac eval_expr_concat_bind >>
  impl_tac >- first_assum ACCEPT_TAC >> disch_then SUBST1_TAC >>
  qpat_x_assum `gas_outcome _ _ _ (eval_exprs _ _) _ _ _`
    (fn th => irule (INST_TYPE [alpha |-> ``:eval_result``]
                       (MATCH_MP concat_values_then_outcome th))) >>
  conj_tac >- simp[] >>
  reverse conj_tac >- simp[PULL_EXISTS] >>
  qx_genl_tac [`vs`, `ee`, `t5`, `gs`] >> simp[] >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >> rpt (pop_assum kall_tac) >>
     strip_tac >> drule eval_exprs_preserves_scopes_dom >> simp[]) >>
  qspecl_then [`ann`, `n`, `MAP expr_type args`, `vs`, `get_tenv cx`, `tvr`]
    mp_tac concat_typed_result >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      simp[LIST_REL_MAP1, combinTheory.o_DEF] >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `v` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qabbrev_tac `bytes = FLAT (MAP concat_payload_bytes vs)` >>
  `mem_bytes_at (B + 32) 0 t.vs_memory = []` by simp[mem_bytes_at_def] >>
  `w2n (n2w B : bytes32) = B` by
    (`B < dimword (:256)` by decide_tac >> simp[]) >>
  `not_fresh_at s4 (STRING #"%" (toString sa.cs_next_var))` by
    (qpat_assum `s4.cs_next_var = _` (fn th => simp[not_fresh_at_def, th])) >>
  `not_fresh_at s5 (STRING #"%" (toString sa.cs_next_var))` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `s4` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `lookup_var (STRING #"%" (toString sa.cs_next_var)) t5 = SOME (n2w B) /\ lookup_var (STRING #"%" (toString (sa.cs_next_var + 2))) t5 = SOME ow` by
    (qpat_assum `!z w. not_fresh_at s4 z /\ _ ==> _` (fn th =>
       conj_tac >> irule th >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  qspecl_then [`(STRING #"%" (toString (sa.cs_next_var + 2)))`, `(STRING #"%" (toString sa.cs_next_var))`, `s5`, `fo`, `s6`, `u'`, `sb`, `t5`, `ow`, `n2w B`]
    mp_tac concat_suffix_run >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `w2n _ = B` (fn th => disch_then (assume_tac o REWRITE_RULE [th])) >>
  qabbrev_tac `mv = mload (w2n ow) t5` >>
  qabbrev_tac `t6 = mstore B mv (update_var (STRING #"%" (toString s5.cs_next_var)) mv t5)` >>
  qspecl_then [`ctx`, `func`, `s5`, `sb`, `t5`, `t6`] mp_tac
    concat_straight_gas_path >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_assum `emitted_insts s5 sb = _`
        (fn th => simp[th, mk_inst_def, is_terminator_def])) >>
  strip_tac >>
  `ee with gas_obs := [] = ee` by
    (qpat_assum `ee.gas_obs = []`
       (fn th => simp[th, evaluation_state_component_equality])) >>
  qexistsl_tac [`INL (Value v)`, `ee`,
                `OK (t6 with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  qpat_assum `evaluate_concat _ _ = _` (fn th1 =>
    qpat_assum `ee with gas_obs := [] = ee` (fn th2 =>
      simp[th1, th2, gas_marked_path_def])) >>
  (* numeric facts *)
  `sa.cs_next_var <= s4.cs_next_var /\ sa.cs_next_var <= s5.cs_next_var /\
   sa.cs_next_id < sb.cs_next_id /\ sa.cs_next_id <= s4.cs_next_id` by
    (qpat_x_assum `s4.cs_next_var = _` mp_tac >>
     qpat_x_assum `s4.cs_next_id = _` mp_tac >>
     qpat_x_assum `s4.cs_next_var <= _` mp_tac >>
     qpat_x_assum `s4.cs_next_id <= _` mp_tac >>
     qpat_x_assum `sb.cs_next_id = _` mp_tac >>
     rpt (pop_assum kall_tac) >> decide_tac) >>
  (* variable frames *)
  `!x. not_fresh_at sa x ==> lookup_var x t6 = lookup_var x t5` by
    (rpt strip_tac >>
     `not_fresh_at s5 x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     `x <> (STRING #"%" (toString s5.cs_next_var))` by
       (qpat_x_assum `not_fresh_at s5 x` mp_tac >> simp[not_fresh_at_def] >>
        disch_then (qspec_then `s5.cs_next_var` mp_tac) >> simp[]) >>
     simp[Abbr `t6`, lookup_var_update_var]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x t = SOME w ==> lookup_var x t5 = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at s4 x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `!z w. not_fresh_at s4 z /\ _ ==> _` irule >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t6 = SOME w` by
    (qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x t6 = _` mp_tac >>
     qpat_x_assum `!x w. not_fresh_at sa x /\ lookup_var x t = SOME w ==> _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x t = SOME w ==> lookup_var x t6 = SOME w` by
    (qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x t6 = _` mp_tac >>
     qpat_x_assum `!x w. not_fresh_at sa x /\ lookup_var x t = SOME w ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  (* local regions at the final state are those at the prefix state *)
  `local_ptrs_rel func cenv es.scopes t` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
  `!nm lb lsz. local_region cenv ee.scopes t6 nm lb lsz ==>
               local_region cenv es.scopes t nm lb lsz` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac >- (qexists_tac `func` >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`sa`, `ee.scopes`, `t6`] >> rpt conj_tac >>
     first_assum ACCEPT_TAC) >>
  `!nm lb lsz. local_region cenv ee.scopes t6 nm lb lsz ==>
               B + bsz <= lb \/ lb + lsz <= B` by
    (rpt strip_tac >>
     qpat_x_assum `!nm lb lsz. local_region cenv ee.scopes t6 _ _ _ ==> _` drule >>
     strip_tac >>
     qpat_x_assum `!name lb lsz. local_region cenv es.scopes t _ _ _ ==> _` drule >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `(STRING #"%" (toString sa.cs_next_var)) <> (STRING #"%" (toString s5.cs_next_var))` by
    (qpat_x_assum `not_fresh_at s5 (STRING #"%" (toString sa.cs_next_var))` mp_tac >> simp[not_fresh_at_def] >>
     disch_then (qspec_then `s5.cs_next_var` mp_tac) >> simp[]) >>
  `lookup_var (STRING #"%" (toString sa.cs_next_var)) t6 = SOME (n2w B)` by
    (qpat_x_assum `lookup_var (STRING #"%" (toString sa.cs_next_var)) t5 = _` mp_tac >>
     qpat_x_assum `(STRING #"%" (toString sa.cs_next_var)) <> (STRING #"%" (toString s5.cs_next_var))` mp_tac >>
     simp[Abbr `t6`, lookup_var_update_var]) >>
  `FLOOKUP t5.vs_allocas sa.cs_next_id = SOME (B,bsz)` by
    (qpat_x_assum `!aid a. FLOOKUP t.vs_allocas aid = SOME a ==> _` irule >>
     qpat_x_assum `binst.inst_id = _` (fn th =>
       qpat_x_assum `FLOOKUP t.vs_allocas binst.inst_id = _`
         (ACCEPT_TAC o REWRITE_RULE [th]))) >>
  `FLOOKUP t6.vs_allocas sa.cs_next_id = SOME (B,bsz)` by
    (qpat_x_assum `FLOOKUP t5.vs_allocas sa.cs_next_id = _` mp_tac >>
     simp[Abbr `t6`]) >>
  `!nm lb lsz. local_region cenv es.scopes t nm lb lsz <=>
               local_region cenv es.scopes s0 nm lb lsz` by
    (rpt gen_tac >> irule concat_local_region_vars >> qexists_tac `sa` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `32 <= bsz` by
    (qpat_x_assum `32 + SUM _ <= bsz` mp_tac >> rpt (pop_assum kall_tac) >>
     decide_tac) >>
  `!p q. p + q <= B \/ B + 32 <= p ==>
         mem_bytes_at p q t6.vs_memory = mem_bytes_at p q t5.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `Abbrev (t6 = _)`
       (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     rewrite_tac[concat_mstore_update_var_mem] >>
     irule mstore_mem_bytes_at_disjoint >> first_assum ACCEPT_TAC) >>
  irule (REWRITE_RULE [vyperASTTheory.expr_type_def]
    (Q.INST [`e` |-> `Builtin ann (Concat n) args`]
       vv_post_allocated_memory_intro)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (simp[base_ptr_def] >> NO_TAC)
  >~ [`val_in_memory`]
  >- (qexistsl_tac [`sa.cs_next_id`, `B`, `bsz`, `tvr`, `n2w B`] >>
      qpat_assum `w2n _ = B` (fn th => rewrite_tac[th]) >>
      rpt conj_tac >> FIRST [
      on_concl ``val_footprint _ _`` (qpat_x_assum `val_footprint _ _ = _` (fn th => rewrite_tac[th]) >>
          qpat_x_assum `LENGTH bytes <= _` mp_tac >>
          qpat_x_assum `32 + SUM _ <= bsz` mp_tac >>
          rpt (pop_assum kall_tac) >> decide_tac),
      on_concl ``eval_operand _ _`` (qpat_assum `buf.buf_operand = _`
            (fn th => simp[th, base_ptr_def, eval_operand_def]) >>
          first_assum ACCEPT_TAC),
      on_concl ``val_in_memory _ _ _ _`` (qpat_x_assum `!off mem. val_in_memory _ _ _ _ <=> _`
            (fn th => rewrite_tac[th]) >>
          conj_tac
          >- (qpat_assum `Abbrev (t6 = _)`
                (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
              rewrite_tac[mem_word_at_eq_mload, mload_mstore_same] >>
              qpat_x_assum `mv = n2w _` ACCEPT_TAC) >>
          `mem_bytes_at (B + 32) (LENGTH bytes) t6.vs_memory =
           mem_bytes_at (B + 32) (LENGTH bytes) t5.vs_memory` by
            (qpat_assum `!p q. _ ==> mem_bytes_at p q t6.vs_memory = _` irule >>
             simp[]) >>
          pop_assum (fn th => rewrite_tac[th]) >>
          qpat_x_assum `mem_bytes_at _ (LENGTH bytes) t5.vs_memory = _`
            (fn th1 => qpat_x_assum `mem_bytes_at _ 0 t.vs_memory = []`
              (fn th2 => rewrite_tac[th1, th2, APPEND]))),
      first_assum ACCEPT_TAC,
      simp[] >> NO_TAC])
  >~ [`wb_frame`]
  >- (rewrite_tac[wb_frame_def] >> rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- (rpt strip_tac >>
          qpat_assum `Abbrev (t6 = _)`
            (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
          simp[] >>
          qpat_x_assum `!aid a. FLOOKUP t.vs_allocas aid = SOME a ==> FLOOKUP t5.vs_allocas aid = SOME a` irule >>
          qpat_x_assum `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> _` irule >>
          first_assum ACCEPT_TAC)
      >- (qx_genl_tac [`aid0`, `off`, `osz`] >> strip_tac >>
          qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _`
            (qspecl_then [`aid0`, `off`, `osz`] mp_tac) >>
          impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
          disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
          `mem_bytes_at off osz t.vs_memory = mem_bytes_at off osz s0.vs_memory` by
            (qpat_x_assum `!p n. _ \/ _ ==> mem_bytes_at p n t.vs_memory = _` irule >>
             qpat_x_assum `w2n ow + 64 <= off \/ _` mp_tac >>
             rpt (pop_assum kall_tac) >> decide_tac) >>
          `FLOOKUP t.vs_allocas aid0 = SOME (off,osz)` by
            (qpat_x_assum `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> _` irule >>
             first_assum ACCEPT_TAC) >>
          `mem_bytes_at off osz t5.vs_memory = mem_bytes_at off osz t.vs_memory` by
            (qpat_x_assum `!aid p n. FLOOKUP t.vs_allocas aid = SOME (p,n) /\ _ ==> _`
               (qspecl_then [`aid0`, `off`, `osz`] mp_tac) >>
             impl_tac
             >- (rpt conj_tac
                 >- first_assum ACCEPT_TAC
                 >- (qpat_x_assum `aid0 < sa.cs_next_id` mp_tac >>
                     qpat_x_assum `sa.cs_next_id <= s4.cs_next_id` mp_tac >>
                     rpt (pop_assum kall_tac) >> decide_tac)
                 >- (qpat_x_assum `B + bsz <= off \/ _` mp_tac >>
                     rpt (pop_assum kall_tac) >> decide_tac)
                 >- (qpat_x_assum `w2n ow + 64 <= off \/ _` mp_tac >>
                     rpt (pop_assum kall_tac) >> decide_tac) >>
                 rpt strip_tac >>
                 `local_region cenv es.scopes s0 name lo sz` by
                   (qpat_x_assum `!nm lb lsz. local_region cenv es.scopes t _ _ _ <=> _`
                      (fn th => rewrite_tac[GSYM th]) >>
                    first_assum ACCEPT_TAC) >>
                 qpat_x_assum `!n b sz'. local_region cenv es.scopes s0 _ _ _ ==> _` drule >>
                 rpt (pop_assum kall_tac) >> decide_tac) >>
             disch_then ACCEPT_TAC) >>
          `mem_bytes_at off osz t6.vs_memory = mem_bytes_at off osz t5.vs_memory` by
            (qpat_assum `!p q. _ ==> mem_bytes_at p q t6.vs_memory = _` irule >>
             qpat_x_assum `B + bsz <= off \/ _` mp_tac >>
             qpat_x_assum `32 <= bsz` mp_tac >>
             rpt (pop_assum kall_tac) >> decide_tac) >>
          qpat_x_assum `mem_bytes_at off osz t6.vs_memory = _` (fn th1 =>
            qpat_x_assum `mem_bytes_at off osz t5.vs_memory = _` (fn th2 =>
              qpat_x_assum `mem_bytes_at off osz t.vs_memory = _` (fn th3 =>
                rewrite_tac[th1, th2, th3])))) >>
      (* locals kept *)
      `locals_kept cenv es s0 t` by
        (irule locals_kept_regions >> qx_genl_tac [`nm`, `lb`, `lsz`] >>
         strip_tac >>
         `local_region cenv es.scopes t nm lb lsz` by
           (qpat_x_assum `!nm lb lsz. local_region cenv es.scopes t _ _ _ <=> _`
              (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
         qpat_x_assum `!name lb lsz. local_region cenv es.scopes t _ _ _ ==> _ /\ _`
           drule >>
         disch_then (assume_tac o CONJUNCT2) >>
         qpat_x_assum `!p n. _ \/ _ ==> mem_bytes_at p n t.vs_memory = _` irule >>
         pop_assum mp_tac >> rpt (pop_assum kall_tac) >> decide_tac) >>
      `locals_kept cenv es s0 t5` by
        (match_mp_tac (Q.SPECL [`cenv`, `es`, `es`, `sa`, `s0`, `t`, `t5`]
                         locals_kept_trans) >>
         rpt conj_tac
         >- first_assum ACCEPT_TAC
         >- REFL_TAC
         >- (rpt strip_tac >>
             qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x t = _` drule >>
             disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
         first_assum ACCEPT_TAC) >>
      match_mp_tac (Q.SPECL [`cenv`, `es`, `s0`, `t5`, `t6`]
                      locals_kept_regions_tail) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qx_genl_tac [`nm`, `lb`, `lsz`] >> strip_tac >>
      `local_region cenv es.scopes t nm lb lsz` by
        (qpat_x_assum `!nm lb lsz. local_region cenv es.scopes t _ _ _ <=> _`
           (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `!name lb lsz. local_region cenv es.scopes t _ _ _ ==> _ /\ _`
        drule >>
      disch_then (assume_tac o CONJUNCT1) >>
      qpat_assum `!p q. _ ==> mem_bytes_at p q t6.vs_memory = _` irule >>
      pop_assum mp_tac >> qpat_x_assum `32 <= bsz` mp_tac >>
      rpt (pop_assum kall_tac) >> decide_tac)
  >~ [`stmt_state_rel _ _ _ _ ee t6`]
  >- (qpat_assum `Abbrev (t6 = _)`
        (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      match_mp_tac (Q.SPECL [`func`, `cenv`, `cx`, `ee`,
        `update_var (STRING #"%" (toString s5.cs_next_var)) mv t5`,
        `B`, `mv`, `binst`, `B`, `bsz`, `ctx`] literal_mstore_state_rel) >>
      rpt conj_tac
      >- (match_mp_tac stmt_state_rel_update_var >>
          conj_tac >- first_assum ACCEPT_TAC >>
          match_mp_tac (Q.SPECL [`cenv`, `sa`, `ee.scopes`, `s5.cs_next_var`]
                          local_ptrs_reserved_fresh) >>
          conj_tac >> first_assum ACCEPT_TAC)
      >- simp[]
      >- (qpat_x_assum `32 <= bsz` mp_tac >> rpt (pop_assum kall_tac) >>
          decide_tac)
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- (simp[] >> qpat_assum `binst.inst_id = _` (fn th => rewrite_tac[th]) >>
          first_assum ACCEPT_TAC) >>
      rpt strip_tac >>
      qpat_x_assum `!nm lb lsz. local_region cenv ee.scopes t6 _ _ _ ==> B + bsz <= _ \/ _`
        (qspecl_then [`name`, `lb`, `lsz`] mp_tac) >>
      impl_tac
      >- (qpat_assum `Abbrev (t6 = _)`
            (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
          rewrite_tac[concat_state_rws] >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC)
QED
