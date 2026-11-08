(* Producer-local capacity probe: the literal temporary is sized by its
   actual byte length (one), not by the annotated dynamic-bytes bound (64). *)
Theory assignBasePtrLiteralSource
Ancestors bodyPtrDefs exprLowering exprLoweringProps exprSimAlloc
  allocationPtr fragGasSeqPtr context emitHelper compileEnv list words
  vyperAST vyperTyping fragExecPtr emitHelperProps venomInst venomExecSemantics
  exprSimLiteralBuffer rich_list fragExec typedCopyLoopHeaderPtr
  decoderGhostFramePtr ghostPcTransportPtr typedCopyPtr venomState finite_map
  instIdxIndep ptrDiscipline

Theorem assign_base_ptr_one_byte_lowering:
  !cenv ty sa.
    lower_value compile_expr cenv ty
      (Literal (BaseT (BytesT (Dynamic 64))) (BytesL [1w])) sa =
    (do buf <- compile_bytelike_literal [1w] 1;
        return buf.buf_operand
     od) sa
Proof
  rpt gen_tac >> simp[lower_value_def, Once compile_expr_def, compile_literal_vv_def,
       expr_type_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_bytelike_literal [1w] 1 sa` >>
  simp[unwrap_value_def, base_ptr_def, as_ptr_val_def,
       is_word_type_def, comp_return_def]
QED

Theorem assign_base_ptr_one_byte_buffer_size:
  !cenv.
    type_memory_bytes cenv
      (lowered_value_type cenv
        (Literal (BaseT (BytesT (Dynamic 64))) (BytesL [1w]))) = 64
Proof
  gen_tac >> EVAL_TAC
QED

Theorem assign_base_ptr_one_byte_initialization:
  compile_bytelike_literal [1w] 1 =
    do buf <- compile_alloc_buffer 64;
       emit_void MSTORE [buf.buf_operand; Lit 1w];
       dst <- emit_op ADD [buf.buf_operand; Lit 32w];
       emit_void MSTORE [dst; Lit (n2w (2 ** 248))];
       return buf
    od
Proof
  `word_of_bytes T (0w:bytes32)
      ((1w:word8)::REPLICATE 31 0w) = n2w (2 ** 248)` by
    (EVAL_TAC >> simp[w2n_n2w, dimword_def]) >>
  simp[compile_bytelike_literal_def, compile_store_byte_chunks_def,
       TAKE_def, DROP_def, TAKE_LENGTH_TOO_LONG, comp_ignore_bind_def,
       comp_bind_assoc] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def] >>
  gen_tac >> rpt pairarg_tac >> gvs[comp_bind_def, comp_return_def]
QED

(* The real allocation run supplies both capacity and its pointer check.
   No freshness assumption excludes re-execution of an allocation site. *)
Theorem assign_base_ptr_alloc_buffer_sequence:
  !ctx func cenv cx es sa sm buf sz s PG G tn D.
    compile_alloc_buffer sz sa = (buf,sm) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
    ~ctx_has_dalloca ctx /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
    ?t w G' tn'.
      run_inst_seq (emitted_insts sa sm) s = OK t /\
      inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sm) s G' tn' /\
      stmt_state_rel ctx func cenv cx es t /\
      eval_operand buf.buf_operand t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      w2n w + sz < dimword (:256) /\
      (?p. buf.buf_operand = Var p /\ ptr_covers G' tn' p t sz) /\
      (!p k. buf.buf_operand <> Var p /\ ptr_covers G tn p s k ==>
         ptr_covers G' tn' p t k) /\
      (!op. op <> buf.buf_operand ==> eval_operand op t = eval_operand op s)
Proof
  rpt strip_tac >> drule_all literal_alloc_buffer_run >> strip_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  `sz < dimword (:256)` by decide_tac >>
  drule_all alloca_step_ptr_covers >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] assume_tac) >>
  qexistsl_tac
    [`step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
        [STRING #"%" (toString sa.cs_next_var)]) t`,
     `step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
        [STRING #"%" (toString sa.cs_next_var)]) s t tn`] >>
  simp[inst_seq_ptr_def, ptr_inst_ok_alloca] >> conj_tac
  >- (rpt strip_tac >> irule alloca_step_old_ptr_covers >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> irule alloca_step_operand_preserved >>
  goal_assum (drule_at Any) >> rpt strip_tac >> gvs[]
QED

Theorem assign_base_ptr_bytelike_counted_path:
  !bs ml sa buf sb ctx func s t PG G tn G' tn' D.
    compile_bytelike_literal bs ml sa = (buf,sb) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    t.vs_current_bb = sb.cs_current_bb
Proof
  rpt strip_tac >> drule literal_bytelike_counted_shape >> strip_tac >>
  drule_all literal_bytelike_gas_path >> strip_tac >>
  gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[DROP_APPEND1] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem assign_base_ptr_one_byte_init_sequence:
  !ctx func PG G tn s p q a i j k D.
    ~ctx_has_dalloca ctx /\ p <> q /\ lookup_var p s = SOME a /\
    ptr_covers G tn p s 64 /\ w2n a + 64 < dimword(:256) ==>
    ?t G' tn'.
      run_inst_seq
        [mk_inst i MSTORE [Var p; Lit 1w] [];
         mk_inst j ADD [Var p; Lit 32w] [q];
         mk_inst k MSTORE [Var q; Lit (n2w (2 ** 248))] []] s = OK t /\
      (!idx. inst_seq_ptr D 0 ctx func PG G tn
        [mk_inst i MSTORE [Var p; Lit 1w] [];
         mk_inst j ADD [Var p; Lit 32w] [q];
         mk_inst k MSTORE [Var q; Lit (n2w (2 ** 248))] []]
        (s with vs_inst_idx := idx) G' tn') /\
      lookup_var p t = SOME a /\ ptr_covers G' tn' p t 64 /\
      w2n a + 64 < dimword(:256)
Proof
  rpt strip_tac >>
  qabbrev_tac `h = mk_inst i MSTORE [Var p; Lit 1w] []` >>
  qabbrev_tac `ad = mk_inst j ADD [Var p; Lit 32w] [q]` >>
  qabbrev_tac `st = mk_inst k MSTORE [Var q; Lit (n2w (2 ** 248))] []` >>
  qabbrev_tac `u = mstore (w2n a) 1w s` >>
  qabbrev_tac `v = update_var q (a + 32w) u` >>
  qabbrev_tac `t = mstore (w2n (a + 32w)) (n2w (2 ** 248)) v` >>
  `lookup_var p u = SOME a /\ lookup_var q v = SOME (a + 32w)` by
    (simp[Abbr `u`, Abbr `v`, lookup_var_def, mstore_def,
          update_var_def, FLOOKUP_UPDATE] >> fs[lookup_var_def]) >>
  `step_inst_base h s = OK u /\ step_inst_base ad u = OK v /\
   step_inst_base st v = OK t` by
    (simp[Abbr `h`, Abbr `ad`, Abbr `st`] >>
     asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors, instruction_accfupds,
                       combinTheory.K_THM, opcode_case_def] >>
     simp[exec_write2_def, exec_pure2_def, eval_operand_def] >>
     simp[Abbr `u`, Abbr `v`, Abbr `t`]) >>
  qabbrev_tac `G1 = step_prov PG G h u` >>
  qabbrev_tac `tn1 = step_taint h s u tn` >>
  qabbrev_tac `G2 = step_prov PG G1 ad v` >>
  qabbrev_tac `tn2 = step_taint ad u v tn1` >>
  qabbrev_tac `G3 = step_prov PG G2 st t` >>
  qabbrev_tac `tn3 = step_taint st v t tn2` >>
  `ptr_covers G1 tn1 p u 64` by
    (simp[Abbr `G1`, Abbr `tn1`] >> irule ptr_covers_step_frame >>
     simp[Abbr `h`]) >>
  `ptr_covers G2 tn2 q v 32` by suspend "offset" >>
  qexistsl_tac [`t`, `G3`, `tn3`] >>
  conj_tac >- simp[run_inst_seq_def] >>
  conj_tac >- suspend "checks" >>
  conj_tac >-
    (simp[Abbr `t`, Abbr `v`, Abbr `u`, lookup_var_def,
          update_var_def, mstore_def, FLOOKUP_UPDATE] >> fs[lookup_var_def]) >>
  simp[] >> suspend "root_frame"
QED

Resume assign_base_ptr_one_byte_init_sequence[offset]:
  simp[Abbr `G2`, Abbr `tn2`, Abbr `ad`, Abbr `v`] >>
  irule typed_copy_loop_dynamic_offset_covers >>
  simp[eval_operand_def] >> qexists_tac `64` >> simp[]
QED

Resume assign_base_ptr_one_byte_init_sequence[checks]:
  gen_tac >>
  `~is_terminator h.inst_opcode /\ ~is_terminator ad.inst_opcode /\
   ~is_terminator st.inst_opcode` by
    simp[Abbr `h`, Abbr `ad`, Abbr `st`, mk_inst_def, is_terminator_def] >>
  simp[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
       Abbr `G1`, Abbr `tn1`, Abbr `G2`, Abbr `tn2`, Abbr `G3`, Abbr `tn3`] >>
  conj_tac >-
    (simp[Abbr `h`] >> irule ptr_inst_ok_mstore >>
     simp[op_taint_def] >> fs[ptr_covers_def] >>
     qexistsl_tac [`a`, `b`, `sz'`] >> simp[] >> decide_tac) >>
  conj_tac >-
    (simp[Abbr `ad`] >> irule ptr_inst_ok_copy_len_binop >>
     fs[ptr_covers_def, op_taint_def]) >>
  simp[Abbr `st`] >> irule ptr_inst_ok_mstore >> simp[op_taint_def]
QED

Resume assign_base_ptr_one_byte_init_sequence[root_frame]:
  simp[Abbr `G3`, Abbr `tn3`] >> irule ptr_covers_step_frame >>
  simp[Abbr `st`, Abbr `t`, lookup_var_def, mstore_def] >>
  simp[Abbr `G2`, Abbr `tn2`] >> irule ptr_covers_step_frame >>
  simp[Abbr `ad`, Abbr `v`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  fs[ptr_covers_def, lookup_var_def]
QED

Finalise assign_base_ptr_one_byte_init_sequence

Theorem assign_base_ptr_one_byte_code:
  !sa buf sb.
    compile_bytelike_literal [1w] 1 sa = (buf,sb) ==>
    buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var)) /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ALLOCA [Lit 64w]
         [STRING #"%" (toString sa.cs_next_var)];
       mk_inst (sa.cs_next_id + 1) MSTORE
         [Var (STRING #"%" (toString sa.cs_next_var)); Lit 1w] [];
       mk_inst (sa.cs_next_id + 2) ADD
         [Var (STRING #"%" (toString sa.cs_next_var)); Lit 32w]
         [STRING #"%" (toString (sa.cs_next_var + 1))];
       mk_inst (sa.cs_next_id + 3) MSTORE
         [Var (STRING #"%" (toString (sa.cs_next_var + 1)));
          Lit (n2w (2 ** 248))] []]
Proof
  simp[assign_base_ptr_one_byte_initialization, compile_alloc_buffer_def,
       emit_void_def, emit_op_def, comp_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, comp_ignore_bind_def] >>
  rpt strip_tac >> gvs[emitted_insts_def] >>
  simp[DROP_APPEND1, arithmeticTheory.ADD_ASSOC]
QED

Theorem assign_base_ptr_alloc_buffer_counted_path:
  !ctx func cenv cx es sa sm buf sz s PG G tn D.
    compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t w G' tn'.
      gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
      stmt_state_rel ctx func cenv cx es t /\
      eval_operand buf.buf_operand t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      w2n w + sz < dimword (:256) /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts /\
      (?p. buf.buf_operand = Var p /\ ptr_covers G' tn' p t sz) /\
      (!p k. buf.buf_operand <> Var p /\ ptr_covers G tn p s k ==>
         ptr_covers G' tn' p t k) /\
      (!op. op <> buf.buf_operand ==> eval_operand op t = eval_operand op s)
Proof
  rpt strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all assign_base_ptr_alloc_buffer_sequence >>
  disch_then (qspecl_then [`PG`, `G`, `tn`, `D`] strip_assume_tac) >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `cs'.cs_current_bb = sa.cs_current_bb` by
    (gvs[emit_op_def, comp_bind_def, comp_return_def, comp_ignore_bind_def,
         fresh_id_def, fresh_var_def, emit_def]) >>
  `t.vs_current_bb = s.vs_current_bb` by suspend "control" >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `isPREFIX (emitted_insts sa cs') (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[DROP_APPEND1] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa cs')` by simp[mk_inst_def, is_terminator_def] >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    run_inst_seq_gas_path_ptr >>
  disch_then (qspecl_then [`t`, `bb`] mp_tac) >>
  simp[mk_inst_def, stmt_state_rel_inst_idx, DROP_APPEND1, is_terminator_def] >>
  strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sa.cs_current_insts + 1`,
               `w`, `G'`, `tn'`] >> simp[stmt_state_rel_inst_idx]
QED

Resume assign_base_ptr_alloc_buffer_counted_path[control]:
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  `step_inst 0 ctx
     (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  drule venomInstProofsTheory.step_preserves_control_flow >>
  simp[mk_inst_def, is_terminator_def]
QED

Finalise assign_base_ptr_alloc_buffer_counted_path
