(* Actual typed copy producers: memory prefix and landing boundaries. *)
Theory bodyCopyMemory
Ancestors
  bodyAllocMemory exprSim exprSimBufferStore exprSimLiteralBuffer exprSimAlloc fragExec fragExecMem instMemFrontier
  stmtLowering
  allocaHistoryFragment exprLoweringProps exprLowering emitHelperProps emitHelper
  compileEnv context venomInst venomState venomExecSemantics venomMemDefs
  valueEncoding valueEncodingProofs list rich_list finite_map words arithmetic

Theorem compile_copy_memory_body_mem_ok:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME w /\
  n < dimword (:256) /\ w2n w + n <= s.vs_alloca_next /\
  w2n d + n <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >> Cases_on `n`
  >- gvs[compile_copy_memory_def, comp_return_def, emitted_insts_def,
         run_inst_seq_mem_ok_def] >>
  gvs[compile_copy_memory_def] >>
  drule emitted_insts_emit_void >> strip_tac >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MCOPY, eval_operand_def]
QED

Theorem copy_memory_body_slice[local]:
  compile_copy_memory dst src n sa = ((),sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  (?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
  s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  rpt strip_tac >> Cases_on `n` >>
  gvs[compile_copy_memory_def, emit_void_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_id_def, emit_def,
      emitted_insts_def, fn_has_code_def, IS_PREFIX_APPEND] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def, is_terminator_def]
QED

Theorem copy_memory_body_history[local]:
  compile_copy_memory dst src n sa = ((),sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt strip_tac >> drule_all copy_memory_body_slice >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem copy_memory_body_run[local]:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME w /\
  n < dimword (:256) /\ val_in_memory tv v (w2n w) s.vs_memory /\
  val_wf tv v /\ val_footprint tv v <= n ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    val_in_memory tv v (w2n d) t.vs_memory /\
    t.vs_vars = s.vs_vars /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_memory = (if n = 0 then s.vs_memory
                  else (mcopy (w2n d) (w2n w) n s).vs_memory) /\
    (!a k. a + k <= w2n d \/ w2n d + n <= a ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  rpt strip_tac >> drule_all buffer_copy_memory_encoding >> strip_tac >>
  drule_all buffer_copy_memory_run >> strip_tac >> gvs[] >>
  Cases_on `n = 0` >> gvs[] >>
  qpat_x_assum `(_ with vs_memory := _) = _` mp_tac >>
  simp[venom_state_component_equality] >> metis_tac[]
QED

(* Cursor-aware lifting, keeping the entry cursor implicit in the judgment. *)
Theorem copy_memory_frag_at_cursor[local]:
  !ctx st st' P Q R.
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    isPREFIX st.cs_current_insts st'.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st st') /\
    (!s. P s /\ ~s.vs_halted /\
       s.vs_current_bb = st.cs_current_bb /\
       s.vs_inst_idx = LENGTH st.cs_current_insts ==>
       run_inst_seq_mem_ok (emitted_insts st st') s /\
       ?t. run_inst_seq (emitted_insts st st') s = OK t /\
           Q (t with vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `P' = \s. P s /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts` >>
  `frag_exec_mem ctx st st' P' Q R` by
    (irule frag_exec_mem_run_inst_seq >> simp[Abbr `P'`] >>
     metis_tac[]) >>
  fs[frag_exec_mem_def, Abbr `P'`] >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem compile_copy_memory_body_frag_mem:
  compile_copy_memory dst src n sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~block_is_terminated sa /\ n < dimword (:256) ==>
  frag_exec_mem ctx sa sb
    (\s. s = s0 /\ eval_operand dst s = SOME d /\
      eval_operand src s = SOME w /\
      w2n w + n <= s.vs_alloca_next /\
      w2n d + n <= s.vs_alloca_next /\
      alloca_history func s /\ alloca_inv s /\
      val_in_memory tv v (w2n w) s.vs_memory /\
      val_wf tv v /\ val_footprint tv v <= n)
    (\t. val_in_memory tv v (w2n d) t.vs_memory /\
      t.vs_vars = s0.vs_vars /\ t.vs_allocas = s0.vs_allocas /\
      t.vs_alloca_next = s0.vs_alloca_next /\ alloca_history func t /\
      t.vs_memory = (if n = 0 then s0.vs_memory
                    else (mcopy (w2n d) (w2n w) n s0).vs_memory) /\
      (!a k. a + k <= w2n d \/ w2n d + n <= a ==>
        mem_bytes_at a k t.vs_memory = mem_bytes_at a k s0.vs_memory)) R
Proof
  rpt strip_tac >> drule buffer_copy_memory_shape >> strip_tac >>
  irule copy_memory_frag_at_cursor >>
  simp[same_blocks_def, IS_PREFIX_APPEND] >>
  reverse conj_tac
  >- (conj_tac >- fs[same_blocks_def] >>
      conj_tac >- fs[same_blocks_def] >>
      Cases_on `n`
      >- gvs[compile_copy_memory_def, comp_return_def, emitted_insts_def] >>
      gvs[compile_copy_memory_def] >>
      drule emitted_insts_emit_void >> strip_tac >>
      simp[mk_inst_def, is_terminator_def]) >>
  rpt strip_tac >> gvs[]
  >- (irule compile_copy_memory_body_mem_ok >>
      metis_tac[ADD_COMM]) >>
  drule_all copy_memory_body_run >> strip_tac >>
  `alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule copy_memory_body_history >> metis_tac[]) >>
  qexists_tac `t` >> gvs[ADD_COMM] >> metis_tac[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_COPY_MEMORY_AUDIT OK\n"
     else raise Fail "body copy inherited admission"
  end) [compile_copy_memory_body_mem_ok, copy_memory_body_slice,
        copy_memory_body_history, copy_memory_body_run,
        copy_memory_frag_at_cursor, compile_copy_memory_body_frag_mem];

Theorem copy_len_arithmetic_mem_ok[local]:
  run_inst_seq_mem_ok
    [mk_inst a ADD ops xs; mk_inst b AND ops' ys; mk_inst c ADD ops'' zs] s
Proof
  `!s. inst_mem_below_frontier (mk_inst a ADD ops xs) s /\
       inst_mem_below_frontier (mk_inst b AND ops' ys) s /\
       inst_mem_below_frontier (mk_inst c ADD ops'' zs) s` by
    simp[below_frontier_no_ranges, mk_inst_def] >>
  simp[run_inst_seq_mem_ok_cons] >>
  Cases_on `step_inst_base (mk_inst a ADD ops xs) s` >> simp[] >>
  Cases_on `step_inst_base (mk_inst b AND ops' ys) v` >>
  simp[run_inst_seq_mem_ok_last]
QED

Theorem compile_bytestring_copy_len_body_mem_ok:
  compile_bytestring_copy_len src sa = (out,sb) /\
  eval_operand src s = SOME w /\ w2n w + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >>
  gvs[compile_bytestring_copy_len_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
      emit_def, emitted_insts_def, DROP_APPEND1] >>
  pure_once_rewrite_tac[run_inst_seq_mem_ok_cons] >>
  simp[below_frontier_MLOAD, copy_len_arithmetic_mem_ok] >>
  Cases_on `step_inst_base (mk_inst sa.cs_next_id MLOAD [src]
    [STRING #"%" (toString sa.cs_next_var)]) s` >> simp[]
QED

Theorem compile_store_bytestring_body_mem_ok:
  compile_store_bytestring src dst sa = ((),sb) /\
  eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  mload (w2n w) s = n2w len /\
  32 + 32 * word_size len < dimword (:256) /\
  w2n w + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  w2n d + (32 + 32 * word_size len) <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
  simp_tac bool_ss [compile_store_bytestring_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `compile_bytestring_copy_len src sa = (out,mid)` >>
  drule_all buffer_copy_len_run >> strip_tac >>
  drule buffer_copy_len_shape >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb` by
    (irule emitted_insts_append >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa mid) s` by
    (irule compile_bytestring_copy_len_body_mem_ok >>
     qexistsl_tac [`out`, `src`, `w`] >> simp[] >> decide_tac) >>
  asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >>
  simp[] >> rpt strip_tac >> gvs[] >>
  `q.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `q with vs_vars := _ = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `eval_operand src q = SOME w` by
    (`eval_operand src q = eval_operand src s` by
       (irule literal_operand_frame >> simp[] >> qexists_tac `sa` >> simp[]) >> simp[]) >>
  `eval_operand dst q = SOME d` by
    (`eval_operand dst q = eval_operand dst s` by
       (irule literal_operand_frame >> simp[] >> qexists_tac `sa` >> simp[]) >> simp[]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MCOPY]
QED

Theorem store_bytestring_body_code[local]:
  compile_store_bytestring src dst sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  rpt strip_tac >>
  gvs[compile_store_bytestring_def, compile_bytestring_copy_len_def,
      emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def,
      emitted_insts_def, DROP_APPEND1] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem store_bytestring_body_history[local]:
  compile_store_bytestring src dst sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt strip_tac >> drule buffer_store_bytestring_shape >> strip_tac >>
  drule store_bytestring_body_code >> strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND, same_blocks_def] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG] >> fs[EVERY_MEM]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem compile_store_bytestring_body_frag_mem:
  compile_store_bytestring src dst sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~block_is_terminated sa /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  32 + 32 * word_size len < dimword (:256) ==>
  frag_exec_mem ctx sa sb
    (\s. s = s0 /\ eval_operand src s = SOME w /\
      eval_operand dst s = SOME d /\ mload (w2n w) s = n2w len /\
      w2n w + (32 + 32 * word_size len) <= s.vs_alloca_next /\
      w2n d + (32 + 32 * word_size len) <= s.vs_alloca_next /\
      alloca_history func s /\ alloca_inv s)
    (\t. t.vs_memory =
        (mcopy (w2n d) (w2n w) (32 + 32 * word_size len) s0).vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
      t.vs_allocas = s0.vs_allocas /\
      t.vs_alloca_next = s0.vs_alloca_next /\ alloca_history func t /\
      (!a k. a + k <= w2n d \/ w2n d + (32 + 32 * word_size len) <= a ==>
        mem_bytes_at a k t.vs_memory = mem_bytes_at a k s0.vs_memory)) R
Proof
  rpt strip_tac >> drule buffer_store_bytestring_shape >> strip_tac >>
  irule copy_memory_frag_at_cursor >>
  simp[same_blocks_def, IS_PREFIX_APPEND] >>
  reverse conj_tac
  >- (fs[same_blocks_def] >> metis_tac[store_bytestring_body_code]) >>
  rpt strip_tac >> gvs[]
  >- (irule compile_store_bytestring_body_mem_ok >> metis_tac[ADD_COMM]) >>
  drule buffer_store_bytestring_run >>
  disch_then drule >> disch_then drule >>
  disch_then (qspec_then `len` mp_tac) >>
  (impl_tac >- metis_tac[ADD_COMM]) >> strip_tac >>
  `q.vs_allocas = s0.vs_allocas /\ q.vs_alloca_next = s0.vs_alloca_next` by
    (qpat_x_assum `q with <|vs_vars := _; vs_memory := _|> = s0` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `alloca_history func (q with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule store_bytestring_body_history >> metis_tac[]) >>
  qpat_x_assum `q with <|vs_vars := _; vs_memory := _|> = s0` kall_tac >>
  qexists_tac `q` >> asm_simp_tac (srw_ss()) [lookup_var_def, ADD_COMM] >>
  conj_tac >- fs[lookup_var_def] >>
  conj_tac
  >- (qpat_x_assum `alloca_history func (_ with vs_inst_idx := _)` mp_tac >>
      asm_simp_tac (srw_ss()) [LENGTH_APPEND]) >>
  metis_tac[buffer_mcopy_exterior]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_BYTESTRING_COPY_MEMORY_AUDIT OK\n"
     else raise Fail "body bytestring copy inherited admission"
  end) [copy_len_arithmetic_mem_ok, compile_bytestring_copy_len_body_mem_ok,
        compile_store_bytestring_body_mem_ok, store_bytestring_body_code,
        store_bytestring_body_history, compile_store_bytestring_body_frag_mem];

Theorem body_name_store_memory_mem_ok:
  expr_sim_pre ce cx env (Name ann id) es /\ stmt_state_rel ctx func ce cx es s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  ~is_word_type ann /\
  compile_store_memory ce (Var p) dst ann ann sa = ((),sb) /\
  type_memory_bytes ce ann = type_memory_size entry.type /\
  type_memory_size entry.type < dimword (:256) /\
  eval_operand dst s = SOME d /\
  w2n d + type_memory_size entry.type <= s.vs_alloca_next /\
  (!x. Var p = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >> drule_all body_name_source_region >> strip_tac >> gvs[] >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  drule val_footprint_le >> strip_tac >>
  Cases_on `is_bytestring_type ann`
  >- (gvs[compile_store_memory_def] >>
      drule_all buffer_typed_bytestring_header >> strip_tac >>
      irule compile_store_bytestring_body_mem_ok >>
      qexistsl_tac [`d`, `dst`, `len`, `Var p`, `w`] >>
      simp[] >> metis_tac[]) >>
  gvs[compile_store_memory_def] >>
  irule compile_copy_memory_body_mem_ok >>
  qexistsl_tac [`d`, `dst`, `type_memory_size entry.type`, `Var p`, `w`] >>
  simp[] >> decide_tac
QED

val () =
  let val th = body_name_store_memory_mem_ok
      val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_NAME_STORE_MEMORY_AUDIT OK\n"
     else raise Fail "body name store inherited admission"
  end;

(* The actual nonword memory assignment has an overlap-safe staging copy. *)
Theorem assign_memory_body_parts[local]:
  compile_assign_value ce dst LocMemory src F (SOME LocMemory)
    ann ann info bytes sa = ((),sb) ==>
  ?buf sm sn.
    compile_alloc_buffer (type_memory_bytes ce ann) sa = (buf,sm) /\
    compile_copy_memory buf.buf_operand src (type_memory_bytes ce ann) sm = ((),sn) /\
    compile_store_memory ce buf.buf_operand dst ann ann sn = ((),sb)
Proof
  simp[compile_assign_value_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  metis_tac[pairTheory.PAIR]
QED

Theorem assign_memory_body_code:
  compile_assign_value ce dst LocMemory src F (SOME LocMemory)
    ann ann info bytes sa = ((),sb) /\ fn_has_code sa sb func ==>
  ?buf sm sn.
    compile_alloc_buffer (type_memory_bytes ce ann) sa = (buf,sm) /\
    compile_copy_memory buf.buf_operand src (type_memory_bytes ce ann) sm = ((),sn) /\
    compile_store_memory ce buf.buf_operand dst ann ann sn = ((),sb) /\
    cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
    fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func /\
    emitted_insts sa sb = emitted_insts sa sm ++
      (emitted_insts sm sn ++ emitted_insts sn sb)
Proof
  rpt strip_tac >> drule assign_memory_body_parts >> strip_tac >>
  `cs_extends sa sm` by
    (drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
     metis_tac[cs_appends_emit_helpers, cs_appends_def]) >>
  `cs_extends sm sn` by
    (drule buffer_copy_memory_shape >> simp[cs_extends_def, same_blocks_def] >>
     strip_tac >> simp[]) >>
  `cs_extends sn sb` by
    (drule buffer_store_memory_shape >> simp[cs_extends_def, same_blocks_def] >>
     strip_tac >> simp[]) >>
  `cs_extends sa sn` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sn func /\ fn_has_code sn sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func` by
    (irule fn_has_code_split >> simp[]) >>
  drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule buffer_copy_memory_shape >> strip_tac >>
  drule buffer_store_memory_shape >> strip_tac >>
  `emitted_insts sa sn = emitted_insts sa sm ++ emitted_insts sm sn` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa sn ++ emitted_insts sn sb` by
    (irule emitted_insts_append >> simp[APPEND_ASSOC]) >>
  qexistsl_tac [`buf`, `sm`, `sn`] >> simp[APPEND_ASSOC]
QED

Theorem assign_name_scratch_run[local]:
  expr_sim_pre ce cx env (Name ann id) es /\
  stmt_state_rel ctx func ce cx es s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  type_memory_bytes ce ann = type_memory_size entry.type /\
  type_memory_size entry.type < dimword (:256) /\
  compile_alloc_buffer (type_memory_bytes ce ann) sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand (Var p) (type_memory_bytes ce ann) sm = ((),sn) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ not_fresh_at sa p ==>
  ?a t w.
    run_inst_seq_mem_ok (emitted_insts sa sm) s /\
    run_inst_seq_mem_ok (emitted_insts sm sn) a /\
    run_inst_seq (emitted_insts sa sm) s = OK a /\
    stmt_state_rel ctx func ce cx es a /\
    run_inst_seq (emitted_insts sm sn) a = OK t /\
    eval_operand buf.buf_operand t = SOME w /\
    val_in_memory entry.type entry.value (w2n w) t.vs_memory /\
    val_wf entry.type entry.value /\
    w2n w + type_memory_size entry.type <= t.vs_alloca_next /\
    t.vs_vars = a.vs_vars /\ t.vs_allocas = a.vs_allocas /\
    t.vs_alloca_next = a.vs_alloca_next /\
    t.vs_labels = s.vs_labels /\
    s.vs_alloca_next <= a.vs_alloca_next /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size entry.type) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    (!b k. b + k <= w2n w \/ w2n w + type_memory_size entry.type <= b ==>
      mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory) /\
    (!x. not_fresh_at sa x ==> lookup_var x a = lookup_var x s)
Proof
  rpt strip_tac >>
  drule_all body_name_source_region >> strip_tac >> gvs[] >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK a` >>
  `w2n w' + type_memory_size entry.type <= a.vs_alloca_next` by
    (qpat_x_assum `stmt_state_rel ctx func ce cx es a` mp_tac >>
     simp_tac (srw_ss()) [stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
     strip_tac >> qpat_x_assum `!aid base sz. FLOOKUP a.vs_allocas aid = _ ==> _` drule >>
     asm_simp_tac (srw_ss()) []) >>
  `eval_operand (Var p) a = SOME w` by
    simp[eval_operand_def] >>
  `val_in_memory entry.type entry.value (w2n w) a.vs_memory` by
    asm_simp_tac (srw_ss()) [] >>
  `val_footprint entry.type entry.value <= type_memory_size entry.type` by
    simp[val_footprint_le] >>
  `s.vs_alloca_next <= a.vs_alloca_next /\ a.vs_labels = s.vs_labels` by
    (drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = OK a` mp_tac >>
     asm_simp_tac (srw_ss()) [run_inst_seq_def, step_inst_base_def, mk_inst_def,
       eval_operand_def, exec_alloca_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
     >- (simp[LET_THM, update_var_def] >> rpt strip_tac >> gvs[]) >>
     PairCases_on `x` >> simp[LET_THM, update_var_def] >>
     rpt strip_tac >> gvs[]) >>
  drule_all copy_memory_body_run >> strip_tac >>
  `t.vs_labels = s.vs_labels` by
    (drule_all buffer_copy_memory_run >>
     qpat_x_assum `run_inst_seq (emitted_insts sm sn) a = OK t`
       (fn th => rewrite_tac [th]) >>
     simp_tac (srw_ss()) [] >> disch_then SUBST1_TAC >>
     Cases_on `type_memory_size entry.type = 0` >>
     asm_simp_tac (srw_ss()) [mcopy_def, write_memory_with_expansion_def, LET_THM]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by
    (drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     simp[run_inst_seq_mem_ok_last] >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sm sn) a` by
    (qpat_x_assum `stmt_state_rel ctx func ce cx es s` kall_tac >>
     drule_all body_name_source_region >> strip_tac >> gvs[] >>
     irule compile_copy_memory_body_mem_ok >>
     qexistsl_tac [`w'`, `Var p'`, `type_memory_size entry.type`, `Var p`, `w`] >>
     asm_simp_tac (srw_ss()) [eval_operand_def] >> decide_tac) >>
  qexistsl_tac [`a`, `t`, `w'`] >>
  asm_simp_tac (srw_ss()) [eval_operand_def, lookup_var_def] >>
  conj_tac
  >- (qpat_x_assum `eval_operand buf.buf_operand a = SOME w'` mp_tac >>
      asm_simp_tac (srw_ss()) [eval_operand_def, lookup_var_def]) >>
  conj_tac >- decide_tac >>
  qx_gen_tac `b` >> qx_gen_tac `k` >>
  qpat_x_assum `!a' k. _ \/ _ ==> _`
    (qspecl_then [`b`, `k`] mp_tac) >>
  asm_simp_tac (srw_ss()) [ADD_COMM]
QED

(* Actual assignment prefix, stopping immediately before the typed scratch store. *)
Theorem compile_assign_value_name_staging_prefix_mem_ok:
  expr_sim_pre ce cx env (Name ann id) es /\
  stmt_state_rel ctx func ce cx es s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  type_memory_bytes ce ann = type_memory_size entry.type /\
  type_memory_size entry.type < dimword (:256) /\
  compile_assign_value ce dst LocMemory (Var p) F (SOME LocMemory)
    ann ann info bytes sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ not_fresh_at sa p ==>
  ?buf sm sn a t w.
    compile_alloc_buffer (type_memory_bytes ce ann) sa = (buf,sm) /\
    compile_copy_memory buf.buf_operand (Var p) (type_memory_bytes ce ann) sm = ((),sn) /\
    compile_store_memory ce buf.buf_operand dst ann ann sn = ((),sb) /\
    fn_has_code sn sb func /\ cs_extends sn sb /\
    run_inst_seq_mem_ok (emitted_insts sa sm ++ emitted_insts sm sn) s /\
    run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sn) s = OK t /\
    stmt_state_rel ctx func ce cx es a /\
    eval_operand buf.buf_operand t = SOME w /\
    val_in_memory entry.type entry.value (w2n w) t.vs_memory /\
    val_wf entry.type entry.value /\
    w2n w + type_memory_size entry.type <= t.vs_alloca_next /\
    t.vs_vars = a.vs_vars /\ t.vs_allocas = a.vs_allocas /\
    t.vs_alloca_next = a.vs_alloca_next /\
    t.vs_labels = s.vs_labels /\
    s.vs_alloca_next <= a.vs_alloca_next /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size entry.type) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    (!b k. b + k <= w2n w \/ w2n w + type_memory_size entry.type <= b ==>
      mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory) /\
    (!x. not_fresh_at sa x ==> lookup_var x a = lookup_var x s)
Proof
  rpt strip_tac >> drule_all assign_memory_body_code >> strip_tac >>
  drule_all assign_name_scratch_run >> strip_tac >>
  qexistsl_tac [`buf`, `sm`, `sn`, `a`, `t`, `w`] >>
  asm_simp_tac (srw_ss()) [] >> conj_tac
  >- (irule run_inst_seq_mem_ok_append >> simp[] >>
      rpt strip_tac >> gvs[]) >>
  rev_drule run_inst_seq_append >>
  disch_then (qspec_then `emitted_insts sm sn` mp_tac) >>
  asm_simp_tac (srw_ss()) [] >> rpt strip_tac >>
  qpat_x_assum `!b k. _ \/ _ ==> _` irule >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_ASSIGN_STAGING_PREFIX_AUDIT OK\n"
     else raise Fail "body assignment staging inherited admission"
  end) [assign_memory_body_parts, assign_memory_body_code,
        assign_name_scratch_run, compile_assign_value_name_staging_prefix_mem_ok];

Theorem assign_scratch_operand_transport[local]:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x a = lookup_var x s) /\
  t.vs_vars = a.vs_vars /\ t.vs_labels = s.vs_labels /\
  eval_operand dst s = SOME d ==>
  eval_operand dst t = SOME d /\
  (!x. buf.buf_operand = Var x \/ dst = Var x ==> not_fresh_at sn x)
Proof
  rpt strip_tac
  >- (Cases_on `dst` >> gvs[eval_operand_def] >>
      rename1 `lookup_var x s = SOME d` >>
      `not_fresh_at sa x` by metis_tac[] >>
      qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x a = _` drule >>
      asm_simp_tac (srw_ss()) [lookup_var_def]) >>
  drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule buffer_copy_memory_shape >> strip_tac >>
  `sm.cs_next_var = sa.cs_next_var + 1 /\
   buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var))` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def] >>
  gvs[not_fresh_at_def, ASCIInumbersTheory.toString_11] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!x. dst = Var x ==> _`
    (qspec_then `STRING #"%" (toString n')` mp_tac) >>
  simp[] >> qexists_tac `n'` >> simp[]
QED

Theorem compile_assign_value_name_staged_mem_ok:
  expr_sim_pre ce cx env (Name ann id) es /\
  stmt_state_rel ctx func ce cx es s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  ~is_word_type ann /\
  type_memory_bytes ce ann = type_memory_size entry.type /\
  type_memory_size entry.type < dimword (:256) /\
  compile_assign_value ce dst LocMemory (Var p) F (SOME LocMemory)
    ann ann info bytes sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!x. Var p = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME d /\
  w2n d + type_memory_size entry.type <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >>
  `not_fresh_at sa p` by metis_tac[] >>
  drule_all compile_assign_value_name_staging_prefix_mem_ok >> strip_tac >>
  drule_all assign_memory_body_code >> strip_tac >> gvs[] >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all assign_scratch_operand_transport >> strip_tac >>
  `w2n d + type_memory_size entry.type <= t.vs_alloca_next` by decide_tac >>
  `run_inst_seq_mem_ok (emitted_insts sn sb) t` by
    (drule_all body_name_source_region >> strip_tac >>
     qpat_x_assum `val_in_memory _ _ _ a.vs_memory` kall_tac >>
     drule val_footprint_le >> strip_tac >>
     Cases_on `is_bytestring_type ann`
     >- (gvs[compile_store_memory_def] >>
         drule_all buffer_typed_bytestring_header >> strip_tac >>
         `32 + 32 * word_size len < dimword (:256) /\
          w2n w + (32 + 32 * word_size len) <= t.vs_alloca_next /\
          w2n d + (32 + 32 * word_size len) <= t.vs_alloca_next` by decide_tac >>
         irule compile_store_bytestring_body_mem_ok >>
         qexistsl_tac [`d`, `dst`, `len`, `buf.buf_operand`, `w`] >>
         simp[] >> rpt strip_tac >>
         qpat_x_assum `!x. buf.buf_operand = Var x \/ _ ==> _` irule >> simp[]) >>
     gvs[compile_store_memory_def] >>
     irule compile_copy_memory_body_mem_ok >>
     qexistsl_tac [`d`, `dst`, `type_memory_size entry.type`, `buf.buf_operand`, `w`] >>
     simp[]) >>
  rewrite_tac [APPEND_ASSOC] >>
  irule run_inst_seq_mem_ok_append >> simp[] >>
  rpt strip_tac >> gvs[]
QED

val () =
  let val th = compile_assign_value_name_staged_mem_ok
      val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_ASSIGN_STAGED_MEMORY_AUDIT OK\n"
     else raise Fail "body assignment staged memory inherited admission"
  end;

Theorem assign_name_staged_run[local]:
  expr_sim_pre ce cx env (Name ann id) es /\
  stmt_state_rel ctx func ce cx es s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  ~is_word_type ann /\
  type_memory_bytes ce ann = type_memory_size entry.type /\
  type_memory_size entry.type < dimword (:256) /\
  compile_assign_value ce dst LocMemory (Var p) F (SOME LocMemory)
    ann ann info bytes sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!x. Var p = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME d ==>
  ?q (w:256 word). run_inst_seq (emitted_insts sa sb) s = OK q /\
    val_in_memory entry.type entry.value (w2n d) q.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP q.vs_allocas aid = SOME b) /\
    s.vs_alloca_next <= q.vs_alloca_next /\
    FLOOKUP q.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size entry.type) /\
    (!b k. (b+k <= w2n w \/ w2n w + type_memory_size entry.type <= b) /\
           (b+k <= w2n d \/ w2n d + type_memory_size entry.type <= b) ==>
      mem_bytes_at b k q.vs_memory = mem_bytes_at b k s.vs_memory)
Proof
  rpt strip_tac >>
  `not_fresh_at sa p` by metis_tac[] >>
  drule_all compile_assign_value_name_staging_prefix_mem_ok >> strip_tac >>
  drule_all assign_memory_body_code >> strip_tac >> gvs[] >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all assign_scratch_operand_transport >> strip_tac >>
  `sa.cs_next_var <= sn.cs_next_var` by
    (drule buffer_copy_memory_shape >> strip_tac >>
     drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
     gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_var_def, fresh_id_def, emit_def]) >>
  drule_all body_name_source_region >> strip_tac >> gvs[] >>
  `expr_val_rel cx ann entry.value buf.buf_operand t` by
    simp[expr_val_rel_def] >>
  drule_all buffer_store_memory_encoding >> strip_tac >>
  `q.vs_allocas = t.vs_allocas /\ q.vs_alloca_next = t.vs_alloca_next` by
    (qpat_x_assum `q with <|vs_vars := _; vs_memory := _|> = t` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `run_inst_seq ((emitted_insts sa sm ++ emitted_insts sm sn) ++
       emitted_insts sn sb) s = OK q` by
    (qpat_x_assum `run_inst_seq (_ ++ _) s = OK t` (mp_tac o MATCH_MP run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts sn sb` mp_tac) >> simp[]) >>
  qexistsl_tac [`q`, `w`] >> asm_simp_tac (srw_ss()) [APPEND_ASSOC] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sn x` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      qpat_x_assum `!x. not_fresh_at sn x ==> _` drule >>
      asm_simp_tac (srw_ss()) [lookup_var_def] >>
      qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >>
      simp[lookup_var_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!a k. _ ==> mem_bytes_at a k q.vs_memory = _`
    (qspecl_then [`b`, `k`] mp_tac) >>
  qpat_x_assum `!b k. _ ==> mem_bytes_at b k t.vs_memory = _`
    (qspecl_then [`b`, `k`] mp_tac) >> metis_tac[ADD_COMM]
QED

Theorem copy_memory_body_code[local]:
  compile_copy_memory dst src n sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  Cases_on `n`
  >- simp[compile_copy_memory_def, comp_return_def, emitted_insts_def] >>
  simp[compile_copy_memory_def] >> strip_tac >>
  drule emitted_insts_emit_void >> simp[mk_inst_def, is_terminator_def]
QED

Theorem store_memory_body_code[local]:
  compile_store_memory ce src dst ann ann sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  Cases_on `is_word_type ann`
  >- (simp[compile_store_memory_def] >> strip_tac >>
      drule emitted_insts_emit_void >> simp[mk_inst_def, is_terminator_def]) >>
  Cases_on `is_bytestring_type ann` >> simp[compile_store_memory_def]
  >- metis_tac[store_bytestring_body_code] >>
  metis_tac[copy_memory_body_code]
QED

Theorem assign_memory_body_shape[local]:
  compile_assign_value ce dst LocMemory src F (SOME LocMemory)
    ann ann info bytes sa = ((),sb) /\ fn_has_code sa sb func ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  rpt strip_tac >> drule_all assign_memory_body_code >> strip_tac >>
  drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule buffer_copy_memory_shape >> strip_tac >>
  drule buffer_store_memory_shape >> strip_tac >>
  `same_blocks sa sb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (fs[same_blocks_def] >> metis_tac[APPEND_ASSOC]) >>
  asm_simp_tac (srw_ss()) [EVERY_APPEND] >> rpt conj_tac
  >- (drule emitted_insts_emit_op >> strip_tac >>
      simp[mk_inst_def, is_terminator_def])
  >- metis_tac[copy_memory_body_code] >>
  metis_tac[store_memory_body_code]
QED

Theorem assign_memory_body_history[local]:
  compile_assign_value ce dst LocMemory src F (SOME LocMemory)
    ann ann info bytes sa = ((),sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt strip_tac >> drule_all assign_memory_body_shape >> strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND, same_blocks_def] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG] >> fs[EVERY_MEM]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem compile_assign_value_name_staged_body_frag_mem:
  expr_sim_pre ce cx env (Name ann id) es /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  ~is_word_type ann /\
  type_memory_bytes ce ann = type_memory_size entry.type /\
  type_memory_size entry.type < dimword (:256) /\
  compile_assign_value ce dst LocMemory (Var p) F (SOME LocMemory)
    ann ann info bytes sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ ~block_is_terminated sa /\
  (!x. Var p = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  frag_exec_mem ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s /\
      alloca_history func s /\ eval_operand dst s = SOME d /\
      w2n d + type_memory_size entry.type <= s.vs_alloca_next)
    (\t. val_in_memory entry.type entry.value (w2n d) t.vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ alloca_history func t /\
      ?w:256 word.
        FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size entry.type) /\
        (!b k. (b+k <= w2n w \/ w2n w + type_memory_size entry.type <= b) /\
               (b+k <= w2n d \/ w2n d + type_memory_size entry.type <= b) ==>
          mem_bytes_at b k t.vs_memory = mem_bytes_at b k s0.vs_memory)) R
Proof
  rpt strip_tac >> drule_all assign_memory_body_shape >> strip_tac >>
  fs[same_blocks_def] >>
  irule copy_memory_frag_at_cursor >>
  asm_simp_tac (srw_ss()) [same_blocks_def, IS_PREFIX_APPEND] >>
  rpt strip_tac >> gvs[] >>
  `!x. Var p = Var x \/ dst = Var x ==> not_fresh_at sa x` by (simp[] >> metis_tac[])
  >- (`w2n d + type_memory_size entry.type <= s0.vs_alloca_next` by decide_tac >>
      drule_all compile_assign_value_name_staged_mem_ok >> simp[]) >>
  drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)
    assign_name_staged_run >> disch_then drule >> disch_then drule >>
  disch_then drule >> simp[] >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `alloca_inv s0` by fs[stmt_state_rel_def] >>
  `alloca_history func (q with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule assign_memory_body_history >> metis_tac[]) >>
  `LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts +
    LENGTH (emitted_insts sa sb)` by simp[] >>
  qexists_tac `q` >> fs[lookup_var_def] >> metis_tac[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_ASSIGN_STAGED_FRAGMENT_AUDIT OK\n"
     else raise Fail "body assignment staged fragment inherited admission"
  end) [assign_scratch_operand_transport, assign_name_staged_run,
        copy_memory_body_code, store_memory_body_code,
        assign_memory_body_shape, assign_memory_body_history,
        compile_assign_value_name_staged_body_frag_mem];
