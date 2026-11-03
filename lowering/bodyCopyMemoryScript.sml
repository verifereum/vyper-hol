(* Actual typed copy producers: memory prefix and landing boundaries. *)
Theory bodyCopyMemory
Ancestors
  bodyAllocMemory exprSimBufferStore fragExec fragExecMem instMemFrontier
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
