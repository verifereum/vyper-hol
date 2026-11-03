(* Declaration store: source-state and memory continuation boundaries. *)
Theory bodyDeclMemory
Ancestors
  bodyCopyMemory bodyMemoryDefs stmtSimDeclMem localPtrsProps stmtSimDeclStore
  stmtSimDecl valueCopy valueCopyBytes exprOperandVar freshWrites
  valueTypingMemoryProps vyperTyping exprSim stmtSim venomState
  valueEncoding valueEncodingProofs intCallResult compileEnv exprLoweringProps
  loweringSlice exprLowering exprSimBufferStore valueEncodingProofs
  words venomExecSemantics stmtLowering context fragExec fragExecMem
  allocaHistoryFragment list rich_list emitHelper emitHelperProps venomInst
  exprSimLiteralBuffer exprSimBuffer

Theorem body_stmt_state_rel_declare_store_frame:
  !func cenv cx es s t sa id p sz w inst v tyv sc rest a ctx.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!b n. b + n <= w2n w \/ w2n w + type_memory_size tyv <= b ==>
           mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    type_memory_size tyv <= sz /\ val_wf tyv v /\
    val_in_memory tyv v (w2n w) t.vs_memory ==>
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
        (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t
Proof
  rpt gen_tac >> strip_tac >>
  `!q. q = p \/ ~not_local_ptr cenv es.scopes q ==>
       lookup_var q t = lookup_var q s` by
    (rpt strip_tac >- simp[] >>
     `not_fresh_at sa q` by
       (gvs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
     simp[]) >>
  `!n b sz'. n <> id /\ local_region cenv es.scopes s n b sz' ==>
       mem_bytes_at b sz' s.vs_memory = mem_bytes_at b sz' t.vs_memory` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) sz b sz'` by
       (irule local_ptrs_rel_alloca_disjoint >>
        qexistsl_tac [`cenv`, `func`, `inst`, `n`, `p`, `es.scopes`, `s`] >>
        fs[stmt_state_rel_def, state_rel_def]) >>
     `b + sz' <= w2n w \/ w2n w + type_memory_size tyv <= b` by
       (fs[regions_disjoint_def] >> decide_tac) >>
     metis_tac[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (`t.vs_data_section = s.vs_data_section` by
       (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
        simp[venom_state_component_equality]) >>
     irule immutables_rel_mem_agree >> qexists_tac `s` >>
     fs[stmt_state_rel_def, state_rel_def] >>
     fs[immutable_alloca_sep_def] >> rpt strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     `regions_disjoint off (type_memory_size tv) (w2n w) sz` by metis_tac[] >>
     `off + type_memory_size tv <= w2n w \/
      w2n w + type_memory_size tyv <= off` by
       (fs[regions_disjoint_def] >> decide_tac) >>
     qpat_x_assum `!b n. _ ==> mem_bytes_at b n t.vs_memory = _`
       (qspecl_then [`off`, `type_memory_size tv`] mp_tac) >> simp[]) >>
  irule stmt_state_rel_declare_memory >> simp[] >>
  qexistsl_tac [`inst`, `s`, `w`] >> gs[] >>
  qpat_x_assum `t with <|vs_memory := _; vs_vars := _|> = s` mp_tac >>
  simp[venom_state_component_equality] >> strip_tac >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem body_typed_store_memory_mem_ok:
  compile_store_memory ce src dst ann ann sa = ((),sb) /\
  ~is_word_type ann /\ evaluate_type tenv ann = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  type_memory_bytes ce ann = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
  w2n w + type_memory_size tv <= s.vs_alloca_next /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >> drule val_footprint_le >> strip_tac >>
  Cases_on `is_bytestring_type ann`
  >- (gvs[compile_store_memory_def] >>
      drule_all buffer_typed_bytestring_header >> strip_tac >>
      irule compile_store_bytestring_body_mem_ok >>
      qexistsl_tac [`d`, `dst`, `len`, `src`, `w`] >>
      simp[] >> metis_tac[]) >>
  gvs[compile_store_memory_def] >>
  irule compile_copy_memory_body_mem_ok >>
  qexistsl_tac [`d`, `dst`, `type_memory_size tv`, `src`, `w`] >> simp[]
QED

Theorem body_store_memory_history[local]:
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND, same_blocks_def] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG] >> fs[EVERY_MEM]) >>
  drule_all allocaHistoryFragmentTheory.alloca_history_run_inst_seq >> simp[]
QED

Theorem body_decl_frag_at_cursor[local]:
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
    (irule frag_exec_mem_run_inst_seq >> simp[Abbr `P'`] >> metis_tac[]) >>
  fs[frag_exec_mem_def, Abbr `P'`] >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem annassign_memory_store_body_frag_mem:
  !ctx func cenv cx es s id p sz w inst v tyv sc rest a src ty sa sb sw d R.
    compile_store_memory cenv src (Var p) ty ty sa = ((), sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
    eval_operand src s = SOME sw /\ lookup_var p s = SOME w /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory tyv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    type_memory_size tyv <= sz /\ type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    w2n sw + type_memory_size tyv <= s.vs_alloca_next /\
    w2n w + type_memory_size tyv <= s.vs_alloca_next /\
    alloca_history func s /\ return_buf_frame d cenv sa s ==>
    frag_exec_mem ctx sa sb (\u. u = s)
      (\t. stmt_state_rel ctx func cenv cx
          (es with scopes :=
            (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t /\
        alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
        return_buf_frame d cenv sb t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)) R
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  drule compile_store_memory_run_size_bound_with_capacity >>
  disch_then (qspecl_then [`s`, `get_tenv cx`, `tyv`, `v`, `sw`, `w`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `stmt_state_rel ctx func cenv cx
     (es with scopes :=
       (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t` by
    (irule body_stmt_state_rel_declare_store_frame >> simp[] >>
     qexistsl_tac [`inst`, `s`, `sa`, `w`] >> gs[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s`, `sa`] >> simp[]) >>
  fs[same_blocks_def] >>
  irule body_decl_frag_at_cursor >>
  asm_simp_tac (srw_ss()) [IS_PREFIX_APPEND] >> rpt strip_tac >> gvs[]
  >- (irule body_typed_store_memory_mem_ok >>
      goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
      qexistsl_tac [`w`, `get_tenv cx`, `tyv`, `v`, `sw`] >>
      simp[] >> metis_tac[])
  >- simp[stmt_state_rel_inst_idx]
  >- (`alloca_inv s` by fs[stmt_state_rel_def] >>
      `alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
        (irule body_store_memory_history >> simp[same_blocks_def] >> metis_tac[]) >>
      `LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts +
         LENGTH (emitted_insts sa sb)` by simp[] >> metis_tac[])
  >- (Cases_on `d` >- fs[return_buf_frame_def] >>
      rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
      fs[return_buf_frame_def, lookup_var_def]) >>
  fs[lookup_var_def]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_DECL_MEMORY_AUDIT OK\n"
     else raise Fail "body declaration memory inherited admission"
  end) [body_stmt_state_rel_declare_store_frame, body_typed_store_memory_mem_ok,
        body_store_memory_history, body_decl_frag_at_cursor,
        annassign_memory_store_body_frag_mem];

(* Scratch copy preserves all source-level live regions. *)
Theorem body_stmt_state_rel_mcopy_alloca:
  !func cenv cx es s inst p dst src sz ctx.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    not_local_ptr cenv es.scopes p /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (dst, sz) ==>
    stmt_state_rel ctx func cenv cx es (mcopy dst src sz s)
Proof
  rpt strip_tac >>
  `(mcopy dst src sz s with <|vs_vars := s.vs_vars;
                             vs_memory := s.vs_memory|>) = s` by
    simp[mcopy_def, write_memory_with_expansion_def, LET_THM] >>
  `!q. lookup_var q (mcopy dst src sz s) = lookup_var q s` by
    simp[mcopy_def, write_memory_with_expansion_def, LET_THM, lookup_var_def] >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
     (mcopy dst src sz s)` by
    (irule immutables_rel_mem_agree >> qexists_tac `s` >>
     conj_tac
     >- simp[mcopy_def, immutableMemoryFrameTheory.immutable_write_memory_capacity,
             arithmeticTheory.MAX_DEF] >>
     conj_tac >- simp[mcopy_def, write_memory_with_expansion_def] >>
     reverse conj_tac >- gvs[stmt_state_rel_def, state_rel_def] >>
     rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >>
     qpat_assum `stmt_state_rel ctx _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def, immutable_alloca_sep_def] >>
     strip_tac >> qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
     disch_then drule_all >> strip_tac >>
     qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> _` drule_all >>
     simp[regions_disjoint_def] >> decide_tac) >>
  irule result_state_memory_frame >> reverse conj_tac
  >- (qexists_tac `s` >> simp[] >>
  rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >>
  `regions_disjoint dst sz b sz'` by
    (irule local_ptrs_rel_alloca_disjoint >>
     qexistsl_tac [`cenv`, `func`, `inst`, `name`, `p`, `es.scopes`, `s`] >>
     fs[stmt_state_rel_def, state_rel_def]) >>
  fs[regions_disjoint_def]) >> first_assum ACCEPT_TAC
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag body_stmt_state_rel_mcopy_alloca)
  in if null axioms andalso null (Thm.hyp body_stmt_state_rel_mcopy_alloca) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_SCRATCH_STATE_MEMORY_AUDIT OK\n"
     else raise Fail "body scratch state inherited admission"
  end;

Theorem body_scratch_alloc_operand[local]:
  compile_alloc_buffer n sa = (buf,sm) ==>
  buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var))
Proof
  simp[compile_alloc_buffer_def, emit_op_def, fresh_var_def, fresh_id_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem body_scratch_copy_state[local]:
  compile_alloc_buffer n sa = (buf,sm) /\ fn_has_code sa sm func /\
  stmt_state_rel ctx func ce cx es a /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  FLOOKUP a.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
  run_inst_seq (emitted_insts sm sn) a = OK t /\
  compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
  eval_operand buf.buf_operand a = SOME w /\ eval_operand src a = SOME sw /\
  n < dimword (:256) ==>
  stmt_state_rel ctx func ce cx es t
Proof
  rpt strip_tac >> drule_all buffer_copy_memory_run >>
  asm_rewrite_tac[] >> strip_tac >> gvs[] >>
  Cases_on `n = 0` >- gvs[] >> gvs[] >>
  drule_all exprSimBufferTheory.buffer_alloc_code >> strip_tac >>
  drule body_scratch_alloc_operand >> strip_tac >>
  irule body_stmt_state_rel_mcopy_alloca >> simp[] >>
  goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  simp[mk_inst_def] >>
  irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]
QED

Theorem body_scratch_prefix_run[local]:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
  fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ n < dimword (:256) /\
  w2n sw + n <= s.vs_alloca_next /\
  val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= n ==>
  ?a t w. run_inst_seq (emitted_insts sa sm) s = OK a /\
    run_inst_seq (emitted_insts sm sn) a = OK t /\
    run_inst_seq_mem_ok (emitted_insts sa sm) s /\
    run_inst_seq_mem_ok (emitted_insts sm sn) a /\
    stmt_state_rel ctx func ce cx es t /\
    eval_operand buf.buf_operand t = SOME w /\
    val_in_memory tv v (w2n w) t.vs_memory /\
    w2n w + n <= t.vs_alloca_next /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)
Proof
  rpt strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK a` >>
  `w2n w + n <= a.vs_alloca_next` by
    (qpat_x_assum `stmt_state_rel ctx func ce cx es a` mp_tac >>
     simp_tac (srw_ss()) [stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.alloca_next_valid_def] >>
     strip_tac >> qpat_x_assum `!aid base sz. FLOOKUP a.vs_allocas aid = _ ==> _` drule >>
     asm_simp_tac (srw_ss()) []) >>
  `s.vs_alloca_next <= a.vs_alloca_next /\ a.vs_labels = s.vs_labels` by
    (drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = OK a` mp_tac >>
     asm_simp_tac (srw_ss()) [run_inst_seq_def, step_inst_base_def, mk_inst_def,
       eval_operand_def, exec_alloca_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
     >- (simp[LET_THM, update_var_def] >> rpt strip_tac >> gvs[]) >>
     PairCases_on `x` >> simp[LET_THM, update_var_def] >> rpt strip_tac >> gvs[]) >>
  `eval_operand src a = SOME sw` by
    (Cases_on `src` >> fs[eval_operand_def] >> metis_tac[]) >>
  `val_in_memory tv v (w2n sw) a.vs_memory` by simp[] >>
  drule_all buffer_copy_memory_encoding >> strip_tac >>
  drule_all buffer_copy_memory_run >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq (emitted_insts sm sn) a = OK t` >>
  `stmt_state_rel ctx func ce cx es t` by
    (irule body_scratch_copy_state >> simp[] >>
     goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >> metis_tac[]) >>
  `t.vs_vars = a.vs_vars /\ t.vs_allocas = a.vs_allocas /\
   t.vs_alloca_next = a.vs_alloca_next` by
    (simp[Abbr `t`] >> Cases_on `n = 0` >>
     simp[mcopy_def, write_memory_with_expansion_def, LET_THM]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by
    (drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >> simp[run_inst_seq_mem_ok_last] >>
     irule instMemFrontierTheory.below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sm sn) a` by
    (irule compile_copy_memory_body_mem_ok >>
     goal_assum (drule_at (Pat `compile_copy_memory _ _ _ _ = _`)) >>
     qexistsl_tac [`w`, `sw`] >> simp[] >> decide_tac) >>
  qexistsl_tac [`a`, `t`, `w`] >> fs[lookup_var_def] >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem body_scratch_prefix_shape[local]:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src n sm = ((),sn) ==>
  same_blocks sa sn /\
  sn.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sn /\
  emitted_insts sa sn = emitted_insts sa sm ++ emitted_insts sm sn /\
  cs_extends sa sm /\ cs_extends sm sn /\
  sa.cs_next_var <= sn.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sn)
Proof
  rpt strip_tac >>
  drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule buffer_copy_memory_shape >> strip_tac >>
  `cs_extends sa sm` by metis_tac[cs_appends_def, cs_appends_emit_helpers] >>
  `cs_appends (compile_copy_memory buf.buf_operand src n)` by
    (Cases_on `n` >> simp[compile_copy_memory_def, cs_appends_return,
      cs_appends_emit_helpers]) >>
  `cs_extends sm sn` by metis_tac[cs_appends_def] >>
  `sm.cs_next_var = sa.cs_next_var + 1` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[]) >>
  `sa.cs_next_var <= sn.cs_next_var` by simp[] >>
  `emitted_insts sa sn = emitted_insts sa sm ++ emitted_insts sm sn` by
    (`LENGTH sa.cs_current_insts -
        (LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sm)) = 0` by decide_tac >>
     CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  fs[same_blocks_def] >>
  asm_simp_tac (srw_ss()) [EVERY_APPEND] >>
  conj_tac
  >- (drule emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def]) >>
  Cases_on `n` >> gvs[compile_copy_memory_def, comp_return_def, emitted_insts_def] >>
  drule emitted_insts_emit_void >>
  simp[mk_inst_def, is_terminator_def, DROP_APPEND]
QED

Theorem compile_scratch_prefix_body_frag_mem:
  !ctx func ce cx es s sa sm sn buf src n sw tv v d R.
    compile_alloc_buffer n sa = (buf,sm) /\
    compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
    fn_has_code sa sn func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
    alloca_history func s /\ return_buf_frame d ce sa s /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ n < dimword (:256) /\
    w2n sw + n <= s.vs_alloca_next /\
    val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= n ==>
    frag_exec_mem ctx sa sn (\u. u = s)
      (\t. stmt_state_rel ctx func ce cx es t /\ alloca_history func t /\
        return_buf_frame d ce sn t /\ s.vs_alloca_next <= t.vs_alloca_next /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        val_wf tv v /\ ?w. eval_operand buf.buf_operand t = SOME w /\
          val_in_memory tv v (w2n w) t.vs_memory /\
          w2n w + n <= t.vs_alloca_next) R
Proof
  rpt gen_tac >> strip_tac >>
  drule_all body_scratch_prefix_shape >> strip_tac >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  drule_all body_scratch_prefix_run >> strip_tac >>
  `run_inst_seq (emitted_insts sa sn) s = OK t` by
    (asm_rewrite_tac[] >>
     qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = OK a`
       (mp_tac o MATCH_MP run_inst_seq_append) >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sn) s` by
    (asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[] >>
     rpt strip_tac >> gvs[]) >>
  `return_buf_frame d ce sn t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`, `s`, `sa`] >> simp[]) >>
  fs[same_blocks_def] >> irule body_decl_frag_at_cursor >>
  asm_simp_tac (srw_ss()) [IS_PREFIX_APPEND] >> rpt strip_tac >> gvs[] >>
  simp[stmt_state_rel_inst_idx] >> conj_tac
  >- (`alloca_inv s` by fs[stmt_state_rel_def] >>
      `alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)` by
        (irule body_store_memory_history >> simp[] >> qexistsl_tac [`s`, `sa`] >>
         simp[same_blocks_def]) >>
      gvs[]) >>
  conj_tac
  >- (Cases_on `d` >- fs[return_buf_frame_def] >>
      rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
      fs[return_buf_frame_def, lookup_var_def]) >>
  fs[lookup_var_def]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_SCRATCH_PREFIX_MEMORY_AUDIT OK\n"
     else raise Fail "body scratch prefix inherited admission"
  end) [body_scratch_alloc_operand, body_scratch_copy_state,
        body_scratch_prefix_run, body_scratch_prefix_shape,
        compile_scratch_prefix_body_frag_mem];
