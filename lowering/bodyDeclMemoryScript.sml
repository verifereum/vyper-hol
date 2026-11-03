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
  exprSimLiteralBuffer exprSimAlloc exprSimBuffer finite_map bodySimDeclCases allocLimits
  bodySim exprSimHyps vyperTypeSystem vyperTypeInvariants memoryLocalRhsProps
  supportedStmtTraverse supportedExprTraverse vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperInterpreter vyperState

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
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
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

Theorem annassign_memory_assign_body_frag_mem:
  !ctx func cenv cx es s id p sz w inst v tyv sc rest a src ty sa sb sw d R info bytes.
    compile_assign_value cenv (Var p) LocMemory src F (SOME LocMemory)
      ty ty info bytes sa = ((), sb) /\
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
  rpt gen_tac >> strip_tac >> drule_all assign_memory_body_code >> strip_tac >>
  `cs_extends sa sn` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sn func` by metis_tac[fn_has_code_split] >>
  `val_footprint tyv v <= type_memory_bytes cenv ty` by
    (drule val_footprint_le >> simp[]) >>
  `type_memory_bytes cenv ty < dimword (:256)` by decide_tac >>
  `w2n sw + type_memory_bytes cenv ty <= s.vs_alloca_next` by simp[] >>
  drule_all compile_scratch_prefix_body_frag_mem >>
  disch_then (qspec_then `R` mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_then) >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  `sa.cs_next_var <= sn.cs_next_var` by
    (drule_all body_scratch_prefix_shape >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sn x` by
    metis_tac[not_fresh_at_mono] >>
  `local_ptrs_reserved cenv sn` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sn x` by
    (drule body_scratch_alloc_operand >> strip_tac >>
     drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule buffer_copy_memory_shape >> strip_tac >>
     qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[not_fresh_at_def]) >>
  `lookup_var p t = SOME w /\
   FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
   w2n w + type_memory_size tyv <= t.vs_alloca_next` by
    (simp[] >> decide_tac) >>
  `w2n w' + type_memory_size tyv <= t.vs_alloca_next` by decide_tac >>
  `not_fresh_at sn p` by simp[] >>
  drule_all annassign_memory_store_body_frag_mem >>
  disch_then (qspecl_then [`a`, `R`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
  disch_then irule >> simp[] >> rpt strip_tac
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_DECL_ASSIGN_MEMORY_AUDIT OK\n"
     else raise Fail "body declaration assignment inherited admission"
  end) [assign_memory_body_code, annassign_memory_assign_body_frag_mem];

Theorem annassign_setup_shape:
  declare_local ce id ty sa = (c,st) /\ ce.ce_alloca_locals /\
  lookup_scopes id es.scopes = NONE /\
  (!l. FLOOKUP ce.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz) /\
  p = STRING #"%" (toString sa.cs_next_var) /\
  emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p] st = ((),sA) /\
  fn_has_code sa sA func /\ local_ptrs_reserved ce sa ==>
  st = sa with cs_next_var := sa.cs_next_var + 1 /\
  FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes ce ty)) /\
  c.ce_return_buf = ce.ce_return_buf /\
  not_local_ptr c es.scopes p /\
  (!x. not_fresh_at sa x ==> x <> p) /\
  local_ptrs_reserved c sA /\ not_fresh_at sA p /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p])
    (fn_insts func)
Proof
  rpt gen_tac >> strip_tac >> drule_all declare_local_ptr >> strip_tac >>
  `cs_extends sA sA` by simp[cs_extends_def] >>
  `fn_has_code st sA func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  gvs[] >> drule_all annassign_alloca_code >> strip_tac >>
  `c.ce_return_buf = ce.ce_return_buf` by
    (qpat_x_assum `c with <|ce_vars := _; ce_dynarray_capacity := _; ce_var_type := _|> = ce` mp_tac >>
     simp[compile_env_component_equality] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (simp[not_local_ptr_def] >> rpt strip_tac >>
      Cases_on `name = id` >> gvs[] >>
      fs[local_ptrs_reserved_def, not_fresh_at_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[not_fresh_at_def]
QED

Theorem body_decl_alloca_run[local]:
  stmt_state_rel ctx func c cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w sz)] /\ inst.inst_outputs = [p] /\
  not_local_ptr c es.scopes p /\ sz < dimword (:256) ==>
  ?t w. exec_alloca inst s (n2w sz : bytes32) = OK t /\
    stmt_state_rel ctx func c cx es t /\ lookup_var p t = SOME w /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    w2n w + sz <= t.vs_alloca_next /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!x. x <> p ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)
Proof
  rpt gen_tac >> strip_tac >>
  `?t. exec_alloca inst s (n2w sz : bytes32) = OK t` by
    (Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >>
     simp[exec_alloca_def] >> PairCases_on `x` >> simp[exec_alloca_def]) >>
  drule_all stmt_state_rel_exec_alloca >> strip_tac >>
  `w2n w + sz <= t.vs_alloca_next` by
    (fs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.alloca_next_valid_def] >>
     gvs[wordsTheory.w2n_n2w] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexistsl_tac [`t`, `w`] >> simp[] >>
  qpat_x_assum `exec_alloca _ _ _ = OK t` mp_tac >>
  simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `inst.inst_id = aid` >> gvs[]
QED

Theorem annassign_setup_body_frag_mem:
  !ctx func ce c cx es s sa st sA id ty p d R.
    declare_local ce id ty sa = (c,st) /\ ce.ce_alloca_locals /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP ce.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz) /\
    p = STRING #"%" (toString sa.cs_next_var) /\
    emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p] st = ((),sA) /\
    type_memory_bytes ce ty < dimword (:256) /\
    fn_has_code sa sA func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
    alloca_history func s /\ return_buf_frame d ce sa s ==>
    frag_exec_mem ctx sa sA (\u. u = s)
      (\t. stmt_state_rel ctx func c cx es t /\ alloca_history func t /\
        return_buf_frame d c sA t /\ s.vs_alloca_next <= t.vs_alloca_next /\
        local_ptrs_reserved c sA /\ not_fresh_at sA p /\
        FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes ce ty)) /\
        not_local_ptr c es.scopes p /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
        ?w. lookup_var p t = SOME w /\
          FLOOKUP t.vs_allocas st.cs_next_id = SOME (w2n w,type_memory_bytes ce ty) /\
          w2n w + type_memory_bytes ce ty <= t.vs_alloca_next) R
Proof
  rpt gen_tac >> strip_tac >> drule_all annassign_setup_shape >> strip_tac >>
  `stmt_state_rel ctx func c cx es s` by metis_tac[stmt_state_rel_declare_local_entry] >>
  qabbrev_tac `A = mk_inst st.cs_next_id ALLOCA
    [Lit (n2w (type_memory_bytes ce ty))] [p]` >>
  `A.inst_opcode = ALLOCA /\ A.inst_operands = [Lit (n2w (type_memory_bytes ce ty))] /\
   A.inst_outputs = [p] /\ A.inst_id = st.cs_next_id` by simp[Abbr `A`, mk_inst_def] >>
  drule_all body_decl_alloca_run >> strip_tac >>
  `sa.cs_next_var <= sA.cs_next_var` by
    (drule emit_inst_extends >> gvs[]) >>
  `return_buf_frame d c sA t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`, `s`, `sa`] >> simp[]) >>
  `emitted_insts sa sA = [A] /\ same_blocks sa sA /\
   sA.cs_current_insts = sa.cs_current_insts ++ [A]` by
    (drule emit_inst_extends >> strip_tac >>
     gvs[emitted_insts_def, same_blocks_def, Abbr `A`, DROP_LENGTH_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sA)` by simp[is_terminator_def] >>
  irule body_decl_frag_at_cursor >> fs[same_blocks_def, IS_PREFIX_APPEND] >>
  rpt strip_tac >> gvs[]
  >- (simp[run_inst_seq_mem_ok_last] >> irule instMemFrontierTheory.below_frontier_no_ranges >> simp[Abbr `A`, mk_inst_def]) >>
  `run_inst_seq (emitted_insts sa sA) s = OK t` by
    (gvs[mk_inst_def] >> simp[run_inst_seq_def, step_inst_base_def]) >>
  `alloca_history func (t with vs_inst_idx := LENGTH sA.cs_current_insts)` by
    (irule body_store_memory_history >> simp[same_blocks_def] >>
     qexistsl_tac [`s`, `sa`] >> simp[] >> fs[stmt_state_rel_def]) >>
  `return_buf_frame d c sA (t with vs_inst_idx := LENGTH sA.cs_current_insts)` by
    (Cases_on `d` >- fs[return_buf_frame_def] >>
     rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
     fs[return_buf_frame_def, lookup_var_def]) >>
  qexists_tac `t` >> gvs[stmt_state_rel_inst_idx, lookup_var_def] >>
  rpt strip_tac >> first_x_assum irule >> strip_tac >> gvs[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_DECL_SETUP_MEMORY_AUDIT OK\n"
     else raise Fail "body declaration setup inherited admission"
  end) [annassign_setup_shape, body_decl_alloca_run, annassign_setup_body_frag_mem];

Theorem annassign_name_rhs_body_frag_mem:
  !ctx func cenv cx env source_id es s id p sz w inst v tyv sc rest a src ty sa sm sb d R info bytes.
    lower_value compile_expr cenv ty (Name ty source_id) sa = (src,sm) /\
    expr_sim_pre cenv cx env (Name ty source_id) es /\
    (do result <- eval_expr cx (Name ty source_id); read_result cx result od) es = (INL v,es) /\
    compile_assign_value cenv (Var p) LocMemory src F (SOME LocMemory)
      ty ty info bytes sm = ((), sb) /\
    not_fresh_at sa p /\ lookup_var p s = SOME w /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    type_memory_size tyv <= sz /\ type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
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
  drule_all bodyAllocMemoryTheory.body_name_source_region >> strip_tac >>
  drule_then (qspecl_then [`cx`, `ty`] assume_tac) eval_name_word >> gvs[] >>
  gvs[lower_value_def, compile_expr_def, compile_name_vv_def,
      comp_bind_def, comp_return_def, unwrap_value_def,
      contextTheory.mk_ptr_def, vyperASTTheory.expr_type_def] >>
  irule annassign_memory_assign_body_frag_mem >> simp[] >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[eval_operand_def] >>
  qexists_tac `inst` >> simp[] >>
  fs[local_ptrs_reserved_def] >> metis_tac[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_DECL_NAME_RHS_MEMORY_AUDIT OK\n"
     else raise Fail "body declaration Name RHS inherited admission"
  end) [annassign_name_rhs_body_frag_mem];

Theorem body_annassign_name_compiler_parts[local]:
  !c lctx ret_ty id typ source_id p sz st sb.
    compile_stmt c lctx ret_ty (AnnAssign id typ (Name typ source_id)) st = ((),sb) /\
    FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz) /\ ~is_word_type typ ==>
    ?sA sV sB vv op.
      emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((),sA) /\
      compile_expr c typ (Name typ source_id) sA = (vv,sV) /\
      unwrap_value c vv sV = (op,sB) /\
      lower_value compile_expr c typ (Name typ source_id) sA = (op,sB) /\
      compile_assign_value c (Var p) LocMemory op F (vv_location vv)
        typ (lowered_value_type c (Name typ source_id))
        (case typ of ArrayT elem_ty (Dynamic _) =>
          SOME ((type_memory_bytes c elem_ty + 31) DIV 32,type_memory_bytes c elem_ty)
        | _ => NONE) (type_memory_bytes c typ) sB = ((),sb)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, emit_local_alloca_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, is_empty_value_expr_def,
       vyperASTTheory.expr_type_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  imp_res_tac emit_inst_unit >>
  gvs[lower_value_def, comp_bind_def] >> metis_tac[]
QED

Theorem body_name_nonword_compile[local]:
  expr_sim_pre ce cx env (Name ty name) es /\ ~is_word_type ty ==>
  ?p sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
    !sa. lower_value compile_expr ce ty (Name ty name) sa = (Var p,sa)
Proof
  rpt strip_tac >>
  `?p sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  qexistsl_tac [`p`, `sz`] >>
  simp[lower_value_def, compile_expr_def, compile_name_vv_def,
       comp_bind_def, comp_return_def, unwrap_value_def,
       contextTheory.mk_ptr_def, vyperASTTheory.expr_type_def]
QED

Theorem body_annassign_read_eval[local]:
  evaluate_type (get_tenv cx) ty = SOME tyv /\
  (do tv <- eval_expr cx e; read_result cx tv od) es = (INL v,es) /\
  lookup_scopes id es.scopes = NONE /\ es.scopes = sc :: rest ==>
  eval_stmt cx (AnnAssign id ty e) es =
    (INL (), es with scopes :=
      (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest)
Proof
  strip_tac >>
  qpat_x_assum `(do tv <- _; _ od) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
       lift_option_type_def] >>
  Cases_on `eval_expr cx e es` >> Cases_on `q` >> simp[] >>
  Cases_on `read_result cx x r` >> Cases_on `q` >> simp[] >>
  strip_tac >> gvs[] >>
  simp[new_variable_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, set_scopes_def, return_def]
QED

Theorem body_annassign_name_exec[local]:
  declare_local ce id ty sa = (c,st) /\ ce.ce_alloca_locals /\
  lookup_scopes id es.scopes = NONE /\ FLOOKUP ce.ce_vars id = NONE /\
  p = STRING #"%" (toString sa.cs_next_var) /\
  emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p] st = ((),sA) /\
  (!u. lower_value compile_expr c ty (Name ty source_id) u = (src,u)) /\
  compile_assign_value c (Var p) LocMemory src F (SOME LocMemory)
    ty ty info bytes sA = ((),sb) /\
  expr_sim_pre c cx env (Name ty source_id) es /\
  (do result <- eval_expr cx (Name ty source_id); read_result cx result od) es = (INL v,es) /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
  type_memory_bytes c ty = type_memory_size tyv /\
  type_memory_bytes ce ty = type_memory_size tyv /\
  type_memory_size tyv + 64 < dimword (:256) /\ es.scopes = sc :: rest /\
  fn_has_code sa sA func /\ fn_has_code sA sb func /\
  cs_extends sa sA /\ cs_extends sA sb /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
  alloca_history func s /\ return_buf_frame d ce sa s ==>
  frag_exec_mem ctx sa sb (\u. u = s)
    (\t. stmt_state_rel ctx func c cx
        (es with scopes :=
          (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest) t /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      return_buf_frame d c sb t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)) R
Proof
  strip_tac >>
  `type_memory_bytes ce ty < dimword (:256)` by decide_tac >>
  `!l. FLOOKUP ce.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz` by simp[] >>
  drule_all annassign_setup_shape >> strip_tac >>
  drule_all annassign_setup_body_frag_mem >>
  disch_then (qspec_then `R` mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_then) >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `MEM A (fn_insts func)` >>
  `A.inst_opcode = ALLOCA /\
   A.inst_outputs = [STRING #"%" (toString sa.cs_next_var)] /\
   A.inst_id = sa.cs_next_id` by simp[Abbr `A`, mk_inst_def] >>
  `w2n w + type_memory_size tyv <= t.vs_alloca_next` by decide_tac >>
  `lower_value compile_expr c ty (Name ty source_id) sA = (src,sA) /\
   lookup_scopes id es.scopes = NONE /\
   not_local_ptr c es.scopes (STRING #"%" (toString sa.cs_next_var)) /\
   FLOOKUP t.vs_allocas A.inst_id = SOME (w2n w,type_memory_size tyv) /\
   type_memory_size tyv <= type_memory_size tyv` by simp[] >>
  `sa.cs_next_var <= sA.cs_next_var` by
    (drule emit_inst_extends >> simp[] >> decide_tac) >>
  drule_all annassign_name_rhs_body_frag_mem >>
  disch_then (qspecl_then [`T`, `R`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  metis_tac[not_fresh_at_mono]
QED

Theorem body_annassign_name_prepare[local]:
  body_inv tops ctx ce cx /\
  supported_stmt tops bindings (AnnAssign id ty (Name ty source_id)) /\
  expr_sim_inv ce cx env es /\ ce_locals_declared ce env /\
  locals_alloc_ok ce env /\
  type_stmt env ret_ty (AnnAssign id ty (Name ty source_id)) = SOME env' /\
  stmt_exprs_ok ce (AnnAssign id ty (Name ty source_id)) /\
  call_evaluation_safe cx (int_calls_stmt (AnnAssign id ty (Name ty source_id))) /\
  eval_stmt cx (AnnAssign id ty (Name ty source_id)) es = (res,es') /\
  ~is_word_type ty /\ 0 < type_memory_bytes ce ty /\
  stmt_env ce lctx ret_ty (AnnAssign id ty (Name ty source_id)) sa = (c,sb) ==>
  ?tyv v sc rest st sA src info.
    res = INL () /\
    es' = es with scopes :=
      (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest /\
    es.scopes = sc :: rest /\ cenv_top_ext ce c es'.scopes /\
    ce.ce_alloca_locals /\ FLOOKUP ce.ce_vars id = NONE /\
    lookup_scopes id es.scopes = NONE /\
    declare_local ce id ty sa = (c,st) /\
    emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))]
      [STRING #"%" (toString sa.cs_next_var)] st = ((),sA) /\
    (!u. lower_value compile_expr c ty (Name ty source_id) u = (src,u)) /\
    compile_assign_value c (Var (STRING #"%" (toString sa.cs_next_var)))
      LocMemory src F (SOME LocMemory) ty ty info (type_memory_bytes ce ty) sA = ((),sb) /\
    expr_sim_pre c cx env (Name ty source_id) es /\
    (do result <- eval_expr cx (Name ty source_id); read_result cx result od) es = (INL v,es) /\
    evaluate_type (get_tenv cx) ty = SOME tyv /\
    type_memory_bytes c ty = type_memory_size tyv /\
    type_memory_bytes ce ty = type_memory_size tyv /\
    type_memory_size tyv + 64 < dimword (:256)
Proof
  strip_tac >>
  `FLOOKUP ce.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `well_typed_expr env (Name ty source_id) /\ assignable_type env.type_defs ty /\
   id NOTIN FDOM env.var_types` by gvs[type_stmt_def, AllCaseEqs()] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) ty = SOME tyv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def,
              optionTheory.IS_SOME_EXISTS] >>
  `ce.ce_alloca_locals` by fs[body_inv_def] >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  `type_memory_bytes ce ty = type_memory_size tyv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_bytes ce ty < 2 ** 64` by
    gvs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `type_memory_size tyv + 64 < dimword (:256)` by
    metis_tac[allocation_limit_word_room] >>
  `expr_sim_pre ce cx env (Name ty source_id) es` by
    (gvs[expr_sim_pre_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
         expr_has_evm_run_def, supported_expr_exists_def, expr_evm_run_root_def,
         call_evaluation_safe_def] >> metis_tac[]) >>
  drule stmt_env_annassign >> strip_tac >>
  `same_frame ce c` by
    (drule_then irule declare_local_same_frame >> simp[]) >>
  `expr_sim_inv c cx env es` by metis_tac[expr_sim_inv_declare_local] >>
  `c.ce_struct_fields = ce.ce_struct_fields` by
    fs[same_frame_def, compile_env_component_equality] >>
  `type_memory_bytes c = type_memory_bytes ce` by
    (irule allocLimitsPropsTheory.type_memory_bytes_frame >> simp[]) >>
  `expr_sim_pre c cx env (Name ty source_id) es` by
    gvs[expr_sim_pre_def, alloc_limits_expr_def, type_alloc_ok_def] >>
  drule_all declare_local_ptr >> strip_tac >>
  drule_all body_annassign_name_compiler_parts >> strip_tac >>
  `?entry. lookup_scopes source_id es.scopes = SOME entry /\
     evaluate_type (get_tenv cx) ty = SOME entry.type /\
     value_has_type entry.type entry.value` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     drule_all vyperTypeEnvTheory.well_typed_Name_lookup >> strip_tac >>
     gvs[env_consistent_def, env_context_consistent_def]) >>
  drule_all body_name_nonword_compile >> strip_tac >>
  `sB = sA` by (qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >> simp[]) >>
  `sV = sA /\ vv_location vv = SOME LocMemory /\
   lowered_value_type c (Name ty source_id) = ty` by
    (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
     simp[compile_expr_def, compile_name_vv_def, comp_return_def,
          vyperASTTheory.expr_type_def, contextTheory.mk_ptr_def,
          vv_location_def, lowered_value_type_def] >>
     rpt strip_tac >> gvs[vv_location_def]) >>
  `(do result <- eval_expr cx (Name ty source_id); read_result cx result od) es =
    (INL entry.value,es)` by (irule eval_name_word >> simp[]) >>
  `?sc rest. es.scopes = sc :: rest` by
    (Cases_on `es.scopes` >> gvs[lookup_scopes_def]) >>
  drule_all body_annassign_read_eval >> strip_tac >>
  `res = INL ()` by (qpat_x_assum `eval_stmt _ _ _ = (res,es')` mp_tac >> simp[]) >>
  qpat_x_assum `eval_stmt _ _ _ = (res,es')` mp_tac >> simp[] >> strip_tac >>
  `cenv_top_ext ce c es'.scopes` by
    (irule annassign_word_top_ext >> simp[] >>
     goal_assum (drule_at (Pat `declare_local _ _ _ _ = _`)) >>
     simp[] >> qexistsl_tac [`cx`, `Name ty source_id`, `es`] >> simp[]) >>
  gvs[] >> goal_assum (drule_at Any)
QED

Theorem body_annassign_name_code[local]:
  declare_local ce id ty sa = (c,st) /\ ce.ce_alloca_locals /\
  FLOOKUP ce.ce_vars id = NONE /\ local_ptrs_reserved ce sa /\
  emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))]
    [STRING #"%" (toString sa.cs_next_var)] st = ((),sA) /\
  compile_assign_value c (Var (STRING #"%" (toString sa.cs_next_var)))
    LocMemory src F (SOME LocMemory) ty ty info bytes sA = ((),sb) /\
  0 < type_memory_bytes c ty /\ fn_has_code sa sb func ==>
  cs_extends sa sA /\ cs_extends sA sb /\
  fn_has_code sa sA func /\ fn_has_code sA sb func /\ ~block_is_terminated sb
Proof
  strip_tac >>
  `!l. FLOOKUP ce.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz` by simp[] >>
  drule_all declare_local_ptr >> strip_tac >>
  `cs_extends sA sb` by
    (irule (SRULE [cs_appends_def] compile_assign_memory_widen_appends) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `fn_has_code st sb func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  drule_all annassign_alloca_code >> strip_tac >>
  `cs_extends sa sA` by
    (drule emit_inst_extends >> strip_tac >> gvs[cs_extends_def]) >>
  simp[] >> conj_tac
  >- gvs[fn_has_code_def, emitted_blocks_def] >>
  irule compile_assign_value_memory_same_open >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >> simp[]
QED

Theorem body_decl_normal_landing[local]:
  frag_exec_mem ctx sa sb (\u. u = s0)
    (\s. stmt_state_rel ctx func c cx es' s /\ alloca_history func s /\
      s0.vs_alloca_next <= s.vs_alloca_next /\ return_buf_frame d c sb s /\
      (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x s0) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b)) (\r. F) /\
  fn_has_code sa sb func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~block_is_terminated sb /\ cenv_top_ext ce c es'.scopes ==>
  ?s c'. stmt_lands lctx sb (INL ()) s /\ ~s.vs_halted /\
    (~block_is_terminated sb /\ c' = c) /\
    cenv_top_ext ce c' es'.scopes /\ stmt_state_rel ctx func c' cx es' s /\
    alloca_history func s /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    return_buf_frame d c' sb s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    !fuel r. run_from fuel ctx func s = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx func s0 = r /\
        (mem_safe_run fuel ctx func s ==> mem_safe_run fuel' ctx func s0)
Proof
  strip_tac >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_mem_def] >>
  disch_then (qspec_then `func` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `s` >> simp[stmt_lands_def] >> metis_tac[]
QED

Theorem body_annassign_name_mem:
  !d tops bindings ctx func cenv cx env env' ret_ty lctx RetQ id typ source_id es res es'.
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ (Name typ source_id)) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AnnAssign id typ (Name typ source_id)) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ (Name typ source_id)) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ (Name typ source_id))) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    eval_stmt cx (AnnAssign id typ (Name typ source_id)) es = (res,es') /\
    ~is_word_type typ /\ 0 < type_memory_bytes cenv typ ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ (Name typ source_id))) es res es'
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all body_annassign_name_prepare >> strip_tac >>
  `0 < type_memory_bytes cenv' typ` by decide_tac >>
  drule_all body_annassign_name_code >> strip_tac >>
  `STRING #"%" (toString sa.cs_next_var) = STRING #"%" (toString sa.cs_next_var)` by simp[] >>
  drule_all body_annassign_name_exec >>
  disch_then (qspec_then `(\r. F)` mp_tac) >>
  strip_tac >> gvs[] >> disj1_tac >>
  drule body_decl_normal_landing >> simp[] >>
  disch_then (qspecl_then [`lctx`, `cenv`] mp_tac) >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_DECL_NAME_CONSUMER_MEMORY_AUDIT OK\n"
     else raise Fail "body declaration Name consumer inherited admission"
  end) [body_annassign_name_exec, body_annassign_name_prepare,
        body_annassign_name_code, body_decl_normal_landing, body_annassign_name_mem];
