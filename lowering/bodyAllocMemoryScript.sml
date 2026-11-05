(* Actual body allocation sites: membership and reused-site size. *)
Theory bodyAllocMemory
Ancestors
  exprSimSource exprSimProps
  builtinBytesMemory allocaFootprint abiBuiltinAllocation exprLoweringProps exprLowering
  exprSimAggregateChildren exprSimLiteralBuffer exprSimAlloc exprSimOps instMemFrontier
  fragExec fragExecMem allocaHistoryFragment rich_list
  bodyMemoryDefs loweringSlice exprSimDefs exprSimOperators exprSimHyps stmtSimAugAssign vyperTypeEnv vyperTypeSystem vyperTypeInvariants
  emitHelperProps emitHelper compileEnv context venomInst venomState
  venomExecSemantics venomMemDefs vyperInterpreter vyperState list finite_map words arithmetic

Theorem compile_alloc_buffer_body_inst[local]:
  !n sa buf sb func.
    compile_alloc_buffer n sa = (buf,sb) /\
    fn_has_code sa sb func /\ ~block_is_terminated sa ==>
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
          [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  rpt gen_tac >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, fresh_var_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  fs[get_instruction_def] >> metis_tac[EL_MEM]
QED

Theorem compile_alloc_buffer_body_site:
  !ctx func cenv cx es s n sa buf sb.
    compile_alloc_buffer n sa = (buf,sb) /\
    fn_has_code sa sb func /\ ~block_is_terminated sa /\
    stmt_state_rel ctx func cenv cx es s /\ n < dimword (:256) ==>
    ?p. FLOOKUP (abi_builtin_allocate_state sa.cs_next_id n s).vs_allocas
          sa.cs_next_id = SOME (p,n)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_alloc_buffer_body_inst >> strip_tac >>
  simp[alloca_site_cases] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
  >- simp[] >>
  PairCases_on `x` >>
  fs[stmt_state_rel_def] >>
  qpat_x_assum `!inst n base sz. _` drule >>
  simp[mk_inst_def]
QED

Theorem compile_alloc_buffer_body_header_mem_ok:
  !ctx func cenv cx es s n sa buf sm value sb.
    compile_alloc_buffer n sa = (buf,sm) /\
    emit_void MSTORE [buf.buf_operand; value] sm = ((),sb) /\
    fn_has_code sa sm func /\ ~block_is_terminated sa /\
    stmt_state_rel ctx func cenv cx es s /\ fresh_vars_wrt sa s /\
    32 <= n /\ n < dimword (:256) ==>
    run_inst_seq_mem_ok
      (emitted_insts sa sm ++ emitted_insts sm sb) s
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_alloc_buffer_body_site >> strip_tac >>
  `alloca_next_valid s` by fs[stmt_state_rel_def, alloca_inv_def] >>
  irule compile_alloc_buffer_header_store_mem_ok >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem compile_alloc_buffer_body_frontier:
  !ctx func cenv cx es s n sa buf sb.
    compile_alloc_buffer n sa = (buf,sb) /\
    fn_has_code sa sb func /\ ~block_is_terminated sa /\
    stmt_state_rel ctx func cenv cx es s /\ n < dimword (:256) ==>
    s.vs_alloca_next <=
      (abi_builtin_allocate_state sa.cs_next_id n s).vs_alloca_next
Proof
  rpt strip_tac >> simp[abi_builtin_allocate_state_def] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id = NONE` >> simp[]
QED

Theorem compile_alloc_buffer_body_header_slice:
  !n sa buf sm value sb func s.
    compile_alloc_buffer n sa = (buf,sm) /\
    emit_void MSTORE [buf.buf_operand; value] sm = ((),sb) /\
    fn_has_code sa sb func /\ ~block_is_terminated sa /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
       DROP s.vs_inst_idx bb.bb_instructions =
         (emitted_insts sa sm ++ emitted_insts sm sb) ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sm ++ emitted_insts sm sb) =
      LENGTH sb.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sm ++ emitted_insts sm sb)
Proof
  rpt gen_tac >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def,
      emitted_insts_def, fn_has_code_def, IS_PREFIX_APPEND] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def, is_terminator_def]
QED

Theorem compile_alloc_buffer_body_header_run_mem:
  !ctx func cenv cx es s n sa buf sm value sb.
    compile_alloc_buffer n sa = (buf,sm) /\
    emit_void MSTORE [buf.buf_operand; value] sm = ((),sb) /\
    fn_has_code sa sb func /\ ~block_is_terminated sa /\
    stmt_state_rel ctx func cenv cx es s /\ fresh_vars_wrt sa s /\
    32 <= n /\ n < dimword (:256) /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (!t fuel. run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK t /\
      mem_safe_run fuel ctx func (t with vs_inst_idx := LENGTH sb.cs_current_insts) ==>
      mem_safe_run fuel ctx func s) /\
    (!a t fuel. run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = Abort a t ==>
      mem_safe_run fuel ctx func s)
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, fresh_var_def, emit_def,
         cs_extends_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all compile_alloc_buffer_body_header_mem_ok >> strip_tac >>
  drule_all compile_alloc_buffer_body_header_slice >> strip_tac >>
  `isPREFIX (emitted_insts sa sm ++ emitted_insts sm sb)
     (DROP s.vs_inst_idx bb.bb_instructions)` by simp[IS_PREFIX_APPEND] >>
  conj_tac >> rpt gen_tac >> strip_tac >>
  drule_all mem_safe_run_inst_seq >> simp[]
QED

Theorem compile_alloc_buffer_body_header_history:
  !ctx func cenv cx es s n sa buf sm value sb t.
    compile_alloc_buffer n sa = (buf,sm) /\
    emit_void MSTORE [buf.buf_operand; value] sm = ((),sb) /\
    fn_has_code sa sb func /\ ~block_is_terminated sa /\
    stmt_state_rel ctx func cenv cx es s /\ fresh_vars_wrt sa s /\
    32 <= n /\ n < dimword (:256) /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    fn_inst_ids_distinct func /\ alloca_history func s /\
    run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK t ==>
    alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_alloc_buffer_body_header_slice >> strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
     (emitted_insts sa sm ++ emitted_insts sm sb)` by fs[EVERY_MEM] >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem compile_alloc_buffer_body_mem_ok:
  !n sa buf sb func ctx cenv cx es s.
    compile_alloc_buffer n sa = (buf,sb) /\
    fn_has_code sa sb func /\ ~block_is_terminated sa /\
    stmt_state_rel ctx func cenv cx es s /\ fresh_vars_wrt sa s /\
    n < dimword (:256) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_alloc_buffer_body_site >> strip_tac >>
  `alloca_next_valid s` by fs[stmt_state_rel_def, alloca_inv_def] >>
  drule_all compile_alloc_buffer_mem_ok >> simp[]
QED

Theorem frag_exec_mem_run_inst_seq_at_cursor[local]:
  !ctx st st' P Q R.
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    isPREFIX st.cs_current_insts st'.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st st') /\
    (!s. P s /\ ~s.vs_halted /\
       s.vs_current_bb = st.cs_current_bb /\
       s.vs_inst_idx = LENGTH st.cs_current_insts ==>
       run_inst_seq_mem_ok (emitted_insts st st') s /\
       ((?t. run_inst_seq (emitted_insts st st') s = OK t /\
              Q (t with vs_inst_idx := LENGTH st'.cs_current_insts)) \/
        (?a t. run_inst_seq (emitted_insts st st') s = Abort a t /\
                !n. R (Abort a (t with vs_inst_idx := n))))) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `P' = \s. P s /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts` >>
  `frag_exec_mem ctx st st' P' Q R` by
    (irule frag_exec_mem_run_inst_seq >> simp[Abbr `P'`]) >>
  fs[frag_exec_mem_def, Abbr `P'`] >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem compile_alloc_buffer_body_history[local]:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  ~block_is_terminated sa /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, fresh_var_def, emit_def,
         emitted_insts_def, fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def, is_terminator_def]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem compile_alloc_buffer_body_frag_mem:
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  sz < dimword (:256) /\ ~block_is_terminated sa ==>
  ?inst x. buf.buf_operand = Var x /\ MEM inst (fn_insts func) /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [x] /\
    inst.inst_id < sm.cs_next_id /\ not_fresh_at sm x /\
    local_ptrs_reserved ce sm /\ (!scopes. not_local_ptr ce scopes x) /\
    frag_exec_mem ctx sa sm
      (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s /\ alloca_history func s)
      (\t. ?b. stmt_state_rel ctx func ce cx es t /\
        lookup_var x t = SOME (n2w b) /\
        FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) /\
        b + sz < dimword (:256) /\ t.vs_memory = s0.vs_memory /\
        (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s0) /\
        (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
          FLOOKUP t.vs_allocas aid = SOME a) /\
        (!aid p n. aid < sa.cs_next_id /\
          FLOOKUP s0.vs_allocas aid = SOME (p,n) ==>
          regions_disjoint b sz p n) /\
        (!name p n. local_region ce es.scopes t name p n ==>
          regions_disjoint b sz p n) /\
        (!name p n. local_region ce es.scopes t name p n <=>
          local_region ce es.scopes s0 name p n) /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next) R
Proof
  rpt strip_tac >> drule_all buffer_alloc_provenance >> strip_tac >>
  qexistsl [`inst`,`x`] >> simp[] >>
  irule frag_exec_mem_run_inst_seq_at_cursor >> simp[] >>
  rpt strip_tac >> gvs[]
  >- (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
      drule emitted_insts_emit_op >> strip_tac >>
      gvs[run_inst_seq_mem_ok_last] >>
      irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  drule_all compile_alloc_buffer_body_inst >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `!name p n. local_region ce es.scopes t name p n <=>
    local_region ce es.scopes s0 name p n` by
    (rpt gen_tac >> eq_tac
     >- (strip_tac >> irule local_region_frame >> conj_tac
         >- (qexists_tac `func` >>
             gvs[stmt_state_rel_def, state_rel_def]) >>
         qexistsl [`sa`, `es.scopes`, `t`] >> simp[]) >>
     metis_tac[local_region_frame_fwd]) >>
  `alloca_history func (t with vs_inst_idx := LENGTH sm.cs_current_insts)` by
    (irule compile_alloc_buffer_body_history >>
     simp[] >> qexistsl [`buf`, `sz`, `s0`, `sa`] >>
     simp[] >> fs[stmt_state_rel_def]) >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     qpat_x_assum `run_inst_seq _ _ = OK t` mp_tac >>
     simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
          exec_alloca_def, eval_operand_def] >>
     Cases_on `FLOOKUP s0.vs_allocas sa.cs_next_id` >>
     simp[update_var_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  `!name p n. local_region ce es.scopes
      (t with vs_inst_idx := LENGTH sm.cs_current_insts) name p n <=>
      local_region ce es.scopes t name p n` by
    simp[NoAsms, local_region_def, lookup_var_def] >>
  disj1_tac >> goal_assum (drule_at Any) >>
  simp[stmt_state_rel_inst_idx, lookup_var_def] >>
  gvs[eval_operand_def, lookup_var_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!aid b len. aid < _ /\ _ ==> regions_disjoint _ _ _ _` irule >>
      qexists_tac `aid` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` irule >>
  qexists_tac `name` >> simp[]
QED

Theorem compile_mapping_subscript_body_mem_ok:
  compile_mapping_subscript base_slot key_op sa = (op,sb) /\
  fn_has_code sa sb func /\ ~block_is_terminated sa /\
  stmt_state_rel ctx func cenv cx es s /\ fresh_vars_wrt sa s /\
  eval_operand base_slot s = SOME b /\ eval_operand key_op s = SOME k ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >>
  `?buf sm. compile_alloc_buffer 64 sa = (buf,sm) /\
     fn_has_code sa sm func` by
    (qpat_x_assum `compile_mapping_subscript _ _ _ = _` mp_tac >>
     simp[compile_mapping_subscript_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >>
     strip_tac >>
     rename1 `compile_alloc_buffer 64 sa = (buf,sm)` >>
     `cs_extends sa sm /\ cs_extends sm sb` by
       (gvs[compile_alloc_buffer_def, emit_op_def, emit_void_def,
            comp_bind_def, comp_ignore_bind_def, comp_return_def,
            fresh_id_def, fresh_var_def, emit_def, cs_extends_def,
            IS_PREFIX_APPEND] >> metis_tac[]) >>
     drule_all fn_has_code_split >> simp[]) >>
  `64 < dimword (:256)` by simp[dimword_def] >>
  drule_all compile_alloc_buffer_body_site >> strip_tac >>
  drule_all compile_alloc_buffer_body_inst >> strip_tac >>
  `alloca_next_valid s /\ alloca_room ctx func s` by
    fs[stmt_state_rel_def, alloca_inv_def] >>
  `p + 64 < dimword (:256)` by
    (fs[alloca_site_cases] >-
       (`sa.cs_next_id NOTIN FDOM s.vs_allocas` by
          fs[FLOOKUP_DEF] >>
        drule alloca_room_fresh >> disch_then drule >>
        simp[mk_inst_def, dimword_def]) >>
     drule_all alloca_room_next_lt >>
     fs[alloca_next_valid_def] >>
     first_x_assum drule >> decide_tac) >>
  irule compile_mapping_subscript_mem_ok >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem body_alloc_history:
  compile_alloc_buffer sz sa = (buf,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (gvs[same_blocks_def, fn_has_code_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     simp[mk_inst_def, is_terminator_def]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem alloc_buffer_source_frag_mem:
  !ctx func cenv cx es sm mid buf sz s src a R.
    compile_alloc_buffer sz sm = (buf,mid) /\ fn_has_code sm mid func /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\ sz < dimword (:256) /\
    eval_operand src s = SOME a /\
    (!x. src = Var x ==> not_fresh_at sm x) /\ alloca_history func s ==>
    ?u w. frag_exec_mem ctx sm mid (\z. z = s)
            (\z. z = u /\ alloca_history func z) R /\
      eval_operand src u = SOME a /\
      stmt_state_rel ctx func cenv cx es u /\
      eval_operand buf.buf_operand u = SOME w /\
      FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,sz) /\
      w2n w + sz < dimword (:256) /\ u.vs_memory = s.vs_memory /\
      sm.cs_next_id < mid.cs_next_id /\
      (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sm.cs_next_id /\
         FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
         regions_disjoint (w2n w) sz b len) /\
      (!name b len. local_region cenv es.scopes u name b len ==>
         regions_disjoint (w2n w) sz b len) /\
      (?p. buf.buf_operand = Var p /\ not_fresh_at mid p) /\
      s.vs_alloca_next <= u.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `t.vs_labels = s.vs_labels` by metis_tac[hash_alloc_buffer_labels] >>
  `eval_operand src t = SOME a` by
    (Cases_on `src` >> gvs[eval_operand_def]) >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     qpat_x_assum `run_inst_seq _ _ = OK t` mp_tac >>
     simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
          exec_alloca_def, eval_operand_def] >>
     Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >>
     simp[update_var_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  qexistsl [`t with vs_inst_idx := LENGTH mid.cs_current_insts`, `w`] >>
  simp[] >> reverse conj_tac
  >- (Cases_on `src` >>
      gvs[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def,
          local_region_def] >> metis_tac[]) >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  `frag_exec_mem ctx sm mid
    (\z. z = s /\ ~z.vs_halted /\ z.vs_current_bb = sm.cs_current_bb /\
         z.vs_inst_idx = LENGTH sm.cs_current_insts)
    (\z. z = (t with vs_inst_idx := LENGTH mid.cs_current_insts) /\
         alloca_history func z) R` by
    (irule frag_exec_mem_run_inst_seq >>
     fs[same_blocks_def] >>
     simp[mk_inst_def, is_terminator_def, IS_PREFIX_APPEND] >>
     rpt strip_tac
     >- (simp[run_inst_seq_mem_ok_last] >>
         irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     `alloca_inv s` by fs[stmt_state_rel_def] >>
     `alloca_history func (t with vs_inst_idx := LENGTH mid.cs_current_insts)` by
       (irule body_alloc_history >> goal_assum (drule_at Any) >>
        simp[] >> metis_tac[]) >>
     gvs[]) >>
  fs[frag_exec_mem_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> simp[]
QED

