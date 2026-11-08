(* Standalone readonly data header; no operand-evaluation history. *)
Theory rawCallDataHeaderPtr
Ancestors rawCallHeaderFramePtr rawCallShapePtr typedOperandsPtr rawCallBufferPtr
  gasContext exprSimWordArgs exprSimDefs gasSummaryComposePtr vyperState
  vyperInterpreter exprSimHash wordOperandsPtr

Theorem raw_call_mload_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [out]) /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME w ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst id MLOAD [Var src] [out])
      (update_var out (mload (w2n w) s) s))
    (step_taint (mk_inst id MLOAD [Var src] [out]) s
      (update_var out (mload (w2n w) s) s) tn)
    (OK ((update_var out (mload (w2n w) s) s) with
      vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MLOAD [Var src] [out]) s =
     OK (update_var out (mload (w2n w) s) s)` by
    (simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs, venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_read1_def,
       venomStateTheory.eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx func G tn
     (mk_inst id MLOAD [Var src] [out]) s` by
    (irule typedCopyPtrTheory.ptr_inst_ok_mload >> simp[]) >>
  `gas_path_ptr_edge D 0 ctx func PG G tn s 0
     (step_prov PG G (mk_inst id MLOAD [Var src] [out])
       (update_var out (mload (w2n w) s) s))
     (step_taint (mk_inst id MLOAD [Var src] [out]) s
       (update_var out (mload (w2n w) s) s) tn)
     (OK ((update_var out (mload (w2n w) s) s) with
       vs_inst_idx := SUC s.vs_inst_idx))` by
    (mp_tac (Q.INST [`i` |-> `mk_inst id MLOAD [Var src] [out]`,
       `fn` |-> `func`, `lo` |-> `0`,
       `u` |-> `update_var out (mload (w2n (w:256 word)) s) s`]
       fragGasSeqPtrTheory.straight_line_ptr_edge) >>
     gvs[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  drule (cj 2 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >> disch_then irule >>
  irule (cj 1 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  simp[venomStateTheory.update_var_def]
QED

Theorem raw_call_add_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [left;right] [out]) /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst id ADD [left;right] [out])
      (update_var out (a+b) s))
    (step_taint (mk_inst id ADD [left;right] [out]) s
      (update_var out (a+b) s) tn)
    (OK ((update_var out (a+b) s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [left;right] [out]) s =
     OK (update_var out (a+b) s)` by
    (simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs, venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_pure2_def]) >>
  `ptr_inst_ok D 0 0 ctx func G tn
     (mk_inst id ADD [left;right] [out]) s` by
    (irule typedCopyPtrTheory.ptr_inst_ok_copy_len_binop >> simp[]) >>
  `gas_path_ptr_edge D 0 ctx func PG G tn s 0
     (step_prov PG G (mk_inst id ADD [left;right] [out]) (update_var out (a+b) s))
     (step_taint (mk_inst id ADD [left;right] [out]) s (update_var out (a+b) s) tn)
     (OK ((update_var out (a+b) s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (mp_tac (Q.INST [`i` |-> `mk_inst id ADD [left;right] [out]`,
       `fn` |-> `func`, `lo` |-> `0`,
       `u` |-> `update_var out ((a:256 word)+(b:256 word)) s`]
       fragGasSeqPtrTheory.straight_line_ptr_edge) >>
     gvs[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  drule (cj 2 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >> disch_then irule >>
  irule (cj 1 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  simp[venomStateTheory.update_var_def]
QED

Theorem raw_call_data_prefix_frame:
  emit_op MLOAD [ptr_op] sa = (len_op,sl) /\
  emit_op ADD [ptr_op; Lit 32w] sl = (data_op,sm) /\
  (!x. ptr_op = Var x ==> not_fresh_at sa x) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
  b < dimword (:256) /\ stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa ==>
  ?t. run_inst_seq (emitted_insts sa sm) s = OK t /\
    eval_operand len_op t = SOME (n2w (LENGTH bs)) /\
    eval_operand data_op t = SOME (n2w (b+32)) /\
    mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sa s t /\
    (!x. len_op = Var x \/ data_op = Var x ==> not_fresh_at sm x)
Proof
  strip_tac >> drule_all hash_data_prefix_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK t` >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `t with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_allocas)`) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule hash_readonly_state_rel >> goal_assum drule >> simp[]) >>
  qexists_tac `t` >> simp[loweringPostsTheory.wb_frame_def,
    loweringPostsTheory.locals_kept_def] >> first_assum ACCEPT_TAC
QED

Theorem raw_call_emit_mload_path_ptr:
  emit_op MLOAD [Var src] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME w ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var src] [out])
      (update_var out (mload (w2n w) s) s))
    (step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s
      (update_var out (mload (w2n w) s) s) tn)
    (OK ((update_var out (mload (w2n w) s) s) with
      vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MLOAD [Var src] [out]]` by
    (gvs[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
      compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.fresh_var_def,
      compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
      compileEnvTheory.comp_return_def]) >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id MLOAD [Var src] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all raw_call_mload_path_ptr >> simp[]
QED

Theorem raw_call_emit_add_path_ptr:
  emit_op ADD [left;right] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id ADD [left;right] [out])
      (update_var out (a+b) s))
    (step_taint (mk_inst sa.cs_next_id ADD [left;right] [out]) s
      (update_var out (a+b) s) tn)
    (OK ((update_var out (a+b) s) with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ADD [left;right] [out]]` by
    (gvs[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
      compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.fresh_var_def,
      compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
      compileEnvTheory.comp_return_def]) >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id ADD [left;right] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all raw_call_add_path_ptr >> simp[]
QED

Theorem raw_call_fresh_update_state_frame:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  ~not_fresh_at sa out ==>
  stmt_state_rel ctx func cenv cx es
    ((update_var out w s) with vs_inst_idx := k) /\
  wb_frame cenv es sa s ((update_var out w s) with vs_inst_idx := k)
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x (update_var out w s) = lookup_var x s` by
    (rpt strip_tac >> `x <> out` by metis_tac[] >>
     simp[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]) >> conj_tac
  >- (simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
      irule hash_readonly_state_rel >> goal_assum (drule_at Any) >>
      simp[venomStateTheory.update_var_def]) >>
  simp[loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def,
    venomStateTheory.update_var_def, venomStateTheory.lookup_var_def] >>
  rpt strip_tac >> `x <> out` by metis_tac[] >>
  simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem raw_call_mload_header_stage:
  emit_op MLOAD [Var x] sa = (Var lx,sl) /\ fn_has_code sa sl func /\
  stmt_state_rel ctx func cenv cx es s /\
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ not_fresh_at sa x /\
  ptr_covers G tn x s 32 /\ lookup_var x s = SOME w /\
  op_taint tn (Var x) = {} /\
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) ==>
  ?H un u. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H un (OK u) /\
    ghost_inv dep cenv cx es H un u /\ ghost_kept cenv es sa G tn s H un /\
    stmt_state_rel ctx func cenv cx es u /\ wb_frame cenv es sa s u /\
    u.vs_current_bb = sl.cs_current_bb /\
    u.vs_inst_idx = LENGTH sl.cs_current_insts /\ ~u.vs_halted /\
    eval_operand (Var x) u = SOME w /\ op_taint un (Var x) = {} /\
    eval_operand (Var lx) u = SOME (mload (w2n w) s) /\
    op_taint un (Var lx) = {} /\
    u.vs_memory = s.vs_memory /\ un.t_mem = tn.t_mem
Proof
  strip_tac >>
  drule_all raw_call_emit_mload_path_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ _ _ H un (OK u)` >>
  `ghost_inv dep cenv cx es H un u /\ ghost_kept cenv es sa G tn s H un` by
    (qunabbrev_tac `u` >> irule raw_call_emit_mload_ghost_frame >>
     goal_assum (drule_at Any) >> simp[Abbr `H`, Abbr `un`] >>
     qexistsl_tac [`PG`, `x`] >> simp[]) >>
  `~not_fresh_at sa lx /\ sl.cs_current_bb = sa.cs_current_bb` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
       compileEnvTheory.comp_return_def] >> rpt strip_tac >> gvs[] >>
     fs[compileEnvTheory.not_fresh_at_def]) >>
  `x <> lx` by metis_tac[] >>
  `stmt_state_rel ctx func cenv cx es u /\ wb_frame cenv es sa s u` by
    (qunabbrev_tac `u` >> irule raw_call_fresh_update_state_frame >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`H`, `un`, `u`] >> simp[] >>
  simp[Abbr `u`, Abbr `un`,
    decoderGhostFramePtrTheory.step_taint_other_output,
    venomInstTheory.mk_inst_def, venomStateTheory.eval_operand_def,
    venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  `eval_operand (Var x) s = SOME w` by
    simp[venomStateTheory.eval_operand_def] >>
  drule_all typedCopyPtrTheory.mload_ghost_clean >>
  simp[] >> disch_then (qspecl_then [`sa.cs_next_id`, `lx`] mp_tac) >>
  gvs[venomStateTheory.lookup_var_def, venomInstTheory.mk_inst_def,
    venomStateTheory.update_var_def]
QED

Theorem raw_call_add_header_stage:
  emit_op ADD [Var x; Lit 32w] sl = (Var dx,sm) /\ fn_has_code sl sm func /\
  stmt_state_rel ctx func cenv cx es s /\
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sl /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sl z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sl z) /\
  s.vs_current_bb = sl.cs_current_bb /\
  s.vs_inst_idx = LENGTH sl.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  not_fresh_at sl x /\ not_fresh_at sl lx /\
  eval_operand (Var x) s = SOME w /\ op_taint tn (Var x) = {} /\
  eval_operand (Var lx) s = SOME len /\ op_taint tn (Var lx) = {} ==>
  ?H un u. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H un (OK u) /\
    ghost_inv dep cenv cx es H un u /\ ghost_kept cenv es sl G tn s H un /\
    stmt_state_rel ctx func cenv cx es u /\ wb_frame cenv es sl s u /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~u.vs_halted /\
    eval_operand (Var x) u = SOME w /\ op_taint un (Var x) = {} /\
    eval_operand (Var lx) u = SOME len /\ op_taint un (Var lx) = {} /\
    eval_operand (Var dx) u = SOME (w+32w) /\ op_taint un (Var dx) = {} /\
    op_prov H (Var dx) = op_prov G (Var x) /\
    u.vs_memory = s.vs_memory /\ un.t_mem = tn.t_mem
Proof
  strip_tac >>
  `op_taint tn (Lit 32w) = {} /\ eval_operand (Lit 32w) s = SOME 32w` by
    simp[ptrDisciplineTheory.op_taint_def, venomStateTheory.eval_operand_def] >>
  drule_all raw_call_emit_add_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `cx_dead cx`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ _ _ H un (OK u)` >>
  `ghost_inv dep cenv cx es H un u /\ ghost_kept cenv es sl G tn s H un` by
    (qunabbrev_tac `u` >> irule raw_call_emit_add_ghost_frame >>
     goal_assum (drule_at Any) >> simp[Abbr `H`, Abbr `un`] >>
     qexistsl_tac [`PG`, `Var x`, `Lit 32w`] >> simp[]) >>
  `~not_fresh_at sl dx /\ sm.cs_current_bb = sl.cs_current_bb` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
       compileEnvTheory.comp_return_def] >> rpt strip_tac >> gvs[] >>
     fs[compileEnvTheory.not_fresh_at_def]) >>
  `op_prov H (Var dx) = op_prov G (Var x)` by
    (Cases_on `FLOOKUP G x` >>
     simp[Abbr `H`, Abbr `u`, ptrDisciplineTheory.step_prov_def,
      ptrDisciplineTheory.out_prov_def, ptrDisciplineTheory.set_prov_def,
      ptrDisciplineTheory.first_prov_def, ptrDisciplineTheory.op_prov_def,
      venomInstTheory.mk_inst_def, finite_mapTheory.FLOOKUP_UPDATE,
      finite_mapTheory.FLOOKUP_DRESTRICT]) >>
  `x <> dx /\ lx <> dx` by metis_tac[] >>
  `stmt_state_rel ctx func cenv cx es u /\ wb_frame cenv es sl s u` by
    (qunabbrev_tac `u` >> irule raw_call_fresh_update_state_frame >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`H`, `un`, `u`] >> simp[] >>
  simp[Abbr `u`, Abbr `un`,
    decoderGhostFramePtrTheory.step_taint_other_output,
    typedCopyPtrTheory.copy_len_binop_ghost_frame,
    venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
    venomStateTheory.update_var_def, venomInstTheory.mk_inst_def,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  fs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]
QED

Theorem raw_call_header_two_steps:
  emit_op MLOAD [Var x] sa = (Var lx,sl) /\
  emit_op ADD [Var x; Lit 32w] sl = (Var dx,sm) /\ fn_has_code sa sm func /\
  stmt_state_rel ctx func cenv cx es s /\
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ not_fresh_at sa x /\
  ptr_covers G tn x s 32 /\ lookup_var x s = SOME w /\
  op_taint tn (Var x) = {} /\
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) ==>
  ?H un u. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H un (OK u) /\
    ghost_inv dep cenv cx es H un u /\ ghost_kept cenv es sa G tn s H un /\
    stmt_state_rel ctx func cenv cx es u /\ wb_frame cenv es sa s u /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~u.vs_halted /\
    eval_operand (Var x) u = SOME w /\ op_taint un (Var x) = {} /\
    eval_operand (Var lx) u = SOME (mload (w2n w) s) /\ op_taint un (Var lx) = {} /\
    eval_operand (Var dx) u = SOME (w+32w) /\ op_taint un (Var dx) = {} /\
    u.vs_memory = s.vs_memory /\ un.t_mem = tn.t_mem /\
    FLOOKUP H x = FLOOKUP G x /\
    op_prov H (Var dx) = op_prov G (Var x) /\
    not_fresh_at sm x /\ not_fresh_at sm lx /\ not_fresh_at sm dx
Proof
  strip_tac >>
  `ci_mono sa sl /\ ci_mono sl sm` by
    metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, pairTheory.SND] >>
  `cs_extends sa sl /\ cs_extends sl sm` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `fn_has_code sa sl func /\ fn_has_code sl sm func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `not_fresh_at sl lx` by
    (qpat_x_assum `emit_op ADD _ _ = _` kall_tac >>
     drule emitHelperPropsTheory.emitted_insts_emit_op >>
     simp[compileEnvTheory.not_fresh_at_def] >> rpt strip_tac >> gvs[] >>
     qexists_tac `sa.cs_next_var` >> simp[]) >>
  `local_ptrs_reserved cenv sl /\ not_fresh_at sl x /\ not_fresh_at sl lx /\

   (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sl z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sl z)` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
       stmtFragPtrTheory.not_fresh_at_mono]) >>
  drule_all raw_call_mload_header_stage >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule_all raw_call_add_header_stage >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "compose"
QED

Resume raw_call_header_two_steps[compose]:
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H' un' (OK u')` by
    (drule_all fragGasPathPtrTheory.gas_path_ptr_then >> simp[]) >>
  `wb_frame cenv es sa s u'` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     goal_assum (drule_at Any) >> simp[] >> conj_tac
     >- (qexistsl_tac [`es`, `sl`, `u`] >>
         fs[exprLoweringPropsTheory.ci_mono_def]) >>
     goal_assum (drule_at Any)) >>
  `ghost_kept cenv es sa G tn s H' un'` by
    (irule wordOperandsPtrTheory.ghost_kept_trans >> simp[] >> conj_tac
     >- (qexists_tac `func` >>
         fs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def]) >>
     qexistsl_tac [`H`, `es`, `u`, `sl`, `un`] >>

     fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `op_prov H' (Var dx) = op_prov G (Var x)` by
    (fs[ptrDisciplineTheory.op_prov_def, bodyPtrDefsTheory.ghost_kept_def] >>
     metis_tac[]) >>
  qexistsl_tac [`H'`, `un'`, `u'`] >> simp[] >>
  conj_tac
  >- (fs[venomStateTheory.eval_operand_def] >>
      irule exprSimWordArgsTheory.wb_frame_vars >>
      qexistsl_tac [`cenv`, `es`, `u`, `sl`] >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `ghost_kept _ _ sl _ _ _ _ _` mp_tac >>
      simp[bodyPtrDefsTheory.ghost_kept_def] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `ghost_kept _ _ sa G tn s H' un'` mp_tac >>
      simp[bodyPtrDefsTheory.ghost_kept_def] >> metis_tac[]) >>
  conj_tac
  >- metis_tac[stmtFragPtrTheory.not_fresh_at_mono,
       exprLoweringPropsTheory.ci_mono_def] >>
  conj_tac
  >- metis_tac[stmtFragPtrTheory.not_fresh_at_mono,
       exprLoweringPropsTheory.ci_mono_def] >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >>
  simp[compileEnvTheory.not_fresh_at_def] >> rpt strip_tac >> gvs[] >>
  qexists_tac `sl.cs_next_var` >> simp[]
QED

Finalise raw_call_header_two_steps
