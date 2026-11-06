(* Counted, checked paths for the reason encoder's straight-line prefix. *)
Theory reasonPrefixPtr
Ancestors
  reasonPrefixResourcesPtr reasonBufferPtr ghostPcTransportPtr bodyPtrDefs
  loweringPosts loweringHalt exprSimProps exprSimAlloc typedCopyPtr codegenRel instIdxIndep
  fragGasSeqPtr fragGasPathPtr fragExec emitHelperProps exprLoweringProps
  ptrSafeRun ptrDiscipline venomInst venomInstProofs venomState
  venomExecSemantics context emitHelper compileEnv allocationPtr fragExecPtr

(* The compiler equation supplies the instruction lookup; callers supply only
   the semantic step and check, never a hand-built control-flow edge. *)
Theorem reason_encoder_emit_path_ptr:
  emit_inst opc ops outs sa = ((), sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  ptr_inst_ok D 0 0 ctx func G tn (mk_inst sa.cs_next_id opc ops outs) s /\
  step_inst_base (mk_inst sa.cs_next_id opc ops outs) s = OK t ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id opc ops outs) t)
    (step_taint (mk_inst sa.cs_next_id opc ops outs) s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id opc ops outs)` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst 0 ctx (mk_inst sa.cs_next_id opc ops outs) s = OK t` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  `~t.vs_halted` by
    (drule step_preserves_halted >> simp[mk_inst_def]) >>
  `gas_path_ptr_edge D 0 ctx func PG G tn s
    (if (mk_inst sa.cs_next_id opc ops outs).inst_opcode = GAS then 1 else 0)
    (step_prov PG G (mk_inst sa.cs_next_id opc ops outs) t)
    (step_taint (mk_inst sa.cs_next_id opc ops outs) s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule straight_line_ptr_edge >> simp[mk_inst_def] >> metis_tac[]) >>
  drule (cj 2 gas_path_ptr_rules) >> simp[] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[]
QED

Theorem reason_encoder_alloc_path_ptr:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  buf.buf_operand = Var out /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK t ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) t)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `emit_inst ALLOCA [Lit (n2w n)] [out]
    (sa with cs_next_var := sa.cs_next_var + 1) = ((),sb)` by
    (gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def, fresh_var_def,
         fresh_id_def, emit_inst_def, emit_def]) >>
  drule reason_encoder_emit_path_ptr >>
  simp[ptr_inst_ok_alloca, mk_inst_def, is_terminator_def] >>
  disch_then irule >>
  gvs[fn_has_code_def, emitted_blocks_def, GSYM mk_inst_def, ptr_inst_ok_alloca]
QED

(* Compiler layout, separate from all execution and ghost reasoning. *)
Theorem reason_encoder_prefix_code:
  compile_alloc_buffer n cc = (buf,c1) /\
  emit_void MSTORE [buf.buf_operand; Lit 0x08c379a0w] c1 = ((),c2) /\
  emit_op ADD [buf.buf_operand; Lit 32w] c2 = (payload,c3) /\
  compile_alloc_buffer m c3 = (tuple,c4) /\
  buf.buf_operand = Var out /\ payload = Var x /\ tuple.buf_operand = Var out2 ==>
  c4.cs_current_bb = cc.cs_current_bb /\ c4.cs_blocks = cc.cs_blocks /\
  c4.cs_current_insts = cc.cs_current_insts ++
    [mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out];
     mk_inst c1.cs_next_id MSTORE [Var out; Lit 0x08c379a0w] [];
     mk_inst c2.cs_next_id ADD [Var out; Lit 32w] [x];
     mk_inst c3.cs_next_id ALLOCA [Lit (n2w m)] [out2]]
Proof
  strip_tac >>
  gvs[compile_alloc_buffer_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def, listTheory.APPEND_ASSOC]
QED

(* Public cursor transport; the encoder preserves the original expression interval. *)
Theorem reason_expr_post_inst_idx[simp]:
  expr_post ctx func ce cx e es sa sb s0 es' v op (s with vs_inst_idx := j) <=>
  expr_post ctx func ce cx e es sa sb s0 es' v op s
Proof
  simp[expr_post_def, stmt_state_rel_inst_idx, expr_val_rel_def,
       expr_val_at_def, local_region_def, lookup_var_def]
QED

Theorem reason_encoder_prefix_path_ptr:
  !ctx func cenv cx e es sa sb s0 es' v op s cc c1 c2 c3 c4 buf payload tuple n m tv ow PG G tn D.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    compile_alloc_buffer n cc = (buf,c1) /\ fn_has_code cc c1 func /\
    emit_void MSTORE [buf.buf_operand; Lit 0x08c379a0w] c1 = ((),c2) /\
    emit_op ADD [buf.buf_operand; Lit 32w] c2 = (payload,c3) /\
    compile_alloc_buffer m c3 = (tuple,c4) /\ fn_has_code c3 c4 func /\
    fn_has_code cc c4 func /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = cc.cs_current_bb /\
    s.vs_inst_idx = LENGTH cc.cs_current_insts /\ ~s.vs_halted /\
    local_ptrs_reserved cenv cc /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    fn_inst_ids_distinct func /\ 32 <= n /\ n < dimword (:256) /\
    m < dimword (:256) /\
    sa.cs_next_var <= cc.cs_next_var /\
    sa.cs_next_id <= cc.cs_next_id /\ sb.cs_next_id <= cc.cs_next_id /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ val_wf tv v /\
    eval_operand op s = SOME ow /\
    (!p. op = Var p ==> not_fresh_at cc p) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n ow) mem) ==>
    ?t out x out2 b2 G4 tn4 b.
      eval_operand buf.buf_operand t = SOME (n2w b) /\
      eval_operand payload t = SOME (n2w b + 32w) /\
      b + n < dimword (:256) /\
      buf.buf_operand = Var out /\ payload = Var x /\
      tuple.buf_operand = Var out2 /\
      gas_path_ptr D 0 ctx func PG G tn s 0 G4 tn4 (OK t) /\
      t.vs_current_bb = c4.cs_current_bb /\
      t.vs_inst_idx = LENGTH c4.cs_current_insts /\
      eval_operand tuple.buf_operand t = SOME (n2w b2) /\
      FLOOKUP t.vs_allocas c3.cs_next_id = SOME (b2,m) /\
      b2 + m < dimword (:256) /\
      expr_post ctx func cenv cx e es sa sb s0 es' v op t /\
      local_ptrs_reserved cenv c4 /\
      eval_operand op t = SOME ow /\
      ptr_covers G4 tn4 out2 t m /\
      ptr_covers G4 tn4 out t n /\ ptr_covers G4 tn4 x t (n - 32) /\
      (!p k. not_fresh_at cc p /\ ptr_covers G tn p s k ==>
        ptr_covers G4 tn4 p t k) /\
      (!mem. mem_agree_outside tn4.t_mem t.vs_memory mem ==>
        val_in_memory tv v (w2n ow) mem) /\
      ~t.vs_halted /\
      MEM (mk_inst c3.cs_next_id ALLOCA [Lit (n2w m)] [out2]) (fn_insts func) /\
      not_local_ptr cenv es'.scopes out2 /\
      (!p. not_fresh_at cc p ==> FLOOKUP G4 p = FLOOKUP G p /\
        op_taint tn4 (Var p) = op_taint tn (Var p)) /\
      op_prov G4 op = op_prov G op /\ op_taint tn4 op = op_taint tn op
Proof
  rpt gen_tac >> strip_tac >>
  drule_all reason_encoder_prefix_post >>
  disch_then (qspecl_then [`PG`, `G`] strip_assume_tac) >>
  drule_all reason_encoder_prefix_code >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `step_inst_base (mk_inst c1.cs_next_id MSTORE [Var out; Lit 0x08c379a0w] []) t = OK u` by
    (qpat_x_assum `run_inst_seq (emitted_insts c1 c2) _ = _` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()]) >>
  `STRING #"%" (toString c2.cs_next_var) = x` by
    (qpat_x_assum `payload = Var x` mp_tac >> simp[]) >>
  `step_inst_base (mk_inst c2.cs_next_id ADD [Var out; Lit 32w] [x]) u = OK r` by
    (qpat_x_assum `run_inst_seq (emitted_insts c2 c3) _ = _` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()]) >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 G3 tn4
    (OK (z with vs_inst_idx := LENGTH c4.cs_current_insts))` by suspend "path" >>
  `~z.vs_halted` by (drule gas_path_ptr_ok_not_halted >> simp[]) >>
  qexistsl_tac [`z with vs_inst_idx := LENGTH c4.cs_current_insts`,
    `out`, `x`, `out2`, `b2`, `G3`, `tn4`, `b`] >>
  conj_tac >- (qpat_x_assum `eval_operand buf.buf_operand z = _` mp_tac >>
               simp[eval_operand_def, lookup_var_def]) >>
  conj_tac >- (qpat_x_assum `eval_operand payload z = _` mp_tac >>
               simp[eval_operand_def, lookup_var_def]) >>
  suspend "endpoint"
QED

Resume reason_encoder_prefix_path_ptr[endpoint]:
  `z.vs_current_bb = c4.cs_current_bb` by suspend "block" >>
  map_every (fn q => qpat_x_assum q mp_tac)
    [`buf.buf_operand = Var out`, `payload = Var x`, `tuple.buf_operand = Var out2`,
     `b + n < _`, `b2 + m < _`,
     `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`, `z.vs_current_bb = _`,
     `eval_operand tuple.buf_operand z = _`, `FLOOKUP z.vs_allocas _ = _`,
     `expr_post _ _ _ _ _ _ _ _ _ _ _ _ z`,
     `local_ptrs_reserved cenv c4`, `eval_operand op z = _`,
     `ptr_covers G3 tn4 out2 z m`, `ptr_covers G3 tn4 out z n`,
     `ptr_covers G3 tn4 x z _`,
     `!p k. not_fresh_at cc p /\ _ ==> _`,
     `!mem. mem_agree_outside tn4.t_mem z.vs_memory mem ==> _`,
     `~z.vs_halted`, `MEM (mk_inst c3.cs_next_id _ _ _) _`,
     `not_local_ptr cenv es'.scopes out2`,
     `!p. not_fresh_at cc p ==> _`,
     `op_prov G3 op = _`, `op_taint tn4 op = _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  gvs[]
QED

Resume reason_encoder_prefix_path_ptr[block]:
  qpat_x_assum `s.vs_current_bb = _` mp_tac >>
  qpat_x_assum `c4.cs_current_bb = _` mp_tac >>
  rpt (qpat_x_assum `step_inst_base _ _ = OK _` mp_tac) >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> simp[] >>
  `!id opc ops outs a b.
     step_inst_base (mk_inst id opc ops outs) a = OK b ==>
     opc <> INVOKE /\ ~is_terminator opc ==>
     b.vs_current_bb = a.vs_current_bb` by
    (rpt strip_tac >>
     `step_inst 0 ctx (mk_inst id opc ops outs) a = OK b` by
       simp[step_inst_non_invoke, mk_inst_def] >>
     drule step_preserves_control_flow >> simp[mk_inst_def]) >>
  qpat_x_assum `!id opc ops outs a b. _` imp_res_tac >>
  fs[is_terminator_def]
QED

Resume reason_encoder_prefix_path_ptr[path]:
  `ptr_covers G1 tn1 out t n` by suspend "first_buffer" >>
  qmatch_asmsub_abbrev_tac `c4.cs_current_insts = cc.cs_current_insts ++ code` >>
  `run_inst_seq code s = OK z` by
    (qpat_x_assum `Abbrev (code = _)` mp_tac >>
     rpt (qpat_x_assum `step_inst_base _ _ = OK _` mp_tac) >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     simp[Abbr `code`, run_inst_seq_def]) >>
  `inst_seq_ptr D 0 ctx func PG G tn code s G3 tn4` by
    suspend "checks" >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    suspend "lookup" >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >>
  simp[Abbr `code`, mk_inst_def]
QED

Resume reason_encoder_prefix_path_ptr[first_buffer]:
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ s` mp_tac >>
  qpat_x_assum `compile_alloc_buffer n cc = _` mp_tac >>
  qpat_x_assum `fn_has_code cc c1 func` mp_tac >>
  qpat_x_assum `n < dimword (:256)` mp_tac >>
  qpat_x_assum `buf.buf_operand = Var out` mp_tac >>
  qpat_x_assum `step_inst_base _ s = OK t` mp_tac >>
  qpat_x_assum `G1 = _` mp_tac >>
  qpat_x_assum `tn1 = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' s` by fs[expr_post_def] >>
  gvs[] >> irule alloca_step_ptr_covers >> metis_tac[]
QED

Resume reason_encoder_prefix_path_ptr[checks]:
  `ptr_covers G1 tn1 out t 32` by
    (qpat_x_assum `ptr_covers G1 tn1 out t n` mp_tac >>
     qpat_x_assum `32 <= n` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[ptr_covers_def] >> rpt strip_tac >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `op_taint tn2 (Var out) = {}` by
    (qpat_x_assum `ptr_covers G1 tn1 out t n` mp_tac >>
     qpat_x_assum `tn2 = _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[ptr_covers_def, op_taint_def, step_taint_def,
       set_var_taint_def, mk_inst_def, finite_mapTheory.DRESTRICT_UNIV]) >>
  `step_prov PG G1 (mk_inst c1.cs_next_id MSTORE [Var out; Lit 0x08c379a0w] []) u = G1` by
    simp[NoAsms, step_prov_def, set_prov_def, mk_inst_def,
         finite_mapTheory.DRESTRICT_UNIV] >>
  suspend "sequence"
QED

Resume reason_encoder_prefix_path_ptr[lookup]:
  qpat_x_assum `fn_has_code cc c4 func` mp_tac >>
  qpat_x_assum `c4.cs_current_bb = _` mp_tac >>
  qpat_x_assum `c4.cs_current_insts = _` mp_tac >>
  qpat_x_assum `s.vs_current_bb = _` mp_tac >>
  qpat_x_assum `s.vs_inst_idx = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[fn_has_code_def] >> rpt strip_tac >>
  qexists_tac `bb` >> simp[] >>
  gvs[rich_listTheory.IS_PREFIX_APPEND] >>
  simp[listTheory.DROP_APPEND, rich_listTheory.IS_PREFIX_APPEND,
       listTheory.APPEND_ASSOC]
QED

Resume reason_encoder_prefix_path_ptr[sequence]:
  qpat_x_assum `Abbrev (code = _)` mp_tac >>
  qpat_x_assum `~ctx_has_dalloca ctx` mp_tac >>
  qpat_x_assum `ptr_covers G1 tn1 out t 32` mp_tac >>
  qpat_x_assum `op_taint tn2 (Var out) = {}` mp_tac >>
  qpat_x_assum `buf.buf_operand = Var out` mp_tac >>
  qpat_x_assum `G1 = _` (mp_tac o SYM) >>
  qpat_x_assum `tn1 = _` (mp_tac o SYM) >>
  qpat_x_assum `tn2 = _` (mp_tac o SYM) >>
  qpat_x_assum `G2 = _` (mp_tac o SYM) >>
  qpat_x_assum `tn3 = _` (mp_tac o SYM) >>
  qpat_x_assum `G3 = _` (mp_tac o SYM) >>
  qpat_x_assum `tn4 = _` (mp_tac o SYM) >>
  qpat_x_assum `step_prov PG G1 _ u = G1` mp_tac >>
  rpt (qpat_x_assum `step_inst_base _ _ = OK _` mp_tac) >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  `!j. ptr_inst_ok D 0 0 ctx func G1 tn1
    (mk_inst c1.cs_next_id MSTORE [Var out; Lit 0x08c379a0w] [])
    (t with vs_inst_idx := j)` by
    (gen_tac >> irule ptr_inst_ok_mstore >> simp[op_taint_def]) >>
  `!j. ptr_inst_ok D 0 0 ctx func G1 tn2
    (mk_inst c2.cs_next_id ADD [Var out; Lit 32w] [x])
    (u with vs_inst_idx := j)` by
    (gen_tac >> irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  fs[mk_inst_def] >>
  simp[Abbr `code`, inst_seq_ptr_def, SRULE [mk_inst_def] ptr_inst_ok_alloca,
       step_inst_inst_idx_indep, mk_inst_def, is_terminator_def,
       exec_result_map_def]
QED

Finalise reason_encoder_prefix_path_ptr
