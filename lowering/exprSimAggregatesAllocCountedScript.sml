(*
 * Counted buffer allocation of aggregate literals (#636)
 *
 * The gas-counted form of exprSimAggregateChildren's buffer_alloc_frag:
 * the buffer's ALLOCA as a counted path that reads no gas.
 *
 * TOP-LEVEL:
 *   buffer_alloc_counted
 *)
Theory exprSimAggregatesAllocCounted
Ancestors
  exprSimAggregateLoops exprSimAggregateChildren exprSimAlloc
  exprSimHyps exprSimHypsDefs exprSimSource exprSimProps exprSimDefs
  loweringPosts gasOutcome gasSummary gasSummaryCompose gasContext
  fragGasMode fragGasPath fragGasSeq fragExec
  exprLowering exprLoweringProps compileEnv valueEncoding
  vyperInterpreter vyperState

(* The buffer's ALLOCA, counted: one instruction that reads no gas. *)
Theorem buffer_alloc_counted:
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  sz < dimword (:256) /\ stmt_state_rel ctx func ce cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?inst x t b. buf.buf_operand = Var x /\ MEM inst (fn_insts func) /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [x] /\
    inst.inst_id < sm.cs_next_id /\ not_fresh_at sm x /\
    local_ptrs_reserved ce sm /\ (!scopes. not_local_ptr ce scopes x) /\
    gas_marked_path F ctx func s0 0 (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    stmt_state_rel ctx func ce cx es t /\
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
      local_region ce es.scopes s0 name p n)
Proof
  strip_tac >>
  drule_all buffer_alloc_provenance >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq _ s0 = OK u` >>
  `emitted_insts sa sm =
     [mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)]] /\
   sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def,
          compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[] >>
     drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[]) >>
  `?bb. lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sm)
          (DROP s0.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
     simp[listTheory.DROP_APPEND]) >>
  `gas_path ctx func s0 0
     (OK (u with vs_inst_idx := LENGTH sm.cs_current_insts))` by
    (drule_all tuple_run_inst_seq_gas_path >>
     simp[venomInstTheory.mk_inst_def]) >>
  `~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb` by
    (qmatch_asmsub_abbrev_tac `emitted_insts sa sm = [ai]` >>
     `step_inst 0 ctx ai s0 = OK u` by
       (fs[run_inst_seq_def, venomExecSemanticsTheory.step_inst_non_invoke,
           Abbr `ai`, venomInstTheory.mk_inst_def, AllCaseEqs()]) >>
     `~is_terminator ai.inst_opcode` by
       simp[Abbr `ai`, venomInstTheory.mk_inst_def,
            venomInstTheory.is_terminator_def] >>
     drule_all venomInstProofsTheory.step_preserves_control_flow >>
     drule_all venomInstProofsTheory.step_preserves_halted >> simp[]) >>
  `!name p n. local_region ce es.scopes u name p n <=>
               local_region ce es.scopes s0 name p n` by
    (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists_tac `sa` >> simp[]) >>
  qexistsl_tac [`inst`, `x`, `u with vs_inst_idx := LENGTH sm.cs_current_insts`,
                `w2n w`] >>
  gvs[gas_marked_path_def, stmt_state_rel_inst_idx,
      venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def, local_region_def,
      wordsTheory.n2w_w2n] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b len. aid < _ /\ _ ==> _` irule >>
      qexists_tac `aid` >> simp[]) >>
  rpt gen_tac >>
  qpat_x_assum `!name b len. _ ==> regions_disjoint _ _ _ _`
    (qspecl_then [`name`, `p'`, `n`] mp_tac) >> simp[]
QED
