Theory placeStoreAllocPath
Ancestors
  exprSimAlloc fragGasSeq context compileEnv loweringSlice exprLoweringProps
  emitHelperProps fragExec localPtrsProps venomInst venomState
  venomExecSemantics venomInstProofs rich_list finite_map

Theorem place_alloc_buffer_source_path:
  !ctx func cenv cx es sm mid buf sz s src a.
    compile_alloc_buffer sz sm = (buf,mid) /\ fn_has_code sm mid func /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\ sz < dimword (:256) /\
    eval_operand src s = SOME a /\
    (!x. src = Var x ==> not_fresh_at sm x) /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u w. gas_path ctx func s 0 (OK u) /\
      ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
      u.vs_inst_idx = LENGTH mid.cs_current_insts /\
      eval_operand src u = SOME a /\
      stmt_state_rel ctx func cenv cx es u /\
      eval_operand buf.buf_operand u = SOME w /\
      FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,sz) /\
      w2n w + sz < dimword (:256) /\ u.vs_memory = s.vs_memory /\
      u.vs_labels = s.vs_labels /\ sm.cs_next_id < mid.cs_next_id /\
      (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sm.cs_next_id /\
         FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
         regions_disjoint (w2n w) sz b len) /\
      (!name b len. local_region cenv es.scopes u name b len ==>
         regions_disjoint (w2n w) sz b len) /\
      (?p. buf.buf_operand = Var p /\ not_fresh_at mid p) /\
      contract_storage u = contract_storage s /\
      contract_transient u = contract_transient s /\
      (?raw. run_inst_seq
         [mk_inst sm.cs_next_id ALLOCA [Lit (n2w sz)]
           [STRING #"%" (toString sm.cs_next_var)]] s = OK raw /\
         u = raw with vs_inst_idx := LENGTH mid.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `t.vs_labels = s.vs_labels` by metis_tac[hash_alloc_buffer_labels] >>
  `contract_storage t = contract_storage s /\
   contract_transient t = contract_transient s` by
    metis_tac[alloc_buffer_storage] >>
  `eval_operand src t = SOME a` by
    (Cases_on `src` >> gvs[eval_operand_def]) >>
  `emitted_insts sm mid =
     [mk_inst sm.cs_next_id ALLOCA [Lit (n2w sz)]
        [STRING #"%" (toString sm.cs_next_var)]] /\
   mid.cs_current_bb = sm.cs_current_bb /\
   LENGTH mid.cs_current_insts = LENGTH sm.cs_current_insts + 1` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
          comp_bind_def, comp_return_def, comp_ignore_bind_def,
          fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `~t.vs_halted /\ t.vs_current_bb = mid.cs_current_bb` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
     `step_inst 0 ctx
        (mk_inst sm.cs_next_id ALLOCA [Lit (n2w sz)]
          [STRING #"%" (toString sm.cs_next_var)]) s = OK t` by
       simp[step_inst_non_invoke, mk_inst_def] >>
     drule step_preserves_halted >>
     drule step_preserves_control_flow >>
     simp[mk_inst_def, is_terminator_def]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH mid.cs_current_insts`, `w`] >>
  simp[] >> reverse conj_tac
  >- (Cases_on `src` >>
      gvs[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def,
          local_region_def, contract_storage_def, contract_transient_def] >>
      metis_tac[]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sm mid)
          (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def] >>
     qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
          comp_bind_def, comp_return_def, comp_ignore_bind_def,
          fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[emitted_insts_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[DROP_LENGTH_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm mid)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all tuple_run_inst_seq_gas_path >>
  simp[mk_inst_def]
QED
