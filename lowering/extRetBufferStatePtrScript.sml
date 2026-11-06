(* Counted buffer allocation retaining concrete statement-state resources. *)
Theory extRetBufferStatePtr
Ancestors
  extRetBufferAllocCountedPtr extRetBulkCopyCountedPtr extRetCountedPtr
  extRetBytesCopyCountedPtr allocaFootprint list rich_list loweringSlice allocationPtr loweringHalt
  abiBuiltinAllocation exprLoweringProps fragGasSeqPtr fragGasPathPtr
  fragExecPtr fragExec emitHelperProps compileEnv emitHelper context
  ptrDiscipline ptrSafeRun bodyPtrDefs venomState venomInst venomExecSemantics
  codegenRel venomMemProps valueEncodingProps valueEncodingProofs
  words finite_map pred_set arithmetic

Theorem compile_alloc_buffer_state_counted_ptr:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb fn /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var)) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ n < dimword(:256) ==>
  ?ip addr Gf tnf sf.
    buf.buf_operand = Var ip /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    stmt_state_rel ctx fn cenv cx es sf /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (addr,n) /\
    addr+n < dimword(:256) /\ lookup_var ip sf = SOME (n2w addr) /\
    ptr_covers Gf tnf ip sf n /\ sf.vs_memory = s.vs_memory /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. i < addr \/ addr+n <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  qabbrev_tac `ip = STRING #"%" (toString sa.cs_next_var)` >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `emit_op ALLOCA [Lit (n2w n)] sa = (Var ip,sb)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> strip_tac >>
     qpat_x_assum `_ = buf` (SUBST_ALL_TAC o SYM) >> gvs[Abbr `ip`]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [ip]]` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [ip]) (fn_insts fn)` by
    (fs[fn_has_code_def] >>
     `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [ip])
       bb.bb_instructions` by gvs[IS_PREFIX_APPEND] >>
     metis_tac[lookup_block_fn_insts]) >>
  `?addr. FLOOKUP (abi_builtin_allocate_state sa.cs_next_id n s).vs_allocas
       sa.cs_next_id = SOME (addr,n) /\ addr+n < dimword(:256)` by
    (Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
     >- (drule_all stmt_state_rel_alloca_fresh_bound >> strip_tac >>
         simp[abi_builtin_allocate_state_def, FLOOKUP_UPDATE]) >>
     rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME site` >>
     PairCases_on `site` >> drule_all stmt_state_rel_alloca_site_bound >>
     strip_tac >> gvs[abi_builtin_allocate_state_def]) >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [ip]` >>
  qabbrev_tac `u = update_var ip (n2w addr)
    (abi_builtin_allocate_state sa.cs_next_id n s)` >>
  `step_inst_base inst s = OK u` by
    (simp[Abbr `inst`, Abbr `u`] >> irule step_alloca_site >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx es u` by
    (drule stmt_state_rel_exec_alloca >>
     disch_then (qspecl_then [`inst`, `ip`, `n2w n`, `u`] mp_tac) >>
     simp[Abbr `inst`, mk_inst_def] >>
     gvs[mk_inst_def, step_inst_base_def]) >>
  qabbrev_tac `Gf = step_prov PG G inst u` >>
  qabbrev_tac `tnf = step_taint inst s u tn` >>
  qexistsl_tac [`ip`, `addr`, `Gf`, `tnf`,
    `u with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- simp[Abbr `ip`] >>
  conj_tac >-
    (qunabbrev_tac `tnf` >> qunabbrev_tac `Gf` >>
     irule emitted_step_counted_ptr >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
     conj_tac >- (qexistsl_tac [`sa`, `sb`] >> simp[mk_inst_def]) >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_alloca) >> simp[]) >>
  `ptr_covers Gf tnf ip (u with vs_inst_idx := SUC s.vs_inst_idx) n` by
    (simp[ptr_covers_def, Abbr `Gf`, Abbr `tnf`, Abbr `inst`,
          step_prov_def, set_prov_def, out_prov_def, step_taint_def,
          set_var_taint_def, out_taint_def, mk_inst_def, eval_operand_def,
          op_taint_def, Abbr `u`, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE, LESS_MOD] >> `addr < dimword(:256)` by decide_tac >>
     simp[LESS_MOD] >> metis_tac[]) >>
  simp[stmt_state_rel_inst_idx, Abbr `ip`] >>
  simp[Abbr `u`, abi_builtin_allocate_state_def, update_var_def,
       lookup_var_def, arithmeticTheory.ADD1] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id = NONE` >>
  (gvs[Abbr `Gf`, Abbr `tnf`, Abbr `inst`, step_prov_def, set_prov_def,
      out_prov_def, step_taint_def, set_var_taint_def, out_taint_def,
      mk_inst_def, imm_taint_def, store_taint_def, adopt_reset_def, op_taint_def,
      abi_builtin_allocate_state_def, update_var_def, FLOOKUP_UPDATE] >>
   rpt gen_tac >> rpt disch_tac >>
   reverse conj_tac >-
     (rpt strip_tac >>
      `v <> STRING #"%" (toString sa.cs_next_var)` by metis_tac[] >> simp[]) >>
   qpat_x_assum `FLOOKUP s.vs_allocas _ = _` mp_tac >>
   POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
   simp[mem_taint_def, new_site_bytes_def, step_writes_def,
        range_bytes_def, written_taint_def, FLOOKUP_UPDATE,
        source_memory_write_ranges_def, eval_operand_def, FLOOKUP_DEF,
        FAPPLY_FUPDATE_THM] >>
   rpt strip_tac >> (eq_tac >-
     (strip_tac >> gvs[] >> decide_tac) >> simp[]))
QED
