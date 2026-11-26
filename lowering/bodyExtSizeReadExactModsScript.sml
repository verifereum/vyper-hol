(* Lift the exact RETURNDATASIZE read at the external-return cut. *)
Theory bodyExtSizeReadExactMods
Ancestors
  rawCallBufferPtr bodyFullUnwrapRun fragGasOriginPtrLoop fragExecMem
  fragGasCopySeqLiftProps fragGasSeqPtr memSafeRun unitTransformDefs
  codegenRel contextCodegenRel
  exprLoweringProps emitHelperProps emitHelper exprLowering
  loweringStateRelDefs venomExecSemantics venomInst venomState
  ptrDiscipline compileEnv words finite_map pred_set list rich_list arithmetic

Theorem ext_size_read_exact_mods:
  emit_op RETURNDATASIZE [] k = (rds,m) /\
  fn_has_code k m func /\
  ~p.vs_halted /\
  p.vs_current_bb = k.cs_current_bb /\
  p.vs_inst_idx = LENGTH k.cs_current_insts /\
  allocas_from lo p /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp p) ==>
  ?w G1 t1.
    run_inst_seq (emitted_insts k m) p = OK w /\
    w = p with vs_vars := w.vs_vars /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (p,Gp,tp) []
      (OK (w with vs_inst_idx := LENGTH m.cs_current_insts),G1,t1)) /\
    op_prov G1 rds = NONE /\
    op_taint t1 rds = {} /\
    (!x. not_fresh_at k x ==> FLOOKUP G1 x = FLOOKUP Gp x /\
      op_taint t1 (Var x) = op_taint tp (Var x)) /\
    t1.t_mem = tp.t_mem /\
    t1.t_stor = tp.t_stor /\
    t1.t_trans = tp.t_trans /\
    t1.t_imm = tp.t_imm
Proof
  strip_tac >>
  drule_then strip_assume_tac emitted_insts_emit_op >>
  drule_then strip_assume_tac (SIMP_RULE bool_ss [same_blocks_def] emit_op_extends) >>
  qabbrev_tac `x = STRING #"%" (toString k.cs_next_var)` >>
  qabbrev_tac `i = mk_inst k.cs_next_id RETURNDATASIZE [] [x]` >>
  qabbrev_tac `v = update_var x (n2w (LENGTH p.vs_returndata)) p` >>
  `step_inst_base i p = OK v` by
    simp[Abbr `i`, Abbr `v`, raw_call_returndatasize_step_base] >>
  `run_inst_seq [i] p = OK v` by simp[run_inst_seq_def] >>
  qexistsl_tac [`v`, `DRESTRICT Gp (COMPL {x})`,
    `tp with t_var := tp.t_var |+ (x,{})`] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[Abbr `v`, update_var_def] >>
  reverse conj_tac >-
    simp[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
         Abbr `x`, not_fresh_at_def] >>
  `i.inst_opcode = RETURNDATASIZE` by simp[Abbr `i`, mk_inst_def] >>
  gen_tac >> irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >> simp[] >>
  qexistsl_tac [`[i]`, `k`] >> simp[is_terminator_def] >>
  conj_tac >-
    (rpt strip_tac >> Cases_on `pre` >> gvs[]) >>
  conj_tac >-
    simp[run_inst_seq_mem_ok_def, inst_mem_below_frontier_def,
         inst_dload_in_section_def, mk_inst_def, Abbr `i`,
         source_memory_read_ranges_def, source_memory_write_ranges_def,
         raw_call_returndatasize_step_base] >>
  irule inst_seq_ptr_lower_bound_transport >> simp[] >>
  qexists_tac `0` >> simp[inst_seq_ptr_def] >>
  conj_tac >- simp[Abbr `i`, ptr_inst_ok_returndatasize] >>
  simp[Abbr `i`, Abbr `v`] >>
  simp[step_prov_def, set_prov_def, out_prov_def,
       step_taint_def, out_taint_def, set_var_taint_def, mem_taint_def,
       new_site_bytes_def, step_writes_def, written_taint_def, adopt_reset_def,
       store_taint_def, imm_taint_def, range_bytes_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       FLOOKUP_DEF, update_var_def, SF CONJ_ss] >>
  simp[op_taint_def, FLOOKUP_UPDATE, taint_component_equality]
QED
