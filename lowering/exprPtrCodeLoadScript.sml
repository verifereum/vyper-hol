(* Counted runtime immutable word load and its ghost frame. *)
Theory exprPtrCodeLoad
Ancestors
  exprPtrUnwrapCodeEdges stmtAppendStorageRunPtr bodyPtrDefs ptrDiscipline
  fragGasPathPtr exprSimPtrProps venomExecSemantics venomInstProofs
  venomInst venomState compileEnv emitHelper emitHelperProps codegenRel fragExec
  finite_map arithmetic

Theorem code_load_step_ptr:
  eval_operand arg s = SOME a /\ op_taint tn arg = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id DLOAD [arg] [out]) ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (update_var out (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) s
        with vs_inst_idx := SUC s.vs_inst_idx)) /\
    op_taint tn' (Var out) = {} /\ op_prov G' (Var out) = NONE /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `u = update_var out (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) s` >>
  `allocas_from 0 s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    simp[allocas_from_def] >>
  drule_all code_load_counted_edge >>
  disch_then (qspecl_then [`PG`, `G`, `D`] mp_tac) >>
  strip_tac >>
  qabbrev_tac `i = mk_inst id DLOAD [arg] [out]` >>
  `new_site_bytes s u = {}` by
    simp[Abbr `u`, update_var_def, new_site_bytes_def, FLOOKUP_DEF,
      pred_setTheory.EXTENSION, SF CONJ_ss] >>
  qexistsl [`step_prov PG G i u`, `step_taint i s u tn`] >>
  rpt conj_tac
  >- (gvs[Abbr `u`] >>
      `~(update_var out (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) s
        with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by simp[update_var_def] >>
      metis_tac[gas_path_ptr_rules, ADD_0])
  >- simp[Abbr `i`, runtime_code_load_clean]
  >- (irule step_prov_out_none >> simp[Abbr `i`, mk_inst_def] >>
      irule out_prov_other_none >> simp[mk_inst_def])
  >- simp[Abbr `i`, step_taint_def, mk_inst_def, set_var_taint_def,
      mem_taint_def, store_taint_def, imm_taint_def, step_writes_def,
      source_memory_write_ranges_def, written_taint_def, range_bytes_def,
      adopt_reset_def]
  >- simp[Abbr `i`, step_taint_def, mk_inst_def, set_var_taint_def,
      mem_taint_def, store_taint_def, imm_taint_def, step_writes_def,
      source_memory_write_ranges_def, written_taint_def, range_bytes_def,
      adopt_reset_def]
  >- simp[Abbr `i`, step_taint_def, mk_inst_def, set_var_taint_def,
      mem_taint_def, store_taint_def, imm_taint_def, step_writes_def,
      source_memory_write_ranges_def, written_taint_def, range_bytes_def,
      adopt_reset_def]
  >- simp[Abbr `i`, step_taint_def, mk_inst_def, set_var_taint_def,
      mem_taint_def, store_taint_def, imm_taint_def, step_writes_def,
      source_memory_write_ranges_def, written_taint_def, range_bytes_def,
      adopt_reset_def] >>
  simp[Abbr `i`, scalar_step_old_prov, scalar_step_old_taint]
QED

Theorem emit_code_load_ptr_path:
  emit_op DLOAD [arg] sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  eval_operand arg s = SOME a /\ op_taint tn arg = {} /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out G' tn' u.
    op = Var out /\ out = STRING #"%" (toString sa.cs_next_var) /\
    u = (update_var out (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) s
        with vs_inst_idx := SUC s.vs_inst_idx) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK u) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    op_taint tn' (Var out) = {} /\ op_prov G' (Var out) = NONE /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> x <> out) /\
    (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id DLOAD [arg]
       [STRING #"%" (toString sa.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all code_load_step_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl [`STRING #"%" (toString sa.cs_next_var)`, `G'`, `tn'`,
    `update_var (STRING #"%" (toString sa.cs_next_var))
      (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) s
        with vs_inst_idx := SUC s.vs_inst_idx`] >>
  gvs[update_var_def] >> rpt strip_tac >> gvs[not_fresh_at_def]
QED
