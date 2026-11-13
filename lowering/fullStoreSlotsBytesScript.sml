(* Joint control arithmetic for live bytestring stores. *)
Theory fullStoreSlotsBytes
Ancestors
  fullStoreSlotsProbe fragGasCopyLoop fragGasSeqAbort bodyPtrEnvBuiltinsEdges
  bytestringCopyExecution fragGasSeqPtr fragGasOriginPtr
  ptrSafetyTransport instMemFrontier fragExecMem fragExec memSafeRun
  context emitHelper emitHelperProps codegenRel contextCodegenRel
  bodyPtrDefs ptrDiscipline venomState venomInst venomExecSemantics
  compileEnv exprLoweringProps loweringStateRelDefs unitTransformDefs
  finite_map pred_set list rich_list arithmetic words

Theorem store_slots_count_arith_ptr:
  lookup_var lv s = SOME w /\ op_taint tn (Var lv) = {} /\ FLOOKUP G lv = NONE /\
  ~ctx_has_dalloca ctx ==>
  !D func PG id.
  inst_seq_ptr D 0 ctx func PG G tn
    [mk_inst id ADD [Var lv;Lit 63w] [sv];
     mk_inst (id+1) SHR [Lit 5w;Var sv] [out]] s
    (DRESTRICT (DRESTRICT G (COMPL {sv})) (COMPL {out}))
    (tn with t_var := (tn.t_var |+ (sv,{})) |+ (out,{}))
Proof
  strip_tac >> rpt gen_tac >>
  `ptr_inst_ok D 0 0 ctx func G tn
    (mk_inst id ADD [Var lv;Lit 63w] [sv]) s` by
    (irule ptr_inst_ok_scalar_builtin >> simp[] >> rpt strip_tac >> gvs[op_taint_def]) >>
  simp[inst_seq_ptr_def, step_inst_base_opcode_eqs, mk_inst_def,
    exec_pure2_def, eval_operand_def] >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
    set_var_taint_def, out_taint_def, op_taint_def, shift_taint_def,
    store_taint_def, imm_taint_def, mem_taint_def, adopt_reset_def,
    step_writes_def, source_memory_write_ranges_def, written_taint_def,
    range_bytes_def, new_site_bytes_def, eval_operand_def,
    update_var_def, lookup_var_def, FLOOKUP_UPDATE, dimword_def] >>
  conj_tac >- (rewrite_tac[GSYM mk_inst_def] >>
    irule ptr_inst_ok_scalar_builtin >> simp[] >> rpt strip_tac >>
    gvs[op_taint_def, FLOOKUP_UPDATE]) >>
  gvs[op_taint_def, first_prov_def, op_prov_def] >>
  simp[taint_component_equality, EXTENSION, FLOOKUP_DEF, SF CONJ_ss]
QED

Theorem store_slots_count_arith_origin_ptr:
  lookup_var lv s = SOME w /\ op_taint tn (Var lv) = {} /\ FLOOKUP G lv = NONE /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ADD [Var lv;Lit 63w] [sv];
    mk_inst (id+1) SHR [Lit 5w;Var sv] [out]]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  !D explicit PG.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (update_var out ((w+63w) >>> 5) (update_var sv (w+63w) s)
        with vs_inst_idx := s.vs_inst_idx+2),
       DRESTRICT (DRESTRICT G (COMPL {sv})) (COMPL {out}),
       tn with t_var := (tn.t_var |+ (sv,{})) |+ (out,{}))
Proof
  strip_tac >> rpt gen_tac >>
  `inst_seq_ptr D 0 ctx func PG G tn
    [mk_inst id ADD [Var lv;Lit 63w] [sv];
     mk_inst (id+1) SHR [Lit 5w;Var sv] [out]] s
    (DRESTRICT (DRESTRICT G (COMPL {sv})) (COMPL {out}))
    (tn with t_var := (tn.t_var |+ (sv,{})) |+ (out,{}))` by
    (irule store_slots_count_arith_ptr >> simp[] >> metis_tac[]) >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`) run_inst_seq_origin_ptr_lift >>
  disch_then (qspecl_then [
    `update_var out ((w+63w) >>> 5) (update_var sv (w+63w) s)`,
    `lo`,`explicit`] mp_tac) >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_mem_ok_def,
    run_inst_seq_def, inst_mem_below_frontier_def, inst_dload_in_section_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def,
    lookup_var_def, update_var_def, FLOOKUP_UPDATE, dimword_def] >>
  gvs[mk_inst_def] >> metis_tac[]
QED

Theorem store_slots_bytes_count_code:
  compile_bytestring_word_count (Var root) sa = (out,sb) ==>
  ?lv sv ov.
    out = Var ov /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id MLOAD [Var root] [lv];
       mk_inst (sa.cs_next_id+1) ADD [Var lv;Lit 63w] [sv];
       mk_inst (sa.cs_next_id+2) SHR [Lit 5w;Var sv] [ov]] /\
    ALL_DISTINCT [lv;sv;ov] /\
    (!x. not_fresh_at sa x ==> ~MEM x [lv;sv;ov])
Proof
  simp[compile_bytestring_word_count_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_var_def, fresh_id_def, emit_def] >> strip_tac >>
  gvs[] >> qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
    `STRING #"%" (toString (sa.cs_next_var+1))`] >>
  simp[ALL_DISTINCT, not_fresh_at_def] >> rpt strip_tac >> metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]
QED

Theorem store_slots_bytes_count_run:
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id MLOAD [Var root] [lv];
    mk_inst (id+1) ADD [Var lv;Lit 63w] [sv];
    mk_inst (id+2) SHR [Lit 5w;Var sv] [out]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  ptr_covers G tn root s 32 /\ lookup_var root s = SOME a /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  w2n a + 32 <= s.vs_alloca_next /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    mem_word_at (w2n a) m = w) ==>
  !D explicit PG.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (update_var out ((w+63w) >>> 5)
        (update_var sv (w+63w) (update_var lv w s))
        with vs_inst_idx := s.vs_inst_idx+3),
       DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {lv})) (COMPL {sv})) (COMPL {out}),
       tn with t_var := ((tn.t_var |+ (lv,{})) |+ (sv,{})) |+ (out,{}))
Proof
  strip_tac >> rpt gen_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  drule_all store_slots_robust_load_origin_ptr >>
  disch_then (qspecl_then [`D`,`explicit`,`PG`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK u,G1,t1)` >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G1,t1) []
    (OK (update_var out ((w+63w) >>> 5) (update_var sv (w+63w) u)
      with vs_inst_idx := u.vs_inst_idx+2),
     DRESTRICT (DRESTRICT G1 (COMPL {sv})) (COMPL {out}),
     t1 with t_var := (t1.t_var |+ (sv,{})) |+ (out,{}))` by
    (irule store_slots_count_arith_origin_ptr >>
     simp[Abbr `u`, Abbr `G1`, Abbr `t1`, update_var_def, lookup_var_def,
       op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, allocas_from_def] >>
     conj_tac >- gvs[allocas_from_def] >>
     qexistsl_tac [`id+1`,`lv`] >> simp[] >>
     gvs[ADD_ASSOC]) >>
  qpat_x_assum `gas_origin_ptr_path _ (s,G,tn) [] _`
    (mp_then Any mp_tac gas_origin_ptr_path_append) >>
  simp[] >> disch_then drule >>
  simp[Abbr `u`, Abbr `G1`, Abbr `t1`, update_var_def, ADD1]
QED

Theorem store_slots_bytestring_count_origin_ptr:
  compile_bytestring_word_count (Var root) sa = (out,sb) /\
  fn_has_code sa sb func /\ not_fresh_at sa root /\
  lookup_var root s = SOME a /\ ptr_covers G tn root s capacity /\
  32 <= capacity /\ len+63 < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  w2n a+32 <= s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    mem_word_at (w2n a) m = n2w len) ==>
  ?u Gf tf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    eval_operand out u = SOME (n2w (1 + word_size len)) /\
    op_taint tf out = {} /\ op_prov Gf out = NONE /\
    ptr_covers Gf tf root u capacity /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule store_slots_bytes_count_code >> strip_tac >> gvs[] >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX [mk_inst sa.cs_next_id MLOAD [Var root] [lv];
      mk_inst (sa.cs_next_id+1) ADD [Var lv;Lit 63w] [sv];
      mk_inst (sa.cs_next_id+2) SHR [Lit 5w;Var sv] [ov]]
      (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[GSYM APPEND_ASSOC, DROP_APPEND]) >>
  qexistsl_tac [
    `update_var ov (((n2w len:bytes32)+63w) >>> 5)
      (update_var sv ((n2w len:bytes32)+63w) (update_var lv (n2w len) s))
      with vs_inst_idx := s.vs_inst_idx+3`,
    `DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {lv})) (COMPL {sv})) (COMPL {ov})`,
    `tn with t_var := ((tn.t_var |+ (lv,{})) |+ (sv,{})) |+ (ov,{})`] >>
  conj_tac >- (rpt gen_tac >> irule store_slots_bytes_count_run >>
    simp[] >> qexistsl_tac [`a`,`sa.cs_next_id`,`root`] >>
    simp[] >> gvs[ptr_covers_def] >>
    qexistsl_tac [`a`,`b`,`sz'`] >> simp[] >> decide_tac) >>
  `root <> lv /\ root <> sv /\ root <> ov` by metis_tac[] >>
  simp[bytestring_word_count_exact, eval_operand_def, lookup_var_def, update_var_def,
    op_taint_def, op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
    venom_state_component_equality, ptr_covers_def]
  >- gvs[ptr_covers_def, op_taint_def, lookup_var_def] >>
  rpt strip_tac >> `x <> lv /\ x <> sv /\ x <> ov` by metis_tac[] >> simp[]
QED
