Theory bodyFullBopBytesEqSuffix
Ancestors
  bodyPtrBopScalarSeq bodyPtrWordBuiltinsAbsSuffix exprSimCompare
  exprLoweringProps exprLowering ptrDiscipline finite_map list pred_set
  compileEnv rich_list emitHelper loweringStateRelDefs
  venomExecSemantics venomState venomInst ptrSafeRun fragGasSeqPtr bodyPtrBopScalarStep
  instIdxIndep

Theorem bop_bytes_eq_suffix_ptr:
  (bop = Eq \/ bop = NotEq) /\
  (ty = BaseT AddressT \/ ?m. ty = BaseT (BytesT (Fixed m))) /\
  compile_binop bop x y ty NONE NONE sa = (op,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  op_prov G y = NONE /\ op_taint tn y = {} /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?G' tn'.
    (!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn') /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!z. not_fresh_at sa z ==>
      FLOOKUP G' z = FLOOKUP G z /\
      FLOOKUP tn'.t_var z = FLOOKUP tn.t_var z)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `bop = Eq`
  >- (gvs[compile_binop_def, compile_compare_def, comp_bind_def, comp_ignore_bind_def,
          emit_op_def, fresh_var_def, fresh_id_def, emit_def, comp_return_def,
          emitted_insts_def, DROP_LENGTH_APPEND] >> suspend "eq") >>
  gvs[compile_binop_def, compile_compare_def, comp_bind_def, comp_ignore_bind_def,
      emit_op_def, fresh_var_def, fresh_id_def, emit_def, comp_return_def,
      emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND] >> suspend "neq"
QED

Resume bop_bytes_eq_suffix_ptr[eq]:
  qmatch_asmsub_abbrev_tac `run_inst_seq [i] s` >>
  Cases_on `step_inst_base i s` >> gvs[run_inst_seq_def] >>
  rename1 `step_inst_base i s = OK u` >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp` by
    (mp_tac (GEN_ALL (Q.INST [`opc` |-> `EQ`] bop_scalar_state_frame)) >>
     simp[Abbr `i`] >> disch_then drule >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  qexistsl_tac [`step_prov PG G i u`, `step_taint i s u tn`] >>
  conj_tac
  >- (gen_tac >> simp[inst_seq_ptr_def] >>
      irule word_abs_scalar_inst_ok >> simp[Abbr `i`, mk_inst_def] >>
      rpt strip_tac >> gvs[]) >>
  mp_tac (Q.INST [`opc` |-> `EQ`, `ops` |-> `[x;y]`,
    `id` |-> `sa.cs_next_id`,
    `tmp` |-> `STRING #"%" (toString sa.cs_next_var)`] bop_scalar_ghost_frame) >>
  simp[Abbr `i`] >> strip_tac >> simp[] >> rpt strip_tac >>
  metis_tac[not_fresh_at_def, arithmeticTheory.LESS_EQ_REFL]
QED

Resume bop_bytes_eq_suffix_ptr[neq]:
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND] >>
  qmatch_asmsub_abbrev_tac `run_inst_seq [i;j] s` >>
  Cases_on `step_inst_base i s` >> gvs[Once run_inst_seq_def] >>
  rename1 `step_inst_base i s = OK u` >>
  `run_inst_seq [j] (u with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[fragExecTheory.run_inst_seq_inst_idx, exec_result_map_def,
          Abbr `j`, mk_inst_def, is_terminator_def]) >>
  qmatch_asmsub_abbrev_tac `run_inst_seq [j] v` >>
  Cases_on `step_inst_base j v` >> gvs[run_inst_seq_def] >>
  rename1 `step_inst_base j v = OK w` >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp` by
    (mp_tac (GEN_ALL (Q.INST [`opc` |-> `EQ`] bop_scalar_state_frame)) >>
     simp[Abbr `i`] >> disch_then drule >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `allocas_from lo v` by (gvs[Abbr `v`, allocas_from_def] >> metis_tac[]) >>
  `w.vs_allocas = v.vs_allocas /\ w.vs_fmp = v.vs_fmp` by
    (mp_tac (GEN_ALL (Q.INST [`opc` |-> `ISZERO`] bop_scalar_state_frame)) >>
     simp[Abbr `j`] >> disch_then drule >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  mp_tac (Q.INST [`opc` |-> `EQ`, `ops` |-> `[x;y]`,
    `id` |-> `sa.cs_next_id`,
    `tmp` |-> `STRING #"%" (toString sa.cs_next_var)`] bop_scalar_ghost_frame) >>
  simp[Abbr `i`] >> strip_tac >>
  qabbrev_tac `G2 = step_prov PG G1 j w` >>
  qabbrev_tac `tn2 = step_taint j v w tn1` >>
  `op_prov G2 (Var (STRING #"%" (toString (sa.cs_next_var + 1)))) = NONE /\
   op_taint tn2 (Var (STRING #"%" (toString (sa.cs_next_var + 1)))) = {} /\
   tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
   tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm /\
   (!z. z <> STRING #"%" (toString (sa.cs_next_var + 1)) ==>
     FLOOKUP G2 z = FLOOKUP G1 z /\ FLOOKUP tn2.t_var z = FLOOKUP tn1.t_var z)` by
    (simp[NoAsms, Abbr `G2`, Abbr `tn2`, Abbr `j`] >>
     irule bop_scalar_ghost_frame >> simp[]) >>
  qexistsl_tac [`G2`, `tn2`] >> conj_tac
  >- (gen_tac >> simp[Once inst_seq_ptr_def] >> conj_tac
      >- (irule word_abs_scalar_inst_ok >> simp[mk_inst_def] >>
          rpt strip_tac >> gvs[]) >>
      simp[Abbr `G1`, Abbr `tn1`, inst_seq_ptr_def, Abbr `G2`, Abbr `tn2`] >>
      irule word_abs_scalar_inst_ok >> gvs[Abbr `j`, mk_inst_def]) >>
  simp[] >> rpt strip_tac >>
  `z <> STRING #"%" (toString sa.cs_next_var) /\
   z <> STRING #"%" (toString (sa.cs_next_var + 1))` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL,
       arithmeticTheory.LESS_EQ_ADD]) >>
  metis_tac[]
QED

Finalise bop_bytes_eq_suffix_ptr
