Theory bodyPtrTypeBuiltinsExtract32BoundsPtr
Ancestors
  bodyPtrTypeBuiltinsBounds bodyPtrBopScalarDynamic bodyPtrBopScalarOutcome
  augAssignPtrScalarRun augAssignPtrScalarCertificate augAssignPtrScalarSafety
  ghostPcTransportPtr instIdxIndep venomExecSemantics
  bodyPtrBopScalarSeq fragGasSeqPtr builtinBytes exprLoweringProps
  compileEnv codegenRel contextCodegenRel ptrDiscipline venomInst venomState finite_map list pred_set

Theorem slice_bounds_scalar_certificate:
  compile_assert_slice_bounds a n limit sa = ((),sb) /\
  a IN A /\ n IN A /\ limit IN A /\
  (!z. z IN R ==> not_fresh_at sa z) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B
Proof
  strip_tac >> drule compile_assert_slice_bounds_shape >> strip_tac >>
  simp[] >>
  `!j. sa.cs_next_var <= j ==> STRING #"%" (toString j) NOTIN R` by
    (rpt strip_tac >> spose_not_then assume_tac >>
     first_x_assum drule >> simp[not_fresh_at_def]) >>
  simp[bop_scalar_seq_def, mk_inst_def]
QED

Theorem slice_bounds_scalar_code:
  compile_assert_slice_bounds a n limit sa = ((),sb) /\
  scalar_available A a /\ scalar_available A n /\ scalar_available A limit ==>
  scalar_code A (emitted_insts sa sb)
Proof
  strip_tac >> drule compile_assert_slice_bounds_shape >> strip_tac >>
  simp[scalar_code_def, scalar_shape_def, scalar_binary_def,
       scalar_unary_def, mk_inst_def, scalar_available_def] >>
  gvs[scalar_available_def] >> simp[]
QED

Theorem scalar_code_certificate_cursor:
  !code A G tn s H tm.
  scalar_code A code /\
  (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
  ~ctx_has_dalloca ctx /\ inst_seq_ptr D 0 ctx fn PG G tn code s H tm ==>
  !k. inst_seq_ptr D 0 ctx fn PG G tn code (s with vs_inst_idx := k) H tm
Proof
  Induct >- simp[inst_seq_ptr_def] >>
  rpt gen_tac >> simp[scalar_code_def] >> strip_tac >>
  `EVERY (\op. op_prov G op = NONE /\ op_taint tn op = {}) h.inst_operands` by
    (gvs[EVERY_MEM] >> metis_tac[scalar_available_clean]) >>
  `~is_terminator h.inst_opcode` by metis_tac[scalar_shape_control] >>
  `!k. ptr_inst_ok D 0 0 ctx fn G tn h (s with vs_inst_idx := k)` by
    (rpt strip_tac >> irule scalar_ptr_inst_ok >> simp[]) >>
  Cases_on `step_inst_base h s` >>
  gvs[Once inst_seq_ptr_def] >>
  simp[Once inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def] >>
  rename1 `step_inst_base h s = OK u` >>
  `!v. v IN A UNION set h.inst_outputs ==>
    op_prov (step_prov PG G h u) (Var v) = NONE /\
    op_taint (step_taint h s u tn) (Var v) = {}` by
    (ho_match_mp_tac scalar_step_clean >> simp[]) >>
  first_x_assum drule >> disch_then drule >> simp[] >>
  disch_then drule >> simp[]
QED

(* The same ghosts certify every cursor, including an aborting assertion. *)
Theorem slice_bounds_fixed_certificate:
  compile_assert_slice_bounds a n limit sa = ((),sb) /\
  scalar_available A a /\ scalar_available A n /\ scalar_available A limit /\
  (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
  ~ctx_has_dalloca ctx ==>
  ?H th. (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) H th) /\
    (!z. not_fresh_at sa z ==> FLOOKUP H z = FLOOKUP G z /\
      op_taint th (Var z) = op_taint tn (Var z)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all slice_bounds_scalar_code >> strip_tac >>
  drule_all scalar_code_inst_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`, `s`] strip_assume_tac) >>
  drule_all scalar_seq_metadata_frame >> strip_tac >>
  qexistsl_tac [`H`, `tm`] >>
  conj_tac >- (irule scalar_code_certificate_cursor >> simp[] >>
    qexists_tac `A` >> simp[]) >> simp[] >>
  `!z. not_fresh_at sa z ==>
    ~MEM z (FLAT (MAP (\i. i.inst_outputs) (emitted_insts sa sb)))` by
    (drule compile_assert_slice_bounds_shape >> strip_tac >>
     simp[mk_inst_def] >> rpt strip_tac >>
     gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LE_ADD]) >>
  metis_tac[]
QED

Theorem slice_bounds_normal_ptr_path:
  compile_assert_slice_bounds a n limit sa = ((),sb) /\
  op_prov G a = NONE /\ op_taint tn a = {} /\
  op_prov G n = NONE /\ op_taint tn n = {} /\
  op_prov G limit = NONE /\ op_taint tn limit = {} /\
  ~ctx_has_dalloca ctx /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th. gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + 6)) /\
    (!z. not_fresh_at sa z ==> FLOOKUP H z = FLOOKUP G z /\
      FLOOKUP th.t_var z = FLOOKUP tn.t_var z) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >>
  `?B. bop_scalar_seq {z | not_fresh_at sa z} {a;n;limit}
    (emitted_insts sa sb) B` by
    (irule slice_bounds_scalar_certificate >> simp[] >>
     qexistsl_tac [`a`, `limit`, `n`] >> simp[]) >>
  `!op. op IN {a;n;limit} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> metis_tac[]) >>
  drule_all bop_scalar_seq_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  drule compile_assert_slice_bounds_shape >> strip_tac >> gvs[]
QED

Theorem slice_bounds_abort_ptr_path:
  compile_assert_slice_bounds a n limit sa = ((),sb) /\
  op_prov G a = NONE /\ op_taint tn a = {} /\
  op_prov G n = NONE /\ op_taint tn n = {} /\
  op_prov G limit = NONE /\ op_taint tn limit = {} /\
  ~ctx_has_dalloca ctx /\ run_inst_seq (emitted_insts sa sb) s = Abort err t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th count j. gas_path_ptr D 0 ctx fn PG G tn s count H th
      (Abort err (t with vs_inst_idx := j)) /\
    (!z. not_fresh_at sa z ==> FLOOKUP H z = FLOOKUP G z /\
      FLOOKUP th.t_var z = FLOOKUP tn.t_var z) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >>
  `?B. bop_scalar_seq {z | not_fresh_at sa z} {a;n;limit}
    (emitted_insts sa sb) B` by
    (irule slice_bounds_scalar_certificate >> simp[] >>
     qexistsl_tac [`a`, `limit`, `n`] >> simp[]) >>
  `!op. op IN {a;n;limit} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> metis_tac[]) >>
  drule_all bop_scalar_seq_abort_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`, `n'`, `j`] >> simp[]
QED
