Theory bodyPtrTypeBuiltinsExtract32BoundsPtr
Ancestors
  extract32Certificate
  bodyPtrTypeBuiltinsBounds bodyPtrBopScalarDynamic bodyPtrBopScalarOutcome
  augAssignPtrScalarRun augAssignPtrScalarCertificate augAssignPtrScalarSafety
  ghostPcTransportPtr instIdxIndep venomExecSemantics
  bodyPtrBopScalarSeq fragGasSeqPtr builtinBytes exprLoweringProps
  compileEnv loweringStateRelDefs codegenRel contextCodegenRel ptrDiscipline venomInst venomState finite_map list pred_set

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

(* The same ghosts certify every cursor, including an aborting assertion. *)
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
