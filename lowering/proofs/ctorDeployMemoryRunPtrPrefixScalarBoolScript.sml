(* BoolClamp ghosts at a named successful scalar endpoint. *)
Theory ctorDeployMemoryRunPtrPrefixScalarBool
Ancestors
  compileEnv
  ctorDeployMemoryRunPtrPrefixScalarPackage
  ctorDeployMemoryRunPtrPrefixCanonical ctorDeployMemoryRunPtrPrefixBoolWord
  abiEncoder abiDecoderContract abiDecoderClampedWord exprLoweringProps
  venomState venomInst venomExecSemantics ptrDiscipline ptrSafeRun
  fragExec finite_map list rich_list words pred_set allocaFrontierBound

Theorem prefix_scalar_bool_success:
  compile_abi_decode_to_buf (Var dst) src DLOAD hi (DecPrimWord BoolClamp) st = ((),st') /\
  x = "%" ++ toString st.cs_next_var /\
  y = "%" ++ toString (st.cs_next_var+1) /\
  z = "%" ++ toString (st.cs_next_var+2) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand src s = SOME a /\ eval_operand (Var dst) s = SOME p /\
  x <> dst /\ y <> dst /\ z <> dst /\ x <> y /\ x <> z /\ y <> z /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= w2n p /\ w2n p+32 <= b+sz /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  ?H qt.
    qt.t_mem = tn.t_mem DIFF range_bytes [(w2n p,32)] /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. v <> x /\ v <> y /\ v <> z ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt
      (t with vs_inst_idx := s.vs_inst_idx+5)) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all prefix_decoder_boolword_ptr >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `word_of_bytes T (0w:bytes32) bytes` >>
  qmatch_goalsub_abbrev_tac `mstore (w2n p) w pre` >>
  qabbrev_tac `end = mstore (w2n p) w pre` >>
  qmatch_goalsub_abbrev_tac `step_taint (mk_inst (st.cs_next_id+4) MSTORE [Var dst;Var x] []) u v qt0` >>
  qabbrev_tac `qt = step_taint (mk_inst (st.cs_next_id+4) MSTORE [Var dst;Var x] []) u v qt0` >>
  qabbrev_tac `H = DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x})) (COMPL {y})) (COMPL {z})` >>
  strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = if _ then _ else _` mp_tac >>
  asm_rewrite_tac[] >> IF_CASES_TAC >> simp[] >> strip_tac >>
  qexistsl [`H`,`qt`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (qpat_x_assum `!v. v <> x /\ _ ==> _` mp_tac >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem prefix_scalar_bool_shape:
  compile_abi_decode_to_buf dst src DLOAD hi (DecPrimWord BoolClamp) st = ((),st') ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  LENGTH st'.cs_current_insts = LENGTH st.cs_current_insts+5
Proof
  simp[compile_abi_decode_to_buf_def, SRULE [LET_THM] prefix_boolword_compile] >>
  strip_tac >> gvs[IS_PREFIX_APPEND]
QED

Theorem prefix_scalar_bool_ghost:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
    (DecPrimWord BoolClamp) st = ((),st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand (Var dst) s = SOME (n2w d) /\ d < dimword (:256) /\
  (!v. src = Var v \/ Var dst = Var v \/ Lit 0w = Var v ==> not_fresh_at st v) /\
  fn_has_code st st' fn /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= d /\ d+32 <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?H qt.
    qt.t_mem = tn.t_mem DIFF range_bytes [(d,32)] /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==> FLOOKUP H v = FLOOKUP G v /\
      op_taint qt (Var v) = op_taint tn (Var v)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt
      (t with vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule prefix_scalar_bool_shape >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX st'.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[emitted_insts_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >> metis_tac[]) >>
  qabbrev_tac `x = "%" ++ toString st.cs_next_var` >>
  qabbrev_tac `y = "%" ++ toString (st.cs_next_var+1)` >>
  qabbrev_tac `z = "%" ++ toString (st.cs_next_var+2)` >>
  `x <> dst /\ y <> dst /\ z <> dst /\ x <> y /\ x <> z /\ y <> z` by
    gvs[Abbr `x`, Abbr `y`, Abbr `z`, not_fresh_at_def] >>
  `x = "%" ++ toString st.cs_next_var /\
   y = "%" ++ toString (st.cs_next_var+1) /\
   z = "%" ++ toString (st.cs_next_var+2)` by simp[Abbr `x`,Abbr `y`,Abbr `z`] >>
  `b <= w2n (n2w d:bytes32) /\ w2n (n2w d:bytes32)+32 <= b+sz` by simp[w2n_n2w] >>
  drule_all prefix_scalar_bool_success >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >>
  `w2n (n2w d:bytes32) = d` by simp[w2n_n2w] >>
  pure_asm_rewrite_tac[] >> strip_tac >>
  qexistsl [`H`,`qt`] >> asm_rewrite_tac[] >>
  gen_tac >> disch_tac >>
  first_x_assum (qspec_then `v` mp_tac) >>
  simp[not_fresh_at_def] >>
  `v <> STRING #"%" (toString st.cs_next_var) /\
   v <> STRING #"%" (toString (st.cs_next_var+1)) /\
   v <> STRING #"%" (toString (st.cs_next_var+2))` by
    (qpat_x_assum `not_fresh_at st v` mp_tac >>
     pure_rewrite_tac[not_fresh_at_def] >> strip_tac >>
     rpt conj_tac >> first_x_assum irule >> decide_tac) >>
  simp[]
QED

val _ = export_theory();
