(* BoolClamp ghosts at a named successful scalar endpoint. *)
Theory ctorDeployMemoryRunPtrPrefixScalarBool
Ancestors
  loweringStateRelDefs
  ctorDeployMemoryRunPtrPrefixScalarPackage
  ctorDeployMemoryRunPtrPrefixCanonical ctorDeployMemoryRunPtrPrefixBoolWord
  abiEncoder abiDecoderContract abiDecoderClampedWord compileEnv exprLoweringProps
  venomState venomInst venomExecSemantics ptrDiscipline ptrSafeRun
  fragExec finite_map list rich_list words pred_set allocaFrontierBound

Theorem prefix_scalar_bool_success:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) hi (DecPrimWord BoolClamp) st = ((),st') /\
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
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecPrimWord BoolClamp) st = ((),st') ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  LENGTH st'.cs_current_insts = LENGTH st.cs_current_insts+5
Proof
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, comp_return_def, compile_abi_decode_range_check_def, SRULE [LET_THM] prefix_boolword_compile] >>
  strip_tac >> gvs[IS_PREFIX_APPEND]
QED

Theorem prefix_scalar_bool_ghost:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
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

val canonical_pair = ``\ty tv.
 !dst src st st' ctx func site initial limit_st sb d D N ids av v root_di
  G tn b sz Ddead lo PG.
 compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
   (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\
 eval_operand (Var dst) initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
   initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (!x. src = Var x \/ Var dst = Var x \/ Lit 0w = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb.
    lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
 unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 FLOOKUP G dst = SOME (b,sz) /\ b <= d /\
 d + type_memory_bytes ce ty <= b+sz /\
 op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx ==>
 ?actual H qt B.
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
    lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\
 FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\
 DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem =
                        mem_bytes_at a 1 actual.vs_memory) ==>
    val_in_memory tv v d mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
                           op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)``;

Theorem prefix_canonical_bool_paired:
  type_to_abi_dec_info sf ce ty = DecPrimWord BoolClamp ==> (^canonical_pair) ty tv
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  drule_all prefix_scalar_prepare >> strip_tac >>
  `d < dimword (:256)` by
    (drule_all alloca_frontier_inv_bound >> decide_tac) >>
  `compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
    (DecPrimWord BoolClamp) st = ((),st')` by metis_tac[] >>
  `d+32 <= b+sz` by metis_tac[] >>
  drule_all prefix_scalar_bool_ghost >>
  disch_then (qspecl_then [`PG`,`Ddead`] strip_assume_tac) >>
  qabbrev_tac `actual = t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  rule_assum_tac (PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all prefix_scalar_transport >> strip_tac >>
  drule_all prefix_scalar_support_package >> strip_tac >>
  qexistsl [`actual`,`H`,`qt`,`range_bytes [(d,32)]`] >>
  asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  simp[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]
QED

val _ = export_theory();
