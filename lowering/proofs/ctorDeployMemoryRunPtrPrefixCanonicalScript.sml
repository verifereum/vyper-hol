(* Canonical value semantics at the concrete checked decoder endpoint. *)
Theory ctorDeployMemoryRunPtrPrefixCanonical
Ancestors
  loweringStateRelDefs valueEncodingDefs
  ctorDeployMemoryRunPtrPrefixWord ctorDeployMemoryRunPtrPrefixSteps
  ctorDeployMemoryRunPtrPrefixBoolWord
  venomState venomInst venomExecSemantics ctorAbiActualWordRun
  abiDecoderContract abiDecoderCoherence abiDecoderTypedContract
  abiDecoderLayout abiDecoderReentryPointer
  abiEncoder emitHelper compileEnv exprLoweringProps finite_map list words
  memLocDefs instIdxIndep ptrDiscipline ptrSafeRun
  ctorAbiActualMemory abiDecoderWordTyped valueEncoding valueEncodingProps
  valueEncodingProofs vyperTyping pred_set ctorAbiActualRecursive
  abiDecoderClampedWord abiDecoderLoop fragExec
  allocaFrontierBound abiDecoderReentry ctorAbiActualWorld ctorAbiActualNarrowWord
  ctorAbiActualFrame

(* Shared recursive consumer interface. B is semantic support, not capacity.
   Singleton windows observe explicit and implicit zero bytes identically. *)
val canonical_pair = ``\ty tv.
 !dst src st st' ctx func site initial limit_st sb d D N ids av v root_di
  G tn b sz Ddead lo PG.
 compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
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

Theorem prefix_canonical_noclamp_value:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
    (DecPrimWord NoClamp) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord NoClamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand (Var dst) initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  x = "%" ++ toString st.cs_next_var /\ x <> dst ==>
  let w = word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP sb initial.vs_data_section ++ REPLICATE 32 0w));
      l = update_var x w initial;
      t = mstore d w l
  in
    run_inst_seq (emitted_insts st st') initial = OK t /\
    val_in_memory tv v d t.vs_memory /\ fresh_vars_wrt limit_st t /\
    abi_decode_frame d 32 initial t /\
    (!op z. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME z ==> eval_operand op t = SOME z) /\
    t.vs_allocas = initial.vs_allocas /\
    t.vs_alloca_next = initial.vs_alloca_next
Proof
  strip_tac >>
  drule_all ctor_actual_word_ceiling_sequence >> strip_tac >>
  drule prefix_decoder_noclamp_code >> strip_tac >>
  simp[] >>
  `run_inst_seq (emitted_insts st st') initial =
    OK (mstore d
      (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP sb initial.vs_data_section ++ REPLICATE 32 0w)))
      (update_var x
        (word_of_bytes T (0w:bytes32)
          (TAKE 32 (DROP sb initial.vs_data_section ++ REPLICATE 32 0w))) initial))` by
    (qpat_x_assum `run_inst_seq _ _ = _` kall_tac >>
     gvs[run_inst_seq_def, prefix_dload_step, prefix_mstore_step,
      step_inst_base_def, mk_inst_def, exec_read1_def, exec_write2_def,
      eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
      w2n_n2w]) >>
  gvs[]
QED

Theorem prefix_canonical_noclamp_ghost_frame:
  eval_operand src s = SOME a /\ eval_operand (Var dst) s = SOME p /\
  x <> dst ==>
  let w = word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w));
      i = mk_inst iid DLOAD [src] [x];
      j = mk_inst (iid+1) MSTORE [Var dst;Var x] [];
      l = update_var x w s;
      t = mstore (w2n p) w l;
      q = step_taint i s l tn;
      r = step_taint j (l with vs_inst_idx := s.vs_inst_idx+1)
             (t with vs_inst_idx := s.vs_inst_idx+1) q
  in
    r.t_mem = tn.t_mem DIFF range_bytes [(w2n p,32)] /\
    (!n. n < 32 ==> w2n p+n NOTIN r.t_mem) /\
    r.t_stor = tn.t_stor /\ r.t_trans = tn.t_trans /\ r.t_imm = tn.t_imm /\
    (!v. v <> x ==> op_taint r (Var v) = op_taint tn (Var v)) /\
    (!v. v <> x ==> FLOOKUP (DRESTRICT G (COMPL {x})) v = FLOOKUP G v)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `update_var x w s` >>
  qabbrev_tac `l = update_var x w s` >>
  qabbrev_tac `t = mstore (w2n p) w l` >>
  qabbrev_tac `q = step_taint (mk_inst iid DLOAD [src] [x]) s l tn` >>
  `q.t_mem = tn.t_mem /\ q.t_stor = tn.t_stor /\
   q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm /\
   (!v. v <> x ==> op_taint q (Var v) = op_taint tn (Var v))` by
    (simp[Abbr `q`] >>
     irule (SRULE [LET_THM] prefix_boolword_pure_taint_frame) >>
     simp[Abbr `l`, update_var_def]) >>
  `op_taint q (Var x) = {}` by
    simp[Abbr `q`, Abbr `l`, Abbr `w`, prefix_dload_output_taint] >>
  `eval_operand (Var dst) l = SOME p /\ eval_operand (Var x) l = SOME w` by
    gvs[Abbr `l`, update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  mp_tac (Q.INST [`s` |-> `l with vs_inst_idx := s.vs_inst_idx+1`,
    `t` |-> `t with vs_inst_idx := s.vs_inst_idx+1`, `tn` |-> `q`,
    `iid` |-> `iid+1`] (SRULE [LET_THM] prefix_boolword_store_taint_frame)) >>
  (impl_tac >- simp[eval_op_inst_idx, Abbr `t`, mstore_def]) >>
  strip_tac >> simp[FLOOKUP_DRESTRICT] >>
  simp[range_bytes_def] >> rpt strip_tac >> decide_tac
QED

Theorem prefix_canonical_noclamp_ghost_nat[local]:
  eval_operand src s = SOME (n2w sb) /\
  eval_operand (Var dst) s = SOME (n2w d) /\
  sb < dimword (:256) /\ d < dimword (:256) /\ x <> dst /\
  w = word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP sb s.vs_data_section ++ REPLICATE 32 0w)) /\
  l = update_var x w s /\ t = mstore d w l /\
  q = step_taint (mk_inst iid DLOAD [src] [x]) s l tn /\
  r = step_taint (mk_inst (iid+1) MSTORE [Var dst;Var x] [])
      (l with vs_inst_idx := s.vs_inst_idx+1)
      (t with vs_inst_idx := s.vs_inst_idx+1) q ==>
  r.t_mem = tn.t_mem DIFF range_bytes [(d,32)] /\
  r.t_stor = tn.t_stor /\ r.t_trans = tn.t_trans /\ r.t_imm = tn.t_imm /\
  (!v. v <> x ==> op_taint r (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  qpat_assum `eval_operand src s = SOME (n2w sb)`
    (mp_then Any (drule_all_then mp_tac) prefix_canonical_noclamp_ghost_frame) >>
  disch_then (qspecl_then [`tn`,`iid`] mp_tac) >>
  disch_then (mp_tac o SPEC_ALL) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  asm_simp_tac std_ss [w2n_n2w] >>
  rpt strip_tac >> gvs[]
QED

Theorem prefix_canonical_noclamp_continuation:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
    (DecPrimWord NoClamp) st = ((),st') /\
  x = "%" ++ toString st.cs_next_var /\ x <> dst /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand src s = SOME a /\ eval_operand (Var dst) s = SOME p /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= w2n p /\ w2n p+32 <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let w = word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w));
      i = mk_inst st.cs_next_id DLOAD [src] [x];
      j = mk_inst (st.cs_next_id+1) MSTORE [Var dst;Var x] [];
      l = update_var x w s;
      t = mstore (w2n p) w l;
      q = step_taint i s l tn;
      r = step_taint j (l with vs_inst_idx := s.vs_inst_idx+1)
             (t with vs_inst_idx := s.vs_inst_idx+1) q;
      H = DRESTRICT G (COMPL {x})
  in
    run_inst_seq (emitted_insts st st') s = OK t /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H r
        (t with vs_inst_idx := s.vs_inst_idx+2)) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `update_var x w s` >>
  qabbrev_tac `l = update_var x w s` >>
  qabbrev_tac `t = mstore (w2n p) w l` >>
  qabbrev_tac `q = step_taint (mk_inst st.cs_next_id DLOAD [src] [x]) s l tn` >>
  `!fuel. ghost_step fuel ctx PG G tn
      (mk_inst st.cs_next_id DLOAD [src] [x]) s =
      (DRESTRICT G (COMPL {x}),q)` by
    (gen_tac >>
     qpat_assum `eval_operand src s = SOME a`
       (mp_then Any mp_tac prefix_dload_ghost_step) >>
     simp[Abbr `q`, Abbr `l`, Abbr `w`]) >>
  conj_tac
  >- (drule prefix_decoder_noclamp_code >> strip_tac >>
      gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def,
           exec_read1_def, exec_write2_def,
           Abbr `t`, Abbr `l`, Abbr `w`, eval_operand_def, lookup_var_def,
           update_var_def, FLOOKUP_UPDATE]) >>
  strip_tac >> gen_tac >>
  drule_all prefix_decoder_noclamp_ptr >>
  disch_then (qspecl_then [`D`,`fuel`,`fn`,`PG`] mp_tac) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  `l' = l /\ t' = t` by
    (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ _ _ _` kall_tac >>
     qpat_x_assum `ptr_safe_block _ _ _ _ _ _ _ _ _ _ ==> _` kall_tac >>
     qpat_x_assum `ghost_step fuel _ _ _ _ _ _ = _` kall_tac >>
     qpat_x_assum `!fuel. ghost_step _ _ _ _ _ _ _ = _` kall_tac >>
     gvs[Abbr `l`, Abbr `t`, Abbr `w`, step_inst_base_def, mk_inst_def,
      exec_read1_def, exec_write2_def, eval_operand_def, lookup_var_def,
      update_var_def, FLOOKUP_UPDATE]) >>
  gvs[] >>
  simp[ptr_safe_run_def] >> first_x_assum irule >>
  qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ _ _ _` (qspec_then `fuel` mp_tac) >>
  simp[ptr_safe_run_def, Abbr `t`, mstore_def, Abbr `l`, update_var_def]
QED

Theorem prefix_canonical_support_window:
  (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 mem') /\
  (!k. k < n ==> p+k IN B) ==>
  mem_bytes_at p n mem = mem_bytes_at p n mem'
Proof
  strip_tac >> irule abiEncoderZeroFrameTheory.abi_encoder_mem_bytes_singletons >> rpt strip_tac >>
  first_x_assum irule >>
  `p + (a-p) IN B` by (first_x_assum irule >> decide_tac) >>
  gvs[]
QED

Theorem prefix_canonical_primitive_support:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord NoClamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  val_in_memory tv v d m /\
  (!a. a IN range_bytes [(d,32)] ==>
       mem_bytes_at a 1 mem = mem_bytes_at a 1 m) ==>
  type_memory_bytes ce ty = 32 /\ val_in_memory tv v d mem
Proof
  strip_tac >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `NoClamp` mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  `mem_word_at d mem = mem_word_at d m` by
    (simp[mem_word_at_def, GSYM mem_bytes_at_def] >> AP_TERM_TAC >>
     irule prefix_canonical_support_window >> qexists `range_bytes [(d,32)]` >>
     simp[range_bytes_def]) >>
  `value_has_type tv v` by gvs[abi_decoder_metadata_def] >>
  Cases_on `v` >> gvs[value_has_type_def, val_in_memory_def] >>
  Cases_on `bt` >> gvs[is_word_type_def, value_has_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[is_word_type_def, value_has_type_def, val_in_memory_def]
QED

Theorem prefix_canonical_noclamp_sim:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w)
    (DecPrimWord NoClamp) st = ((),st') /\
  run_inst_seq (emitted_insts st st') initial = OK t /\
  fn_has_code st st' func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_decode_sim ctx func initial
    (t with vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `frag_exec ctx st st' (\s. s = initial)
     (\s. s = t with vs_inst_idx := LENGTH st'.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> simp[] >> gvs[EVERY_CONJ]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[]
QED

Theorem prefix_canonical_noclamp_shape:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
    (DecPrimWord NoClamp) st = ((),st') ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_next_var = st.cs_next_var+1 /\
  st'.cs_current_insts = st.cs_current_insts ++
    [mk_inst st.cs_next_id DLOAD [src] ["%" ++ toString st.cs_next_var];
     mk_inst (st.cs_next_id+1) MSTORE
       [Var dst; Var ("%" ++ toString st.cs_next_var)] []]
Proof
  simp[compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
       compile_abi_clamp_basetype_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[APPEND_ASSOC]
QED

Theorem prefix_canonical_noclamp_certificate:
  eval_operand src s = SOME a /\ eval_operand (Var dst) s = SOME p /\
  x <> dst /\ FLOOKUP G dst = SOME (b,sz) /\
  b <= w2n p /\ w2n p+32 <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let w = word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w));
      i = mk_inst iid DLOAD [src] [x];
      j = mk_inst (iid+1) MSTORE [Var dst;Var x] [];
      l = update_var x w s;
      t = mstore (w2n p) w l;
      H = DRESTRICT G (COMPL {x});
      q = step_taint i s l tn;
      r = step_taint j (l with vs_inst_idx := s.vs_inst_idx+1)
             (t with vs_inst_idx := s.vs_inst_idx+1) q;
      u = (\n:num. if n=0 then s else if n=1 then l else t);
      g = (\n:num. if n=0 then G else H);
      qt = (\n:num. if n=0 then tn else if n=1 then q else r)
  in
    run_inst_seq [i;j] s = OK t /\
    (!fuel n. n < 2 ==>
      step_inst_base (EL n [i;j]) (u n) = OK (u (SUC n)) /\
      step_inst fuel ctx (EL n [i;j]) ((u n) with vs_inst_idx := s.vs_inst_idx+n) =
        OK ((u (SUC n)) with vs_inst_idx := s.vs_inst_idx+n) /\
      ptr_safe_step D lo fuel ctx fn PG (g n) (qt n) (EL n [i;j])
        ((u n) with vs_inst_idx := s.vs_inst_idx+n) /\
      ghost_step fuel ctx PG (g n) (qt n) (EL n [i;j])
        ((u n) with vs_inst_idx := s.vs_inst_idx+n) = (g (SUC n),qt (SUC n)))
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `update_var x w s` >>
  qabbrev_tac `l = update_var x w s` >>
  qabbrev_tac `t = mstore (w2n p) w l` >>
  `!fuel. step_inst_base (mk_inst iid DLOAD [src] [x]) s = OK l /\
     step_inst_base (mk_inst (iid+1) MSTORE [Var dst;Var x] []) l = OK t /\
     ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst iid DLOAD [src] [x]) s` by
    (gen_tac >>
     qpat_assum `eval_operand src s = SOME a`
       (mp_then Any (drule_all_then mp_tac) prefix_noclamp_steps) >>
     disch_then (qspec_then `iid` mp_tac) >>
     disch_then (qspecl_then [`D`,`fuel`,`fn`,`PG`] mp_tac) >>
     simp[Abbr `l`, Abbr `t`, Abbr `w`]) >>
  conj_tac >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  `n=0 \/ n=1` by decide_tac >> gvs[]
  >- (qpat_assum `eval_operand src s = SOME a`
        (mp_then Any mp_tac prefix_dload_ghost_step) >> strip_tac >>
      simp[step_inst_non_invoke, Abbr `l`, Abbr `w`, update_var_def] >>
      gvs[mk_inst_def, update_var_def]) >>
  suspend "store"
QED

Resume prefix_canonical_noclamp_certificate[store]:
  qpat_assum `eval_operand src s = SOME a`
    (mp_then Any (drule_all_then mp_tac) prefix_noclamp_steps) >>
  disch_then (qspec_then `iid` mp_tac) >>
  disch_then (qspecl_then [`D`,`fuel`,`fn`,`PG`] mp_tac) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  simp[Abbr `w`, Abbr `l`, Abbr `t`] >> strip_tac >>
  conj_tac
  >- simp[step_inst_non_invoke, step_inst_inst_idx_indep,
          exec_result_map_def, mk_inst_def, is_terminator_def] >>
  conj_tac
  >- (irule prefix_mstore_ptr_step >>
      simp[eval_op_inst_idx, prefix_dload_output_taint] >>
      gvs[allocas_from_def] >> metis_tac[]) >>
  irule prefix_mstore_ghost_step >>
  simp[step_inst_non_invoke, step_inst_inst_idx_indep,
       exec_result_map_def, mk_inst_def, is_terminator_def]
QED
Finalise prefix_canonical_noclamp_certificate

Theorem prefix_canonical_noclamp_continue_nat[local]:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
    (DecPrimWord NoClamp) st = ((),st') /\
  x = "%" ++ toString st.cs_next_var /\ x <> dst /\
  fn_has_code st st' fn /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand (Var dst) s = SOME (n2w d) /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= d /\ d+32 <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  w = word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP sb s.vs_data_section ++ REPLICATE 32 0w)) /\
  l = update_var x w s /\ t = mstore d w l /\
  q = step_taint (mk_inst st.cs_next_id DLOAD [src] [x]) s l tn /\
  r = step_taint (mk_inst (st.cs_next_id+1) MSTORE [Var dst;Var x] [])
      (l with vs_inst_idx := s.vs_inst_idx+1)
      (t with vs_inst_idx := s.vs_inst_idx+1) q /\
  actual = (t with vs_inst_idx := LENGTH st'.cs_current_insts) ==>
  ((!fuel. ptr_safe_run D lo fuel ctx fn PG (DRESTRICT G (COMPL {x})) r actual) ==>
   !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule prefix_canonical_noclamp_shape >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX st'.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[emitted_insts_def, rich_listTheory.IS_PREFIX_APPEND,
         rich_listTheory.DROP_LENGTH_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND, APPEND] >>
     metis_tac[]) >>
  `b <= w2n (n2w d : bytes32) /\ w2n (n2w d : bytes32)+32 <= b+sz` by
    simp[w2n_n2w] >>
  drule_all prefix_canonical_noclamp_continuation >>
  disch_then (mp_tac o SPEC_ALL) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  asm_simp_tac std_ss [w2n_n2w] >>
  rpt strip_tac >> gvs[]
QED

(* Additive same-witness floor contract; the original contract is retained below. *)
val canonical_pair_allocations = ``\ty tv.
 !dst src st st' ctx func site initial limit_st sb d D N ids av v root_di
  G tn b sz Ddead lo PG.
 compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
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
 actual.vs_allocas = initial.vs_allocas /\
 actual.vs_alloca_next = initial.vs_alloca_next /\
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

Theorem prefix_canonical_noclamp_paired_allocations:
  type_to_abi_dec_info sf ce ty = DecPrimWord NoClamp ==>
  (^canonical_pair_allocations) ty tv
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
     (DecPrimWord NoClamp) st = ((),st')` by metis_tac[] >>
  drule abi_decoder_primitive_cases >>
  disch_then (qspec_then `NoClamp` mp_tac) >>
  asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) = 32` by
    (qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
      (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
     drule_all abi_decoder_descended_encoding_length >> simp[]) >>
  `sb < dimword (:256) /\ d < dimword (:256)` by
    (drule_all alloca_frontier_inv_bound >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var (Var dst)` by
    (Cases_on `src` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  qabbrev_tac `x = "%" ++ toString st.cs_next_var` >>
  `x <> dst /\ (!z. not_fresh_at st z ==> z <> x)` by
    (gvs[Abbr `x`, not_fresh_at_def] >> metis_tac[]) >>
  `mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av` by
    metis_tac[] >>
  `x = "%" ++ toString st.cs_next_var` by simp[Abbr `x`] >>
  drule_all prefix_canonical_noclamp_value >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qmatch_asmsub_abbrev_tac `update_var x w initial` >>
  qabbrev_tac `l = update_var x w initial` >>
  qabbrev_tac `t = mstore d w l` >>
  qabbrev_tac `actual = t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  qabbrev_tac `q = step_taint (mk_inst st.cs_next_id DLOAD [src] [x]) initial l tn` >>
  qabbrev_tac `r = step_taint (mk_inst (st.cs_next_id+1) MSTORE [Var dst;Var x] [])
    (l with vs_inst_idx := initial.vs_inst_idx+1)
    (t with vs_inst_idx := initial.vs_inst_idx+1) q` >>
  qexistsl [`actual`, `DRESTRICT G (COMPL {x})`, `r`, `range_bytes [(d,32)]`] >>
  suspend "package"
QED

Resume prefix_canonical_noclamp_paired_allocations[package]:
  `abi_decode_sim ctx func initial actual` by
    (simp[Abbr `actual`] >> irule prefix_canonical_noclamp_sim >> metis_tac[]) >>
  `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
     [(d,32)] initial actual /\ alloca_inv actual /\
     alloca_frontier_inv ctx func site actual` by
    (mp_tac (Q.INST [`s` |-> `initial`, `t` |-> `actual`, `n` |-> `32`,
        `fn` |-> `func`, `ids` |-> `ctor_actual_sites func (frag_ids st st')`]
       ctor_actual_scratch_free_effect) >>
     (impl_tac >-
       (conj_tac >-
          (qpat_x_assum `abi_decode_frame d 32 initial t` mp_tac >>
           simp[NoAsms, Abbr `actual`, abi_decode_frame_def] >>
           rpt strip_tac >> asm_rewrite_tac[]) >>
        simp[NoAsms, Abbr `actual`, Abbr `t`, Abbr `l`, mstore_def, update_var_def])) >>
     simp[]) >>
  `ctor_actual_scratch func ids D N actual` by
    (qpat_x_assum `ctor_actual_scratch func ids D N initial` mp_tac >>
     simp[NoAsms, Abbr `actual`, ctor_actual_scratch_def] >>
     asm_rewrite_tac[]) >>
  `st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
   LENGTH st'.cs_current_insts = LENGTH st.cs_current_insts+2` by
    (drule prefix_canonical_noclamp_shape >> simp[]) >>
  `actual.vs_memory = t.vs_memory /\ actual.vs_alloca_next = initial.vs_alloca_next /\
   actual.vs_data_section = initial.vs_data_section /\
   actual.vs_call_ctx = initial.vs_call_ctx /\
   ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
   actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
   actual.vs_labels = initial.vs_labels` by
    (simp[NoAsms, Abbr `actual`, Abbr `t`, Abbr `l`, mstore_def, update_var_def] >>
     asm_rewrite_tac[]) >>
  `fresh_vars_wrt limit_st actual` by
    (qpat_x_assum `fresh_vars_wrt limit_st t` mp_tac >>
     simp[NoAsms, Abbr `actual`, fresh_vars_wrt_def]) >>
  `actual.vs_allocas = initial.vs_allocas` by
    simp[Abbr `actual`, Abbr `t`, Abbr `l`, mstore_def, update_var_def] >>
  asm_rewrite_tac[] >>
  conj_tac >- suspend "live" >>
  suspend "rest"
QED
Resume prefix_canonical_noclamp_paired_allocations[live]:
  rpt gen_tac >> strip_tac >>
  `abi_decoder_operand_live st.cs_next_var (Var x')` by
    (simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  simp[NoAsms, Abbr `actual`, eval_operand_def] >>
  qpat_x_assum `!op z. _ ==> eval_operand op t = SOME z` mp_tac >>
  disch_then (qspec_then `Var x'` mp_tac) >>
  simp[eval_operand_def, lookup_var_def]
QED

Resume prefix_canonical_noclamp_paired_allocations[rest]:
  `r.t_mem = tn.t_mem DIFF range_bytes [(d,32)] /\
   r.t_stor = tn.t_stor /\ r.t_trans = tn.t_trans /\ r.t_imm = tn.t_imm /\
   (!v. v <> x ==> op_taint r (Var v) = op_taint tn (Var v))` by
    (irule prefix_canonical_noclamp_ghost_nat >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl [`dst`,`st.cs_next_id`,`l`,`q`,`initial`,`sb`,`src`,`t`,`w`] >>
     rule_assum_tac (PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
     asm_rewrite_tac[]) >>
  `FINITE (range_bytes [(d,32)])` by
    (irule SUBSET_FINITE_I >> qexists `count (d+32)` >>
     simp[range_bytes_def, SUBSET_DEF]) >>
  asm_rewrite_tac[SUBSET_REFL] >>
  conj_tac >- suspend "clean" >>
  conj_tac
  >- (rpt strip_tac >> drule_all prefix_canonical_primitive_support >> simp[]) >>
  conj_tac >- suspend "subset" >>
  conj_tac >- suspend "ghostlive" >>
  suspend "continuation"
QED
Resume prefix_canonical_noclamp_paired_allocations[clean]:
  simp[DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED
Resume prefix_canonical_noclamp_paired_allocations[subset]:
  simp[SUBSET_DEF]
QED
Resume prefix_canonical_noclamp_paired_allocations[ghostlive]:
  rpt strip_tac >>
  `x' <> x` by metis_tac[] >>
  `x' <> "%" ++ toString st.cs_next_var` by metis_tac[] >>
  simp[FLOOKUP_DRESTRICT]
QED
Resume prefix_canonical_noclamp_paired_allocations[continuation]:
  match_mp_tac prefix_canonical_noclamp_continue_nat >>
  rule_assum_tac (PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  asm_rewrite_tac[] >> metis_tac[]
QED
Finalise prefix_canonical_noclamp_paired_allocations

Theorem prefix_canonical_noclamp_paired:
  type_to_abi_dec_info sf ce ty = DecPrimWord NoClamp ==>
  (^canonical_pair) ty tv
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule prefix_canonical_noclamp_paired_allocations >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (drule_all_then (qspecl_then [`Ddead`,`PG`] strip_assume_tac)) >>
  qexistsl [`actual`,`H`,`qt`,`B`] >> asm_rewrite_tac[]
QED

val _ = export_theory();
