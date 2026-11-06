Theory exprSimAbiDecodeResourceMutual
Ancestors
  exprSimAbiDecodeFramed exprSimAbiDecodeResourcePrims exprSimAbiDecodeResource abiEncoder compileEnv emitHelper context venomInst pred_set

Theorem decode_framed_copy[local]:
  d <> Label ex /\ s <> Label ex /\ n <> Label ex ==>
  decode_framed ex
    (case opc of
       CALLDATALOAD => emit_void CALLDATACOPY [d;s;n]
     | DLOAD => emit_void DLOADBYTES [d;s;n]
     | _ => emit_void MCOPY [d;s;n]) (\u. T)
Proof
  strip_tac >> irule decode_straight_framed >>
  Cases_on `opc` >> simp[decode_straight_emit_void]
QED

Theorem decode_framed_head[local]:
  src <> Label ex /\ hi <> Label ex ==>
  decode_framed ex
    (if hi = Lit 0w then comp_return (Lit 0w)
     else do h <- emit_op ADD [src; Lit 32w];
             compile_abi_decode_range_check src h hi; comp_return h od)
    (\v. v <> Label ex)
Proof
  strip_tac >> irule decode_straight_framed >> Cases_on `hi = Lit 0w` >> simp[]
  >- (irule decode_straight_return >> simp[]) >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >> rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_straight_ignore_bind) >> qexists_tac `\u. T` >>
  conj_tac >- simp[decode_straight_range_check] >>
  irule decode_straight_return >> simp[]
QED

Theorem decode_framed_mutual:
  (!dst src opc bop hi info. !ex.
    opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\ opc <> STOP /\ opc <> RETURN /\
    dst <> Label ex /\ src <> Label ex /\ bop <> Label ex /\ hi <> Label ex ==>
    decode_framed ex (compile_abi_decode_to_buf dst src opc bop hi info) (\u. T)) /\
  (!dst src opc bop hi elems ao vo. !ex.
    opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\ opc <> STOP /\ opc <> RETURN /\
    dst <> Label ex /\ src <> Label ex /\ bop <> Label ex /\ hi <> Label ex ==>
    decode_framed ex (compile_abi_decode_complex_elems dst src opc bop hi elems ao vo) (\u. T)) /\
  (!dst src opc bop hi info abi_sz mem_sz ip cnt. !ex.
    opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\ opc <> STOP /\ opc <> RETURN /\
    dst <> Label ex /\ src <> Label ex /\ bop <> Label ex /\ hi <> Label ex /\
    ip <> Label ex /\ cnt <> Label ex ==>
    decode_framed ex (compile_abi_decode_dyn_loop dst src opc bop hi info abi_sz mem_sz ip cnt) (\u. T))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >>
  rpt conj_tac >> rpt gen_tac
  >- (strip_tac >> once_rewrite_tac[compile_abi_decode_to_buf_def] >>
      match_mp_tac (GEN_ALL decode_framed_bind) >> qexists_tac `\v. v <> Label ex` >>
      conj_tac >- (irule decode_straight_framed >> simp[decode_straight_dec_addr]) >>
      rpt strip_tac >> gvs[] >> irule decode_straight_framed >>
      irule decode_straight_static >> simp[decode_straight_clamp_basetype])
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- (strip_tac >> once_rewrite_tac[compile_abi_decode_to_buf_def] >>
      irule decode_framed_return >> simp[])
  >- suspend "elems"
  >> suspend "loop"
QED

Resume decode_framed_mutual[bytes]:
  strip_tac >> once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  match_mp_tac (GEN_ALL decode_framed_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac
  >- simp[decode_framed_head] >>
  rpt strip_tac >> gvs[] >>
  ntac 4 (match_mp_tac (GEN_ALL decode_framed_bind) >>
       qexists_tac `\v. v <> Label ex` >> conj_tac
       >- (irule decode_straight_framed >>
           simp[decode_straight_emit_op, decode_straight_dec_addr]) >>
       rpt strip_tac >> gvs[]) >>
  match_mp_tac (GEN_ALL decode_framed_ignore_bind) >> qexists_tac `\u. T` >>
  conj_tac >- (irule decode_straight_framed >> simp[decode_straight_emit_void]) >>
  match_mp_tac (GEN_ALL decode_framed_ignore_bind) >> qexists_tac `\u. T` >>
  conj_tac
  >- (irule decode_straight_framed >> Cases_on `hi = Lit 0w` >> simp[]
      >- (irule decode_straight_return >> simp[]) >>
      match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
      conj_tac >- simp[decode_straight_emit_op] >>
      simp[decode_straight_range_check]) >>
  Cases_on `bop = Lit 0w` >> simp[LET_THM]
  >- (irule decode_framed_copy >> simp[]) >>
  ntac 4 (match_mp_tac (GEN_ALL decode_framed_bind) >>
       qexists_tac `\v. v <> Label ex` >> conj_tac
       >- (irule decode_straight_framed >> simp[decode_straight_emit_op]) >>
       rpt strip_tac >> gvs[]) >>
  match_mp_tac (GEN_ALL decode_framed_ignore_bind) >> qexists_tac `\u. T` >>
  conj_tac >- (irule decode_straight_framed >> simp[decode_straight_emit_void]) >>
  match_mp_tac (GEN_ALL decode_framed_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- (irule decode_straight_framed >> simp[decode_straight_emit_op]) >>
  rpt strip_tac >> gvs[] >> irule decode_straight_framed >> simp[decode_straight_emit_void]
QED
Resume decode_framed_mutual[array]:
  strip_tac >> gen_tac >> strip_tac >>
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  match_mp_tac (GEN_ALL decode_framed_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_framed_head] >> rpt strip_tac >> gvs[] >>
  ntac 4 (match_mp_tac (GEN_ALL decode_framed_bind) >>
       qexists_tac `\v. v <> Label ex` >> conj_tac
       >- (irule decode_straight_framed >>
           simp[decode_straight_emit_op, decode_straight_dec_addr]) >>
       rpt strip_tac >> gvs[]) >>
  match_mp_tac (GEN_ALL decode_framed_ignore_bind) >> qexists_tac `\u. T` >>
  conj_tac >- (irule decode_straight_framed >> simp[decode_straight_emit_void]) >>
  match_mp_tac (GEN_ALL decode_framed_ignore_bind) >> qexists_tac `\u. T` >>
  conj_tac
  >- (irule decode_straight_framed >> Cases_on `hi = Lit 0w` >> simp[]
      >- (irule decode_straight_return >> simp[]) >>
      ntac 2 (match_mp_tac (GEN_ALL decode_straight_bind) >>
        qexists_tac `\v. v <> Label ex` >> conj_tac
        >- simp[decode_straight_emit_op] >> rpt strip_tac >> gvs[]) >>
      simp[decode_straight_range_check]) >>
  match_mp_tac (GEN_ALL decode_framed_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- (irule decode_straight_framed >> simp[decode_straight_emit_op]) >>
  rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_framed_ignore_bind) >> qexists_tac `\u. T` >>
  conj_tac >- (irule decode_straight_framed >> simp[decode_straight_emit_void]) >>
  simp[LET_THM] >> Cases_on `~elem_is_dyn /\ ~dec_info_needs_clamp info` >> simp[]
  >- (ntac 4 (match_mp_tac (GEN_ALL decode_framed_bind) >>
        qexists_tac `\v. v <> Label ex` >> conj_tac
        >- (irule decode_straight_framed >>
            simp[decode_straight_emit_op, decode_straight_dec_addr]) >>
        rpt strip_tac >> gvs[]) >> irule decode_framed_copy >> simp[]) >>
  match_mp_tac (GEN_ALL decode_framed_bind) >>
  qexists_tac `\b. b.buf_operand <> Label ex` >>
  conj_tac >- (irule decode_straight_framed >> simp[decode_straight_alloc_buffer]) >>
  rpt strip_tac >> gnvs[LET_THM] >>
  match_mp_tac (GEN_ALL decode_framed_ignore_bind) >> qexists_tac `\u. T` >>
  conj_tac >- (irule decode_straight_framed >> simp[decode_straight_emit_void]) >>
  qmatch_goalsub_abbrev_tac `b.buf_operand` >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[Abbr `b`]
QED
Resume decode_framed_mutual[complex]:
  strip_tac >> gen_tac >> strip_tac >> Cases_on `hi = Lit 0w` >> gvs[] >>
  once_rewrite_tac[compile_abi_decode_to_buf_def] >> simp[LET_THM] >>
  rpt (match_mp_tac (GEN_ALL decode_framed_bind) >> qexists_tac `\v. v <> Label ex` >>
       conj_tac >- (irule decode_straight_framed >> simp[decode_straight_emit_op]) >>
       rpt strip_tac >> gvs[]) >>
  rpt (match_mp_tac (GEN_ALL decode_framed_ignore_bind) >> qexists_tac `\u. T` >>
       conj_tac >- (irule decode_straight_framed >> simp[decode_straight_range_check])) >>
  first_x_assum irule >> simp[]
QED
Resume decode_framed_mutual[elems]:
  strip_tac >> gen_tac >> strip_tac >> gvs[] >>
  once_rewrite_tac[compile_abi_decode_to_buf_def] >> simp[LET_THM] >>
  ntac 2 (match_mp_tac (GEN_ALL decode_framed_bind) >> qexists_tac `\v. v <> Label ex` >>
       conj_tac >- (irule decode_straight_framed >>
         simp[decode_straight_emit_op, decode_straight_getelemptr]) >>
       rpt strip_tac >> gvs[]) >>
  match_mp_tac (GEN_ALL decode_framed_ignore_bind) >> qexists_tac `\u. T` >>
  conj_tac >> first_x_assum irule >> simp[]
QED
Resume decode_framed_mutual[loop]:
  strip_tac >> gen_tac >> strip_tac >> gvs[] >>
  once_rewrite_tac[compile_abi_decode_to_buf_def] >> simp[LET_THM] >>
  rewrite_tac[decode_framed_def] >> rpt strip_tac >>
  ho_match_mp_tac decode_resource_fresh_label_then >>
  (conj_tac >- simp[]) >>
  map_every qx_gen_tac [`hdr`, `s1`, `P1`] >> strip_tac >>
  ho_match_mp_tac decode_resource_fresh_label_then >>
  (conj_tac >- simp[]) >>
  map_every qx_gen_tac [`body_lbl`, `s2`, `P2`] >> strip_tac >>
  ho_match_mp_tac decode_resource_fresh_label_then >>
  (conj_tac >- simp[]) >>
  map_every qx_gen_tac [`exit`, `s3`, `P3`] >> strip_tac >>
  ho_match_mp_tac decode_resource_terminator_then >>
  conj_tac >- simp[] >> conj_tac >- ASM_SET_TAC[] >>
  conj_tac >- simp[] >>
  qx_gen_tac `s4` >> strip_tac >>
  drule decode_resource_run_pool >> strip_tac >>
  ntac 5 (ho_match_mp_tac (GEN_ALL decode_framed_then) >>
    qexists_tac `\v. v <> Label ex` >>
    conj_tac >- (irule decode_straight_framed >>
      simp[decode_straight_emit_op, decode_straight_dec_addr]) >>
    conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
    RULE_ASSUM_TAC BETA_RULE >> BETA_TAC) >>
  ho_match_mp_tac decode_resource_terminator_then >>
  conj_tac >- simp[] >> conj_tac >- ASM_SET_TAC[] >>
  conj_tac >- simp[] >>
  qx_gen_tac `s5` >> strip_tac >>
  drule decode_resource_run_pool >> strip_tac >>
  ntac 4 (ho_match_mp_tac (GEN_ALL decode_framed_then) >>
    qexists_tac `\v. v <> Label ex` >>
    conj_tac >- (irule decode_straight_framed >> simp[decode_straight_emit_op]) >>
    conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
    RULE_ASSUM_TAC BETA_RULE >> BETA_TAC) >>
  ho_match_mp_tac (GEN_ALL decode_framed_then) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac
  >- (irule decode_straight_framed >> Cases_on `dec_info_needs_offset info` >> simp[]
      >- simp[decode_straight_dyn_elem_ptr] >>
      irule decode_straight_return >> simp[]) >>
  conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  RULE_ASSUM_TAC BETA_RULE >> BETA_TAC >>
  ntac 3 (ho_match_mp_tac (GEN_ALL decode_framed_then) >>
    qexists_tac `\v. v <> Label ex` >>
    conj_tac >- (irule decode_straight_framed >> simp[decode_straight_emit_op]) >>
    conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
    RULE_ASSUM_TAC BETA_RULE >> BETA_TAC) >>
  ho_match_mp_tac (GEN_ALL decode_framed_ignore_then) >> qexists_tac `\u. T` >>
  conj_tac >- (first_x_assum irule >> simp[]) >>
  conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  ho_match_mp_tac (GEN_ALL decode_framed_then) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- (irule decode_straight_framed >> simp[decode_straight_emit_op]) >>
  conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  RULE_ASSUM_TAC BETA_RULE >> BETA_TAC >>
  ho_match_mp_tac (GEN_ALL decode_framed_ignore_then) >> qexists_tac `\u. T` >>
  conj_tac >- (irule decode_straight_framed >> simp[decode_straight_emit_void]) >>
  conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  ho_match_mp_tac decode_resource_terminator_then >>
  conj_tac >- simp[] >> conj_tac >- ASM_SET_TAC[] >>
  conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  drule decode_resource_run_pool >> strip_tac >>
  irule_at Any decode_resource_run_return >> simp[] >> ASM_SET_TAC[]
QED
Finalise decode_framed_mutual

Theorem decode_framed_to_buf:
  opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\ opc <> STOP /\ opc <> RETURN /\
  dst <> Label ex /\ src <> Label ex /\ bop <> Label ex /\ hi <> Label ex ==>
  decode_framed ex (compile_abi_decode_to_buf dst src opc bop hi info) (\u. T)
Proof
  metis_tac[decode_framed_mutual]
QED
