(* The production decoder closes its own branches, including loop backedges. *)
Theory createSizeDecodeCode
Ancestors
  createSizeDecodeLoopCode createSizeCutCode abiEncoder context
  emitHelper compileEnv venomInst pair list

val [dec_word, dec_bytes, dec_array, dec_complex, dec_nil, dec_cons, _] =
  CONJUNCTS compile_abi_decode_to_buf_def;

(* An independent cut in the continuation prevents duplication of the entire
   decoder prefix in each operand of the remaining instructions. *)
Theorem decode_cut_sequence[local]:
  ((!a. create_cut_code {} a (SND (m a))) /\
   (!v a. create_cut_code {} a (SND (k v a)))) ==>
  !a. create_cut_code {} a (SND (comp_bind m k a))
Proof
  strip_tac >> gen_tac >> irule create_cut_code_bind >> simp[]
QED

fun decode_steps ths =
  rpt (FIRST [CHANGED_TAC (simp (comp_ignore_bind_def :: ths)),
              match_mp_tac decode_cut_sequence >> BETA_TAC,
              irule create_cut_code_emit_op, irule create_cut_code_emit_void,
              CHANGED_TAC (simp[create_cut_targets_def]),
              conj_tac, IF_CASES_TAC, gen_tac]);

Theorem decode_clamp_cut[local]:
  !a. create_cut_code {} a (SND (compile_abi_clamp_basetype v cl a))
Proof
  Cases_on `cl` >>
  decode_steps [compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
                compile_abi_bytes_clamp_def, LET_THM]
QED

Theorem decode_copy_select[local]:
  (case load_opc of
     CALLDATALOAD => emit_void CALLDATACOPY ops
   | DLOAD => emit_void DLOADBYTES ops
   | _ => emit_void MCOPY ops) =
  emit_void (if load_opc = CALLDATALOAD then CALLDATACOPY
             else if load_opc = DLOAD then DLOADBYTES else MCOPY) ops
Proof
  Cases_on `load_opc` >> simp[]
QED

val decode_straight =
  decode_steps [compile_abi_dec_addr_def, compile_abi_decode_range_check_def,
                compile_getelemptr_abi_def, compile_alloc_buffer_def,
                decode_clamp_cut];

Theorem decode_cut_family[local]:
  (!dst src load base hi info. (!ops. create_cut_targets load ops = []) ==>
    !a. create_cut_code {} a
      (SND (compile_abi_decode_to_buf dst src load base hi info a))) /\
  (!dst src load base hi elems ao vo. (!ops. create_cut_targets load ops = []) ==>
    !a. create_cut_code {} a
      (SND (compile_abi_decode_complex_elems dst src load base hi elems ao vo a))) /\
  (!dst src load base hi info asz msz ip cnt. (!ops. create_cut_targets load ops = []) ==>
    !a. create_cut_code {} a
      (SND (compile_abi_decode_dyn_loop dst src load base hi info asz msz ip cnt a)))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt conj_tac
  >- (rpt strip_tac >> qid_spec_tac `a` >>
      simp_tac std_ss [dec_word, compile_abi_decode_static_def] >> decode_straight)
  >- (rpt strip_tac >> qid_spec_tac `a` >>
      simp_tac std_ss [dec_bytes, LET_THM, decode_copy_select] >> decode_straight)
  >- (rpt strip_tac >> qid_spec_tac `a` >>
      simp_tac std_ss [dec_array, LET_THM, decode_copy_select] >>
      decode_straight >> fs[] >> metis_tac[])
  >- (rpt strip_tac >> qid_spec_tac `a` >> simp_tac std_ss [dec_complex, LET_THM] >>
      decode_straight >> fs[] >> metis_tac[])
  >- simp[dec_nil]
  >- (rpt strip_tac >> qid_spec_tac `a` >> simp_tac std_ss [dec_cons, LET_THM] >>
      decode_straight >> fs[] >> metis_tac[])
  >> rpt strip_tac >> irule create_decode_dyn_loop_case >> simp[] >> metis_tac[]
QED

Theorem create_decode_to_buf_cut_code:
  (!ops. create_cut_targets load ops = []) ==>
  !a. create_cut_code {} a
    (SND (compile_abi_decode_to_buf dst src load bop hi info a))
Proof
  simp[CONJUNCT1 decode_cut_family]
QED
