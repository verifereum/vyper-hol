(* Decoder loads must not be PHI; pointer arithmetic emits ADD independently. *)
Theory abiDecoderFirstEmission
Ancestors
  compilerFirstEmission entryConditionalFirstEmission abiDecoderAppend
  abiEncoder fragExec compileEnv emitHelper venomInst context

val decoder_append_simps =
  [cs_appends_return, cs_appends_prims, cs_appends_emit_helpers,
   cs_appends_abi_alloc_buffer, cs_appends_abi_decode_mutual,
   cs_appends_abi_member_pointer, cs_appends_abi_array_pointer,
   cs_appends_abi_clamp, LET_THM];
fun decoder_append_tac g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss()) decoder_append_simps],
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- decoder_append_tac >> rpt gen_tac >> decoder_append_tac,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> decoder_append_tac,
    IF_CASES_TAC >> decoder_append_tac,
    Cases_on `opc` >> decoder_append_tac]) g;
fun decoder_tail_tac g =
  (rpt gen_tac >> strip_tac >>
   qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
   `cs_appends tail` by
     (simp_tac bool_ss [Abbr `tail`] >> decoder_append_tac) >>
   fs[cs_appends_def]) g;
fun decoder_emit_tac g =
  (rpt gen_tac >> strip_tac >>
   FIRST (map (fn th => drule_at (Pos (el 2)) th >> simp[])
     [cj 1 first_emission_emit_helpers, cj 2 first_emission_emit_helpers,
      cj 3 first_emission_emit_helpers])) g;
fun decoder_strong_tac g =
  (FIRST [decoder_emit_tac,
    ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- decoder_strong_tac >> decoder_tail_tac,
    ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
      >- decoder_strong_tac >> decoder_tail_tac]) g;

Theorem first_emission_abi_member_pointer:
  !a x b. compile_getelemptr_abi src dyn off opc hi a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rewrite_tac[compile_getelemptr_abi_def] >> decoder_strong_tac
QED

Theorem first_emission_abi_decode_complex_elems:
  !a x b. compile_abi_decode_complex_elems dst src opc hi elems ao vo a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Cases_on `elems`
  >- (simp_tac bool_ss [Once compile_abi_decode_to_buf_def] >>
      metis_tac[first_emission_return]) >>
  PairCases_on `h` >> simp_tac bool_ss [Once compile_abi_decode_to_buf_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_abi_member_pointer >> decoder_tail_tac
QED

Theorem first_emission_abi_decode_to_buf:
  opc <> PHI ==>
  !a x b. compile_abi_decode_to_buf dst src opc hi info a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> Cases_on `info` >>
  simp_tac bool_ss [Once compile_abi_decode_to_buf_def,
    compile_abi_decode_static_def, LET_THM]
  >- (ho_match_mp_tac first_emission_strong >> decoder_strong_tac)
  >- (ho_match_mp_tac first_emission_strong >> decoder_strong_tac)
  >- (ho_match_mp_tac first_emission_strong >> decoder_strong_tac) >>
  IF_CASES_TAC
  >- MATCH_ACCEPT_TAC first_emission_abi_decode_complex_elems >>
  ho_match_mp_tac first_emission_strong >> decoder_strong_tac
QED

Theorem first_emission_abi_decode_dyn_loop:
  !a x b. compile_abi_decode_dyn_loop dst src opc hi ei asz msz ip cnt a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  simp_tac bool_ss [Once compile_abi_decode_to_buf_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_no_code >>
      MATCH_ACCEPT_TAC (cj 1 first_emission_counters)) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_no_code >>
      MATCH_ACCEPT_TAC (cj 1 first_emission_counters)) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_no_code >>
      MATCH_ACCEPT_TAC (cj 1 first_emission_counters)) >>
  gen_tac >> ho_match_mp_tac first_emission_strong >> decoder_strong_tac
QED
