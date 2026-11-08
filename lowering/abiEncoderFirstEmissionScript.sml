(* Encoder prefixes witness first emission before any recursive suffix. *)
Theory abiEncoderFirstEmission
Ancestors
  compilerFirstEmission entryConditionalFirstEmission abiEncoderAppend
  abiDecoderAppend abiEncoder fragExec compileEnv emitHelper venomInst context

val encoder_append_simps =
  [cs_appends_return, cs_appends_prims, cs_appends_emit_helpers,
   cs_appends_abi_alloc_buffer, cs_appends_abi_encode_mutual,
   cs_appends_abi_encode_static, cs_appends_abi_encode_static_info,
   cs_appends_abi_encode_static_loop, LET_THM];
fun encoder_append_tac g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss()) encoder_append_simps],
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- encoder_append_tac >> rpt gen_tac >> encoder_append_tac,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> encoder_append_tac,
    IF_CASES_TAC >> encoder_append_tac]) g;
fun encoder_tail_tac g =
  (rpt gen_tac >> strip_tac >>
   qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
   `cs_appends tail` by
     (simp_tac bool_ss [Abbr `tail`] >> encoder_append_tac) >>
   fs[cs_appends_def]) g;
fun encoder_emit_tac g =
  (rpt gen_tac >> strip_tac >>
   FIRST (map (fn th => drule_at (Pos (el 2)) th >> simp[])
     [cj 1 first_emission_emit_helpers, cj 2 first_emission_emit_helpers,
      cj 3 first_emission_emit_helpers])) g;

Theorem first_emission_abi_encode_static:
  !a x b. compile_abi_encode_static dst src a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rewrite_tac[compile_abi_encode_static_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- encoder_emit_tac >> encoder_tail_tac
QED

Theorem first_emission_abi_encode_child:
  !a x b. compile_abi_encode_child dst src ei dyn off dynptr a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rewrite_tac[Once compile_abi_encode_child_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- encoder_emit_tac >> encoder_tail_tac
QED

Theorem first_emission_abi_encode_complex_elems:
  !a x b. compile_abi_encode_complex_elems dst src elems so ho dynptr a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Cases_on `elems`
  >- (simp_tac bool_ss [Once compile_abi_encode_child_def] >>
      metis_tac[first_emission_return]) >>
  PairCases_on `h` >> rewrite_tac[Once compile_abi_encode_child_def] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- encoder_emit_tac >> encoder_tail_tac
QED

fun encoder_strong_tac g =
  (FIRST [encoder_emit_tac,
    MATCH_ACCEPT_TAC first_emission_abi_encode_static,
    ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- encoder_strong_tac >> encoder_tail_tac,
    ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
      >- encoder_strong_tac >> encoder_tail_tac]) g;

Theorem first_emission_abi_encode_static_loop:
  !a x b. compile_abi_encode_dyn_static_loop dst src ei asz msz len a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_abi_encode_dyn_static_loop_def,
    compile_alloc_buffer_def, LET_THM] >> encoder_strong_tac
QED

Theorem first_emission_abi_encode_dyn_loop:
  !a x b. compile_abi_encode_dyn_loop dst src ei asz msz len a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [Once compile_abi_encode_child_def,
    compile_alloc_buffer_def, LET_THM] >> encoder_strong_tac
QED

Theorem first_emission_abi_encode_to_buf:
  !a x b. compile_abi_encode_to_buf dst src ei a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Cases_on `ei` >> simp_tac bool_ss [Once compile_abi_encode_child_def,
    compile_alloc_buffer_def, LET_THM]
  >- (ho_match_mp_tac first_emission_strong >> encoder_strong_tac)
  >- (ho_match_mp_tac first_emission_strong >> encoder_strong_tac)
  >- (ho_match_mp_tac first_emission_strong >> encoder_strong_tac)
  >- (ho_match_mp_tac first_emission_strong >> encoder_strong_tac) >>
  Cases_on `l` >> simp_tac bool_ss [Once compile_abi_encode_child_def,
    compile_alloc_buffer_def, LET_THM]
  >- metis_tac[first_emission_return] >>
  IF_CASES_TAC
  >- (ho_match_mp_tac first_emission_strong >> encoder_strong_tac) >>
  ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_abi_encode_complex_elems >>
  metis_tac[first_emission_return]
QED
