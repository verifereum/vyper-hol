(* Byte-slice prefixes emit before bounds checking and copying. *)
Theory builtinBytesFirstEmission
Ancestors
  compilerFirstEmission builtinBytes fragExec compileEnv emitHelper venomInst context

fun bytes_append_tac g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss())
       [cs_appends_return, cs_appends_prims, cs_appends_emit_helpers, LET_THM]],
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- bytes_append_tac >> rpt gen_tac >> bytes_append_tac,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> bytes_append_tac,
    IF_CASES_TAC >> bytes_append_tac]) g;
fun bytes_tail_tac g =
  (rpt gen_tac >> strip_tac >>
   qmatch_asmsub_abbrev_tac `tail st0 = (y,c)` >>
   `cs_appends tail` by
     (simp_tac bool_ss [Abbr `tail`] >> bytes_append_tac) >>
   fs[cs_appends_def]) g;
fun bytes_emit_tac g =
  (rpt gen_tac >> strip_tac >>
   FIRST (map (fn th => drule_at (Pos (el 2)) th >> simp[])
     [cj 1 first_emission_emit_helpers, cj 2 first_emission_emit_helpers,
      cj 3 first_emission_emit_helpers])) g;
fun bytes_strong_tac g =
  (FIRST [bytes_emit_tac,
    ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- bytes_strong_tac >> bytes_tail_tac,
    ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
      >- bytes_strong_tac >> bytes_tail_tac]) g;

Theorem first_emission_assert_slice_bounds:
  !a x b. compile_assert_slice_bounds start len sz a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_assert_slice_bounds_def] >> bytes_strong_tac
QED

Theorem first_emission_bytestring_src:
  !a x b. compile_bytestring_src p a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_bytestring_src_def] >> bytes_strong_tac
QED

Theorem first_emission_slice_out_buf:
  !a x b. compile_slice_out_buf sz a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_slice_out_buf_def, compile_alloc_buffer_def] >>
  bytes_strong_tac
QED

Theorem first_emission_slice_data:
  !a x b. compile_slice_data sl sd start len sz a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_slice_data_def, compile_assert_slice_bounds_def,
    compile_alloc_buffer_def] >> bytes_strong_tac
QED

Theorem first_emission_slice_calldata:
  !a x b. compile_slice_calldata start len sz a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_slice_calldata_def, compile_slice_out_buf_def,
    compile_assert_slice_bounds_def, compile_alloc_buffer_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- bytes_strong_tac >>
  rpt gen_tac >> PairCases_on `x` >>
  simp_tac bool_ss [pairTheory.UNCURRY_DEF] >> bytes_tail_tac
QED

Theorem first_emission_slice_code:
  !a x b. compile_slice_code start len sz a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_slice_code_def, compile_slice_out_buf_def,
    compile_assert_slice_bounds_def, compile_alloc_buffer_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- bytes_strong_tac >>
  rpt gen_tac >> PairCases_on `x` >>
  simp_tac bool_ss [pairTheory.UNCURRY_DEF] >> bytes_tail_tac
QED

Theorem first_emission_slice_extcode:
  !a x b. compile_slice_extcode addr start len buf data a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_slice_extcode_def, compile_assert_slice_bounds_def] >>
  bytes_strong_tac
QED

Theorem first_emission_extract32_load:
  !a x b. compile_extract32_load sl sd start a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_extract32_load_def, compile_assert_slice_bounds_def] >>
  bytes_strong_tac
QED
