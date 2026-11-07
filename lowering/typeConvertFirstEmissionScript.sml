(* Finite conversion closure: optional checks retain the unchanged-code arm. *)
Theory typeConvertFirstEmission
Ancestors
  conditionalConversionFirstEmission compilerFirstEmission conversionFirstEmission
  contextFirstEmission builtinSimple exprValueFirstEmission exprLowering fragExec compileEnv emitHelper venomInst context

Theorem type_convert_clamp_appends[local]:
  cs_appends (compile_int_clamp s n v)
Proof
  simp[cs_appends_def] >> metis_tac[first_emission_int_clamp]
QED

fun type_convert_append_tac g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss())
      [cs_appends_return, cs_appends_prims, cs_appends_emit_helpers,
       type_convert_clamp_appends, LET_THM]],
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- type_convert_append_tac >> rpt gen_tac >> type_convert_append_tac,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> type_convert_append_tac,
    IF_CASES_TAC >> type_convert_append_tac]) g;
fun type_convert_tail_tac g =
  (rpt gen_tac >> strip_tac >>
   qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
   `cs_appends tail` by
     (simp_tac bool_ss [Abbr `tail`] >> type_convert_append_tac) >>
   fs[cs_appends_def]) g;
fun type_convert_op_tac g =
  (rpt gen_tac >> strip_tac >>
   drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) g;
fun type_convert_emitting_bind_tac g =
  (ho_match_mp_tac first_emission_strong >>
   ho_match_mp_tac first_emission_strong_bind >> conj_tac
   >- type_convert_op_tac >> type_convert_tail_tac) g;

Theorem first_emission_type_convert:
  !cv v a x b. compile_type_convert v cv a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Cases
  >~ [`ConvToBool`] >- (gen_tac >> rewrite_tac[compile_type_convert_def] >> type_convert_emitting_bind_tac)
  >~ [`ConvIntToInt`] >- suspend "int_int"
  >~ [`ConvBytesToInt`] >- suspend "bytes_int"
  >~ [`ConvIntToBytesM`] >- metis_tac[first_emission_int_to_bytesm]
  >~ [`ConvIntToDecimal`] >- suspend "int_decimal"
  >~ [`ConvDecimalToInt`] >- suspend "decimal_int"
  >~ [`ConvBoolToDecimal`] >- (gen_tac >> rewrite_tac[compile_type_convert_def] >>
      ho_match_mp_tac first_emission_strong >> type_convert_op_tac)
  >~ [`ConvToAddress`] >- (gen_tac >> simp_tac bool_ss [compile_type_convert_def, LET_THM] >>
      type_convert_emitting_bind_tac)
  >~ [`ConvBytesToAddress`] >- (gen_tac >> simp_tac bool_ss [compile_type_convert_def, LET_THM] >>
      type_convert_emitting_bind_tac)
  >~ [`ConvToFlag`] >- suspend "flag"
  >~ [`ConvBytesMToDecimal`] >- (gen_tac >> simp_tac bool_ss [compile_type_convert_def, LET_THM] >>
      type_convert_emitting_bind_tac)
  >~ [`ConvBytesMToBytesM`] >- suspend "bytes_bytes"
  >~ [`ConvBytestringToBool`] >- suspend "string_bool"
  >~ [`ConvBytestringToInt`] >- suspend "string_int"
  >~ [`ConvBytestringToDecimal`] >- suspend "string_decimal"
  >~ [`ConvBytestringToBytesM`] >- suspend "string_bytes"
  >~ [`ConvBytestringCast`] >- suspend "string_cast"
  >~ [`ConvIdentity`] >- (simp_tac bool_ss [compile_type_convert_def] >> metis_tac[first_emission_return])
QED

Resume first_emission_type_convert[int_int]:
  gen_tac >> simp_tac bool_ss [compile_type_convert_def, LET_THM] >>
  ho_match_mp_tac first_emission_cond >> conj_tac
  >- (ho_match_mp_tac first_emission_cond >> conj_tac >> type_convert_emitting_bind_tac) >>
  ho_match_mp_tac first_emission_cond >> conj_tac
  >- type_convert_emitting_bind_tac >>
  ho_match_mp_tac first_emission_cond >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_int_clamp) >>
  metis_tac[first_emission_return]
QED

Resume first_emission_type_convert[bytes_int]:
  gen_tac >> simp_tac bool_ss [compile_type_convert_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_cond >> conj_tac >>
      ho_match_mp_tac first_emission_strong >> type_convert_op_tac) >>
  gen_tac >> ho_match_mp_tac first_emission_cond >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_int_clamp) >>
  metis_tac[first_emission_return]
QED

Resume first_emission_type_convert[flag]:
  gen_tac >> simp_tac bool_ss [compile_type_convert_def] >>
  ho_match_mp_tac first_emission_cond >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_int_clamp) >>
  metis_tac[first_emission_return]
QED

Resume first_emission_type_convert[bytes_bytes]:
  gen_tac >> simp_tac bool_ss [compile_type_convert_def, LET_THM] >>
  ho_match_mp_tac first_emission_cond >> conj_tac
  >- type_convert_emitting_bind_tac >> metis_tac[first_emission_return]
QED

Resume first_emission_type_convert[string_cast]:
  gen_tac >> simp_tac bool_ss [compile_type_convert_def, LET_THM] >>
  ho_match_mp_tac first_emission_cond >> conj_tac
  >- type_convert_emitting_bind_tac >> metis_tac[first_emission_return]
QED

fun type_convert_decimal_tac g =
  (gen_tac >> simp_tac bool_ss [compile_type_convert_def, LET_THM] >>
   ho_match_mp_tac first_emission_ignore_bind >> conj_tac
   >- (ho_match_mp_tac first_emission_cond >> conj_tac
       >- type_convert_emitting_bind_tac >>
       metis_tac[first_emission_return]) >>
   ho_match_mp_tac first_emission_ignore_bind >> conj_tac
   >- (ho_match_mp_tac first_emission_cond >> conj_tac
       >- (ho_match_mp_tac first_emission_bind >> conj_tac
           >- (ho_match_mp_tac first_emission_cond >> conj_tac >>
               ho_match_mp_tac first_emission_strong >> type_convert_op_tac) >>
           gen_tac >> type_convert_emitting_bind_tac) >>
       metis_tac[first_emission_return]) >>
   ho_match_mp_tac first_emission_strong >> type_convert_op_tac) g;

Resume first_emission_type_convert[int_decimal]:
  type_convert_decimal_tac
QED
Resume first_emission_type_convert[decimal_int]:
  type_convert_decimal_tac
QED

fun type_convert_string_tac g =
  (gen_tac >> simp_tac bool_ss [compile_type_convert_def, LET_THM] >>
   ho_match_mp_tac first_emission_strong >>
   ho_match_mp_tac first_emission_strong_bind >> conj_tac
   >- (match_mp_tac first_emission_load_bytestring_as_word >> simp[]) >>
   rpt gen_tac >> PairCases_on `x` >> simp_tac (srw_ss()) [] >> type_convert_tail_tac) g;

Resume first_emission_type_convert[string_bool]:
  type_convert_string_tac
QED
Resume first_emission_type_convert[string_decimal]:
  type_convert_string_tac
QED
Resume first_emission_type_convert[string_bytes]:
  type_convert_string_tac
QED
Resume first_emission_type_convert[string_int]:
  gen_tac >> simp_tac bool_ss [compile_type_convert_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (match_mp_tac first_emission_load_bytestring_as_word >>
      IF_CASES_TAC >> simp[]) >>
  rpt gen_tac >> PairCases_on `x` >> simp_tac (srw_ss()) [] >> type_convert_tail_tac
QED

Finalise first_emission_type_convert

Theorem type_convert_zero_words_appends[local]:
  !n ptr. cs_appends (compile_zero_words ptr n)
Proof
  Induct >> gen_tac >> rewrite_tac[compile_zero_words_def] >> type_convert_append_tac
QED

fun type_convert_alloc_tac g =
  (rewrite_tac[compile_alloc_buffer_def] >>
   ho_match_mp_tac first_emission_strong_bind >> conj_tac
   >- type_convert_op_tac >> type_convert_tail_tac) g;

Theorem first_emission_bytestring_widen_copy:
  !a x b. compile_bytestring_widen_copy nbytes v n a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rewrite_tac[compile_bytestring_widen_copy_def] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- type_convert_alloc_tac >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
  `cs_appends tail` by
    (simp_tac bool_ss [Abbr `tail`] >>
     ho_match_mp_tac cs_appends_ignore_bind >>
     simp[cs_appends_return, cs_appends_def] >> metis_tac[first_emission_copy_memory]) >>
  fs[cs_appends_def]
QED

Theorem first_emission_builtin_empty_complex:
  !a x b. compile_builtin_empty_complex nbytes is_bytes a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rewrite_tac[compile_builtin_empty_complex_def] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- type_convert_alloc_tac >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
  `cs_appends tail` by
    (simp_tac bool_ss [Abbr `tail`] >>
     ho_match_mp_tac cs_appends_bind >> conj_tac >- simp[cs_appends_return] >>
     gen_tac >> Cases_on `is_bytes` >>
     simp_tac (srw_ss()) [cs_appends_ignore_bind, cs_appends_return,
       cs_appends_emit_helpers, type_convert_zero_words_appends, LET_THM]) >>
  fs[cs_appends_def]
QED

fun type_convert_wrapped_tac th g =
  (rpt gen_tac >> qmatch_goalsub_abbrev_tac `as_stack_val _ result` >>
   Cases_on `result` >> simp[as_stack_val_def] >> strip_tac >> gvs[] >>
   drule th >> simp[]) g;

Theorem first_emission_type_builtin_convert:
  (!a x b. cfn ce (expr_type (HD args)) (HD args) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_type_builtin_dispatch_body cfn ce vt ty Convert rt args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> simp_tac (srw_ss()) [compile_type_builtin_dispatch_body_def, LET_THM] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> first_assum ACCEPT_TAC) >>
  gen_tac >> Cases_on `is_bytestring_type (expr_type (HD args)) /\ is_word_type rt /\
    (lowered_value_type ce (HD args) = BaseT (BytesT (Dynamic 0)) \/
     lowered_value_type ce (HD args) = BaseT (StringT 0))` >> asm_simp_tac bool_ss []
  >- (rpt strip_tac >> gvs[cs_extends_refl]) >>
  Cases_on `is_bytestring_type (expr_type (HD args)) /\ is_bytestring_type rt /\
    type_memory_bytes ce (lowered_value_type ce (HD args)) < type_memory_bytes ce rt` >>
  asm_simp_tac bool_ss []
  >- type_convert_wrapped_tac first_emission_bytestring_widen_copy >>
  Cases_on `rt` >> simp_tac (srw_ss()) [] >>
  type_convert_wrapped_tac first_emission_type_convert
QED
