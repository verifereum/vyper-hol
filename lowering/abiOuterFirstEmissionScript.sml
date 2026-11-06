(* ABI builtin wrappers emit before invoking recursive encoder/decoder suffixes. *)
Theory abiOuterFirstEmission
Ancestors
  compilerFirstEmission abiEncoderAppend abiDecoderAppend builtinAbi
  exprValueFirstEmission exprLowering
  fragExec compileEnv emitHelper venomInst context

fun abi_outer_append_tac g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss())
      [cs_appends_return, cs_appends_prims, cs_appends_emit_helpers,
       cs_appends_abi_alloc_buffer, cs_appends_abi_encode_mutual,
       cs_appends_abi_decode_mutual, LET_THM]],
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- abi_outer_append_tac >> rpt gen_tac >> abi_outer_append_tac,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> abi_outer_append_tac,
    IF_CASES_TAC >> abi_outer_append_tac]) g;
fun abi_outer_tail_tac g =
  (rpt gen_tac >> strip_tac >>
   qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
   `cs_appends tail` by
     (simp_tac bool_ss [Abbr `tail`] >> abi_outer_append_tac) >>
   fs[cs_appends_def]) g;

Theorem first_emission_lower_abi_decode:
  !a x b. lower_abi_decode src di lo hi sz a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rewrite_tac[lower_abi_decode_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
  abi_outer_tail_tac
QED

Theorem first_emission_lower_abi_encode:
  !a x b. lower_abi_encode ensure mid src ei len a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  Cases_on `mid` >> simp_tac bool_ss [lower_abi_encode_def,
    optionTheory.option_case_def, compile_alloc_buffer_def, LET_THM] >>
  (ho_match_mp_tac first_emission_strong_bind >> conj_tac
   >- (ho_match_mp_tac first_emission_strong_bind >> conj_tac
       >- (rpt gen_tac >> strip_tac >>
           drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
       abi_outer_tail_tac) >>
   abi_outer_tail_tac)
QED

Theorem first_emission_type_abi_decode:
  (!a x b. cfn ce (expr_type (HD args)) (HD args) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_type_builtin_dispatch_body cfn ce vt ty
      (AbiDecode unwrap) rt args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> simp_tac (srw_ss()) [compile_type_builtin_dispatch_body_def, LET_THM] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- first_assum ACCEPT_TAC >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_unwrap_value >>
  gen_tac >> rpt gen_tac >>
  qmatch_goalsub_abbrev_tac `as_ptr_val _ _ result` >>
  Cases_on `result` >> simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
  drule first_emission_lower_abi_decode >> simp[]
QED
