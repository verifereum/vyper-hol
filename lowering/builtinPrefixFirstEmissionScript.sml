(* Builtin prefixes: stop first-emission reasoning at the first opcode. *)
Theory builtinPrefixFirstEmission
Ancestors
  compilerFirstEmission entryConditionalFirstEmission abiEncoderAppend
  abiDecoderAppend builtinStrings builtinSystem builtinCreate builtinSimple
  fragExec compileEnv emitHelper venomInst context

val builtin_append_simps =
  [cs_appends_return, cs_appends_prims, cs_appends_emit_helpers,
   cs_appends_abi_alloc_buffer, cs_appends_abi_encode_mutual, LET_THM];
fun builtin_append_tac g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss()) builtin_append_simps],
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- builtin_append_tac >> rpt gen_tac >> builtin_append_tac,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> builtin_append_tac,
    IF_CASES_TAC >> builtin_append_tac]) g;
fun builtin_tail_tac g =
  (rpt gen_tac >> strip_tac >>
   qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
   `cs_appends tail` by
     (simp_tac bool_ss [Abbr `tail`] >> builtin_append_tac) >>
   fs[cs_appends_def]) g;
fun builtin_emit_tac g =
  (rpt gen_tac >> strip_tac >>
   FIRST (map (fn th => drule_at (Pos (el 2)) th >> simp[])
     [cj 1 first_emission_emit_helpers, cj 2 first_emission_emit_helpers,
      cj 3 first_emission_emit_helpers])) g;
fun builtin_strong_tac g =
  (FIRST [builtin_emit_tac,
    ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- builtin_strong_tac >> builtin_tail_tac,
    ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
      >- builtin_strong_tac >> builtin_tail_tac]) g;

Theorem first_emission_uint2str:
  !a x b. compile_uint2str op nd sz a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_uint2str_def, compile_alloc_buffer_def] >>
  builtin_strong_tac
QED

Theorem first_emission_msg_data_to_memory:
  !a x b. compile_msg_data_to_memory a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rewrite_tac[compile_msg_data_to_memory_def, compile_alloc_dynamic_def] >>
  builtin_strong_tac
QED

Theorem first_emission_raw_call_outbuf:
  !a x b. compile_raw_call_outbuf maxsize a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_raw_call_outbuf_def, compile_alloc_buffer_def, LET_THM] >>
  IF_CASES_TAC >> builtin_strong_tac
QED

Theorem first_emission_raw_call_finish:
  !a x b. compile_raw_call_finish dest dp dl gas val ct maxsize rev ov op a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  Cases_on `ct` >>
  simp_tac bool_ss [compile_raw_call_finish_def, call_type_case_def,
    compile_select_def, LET_THM] >>
  builtin_strong_tac
QED

Theorem first_emission_create_dispatch:
  !a x b. compile_create_dispatch codeptr codelen v salt rev a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  Cases_on `salt` >>
  simp_tac bool_ss [compile_create_dispatch_def, optionTheory.option_case_def,
    compile_check_create_result_def] >> builtin_strong_tac
QED

Theorem first_emission_create_proxy_buf:
  !a x b. compile_create_proxy_buf dest a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_create_proxy_buf_def, compile_alloc_buffer_def] >>
  builtin_strong_tac
QED

Theorem first_emission_create_blueprint_check:
  !a x b. compile_create_blueprint_check dest off a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rewrite_tac[compile_create_blueprint_check_def] >> builtin_strong_tac
QED

Theorem first_emission_check_create_result:
  !a x b. compile_check_create_result result rev a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Cases_on `rev` >> simp_tac bool_ss [compile_check_create_result_def]
  >- (ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac first_emission_no_code >>
          MATCH_ACCEPT_TAC (cj 1 first_emission_counters)) >>
      gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac first_emission_no_code >>
          MATCH_ACCEPT_TAC (cj 1 first_emission_counters)) >>
      gen_tac >> ho_match_mp_tac first_emission_strong >> builtin_strong_tac) >>
  metis_tac[first_emission_return]
QED

Theorem cs_appends_create_dispatch_prefix[local]:
  cs_appends (compile_create_dispatch codeptr codelen v salt rev)
Proof
  simp[cs_appends_def] >> metis_tac[first_emission_create_dispatch]
QED

Theorem first_emission_create_proxy:
  !a x b. compile_create_proxy dest v salt rev a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rewrite_tac[compile_create_proxy_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_create_proxy_buf >>
  metis_tac[first_emission_create_dispatch]
QED

Theorem first_emission_create_copy:
  !a x b. compile_create_copy dest v salt rev a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  Cases_on `salt` >> simp_tac bool_ss [compile_create_copy_def,
    compile_check_create_result_def, compile_alloc_dynamic_def,
    optionTheory.option_case_def, LET_THM] >> builtin_strong_tac
QED

Theorem first_emission_create_blueprint_append:
  !a x b. compile_create_blueprint_append dest v salt off codesz ap al rev a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  Cases_on `salt` >> simp_tac bool_ss [compile_create_blueprint_append_def,
    compile_check_create_result_def, compile_alloc_dynamic_def,
    compile_copy_memory_dynamic_def, optionTheory.option_case_def] >> builtin_strong_tac
QED
