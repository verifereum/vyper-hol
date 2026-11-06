(* Callback-facing creation and call argument stages. *)
Theory exprCallFirstEmission
Ancestors
  exprValueFirstEmission contextFirstEmission compilerFirstEmission
  entryConditionalFirstEmission abiEncoderFirstEmission abiEncoderAppend
  abiDecoderAppend exprLowering fragExec compileEnv emitHelper
  venomInst context builtinSimple

fun call_emit_tac g =
  (rpt gen_tac >> strip_tac >>
   FIRST (map (fn th => drule_at (Pos (el 2)) th >> simp[])
     [cj 1 first_emission_emit_helpers, cj 2 first_emission_emit_helpers,
      cj 3 first_emission_emit_helpers])) g;
fun call_weak_tac g =
  (FIRST [FIRST_PROVE [metis_tac[first_emission_return]],
    ho_match_mp_tac first_emission_strong >> call_emit_tac,
    ho_match_mp_tac first_emission_bind >> conj_tac
      >- call_weak_tac >> gen_tac >> call_weak_tac,
    ho_match_mp_tac first_emission_ignore_bind >> conj_tac >> call_weak_tac]) g;

Theorem first_emission_create_salt:
  (!e a x b. cfn ce (expr_type e) e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_create_salt cfn ce salt a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> Cases_on `salt` >> rewrite_tac[compile_create_salt_def]
  >- metis_tac[first_emission_return] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> metis_tac[first_emission_return]
QED

Theorem first_emission_extcall_store_values:
  !vs off a x b. compile_extcall_store_values ce vs buf off a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Induct >> simp_tac bool_ss [compile_extcall_store_values_def]
  >- metis_tac[first_emission_return] >>
  qx_gen_tac `h` >> PairCases_on `h` >> gen_tac >> simp_tac bool_ss [compile_extcall_store_values_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> call_emit_tac) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_unwrap_value >>
  gen_tac >> ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- (rpt IF_CASES_TAC >>
      FIRST [ho_match_mp_tac first_emission_strong >>
               MATCH_ACCEPT_TAC first_emission_store_bytestring,
             call_weak_tac]) >>
  first_x_assum MATCH_ACCEPT_TAC
QED

Theorem first_emission_create_ctor_tuple:
  (!e a x b. MEM e es /\ cfn ce (expr_type e) e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_create_ctor_tuple cfn ce es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> simp_tac bool_ss [compile_create_ctor_tuple_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_multi_vvs >> first_assum ACCEPT_TAC) >>
  gen_tac >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (simp_tac bool_ss [compile_alloc_buffer_def] >> call_weak_tac) >>
  gen_tac >> simp_tac bool_ss [LET_THM] >>
  ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_extcall_store_values >>
  metis_tac[first_emission_return]
QED

Theorem first_emission_create_blueprint_args:
  (!e a x b. cfn ce (expr_type e) e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_create_blueprint_args cfn ce raw es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> Cases_on `raw`
  >- (Cases_on `es`
      >- (simp_tac bool_ss [compile_create_blueprint_args_def, listTheory.list_case_def] >> call_weak_tac) >>
      Cases_on `t`
      >- (simp_tac bool_ss [compile_create_blueprint_args_def, listTheory.list_case_def] >>
          ho_match_mp_tac first_emission_bind >> conj_tac
          >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
          gen_tac >> call_weak_tac) >>
      simp_tac bool_ss [compile_create_blueprint_args_def, listTheory.list_case_def] >> call_weak_tac) >>
  simp_tac bool_ss [compile_create_blueprint_args_def, listTheory.list_case_def] >> IF_CASES_TAC
  >- call_weak_tac >>
  simp_tac bool_ss [LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (simp_tac bool_ss [compile_alloc_buffer_def] >> call_weak_tac) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_create_ctor_tuple >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_abi_encode_to_buf >>
  gen_tac >> call_weak_tac
QED

Theorem first_emission_create_snapshot:
  !a x b. compile_create_snapshot ce vv ty a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  simp_tac bool_ss [compile_create_snapshot_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (simp_tac bool_ss [compile_alloc_buffer_def] >> call_weak_tac) >>
  gen_tac >> ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- (Cases_on `vv_location vv` >>
      simp_tac bool_ss [optionTheory.option_case_def]
      >- (rewrite_tac[compile_copy_memory_dynamic_def] >> call_weak_tac) >>
      Cases_on `x` >>
      simp_tac bool_ss [data_location_case_def, compile_slot_to_memory_def,
        compile_copy_memory_dynamic_def] >>
      FIRST [call_weak_tac,
        ho_match_mp_tac first_emission_ignore_bind >> conj_tac
          >- (ho_match_mp_tac first_emission_strong >>
              MATCH_ACCEPT_TAC first_emission_word_copy_loop) >> call_weak_tac,
        ho_match_mp_tac first_emission_ignore_bind >> conj_tac
          >- MATCH_ACCEPT_TAC first_emission_imm_copy >> call_weak_tac]) >>
  call_weak_tac
QED

val call_append_simps =
  [cs_appends_return, cs_appends_prims, cs_appends_emit_helpers,
   cs_appends_abi_alloc_buffer, cs_appends_abi_encode_mutual,
   cs_appends_abi_decode_mutual, LET_THM];
fun call_append_tac g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss()) call_append_simps],
    (rename1 `cs_appends (compile_extcall_store_values _ _ _ _)` >>
      simp[cs_appends_def] >> metis_tac[first_emission_extcall_store_values]),
    (rename1 `cs_appends (compile_store_memory _ _ _ _ _)` >>
      simp[cs_appends_def] >> metis_tac[first_emission_store_memory]),
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- call_append_tac >> rpt gen_tac >> call_append_tac,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> call_append_tac,
    IF_CASES_TAC >> call_append_tac]) g;
fun call_tail_tac g =
  (rpt gen_tac >> strip_tac >>
   qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
   `cs_appends tail` by
     (simp_tac bool_ss [Abbr `tail`] >> call_append_tac) >>
   fs[cs_appends_def]) g;
fun call_strong_tac g =
  (FIRST [call_emit_tac,
    ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- call_strong_tac >> call_tail_tac,
    ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
      >- call_strong_tac >> call_tail_tac]) g;

Theorem first_emission_external_call_kwargs:
  !a x b.
    compile_external_call_kwargs ce addr vals tys msz asz mid rsz minsz rmsz static
      value gas skip def dop rty dty einfo dinfo a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_external_call_kwargs_def, compile_alloc_buffer_def,
    compile_default_return_path_def, compile_extcodesize_check_def,
    compile_return_value_decode_def, compile_select_def, LET_THM] >>
  call_strong_tac
QED
