(* Callback-facing creation and call argument stages. *)
Theory exprCallFirstEmission
Ancestors
  exprValueFirstEmission contextFirstEmission compilerFirstEmission
  entryConditionalFirstEmission abiEncoderFirstEmission abiEncoderAppend
  abiDecoderAppend exprLowering fragExec compileEnv emitHelper
  venomInst context builtinSimple builtinPrefixFirstEmission

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
  (!e a x b. salt = SOME e /\ cfn ce (expr_type e) e a = (x,b) ==>
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
  >- (match_mp_tac first_emission_lower_value >> metis_tac[listTheory.MEM]) >>
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
  (!e a x b. MEM e es /\ cfn ce (expr_type e) e a = (x,b) ==>
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
          >- (match_mp_tac first_emission_lower_value >> metis_tac[listTheory.MEM]) >>
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

val call_append_simps =
  [cs_appends_return, cs_appends_prims, cs_appends_emit_helpers,
   cs_appends_abi_alloc_buffer, cs_appends_abi_encode_mutual,
   cs_appends_abi_decode_mutual, LET_THM];
fun call_append_tac g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss()) call_append_simps],
    (rename1 `cs_appends (compile_extcall_store_values _ _ _ _)` >>
      simp[cs_appends_def] >> metis_tac[first_emission_extcall_store_values]),
    (rename1 `cs_appends (unwrap_value _ _)` >>
      simp[cs_appends_def] >> metis_tac[first_emission_unwrap_value]),
    (rename1 `cs_appends (compile_store_memory _ _ _ _ _)` >>
      simp[cs_appends_def] >> metis_tac[first_emission_store_memory]),
    (rename1 `cs_appends (compile_word_copy_loop _ _ _ _ _ _)` >>
      simp[cs_appends_def] >> metis_tac[first_emission_word_copy_loop]),
    (rename1 `cs_appends (compile_imm_copy_to_memory _ _ _ _ _ _)` >>
      simp[cs_appends_def] >> metis_tac[first_emission_imm_copy]),
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

Theorem first_emission_create_snapshot:
  !a x b. compile_create_snapshot ce vv ty a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_create_snapshot_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (simp_tac bool_ss [compile_alloc_buffer_def] >> call_strong_tac) >>
  gen_tac >> Cases_on `vv_location vv` >>
  simp_tac bool_ss [optionTheory.option_case_def]
  >- (rewrite_tac[compile_copy_memory_dynamic_def] >> call_tail_tac) >>
  Cases_on `x` >>
  simp_tac bool_ss [data_location_case_def, compile_slot_to_memory_def,
    compile_copy_memory_dynamic_def] >> call_tail_tac
QED

Theorem cs_appends_lower_value_callback[local]:
  cs_appends (cfn ce ty e) ==> cs_appends (lower_value cfn ce ty e)
Proof
  strip_tac >> rewrite_tac[lower_value_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> simp[cs_appends_def] >> metis_tac[first_emission_unwrap_value]
QED

Theorem cs_appends_multi_vvs_callback[local]:
  (!ce ty e. cs_appends (cfn ce ty e)) ==>
  !es. cs_appends (compile_multi_vvs cfn ce es)
Proof
  strip_tac >> Induct >> rewrite_tac[compile_multi_vvs_def]
  >- simp[cs_appends_return] >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac >- simp[] >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> simp[cs_appends_return]
QED

Theorem cs_appends_create_ctor_callback[local]:
  (!ce ty e. cs_appends (cfn ce ty e)) ==>
  cs_appends (compile_create_ctor_tuple cfn ce es)
Proof
  strip_tac >> simp_tac bool_ss [compile_create_ctor_tuple_def, LET_THM] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (irule cs_appends_multi_vvs_callback >> simp[]) >>
  gen_tac >> call_append_tac
QED

Theorem cs_appends_create_salt_callback[local]:
  (!ce ty e. cs_appends (cfn ce ty e)) ==>
  cs_appends (compile_create_salt cfn ce salt)
Proof
  strip_tac >> Cases_on `salt` >> rewrite_tac[compile_create_salt_def]
  >- simp[cs_appends_return] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (irule cs_appends_lower_value_callback >> simp[]) >>
  simp[cs_appends_return]
QED

fun creation_append_tac g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss())
      [cs_appends_lower_value_callback, cs_appends_multi_vvs_callback,
       cs_appends_create_ctor_callback, cs_appends_create_salt_callback,
       cs_appends_return]],
    call_append_tac,
    (rename1 `cs_appends (compile_create_dispatch _ _ _ _ _)` >>
      simp[cs_appends_def] >> metis_tac[first_emission_create_dispatch]),
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- creation_append_tac >>
      simp_tac bool_ss [pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF] >>
      rpt gen_tac >> creation_append_tac,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> creation_append_tac,
    IF_CASES_TAC >> creation_append_tac]) g;
fun creation_tail_tac g =
  (rpt gen_tac >> strip_tac >>
   qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
   `cs_appends tail` by
     (simp_tac bool_ss [Abbr `tail`] >> creation_append_tac) >>
   fs[cs_appends_def]) g;

Theorem first_emission_raw_create:
  (!ce ty e. cs_appends (cfn ce ty e)) /\
  (!a x b. cfn ce (expr_type bytecode) bytecode a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_raw_create cfn ce bytecode value args salt rof a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> simp_tac bool_ss [compile_raw_create_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- first_assum ACCEPT_TAC >>
  gen_tac >> ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_create_snapshot >>
  simp_tac bool_ss [compile_copy_memory_dynamic_def] >> creation_tail_tac
QED

Theorem first_emission_materialize_vv:
  !a x b. compile_materialize_vv ce ty vv a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_materialize_vv_def, compile_alloc_buffer_def, LET_THM] >>
  call_strong_tac
QED

Theorem first_emission_ext_call_kwarg:
  (!ty a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_ext_call_kwarg cfn ce rty k e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> simp_tac bool_ss [compile_ext_call_kwarg_def, LET_THM] >>
  IF_CASES_TAC
  >- (ho_match_mp_tac first_emission_bind >> conj_tac
      >- metis_tac[] >> gen_tac >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_materialize_vv) >>
      gen_tac >> metis_tac[first_emission_return]) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> metis_tac[first_emission_return]
QED

Theorem first_emission_ext_call_kwargs:
  !es ks.
  (!e ty a x b. MEM e es /\ cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_ext_call_kwargs cfn ce rty ks es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Induct >> Cases_on `ks` >> simp_tac bool_ss [compile_ext_call_kwargs_def]
  >- metis_tac[first_emission_return]
  >- metis_tac[first_emission_return]
  >- metis_tac[first_emission_return] >>
  rpt gen_tac >> strip_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_ext_call_kwarg >> metis_tac[listTheory.MEM]) >>
  qx_gen_tac `res` >> PairCases_on `res` >> simp_tac bool_ss [pairTheory.UNCURRY_DEF] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (first_x_assum match_mp_tac >> metis_tac[listTheory.MEM]) >>
  qx_gen_tac `out` >> PairCases_on `out` >> simp_tac bool_ss [pairTheory.UNCURRY_DEF] >>
  metis_tac[first_emission_return]
QED

Theorem first_emission_stage_intcall_args:
  !ce vals flags tys a x b. compile_stage_intcall_args ce vals flags tys a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  recInduct compile_stage_intcall_args_ind >> rpt conj_tac
  >- (simp_tac bool_ss [compile_stage_intcall_args_def] >> metis_tac[first_emission_return])
  >- (rpt gen_tac >> strip_tac >> simp_tac bool_ss [compile_stage_intcall_args_def] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- MATCH_ACCEPT_TAC first_emission_unwrap_value >> gen_tac >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- first_assum ACCEPT_TAC >> gen_tac >> metis_tac[first_emission_return])
  >- (rpt gen_tac >> strip_tac >>
      simp_tac bool_ss [compile_stage_intcall_args_def, LET_THM] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- MATCH_ACCEPT_TAC first_emission_unwrap_value >> gen_tac >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- (POP_ASSUM_LIST (K all_tac) >>
          simp_tac bool_ss [compile_alloc_buffer_def] >> call_weak_tac) >>
      gen_tac >> rule_assum_tac (SRULE []) >>
      ho_match_mp_tac first_emission_ignore_bind >> conj_tac
      >- (IF_CASES_TAC
          >- (ho_match_mp_tac first_emission_strong >> call_emit_tac) >>
          IF_CASES_TAC
          >- (ho_match_mp_tac first_emission_ignore_bind >> conj_tac
              >- (ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_store_bytestring) >>
              metis_tac[first_emission_return]) >>
          MATCH_ACCEPT_TAC first_emission_store_memory) >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- first_assum ACCEPT_TAC >> gen_tac >> metis_tac[first_emission_return]) >>
  rpt gen_tac >> strip_tac >>
  asm_simp_tac bool_ss [compile_stage_intcall_args_def] >>
  (ho_match_mp_tac first_emission_bind >> conj_tac
   >- MATCH_ACCEPT_TAC first_emission_unwrap_value >> gen_tac >>
   ho_match_mp_tac first_emission_bind >> conj_tac
   >- first_assum ACCEPT_TAC >> gen_tac >> metis_tac[first_emission_return])
QED

Theorem cs_appends_store_multi_results[local]:
  !ops off. cs_appends (store_multi_results buf ops off)
Proof
  Induct >> simp_tac bool_ss [store_multi_results_def]
  >- MATCH_ACCEPT_TAC cs_appends_return >>
  rpt gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >> gen_tac >>
  ho_match_mp_tac cs_appends_ignore_bind >> simp[cs_appends_emit_helpers]
QED

Theorem first_emission_fresh_vars[local]:
  !n a x b. fresh_vars n a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Induct >> simp_tac bool_ss [fresh_vars_def]
  >- metis_tac[first_emission_return] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_fresh] >> gen_tac >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- first_assum ACCEPT_TAC >> gen_tac >> metis_tac[first_emission_return]
QED

Theorem first_emission_multi_op:
  opc <> PHI ==>
  !a x b. emit_multi_op opc ops n a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  strip_tac >> rewrite_tac[emit_multi_op_def] >>
  ho_match_mp_tac entry_first_emission_then_strong >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_fresh_vars >> gen_tac >>
  ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_at (Pos (el 2)) (cj 1 first_emission_emit_helpers) >> simp[]) >>
  metis_tac[first_emission_return]
QED

Theorem first_emission_intcall:
  (!e ty a x b. MEM e args /\ cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_call cfn ce rty ty (IntCall fid) args defret a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> simp_tac bool_ss [compile_call_def, LET_THM] >>
  pairarg_tac >> asm_simp_tac bool_ss [LET_THM, pairTheory.UNCURRY_DEF, pairTheory.FST, pairTheory.SND] >>
  qmatch_goalsub_abbrev_tac `Label ilbl` >>
  qmatch_goalsub_abbrev_tac `StackValue cty` >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_multi_vvs >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (Cases_on `returns_count > 0` >> asm_simp_tac bool_ss []
      >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
          >- (POP_ASSUM_LIST (K all_tac) >>
              simp_tac bool_ss [compile_alloc_buffer_def] >> call_weak_tac) >>
          gen_tac >> simp[cs_extends_refl]) >>
      Cases_on `return_buf_size > 0` >> asm_simp_tac bool_ss []
      >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
          >- (POP_ASSUM_LIST (K all_tac) >>
              simp_tac bool_ss [compile_alloc_buffer_def] >> call_weak_tac) >>
          gen_tac >> simp[cs_extends_refl]) >>
      simp[cs_extends_refl]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_stage_intcall_args >>
  gen_tac >> POP_ASSUM_LIST (K all_tac) >>
  Cases_on `returns_count > 0` >> Cases_on `return_buf` >>
  asm_simp_tac (srw_ss()) [] >>
  (rewrite_tac[state_pair_let_bind] >>
   ho_match_mp_tac first_emission_strong >>
   ho_match_mp_tac first_emission_strong_bind >> conj_tac
   >- FIRST [call_emit_tac, match_mp_tac first_emission_multi_op >> simp[]] >>
   rpt gen_tac >> simp_tac bool_ss [comp_bind_def] >>
   simp[cs_extends_refl] >> pairarg_tac >>
   gvs[] >> metis_tac[cs_appends_store_multi_results, cs_appends_def])
QED

Theorem first_emission_extcall:
  (!e ty a x b. MEM e args /\ cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_call cfn ce rty ty (ExtCall static skip (nm,tys,rt) opts) args defret a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> Cases_on `args` >> simp_tac (srw_ss()) [compile_call_def, LET_THM]
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (ho_match_mp_tac first_emission_strong >> call_emit_tac) >>
      gen_tac >> simp[cs_extends_refl]) >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[listTheory.MEM]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_multi_vvs >> metis_tac[listTheory.MEM, rich_listTheory.MEM_TAKE]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_ext_call_kwargs >> metis_tac[listTheory.MEM, rich_listTheory.MEM_DROP_IMP]) >>
  qx_gen_tac `kw` >> PairCases_on `kw` >>
  simp_tac bool_ss [pairTheory.UNCURRY_DEF, pairTheory.FST, pairTheory.SND] >>
  pairarg_tac >> asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF, pairTheory.FST, pairTheory.SND] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (Cases_on `kw1` >> simp_tac (srw_ss()) []
      >- (ho_match_mp_tac first_emission_strong >> call_emit_tac) >>
      simp[cs_extends_refl]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_external_call_kwargs) >>
  gen_tac >> rpt gen_tac >> IF_CASES_TAC >> simp[cs_extends_refl]
QED

Theorem first_emission_send:
  (!e ty a x b. MEM e args /\ cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_call cfn ce rty ty (Send has_gas) args defret a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> Cases_on `args` >> simp_tac (srw_ss()) [compile_call_def, LET_THM]
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (ho_match_mp_tac first_emission_strong >> call_emit_tac) >>
      gen_tac >> simp[cs_extends_refl]) >>
  Cases_on `t` >> simp_tac (srw_ss()) []
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (ho_match_mp_tac first_emission_strong >> call_emit_tac) >>
      gen_tac >> simp[cs_extends_refl]) >>
  Cases_on `LENGTH t' = (if has_gas then 1 else 0)` >> asm_simp_tac bool_ss []
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (match_mp_tac first_emission_lower_value >> metis_tac[listTheory.MEM]) >>
      gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (match_mp_tac first_emission_lower_value >> metis_tac[listTheory.MEM]) >>
      gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (Cases_on `t'` >> simp_tac (srw_ss()) []
          >- simp[cs_extends_refl] >>
          Cases_on `t` >> simp_tac (srw_ss()) []
          >- (match_mp_tac first_emission_lower_value >> metis_tac[listTheory.MEM]) >>
          simp[cs_extends_refl]) >>
      gen_tac >> POP_ASSUM_LIST (K all_tac) >>
      rewrite_tac[state_pair_let_bind] >>
      ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- call_emit_tac >>
      rpt gen_tac >> simp_tac bool_ss [comp_bind_def, LET_THM] >> pairarg_tac >>
      gvs[] >> metis_tac[cs_appends_emit_helpers, cs_appends_def]) >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> call_emit_tac) >>
  gen_tac >> simp[cs_extends_refl]
QED

Theorem cs_appends_ext_call_kwarg_callback[local]:
  (!ce ty e. cs_appends (cfn ce ty e)) ==>
  cs_appends (compile_ext_call_kwarg cfn ce rty k e)
Proof
  strip_tac >> simp_tac bool_ss [compile_ext_call_kwarg_def, LET_THM] >>
  IF_CASES_TAC >> ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[]
  >- (gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac
      >- (simp[cs_appends_def] >> metis_tac[first_emission_materialize_vv]) >>
      simp[cs_appends_return])
  >- (irule cs_appends_lower_value_callback >> simp[]) >>
  simp[cs_appends_return]
QED

Theorem cs_appends_ext_call_kwargs_callback[local]:
  (!ce ty e. cs_appends (cfn ce ty e)) ==>
  !es ks. cs_appends (compile_ext_call_kwargs cfn ce rty ks es)
Proof
  strip_tac >> Induct >> Cases_on `ks` >>
  simp_tac bool_ss [compile_ext_call_kwargs_def]
  >- simp[cs_appends_return]
  >- simp[cs_appends_return]
  >- simp[cs_appends_return] >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (irule cs_appends_ext_call_kwarg_callback >> simp[]) >>
  simp_tac bool_ss [pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF] >>
  rpt gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac >- simp[] >>
  simp_tac bool_ss [pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF] >>
  simp[cs_appends_return]
QED

fun raw_result_append_tac g =
  (CONV_TAC (DEPTH_CONV ETA_CONV) >>
   ho_match_mp_tac cs_appends_bind >> conj_tac
   >- (simp[cs_appends_def] >> metis_tac[first_emission_raw_call_outbuf]) >>
   simp_tac bool_ss [pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF] >>
   rpt gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac
   >- (simp[cs_appends_def] >> metis_tac[first_emission_raw_call_finish]) >>
   gen_tac >> Cases_on `rcf.rcf_max_outsize = 0` >>
   asm_simp_tac bool_ss [] >> simp[cs_appends_def, cs_extends_refl]) g;

Theorem first_emission_rawcall:
  (!ce ty e. cs_appends (cfn ce ty e)) /\
  (!e ty a x b. MEM e args /\ cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_call cfn ce rty ty (RawCallTarget rcf) args defret a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> Cases_on `args` >> simp_tac (srw_ss()) [compile_call_def, LET_THM]
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (ho_match_mp_tac first_emission_strong >> call_emit_tac) >>
      gen_tac >> simp[cs_extends_refl]) >>
  Cases_on `t` >> simp_tac (srw_ss()) []
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (ho_match_mp_tac first_emission_strong >> call_emit_tac) >>
      gen_tac >> simp[cs_extends_refl]) >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[listTheory.MEM]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[listTheory.MEM]) >>
  gen_tac >> rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- call_emit_tac >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
  `cs_appends tail` suffices_by metis_tac[cs_appends_def] >>
  simp_tac bool_ss [Abbr `tail`] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >>
  gen_tac >> CONV_TAC (RAND_CONV ETA_CONV) >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (irule cs_appends_ext_call_kwargs_callback >> simp[]) >>
  simp_tac bool_ss [pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF] >>
  rpt gen_tac >> Cases_on `p_1'` >>
  simp_tac bool_ss [optionTheory.option_case_def, pairTheory.UNCURRY_DEF] >>
  rewrite_tac[state_pair_let_bind] >> CONV_TAC (DEPTH_CONV ETA_CONV)
  >- (ho_match_mp_tac cs_appends_bind >> conj_tac
      >- simp[cs_appends_emit_helpers] >>
      gen_tac >> raw_result_append_tac) >>
  raw_result_append_tac
QED

Theorem first_emission_rawcall_calldata:
  (!e ty a x b. MEM e args /\ cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_call cfn ce rty ty (RawCallCalldataTarget rcf) args defret a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> Cases_on `args` >> simp_tac (srw_ss()) [compile_call_def, LET_THM]
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (ho_match_mp_tac first_emission_strong >> call_emit_tac) >>
      gen_tac >> simp[cs_extends_refl]) >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[listTheory.MEM]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_ext_call_kwargs >> metis_tac[listTheory.MEM]) >>
  qx_gen_tac `kw` >> PairCases_on `kw` >>
  simp_tac bool_ss [pairTheory.UNCURRY_DEF, pairTheory.FST, pairTheory.SND] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (Cases_on `kw1` >> simp_tac (srw_ss()) []
      >- (ho_match_mp_tac first_emission_strong >> call_emit_tac) >>
      simp[cs_extends_refl]) >>
  gen_tac >> rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_raw_call_outbuf >>
  simp_tac bool_ss [pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF] >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
  `cs_appends tail` suffices_by metis_tac[cs_appends_def] >>
  simp_tac bool_ss [Abbr `tail`] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (simp[cs_appends_def] >> metis_tac[first_emission_msg_data_to_memory]) >>
  simp_tac bool_ss [pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF] >>
  rpt gen_tac >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (simp[cs_appends_def] >> metis_tac[first_emission_raw_call_finish]) >>
  gen_tac >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >>
  gen_tac >> Cases_on `rcf.rcf_max_outsize = 0` >>
  asm_simp_tac bool_ss [] >> simp[cs_appends_def, cs_extends_refl]
QED
