(* ABI builtin wrappers emit before invoking recursive encoder/decoder suffixes. *)
Theory abiOuterFirstEmission
Ancestors
  compilerFirstEmission abiEncoderAppend abiDecoderAppend builtinAbi
  exprValueFirstEmission exprAggregateFirstEmission exprLowering contextFirstEmission guardedCallbackFirstEmission
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

Theorem abi_outer_store_tuple_appends[local]:
  !es ce buf off. cs_appends (compile_store_abi_tuple ce buf off es)
Proof
  Induct >- simp[compile_store_abi_tuple_def, cs_appends_return] >>
  rpt gen_tac >> PairCases_on `h` >>
  `!dst src n. cs_appends (compile_copy_memory dst src n)` by
    metis_tac[first_emission_copy_memory, cs_appends_def] >>
  rewrite_tac[compile_store_abi_tuple_def] >> abi_outer_append_tac
QED

Theorem abi_outer_encode_ptr[local]:
  !a x b. as_ptr_val vt LocMemory
      (lower_abi_encode ensure mid src ei len a) = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> qmatch_goalsub_abbrev_tac `as_ptr_val _ _ result` >>
  Cases_on `result` >> simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
  drule first_emission_lower_abi_encode >> simp[]
QED

Theorem abi_outer_encode_ptr_appends[local]:
  cs_appends (\s. as_ptr_val vt LocMemory (lower_abi_encode ensure mid src ei len s))
Proof
  simp[cs_appends_def] >> metis_tac[abi_outer_encode_ptr]
QED

fun abi_alloc_suffix_tac g =
  (gen_tac >> rewrite_tac[state_pair_let_bind] >>
   ho_match_mp_tac first_emission_strong >>
   ho_match_mp_tac first_emission_strong_bind >> conj_tac
   >- (rewrite_tac[compile_alloc_buffer_def] >>
       ho_match_mp_tac first_emission_strong_bind >> conj_tac
       >- (rpt gen_tac >> strip_tac >>
           drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
       metis_tac[cs_appends_return, cs_appends_def]) >>
   rpt gen_tac >> strip_tac >>
   qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
   `cs_appends tail` by
     (simp_tac bool_ss [Abbr `tail`] >>
      ho_match_mp_tac cs_appends_bind >> conj_tac
      >- simp[abi_outer_store_tuple_appends, cs_appends_emit_helpers] >>
      rpt gen_tac >> MATCH_ACCEPT_TAC abi_outer_encode_ptr_appends) >>
   fs[cs_appends_def]) g;

Theorem first_emission_type_abi_encode:
  (!e a x b. MEM e args /\ cfn ce (expr_type e) e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_type_builtin_dispatch_body cfn ce vt ty
      (AbiEncode ensure mid) rt args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> simp_tac (srw_ss()) [compile_type_builtin_dispatch_body_def, LET_THM] >>
  Cases_on `LENGTH args = 1 /\ ~ensure` >> asm_simp_tac (srw_ss()) []
  >- (`MEM (HD args) args` by (Cases_on `args` >> fs[]) >>
      Cases_on `is_word_type (expr_type (HD args))` >> asm_simp_tac (srw_ss()) []
      >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
          >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
          abi_alloc_suffix_tac) >>
      ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- metis_tac[] >>
      gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- MATCH_ACCEPT_TAC first_emission_unwrap_value >>
      gen_tac >> MATCH_ACCEPT_TAC abi_outer_encode_ptr) >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_multi_exprs >> first_assum ACCEPT_TAC) >>
  abi_alloc_suffix_tac
QED

(* Consumer check at the exact list-sized callback used by the recursive compiler. *)
Theorem first_emission_guarded_abi_encode[local]:
  (!ce ty e a x b. expr_size e < list_size expr_size args /\
    cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_type_builtin_dispatch_body
      (expr_child_callback (list_size expr_size args) cfn) ce vt ty
      (AbiEncode ensure mid) rt args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> match_mp_tac first_emission_type_abi_encode >>
  drule first_emission_expr_child_callback >> metis_tac[]
QED
