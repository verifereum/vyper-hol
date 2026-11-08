(* Statement compiler original-block first-emission boundaries. *)
Theory stmtCompilerFirstEmission
Ancestors
  exprCompilerFirstEmission stmtLoweringMono entryConditionalFirstEmission
  compilerFirstEmission exprValueFirstEmission contextFirstEmission
  targetPointerFirstEmission fragExec stmtLowering exprLoweringProps exprLowering
  context compileEnv emitHelper venomInst

Theorem stmt_first_emission_lower_value[local]:
  !ce ty e a x b. lower_value compile_expr ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_lower_value >>
  metis_tac[cj 1 first_emission_expr_compilers]
QED

Theorem stmt_declare_local_no_code[local]:
  declare_local ce id ty a = (x,b) ==>
  cs_extends a b /\ a.cs_blocks = b.cs_blocks /\
  a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts
Proof
  simp_tac bool_ss [declare_local_def, LET_THM] >> IF_CASES_TAC
  >- (simp_tac bool_ss [comp_bind_def] >> Cases_on `fresh_var a` >>
      simp_tac (srw_ss()) [comp_return_def] >> strip_tac >> gvs[] >>
      metis_tac[first_emission_fresh]) >>
  metis_tac[first_emission_return]
QED

Theorem stmt_declare_stmt_no_code[local]:
  declare_stmt_local ce s a = (x,b) ==>
  cs_extends a b /\ a.cs_blocks = b.cs_blocks /\
  a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts
Proof
  Cases_on `s` >> simp_tac (srw_ss()) [declare_stmt_local_def] >>
  metis_tac[stmt_declare_local_no_code, first_emission_return]
QED

Theorem stmt_first_emission_local_alloca[local]:
  !ce id a x b. emit_local_alloca ce id a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> simp_tac bool_ss [emit_local_alloca_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp_tac (srw_ss()) []
  >- metis_tac[first_emission_return] >>
  Cases_on `x'` >> simp_tac (srw_ss()) []
  >~ [`PtrVar op sz`] >- (Cases_on `op` >> simp_tac (srw_ss()) [] >>
    metis_tac[first_emission_return,
      SRULE [] (Q.SPEC `ALLOCA` (cj 1 first_emission_emit_helpers))]) >>
  metis_tac[first_emission_return,
    SRULE [] (Q.SPEC `ALLOCA` (cj 1 first_emission_emit_helpers))]
QED

(* Convert existing monotonicity boundaries to code-extension contracts. *)
Theorem stmt_ci_mono_appends[local]:
  (!a. ci_mono a (SND (m a))) ==> cs_appends m
Proof
  simp[ci_mono_def, cs_appends_def] >> metis_tac[pairTheory.SND]
QED

val stmt_ci_leaves = List.concat (map BODY_CONJUNCTS
  [ci_mono_emit_op, ci_mono_emit_void, ci_mono_emit_inst,
   ci_mono_fresh_var, ci_mono_fresh_label, ci_mono_new_block,
   ci_mono_compile_alloc_buffer, ci_mono_compile_store_byte_chunks, ci_mono_unwrap_value,
   ci_mono_compile_expr_sa, ci_mono_context_helpers,
   ci_mono_compile_dynarray_append, ci_mono_comp_get,
   ci_mono_compile_get_target_ptr, ci_mono_stmt_helpers,
   ci_mono_list_helpers, ci_mono_return_helpers, compile_stmt_ci_mono,
   ci_mono_compile_store_memory, ci_mono_compile_copy_memory,
   ci_mono_compile_word_copy_loop,
   ci_mono_typed_memory_family, ci_mono_compile_abi_encode, ci_mono_compile_ptr_load,
   ci_mono_compile_imm_store_word, ci_mono_compile_imm_store_words,
   ci_mono_compile_imm_copy_to_memory, ci_mono_comp_return]);

fun stmt_append_tac g =
  (FIRST [ho_match_mp_tac stmt_ci_mono_appends >> rpt gen_tac >>
      FIRST (map MATCH_ACCEPT_TAC stmt_ci_leaves),
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- stmt_append_tac >> gen_tac >> stmt_append_tac,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> stmt_append_tac,
    IF_CASES_TAC >> stmt_append_tac,
    BasicProvers.TOP_CASE_TAC >> simp_tac bool_ss [LET_THM] >> stmt_append_tac]) g;

fun stmt_ext_tac g =
  (rpt gen_tac >> strip_tac >>
   qmatch_asmsub_abbrev_tac `tail initial_cs = (result,final_cs)` >>
   `cs_appends tail` by (simp_tac bool_ss [Abbr `tail`] >> stmt_append_tac) >>
   fs[cs_appends_def]) g;

fun stmt_emit_tac g =
  (rpt gen_tac >> strip_tac >>
   FIRST (map (fn th => drule_at (Pos (el 2)) th >> simp[] >> NO_TAC)
     [cj 1 first_emission_emit_helpers, cj 2 first_emission_emit_helpers,
      cj 3 first_emission_emit_helpers])) g;

Theorem stmt_alloc_buffer_first_emission[local]:
  !a x b. compile_alloc_buffer sz a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_alloc_buffer_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- stmt_emit_tac >> stmt_ext_tac
QED

val stmt_weak_leaves = [stmt_first_emission_lower_value,
  cj 1 first_emission_expr_compilers, first_emission_unwrap_value,
  stmt_first_emission_local_alloca, first_emission_store_memory,
  first_emission_copy_memory, cj 1 first_emission_context_typed_copy];

fun stmt_known_strong_tac g =
  (FIRST (map MATCH_ACCEPT_TAC
    [first_emission_word_copy_loop, first_emission_ptr_load,
     first_emission_ptr_store, first_emission_imm_store,
     stmt_alloc_buffer_first_emission, first_emission_dynarray_to_storage])) g;

fun stmt_fe_with leaves g =
  (FIRST [FIRST (map MATCH_ACCEPT_TAC leaves), first_assum MATCH_ACCEPT_TAC,
    ho_match_mp_tac first_emission_no_code >>
      FIRST (map MATCH_ACCEPT_TAC [first_emission_return, first_emission_get,
        first_emission_fresh, cj 1 first_emission_counters,
        stmt_declare_local_no_code, stmt_declare_stmt_no_code]),
    ho_match_mp_tac first_emission_strong >> stmt_known_strong_tac,
    ho_match_mp_tac first_emission_strong >> stmt_emit_tac,
    ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
        >- stmt_emit_tac >> stmt_ext_tac,
    ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
        >- stmt_emit_tac >> stmt_ext_tac,
    ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
        >- stmt_known_strong_tac >> stmt_ext_tac,
    ho_match_mp_tac first_emission_bind >> conj_tac
      >- stmt_fe_with leaves >> gen_tac >> stmt_fe_with leaves,
    ho_match_mp_tac first_emission_ignore_bind >> conj_tac >> stmt_fe_with leaves,
    IF_CASES_TAC >> asm_simp_tac bool_ss [] >> stmt_fe_with leaves,
    BasicProvers.TOP_CASE_TAC >> simp_tac bool_ss [LET_THM] >> stmt_fe_with leaves]) g;

fun stmt_fe_tac g = stmt_fe_with stmt_weak_leaves g;

Theorem stmt_first_emission_log_eval[local]:
  !es ce a x b. compile_log_eval_all ce es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Induct
  >- (simp_tac bool_ss [compile_log_eval_all_def] >> metis_tac[first_emission_return]) >>
  qx_gen_tac `e` >> qx_gen_tac `ce` >>
  simp_tac bool_ss [compile_log_eval_all_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- MATCH_ACCEPT_TAC stmt_first_emission_lower_value >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- first_assum MATCH_ACCEPT_TAC >>
  gen_tac >> metis_tac[first_emission_return]
QED

Theorem stmt_first_emission_log_topic[local]:
  !v bs a x b. compile_encode_log_topic v bs a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 2 gen_tac >> simp_tac bool_ss [compile_encode_log_topic_def] >>
  stmt_fe_tac
QED

Theorem stmt_first_emission_log_topics[local]:
  !xs a x b. compile_log_topic_ops xs a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Induct
  >- (simp_tac bool_ss [compile_log_topic_ops_def] >> metis_tac[first_emission_return]) >>
  gen_tac >> simp_tac bool_ss [compile_log_topic_ops_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- MATCH_ACCEPT_TAC stmt_first_emission_log_topic >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- first_assum MATCH_ACCEPT_TAC >>
  gen_tac >> metis_tac[first_emission_return]
QED

Theorem stmt_first_emission_reason[local]:
  !ce e a x b. compile_reason_message ce e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 2 gen_tac >> Cases_on `e` >> simp_tac bool_ss [compile_reason_message_def]
  >>~- ([`compile_expr _ _ _ _ = _`], MATCH_ACCEPT_TAC (cj 1 first_emission_expr_compilers)) >>
  rename1 `Literal ty lit` >> Cases_on `ty` >> Cases_on `lit` >>
  simp_tac bool_ss [compile_reason_message_def]
  >>~- ([`compile_expr _ _ _ _ = _`], MATCH_ACCEPT_TAC (cj 1 first_emission_expr_compilers)) >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp_tac bool_ss [compile_reason_message_def]
  >>~- ([`compile_expr _ _ _ _ = _`], MATCH_ACCEPT_TAC (cj 1 first_emission_expr_compilers)) >>
  simp_tac bool_ss [compile_bytelike_literal_def, compile_alloc_buffer_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- (ho_match_mp_tac first_emission_strong_bind >> conj_tac
          >- stmt_emit_tac >> stmt_ext_tac) >> stmt_ext_tac) >>
  gen_tac >> metis_tac[first_emission_return]
QED


Theorem stmt_first_emission_imm_words[local]:
  !imm src dst n off a x b. compile_imm_store_words imm src dst n off a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 4 gen_tac >> Cases_on `n` >> gen_tac >>
  simp_tac bool_ss [compile_imm_store_words_def]
  >- stmt_fe_tac >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_lit_byte_offset >> gen_tac >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- stmt_emit_tac >>
  simp_tac bool_ss [compile_lit_byte_offset_def] >> stmt_ext_tac
QED

val stmt_weak_leaves = stmt_first_emission_imm_words :: stmt_weak_leaves;

Theorem stmt_first_emission_assign[local]:
  !ce dst loc v prim src dt st di sz a x b.
    compile_assign_value ce dst loc v prim src dt st di sz a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 10 gen_tac >> Cases_on `loc` >>
  simp_tac bool_ss [compile_assign_value_def, data_location_case_def, LET_THM]
  >~ [`if prim then emit_void MSTORE _ else _`] >-
    (IF_CASES_TAC >- stmt_fe_tac >> IF_CASES_TAC
     >- (ho_match_mp_tac first_emission_strong >>
         ho_match_mp_tac first_emission_strong_bind >> conj_tac
         >- MATCH_ACCEPT_TAC stmt_alloc_buffer_first_emission >> stmt_ext_tac) >>
     stmt_fe_tac)
  >~ [`emit_inst INVALID`] >- stmt_fe_tac >>
  Cases_on `~prim /\ dt <> st /\ (~is_bytestring_type dt \/ ~is_bytestring_type st)` >>
  asm_simp_tac bool_ss []
  >>~- ([`compile_alloc_buffer sz`],
    ho_match_mp_tac first_emission_strong >>
    ho_match_mp_tac first_emission_strong_bind >> conj_tac
    >- (ho_match_mp_tac first_emission_strong_bind >> conj_tac
        >- MATCH_ACCEPT_TAC stmt_alloc_buffer_first_emission >> stmt_ext_tac) >>
    stmt_ext_tac)
  >> ho_match_mp_tac first_emission_bind
  >> (conj_tac >- stmt_fe_tac >> gen_tac)
  >> (IF_CASES_TAC >- stmt_fe_tac)
  >>~- ([`compile_memory_to_storage _ _ _`],
    namedCases_on `di` ["", "coords"] >> simp_tac bool_ss [optionTheory.option_case_def]
    >- (simp_tac bool_ss [compile_memory_to_storage_def,
        compile_memory_to_transient_def] >> stmt_fe_tac) >>
    PairCases_on `coords` >>
    simp_tac bool_ss [pairTheory.pair_case_def] >> stmt_fe_tac)
  >>~- ([`compile_memory_to_transient _ _ _`],
    namedCases_on `di` ["", "coords"] >> simp_tac bool_ss [optionTheory.option_case_def]
    >- (simp_tac bool_ss [compile_memory_to_transient_def] >> stmt_fe_tac) >>
    PairCases_on `coords` >> simp_tac bool_ss [pairTheory.pair_case_def] >> stmt_fe_tac)
  >> (IF_CASES_TAC >- stmt_fe_tac) >>
  MATCH_ACCEPT_TAC stmt_first_emission_imm_words
QED

Theorem stmt_first_emission_tuple_load[local]:
  !tys ce src off a x b. compile_tuple_load_all ce src tys off a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Cases >> ntac 3 gen_tac >> simp_tac bool_ss [compile_tuple_load_all_def, LET_THM]
  >- stmt_fe_tac >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- stmt_emit_tac >> stmt_ext_tac
QED

Theorem stmt_first_emission_store_at_loc[local]:
  !imm dst v loc a x b. compile_store_at_loc imm dst v loc a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 4 gen_tac >> Cases_on `loc`
  >- (simp_tac bool_ss [compile_store_at_loc_def] >> stmt_fe_tac) >>
  Cases_on `x` >> simp_tac bool_ss [compile_store_at_loc_def] >> stmt_fe_tac
QED

Theorem stmt_first_emission_tuple_store[local]:
  !ce tys ts vs a x b. compile_tuple_store_all ce tys ts vs a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  recInduct compile_tuple_store_all_ind >> rpt conj_tac >> rpt gen_tac >>
  simp_tac bool_ss [compile_tuple_store_all_def, LET_THM]
  >>~- ([`comp_return () _ = _`], metis_tac[first_emission_return])
  >> strip_tac
  >~ [`compile_get_target_ptr compile_expr _ _`] >-
    (ho_match_mp_tac first_emission_bind >> conj_tac
     >- (ho_match_mp_tac first_emission_get_target_ptr >>
         MATCH_ACCEPT_TAC (cj 1 first_emission_expr_compilers)) >>
     gen_tac >> stmt_fe_with [stmt_first_emission_assign,
       stmt_first_emission_store_at_loc]) >>
  stmt_fe_with (stmt_first_emission_assign :: stmt_first_emission_store_at_loc ::
    (SRULE [cj 1 first_emission_expr_compilers]
      (Q.SPEC `compile_expr` first_emission_get_target_ptr)) :: stmt_weak_leaves)
QED

Theorem stmt_first_emission_tuple_unpack[local]:
  !ce ty stage ts src a x b. compile_tuple_unpack ce ty stage ts src a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 5 gen_tac >> simp_tac bool_ss [compile_tuple_unpack_def, LET_THM] >>
  IF_CASES_TAC >- stmt_fe_tac >>
  IF_CASES_TAC
  >- (asm_simp_tac bool_ss [] >> ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- (ho_match_mp_tac first_emission_strong_bind >> conj_tac
          >- MATCH_ACCEPT_TAC stmt_alloc_buffer_first_emission >> stmt_ext_tac) >>
      stmt_ext_tac) >>
  asm_simp_tac bool_ss [] >>
  stmt_fe_with [stmt_first_emission_tuple_load, stmt_first_emission_tuple_store]
QED

Theorem stmt_first_emission_return_elements[local]:
  !tys ce src off a x b. compile_load_tuple_elements ce src tys off a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Cases >> ntac 3 gen_tac >> simp_tac bool_ss [compile_load_tuple_elements_def, LET_THM]
  >- stmt_fe_tac >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- stmt_emit_tac >> stmt_ext_tac
QED

Theorem stmt_first_emission_internal_return[local]:
  !ce rv pc cnt rt st tys buf a x b.
    compile_internal_return ce rv pc cnt rt st tys buf a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 8 gen_tac >> Cases_on `rv` >> Cases_on `buf` >>
  simp_tac bool_ss [compile_internal_return_def, optionTheory.option_case_def] >>
  stmt_fe_with (stmt_first_emission_return_elements :: stmt_weak_leaves)
QED

Theorem stmt_first_emission_external_return[local]:
  !rv prim raw info sz nr nk ut iv a x b.
    compile_external_return rv prim raw info sz nr nk ut iv a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 9 gen_tac >> simp_tac bool_ss [compile_external_return_def] >>
  ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- (simp_tac bool_ss [compile_nonreentrant_unlock_def] >> stmt_fe_tac) >>
  Cases_on `rv` >> simp_tac bool_ss [optionTheory.option_case_def]
  >- stmt_fe_tac >>
  IF_CASES_TAC >- stmt_fe_tac >>
  IF_CASES_TAC >> asm_simp_tac bool_ss [] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >> (FIRST [MATCH_ACCEPT_TAC stmt_alloc_buffer_first_emission, stmt_ext_tac])
QED

Theorem stmt_first_emission_append[local]:
  lop <> PHI ==>
  !a x b. compile_dynarray_append ce base_op v ws es dt st cap prim lop sop a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  strip_tac >> simp_tac bool_ss [compile_dynarray_append_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `dst_loc = LocMemory` >>
  qpat_x_assum `Abbrev (dst_loc = _)` kall_tac >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- stmt_emit_tac >> stmt_ext_tac
QED

Theorem stmt_first_emission_range_checks[local]:
  !a x b. compile_range_bound_checks start_op end_op rounds bound signed a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_range_bound_checks_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (IF_CASES_TAC >> stmt_emit_tac) >> stmt_ext_tac
QED

Theorem stmt_first_emission_iter_copy[local]:
  !ce ep ip sz loc slots dt st a x b.
    compile_iter_elem_copy ce ep ip sz loc slots dt st a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 8 gen_tac >> Cases_on `loc` >>
  simp_tac bool_ss [compile_iter_elem_copy_def, data_location_case_def,
    compile_slot_to_memory_def] >>
  (IF_CASES_TAC
   >- (ho_match_mp_tac first_emission_strong >>
       ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
       >- MATCH_ACCEPT_TAC first_emission_word_copy_loop >> stmt_ext_tac) >>
   stmt_fe_with (first_emission_imm_copy :: stmt_weak_leaves))
QED

Theorem stmt_first_emission_internal_return_env[local]:
  !ce ty sty v pc a x b.
    compile_internal_return_from_env ce ty sty v pc a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 5 gen_tac >> simp_tac bool_ss [compile_internal_return_from_env_def] >>
  Cases_on `ce.ce_return_buf`
  >- (simp_tac bool_ss [optionTheory.option_case_def] >>
      stmt_fe_with [stmt_first_emission_internal_return]) >>
  Cases_on `x` >> simp_tac bool_ss [optionTheory.option_case_def, var_location_case_def] >>
  stmt_fe_with [stmt_first_emission_internal_return]
QED
Theorem stmt_comp_bind_return[local]:
  comp_bind (comp_return v) k = k v
Proof
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def]
QED

fun stmt_ci_step g =
  (FIRST [FIRST (map MATCH_ACCEPT_TAC stmt_ci_leaves),
    ho_match_mp_tac ci_mono_bind, ho_match_mp_tac ci_mono_ignore_bind,
    IF_CASES_TAC, BasicProvers.TOP_CASE_TAC] >>
   rpt conj_tac >> rpt gen_tac >> pure_rewrite_tac [LET_THM] >> BETA_TAC) g;


val stmt_all_leaves = [stmt_first_emission_assign, stmt_first_emission_store_at_loc,
  stmt_first_emission_tuple_unpack, stmt_first_emission_internal_return_env,
  stmt_first_emission_external_return, stmt_first_emission_log_eval,
  stmt_first_emission_log_topics, stmt_first_emission_reason,
  first_emission_imm_copy] @ stmt_weak_leaves;

Theorem first_emission_stmt_compilers:
  (!ce lc ty s a x b. compile_stmt ce lc ty s a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ce lc ty ss a x b. compile_stmts ce lc ty ss a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)))
Proof
  ho_match_mp_tac compile_stmt_ind >> rpt conj_tac
  >- suspend "pass" >- suspend "expr" >- suspend "ann"
  >- suspend "assign" >- suspend "aug"
  >- suspend "assert_bare" >- suspend "assert_unreachable"
  >- suspend "assert_reason" >- suspend "log"
  >- suspend "raise_bare" >- suspend "raise_unreachable" >- suspend "raise_reason"
  >- suspend "return_none" >- suspend "return_value" >- suspend "append"
  >- suspend "tuple_assign" >- suspend "if"
  >- suspend "range" >- suspend "for" >- suspend "break"
  >- suspend "continue" >- suspend "continue_no_loop"
  >- suspend "break_no_loop" >- suspend "assert_custom_error" >- suspend "raise_custom_error"
  >- suspend "nil" >> suspend "cons"
QED

Resume first_emission_stmt_compilers[pass]:
  ntac 3 gen_tac >> simp_tac bool_ss [compile_stmt_def] >> stmt_fe_tac
QED

Resume first_emission_stmt_compilers[expr]:
  ntac 4 gen_tac >> simp_tac bool_ss [compile_stmt_def] >> stmt_fe_tac
QED

Resume first_emission_stmt_compilers[ann]:
  ntac 6 gen_tac >> simp_tac bool_ss [compile_stmt_def, LET_THM] >>
  Cases_on `FLOOKUP ce.ce_vars id`
  >- (simp_tac bool_ss [optionTheory.option_case_def] >> stmt_fe_tac) >>
  Cases_on `x` >> simp_tac bool_ss [optionTheory.option_case_def, var_location_case_def] >>
  stmt_fe_with (stmt_first_emission_assign :: stmt_weak_leaves)
QED

Resume first_emission_stmt_compilers[assign]:
  ntac 5 gen_tac >> simp_tac bool_ss [compile_stmt_def, LET_THM] >>
  IF_CASES_TAC
  >- (asm_simp_tac bool_ss [] >> ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac first_emission_get_target_ptr >>
          MATCH_ACCEPT_TAC (cj 1 first_emission_expr_compilers)) >>
      gen_tac >> MATCH_ACCEPT_TAC stmt_first_emission_store_at_loc) >>
  asm_simp_tac bool_ss [] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- MATCH_ACCEPT_TAC (cj 1 first_emission_expr_compilers) >> gen_tac >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_get_target_ptr >>
      MATCH_ACCEPT_TAC (cj 1 first_emission_expr_compilers)) >>
  gen_tac >> stmt_fe_with stmt_all_leaves
QED

Resume first_emission_stmt_compilers[aug]:
  ntac 7 gen_tac >> simp_tac bool_ss [compile_stmt_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_get_target_ptr >>
      MATCH_ACCEPT_TAC (cj 1 first_emission_expr_compilers)) >>
  gen_tac >> simp_tac bool_ss [stmt_comp_bind_return] >>
  Cases_on `FST (SND tgt_result)`
  >- (simp_tac bool_ss [optionTheory.option_case_def] >> stmt_fe_tac) >>
  Cases_on `x` >> simp_tac bool_ss [optionTheory.option_case_def,
    data_location_case_def, stmt_comp_bind_return] >>
  (ho_match_mp_tac first_emission_strong >>
   ho_match_mp_tac first_emission_strong_bind >> conj_tac
   >- stmt_emit_tac >> stmt_ext_tac)
QED

Resume first_emission_stmt_compilers[assert_bare]:
  ntac 4 gen_tac >> simp_tac bool_ss [compile_stmt_def] >> stmt_fe_with stmt_all_leaves
QED

Resume first_emission_stmt_compilers[assert_unreachable]:
  ntac 4 gen_tac >> simp_tac bool_ss [compile_stmt_def] >> stmt_fe_with stmt_all_leaves
QED

Resume first_emission_stmt_compilers[assert_reason]:
  ntac 5 gen_tac >> simp_tac bool_ss [compile_stmt_def] >> stmt_fe_with stmt_all_leaves
QED

Resume first_emission_stmt_compilers[log]:
  ntac 5 gen_tac >> simp_tac bool_ss [compile_stmt_def, LET_THM] >>
  namedCases_on `ce.ce_event_info (nsid_to_string event_id)` ["", "info"]
  >- (simp_tac bool_ss [optionTheory.option_case_def] >> stmt_fe_tac) >>
  PairCases_on `info` >> simp_tac bool_ss [optionTheory.option_case_def] >>
  stmt_fe_with stmt_all_leaves
QED

Resume first_emission_stmt_compilers[raise_bare]:
  ntac 3 gen_tac >> simp_tac bool_ss [compile_stmt_def] >> stmt_fe_tac
QED

Resume first_emission_stmt_compilers[raise_unreachable]:
  ntac 3 gen_tac >> simp_tac bool_ss [compile_stmt_def] >> stmt_fe_tac
QED

Resume first_emission_stmt_compilers[raise_reason]:
  ntac 4 gen_tac >> simp_tac bool_ss [compile_stmt_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- MATCH_ACCEPT_TAC stmt_first_emission_reason >> gen_tac >>
  simp_tac bool_ss [compile_revert_with_reason_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- MATCH_ACCEPT_TAC stmt_alloc_buffer_first_emission >> stmt_ext_tac
QED

Resume first_emission_stmt_compilers[return_none]:
  ntac 3 gen_tac >> Cases_on `ce.ce_nonreentrant` >>
  rename1 `ce.ce_nonreentrant = (nr, nr_info)` >> PairCases_on `nr_info` >>
  asm_simp_tac bool_ss [compile_stmt_def, LET_THM, pairTheory.UNCURRY_DEF] >>
  Cases_on `ce.ce_return_pc`
  >- (simp_tac bool_ss [optionTheory.option_case_def, compile_nonreentrant_unlock_def] >>
      stmt_fe_tac) >>
  Cases_on `x` >> simp_tac bool_ss [optionTheory.option_case_def,
    var_location_case_def, compile_nonreentrant_unlock_def]
  >~ [`ce.ce_return_pc = SOME (MemLoc _ _)`] >- stmt_fe_tac
  >~ [`ce.ce_return_pc = SOME (PtrVar _ _)`] >- stmt_fe_tac
  >~ [`ce.ce_return_pc = SOME (StorageLoc _)`] >- stmt_fe_tac
  >~ [`ce.ce_return_pc = SOME (TransientLoc _)`] >- stmt_fe_tac
  >> stmt_fe_tac
QED

Resume first_emission_stmt_compilers[return_value]:
  ntac 4 gen_tac >> simp_tac bool_ss [compile_stmt_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- MATCH_ACCEPT_TAC stmt_first_emission_lower_value >> gen_tac >>
  Cases_on `ce.ce_return_pc`
  >- (simp_tac bool_ss [optionTheory.option_case_def] >> stmt_fe_with stmt_all_leaves) >>
  Cases_on `x` >> simp_tac bool_ss [optionTheory.option_case_def, var_location_case_def]
  >~ [`ce.ce_return_pc = SOME (MemLoc _ _)`] >- stmt_fe_with stmt_all_leaves
  >~ [`ce.ce_return_pc = SOME (PtrVar _ _)`] >- stmt_fe_with stmt_all_leaves
  >~ [`ce.ce_return_pc = SOME (StorageLoc _)`] >- stmt_fe_with stmt_all_leaves
  >~ [`ce.ce_return_pc = SOME (TransientLoc _)`] >- stmt_fe_with stmt_all_leaves
  >> stmt_fe_with stmt_all_leaves
QED

Resume first_emission_stmt_compilers[append]:
  ntac 5 gen_tac >> simp_tac bool_ss [compile_stmt_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- MATCH_ACCEPT_TAC stmt_first_emission_lower_value >> gen_tac >>
  simp_tac bool_ss [stmt_comp_bind_return] >>
  qmatch_goalsub_abbrev_tac `is_word_type ety` >>
  qpat_x_assum `Abbrev (ety = _)` kall_tac >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- stmt_fe_with stmt_all_leaves >> gen_tac >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac stmt_first_emission_append >>
  Cases_on `infer_array_location ce (target_to_expr target)` >> simp[load_opc_for_def]
QED

Resume first_emission_stmt_compilers[tuple_assign]:
  ntac 5 gen_tac >> simp_tac bool_ss [compile_stmt_def, LET_THM] >>
  stmt_fe_with stmt_all_leaves
QED

Resume first_emission_stmt_compilers[if]:
  ntac 6 gen_tac >> strip_tac >> simp_tac bool_ss [compile_stmt_def] >>
  stmt_fe_with stmt_all_leaves
QED

Resume first_emission_stmt_compilers[range]:
  ntac 9 gen_tac >> strip_tac >>
  qpat_x_assum `!is_signed. _` kall_tac >>
  simp_tac bool_ss [compile_stmt_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- MATCH_ACCEPT_TAC stmt_first_emission_lower_value >> gen_tac >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- MATCH_ACCEPT_TAC stmt_first_emission_lower_value >> gen_tac >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_no_code >> MATCH_ACCEPT_TAC stmt_declare_local_no_code) >>
  gen_tac >> ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- MATCH_ACCEPT_TAC stmt_first_emission_local_alloca >>
  ntac 5 (ho_match_mp_tac first_emission_bind >> conj_tac
    >- (ho_match_mp_tac first_emission_no_code >>
        MATCH_ACCEPT_TAC (cj 1 first_emission_counters)) >> gen_tac) >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- stmt_emit_tac >> suspend "range_suffix"
QED

Resume first_emission_stmt_compilers[range_suffix]:
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `tail initial_cs = (result,final_cs)` >>
  `cs_appends tail` suffices_by (simp[cs_appends_def] >> metis_tac[]) >>
  simp_tac bool_ss [Abbr `tail`] >>
  ho_match_mp_tac stmt_ci_mono_appends >> rpt gen_tac >>
  stmt_ci_step >> stmt_ci_step >> stmt_ci_step >> stmt_ci_step >>
  stmt_ci_step >> stmt_ci_step >> stmt_ci_step >> stmt_ci_step >>
  stmt_ci_step >> stmt_ci_step >> stmt_ci_step >> stmt_ci_step >>
  stmt_ci_step >> stmt_ci_step >> stmt_ci_step >> stmt_ci_step >>
  stmt_ci_step >> stmt_ci_step >> stmt_ci_step >> stmt_ci_step >>
  stmt_ci_step >> stmt_ci_step >> stmt_ci_step >> stmt_ci_step >>
  stmt_ci_step >> stmt_ci_step >> stmt_ci_step >> stmt_ci_step >>
  stmt_ci_step >> stmt_ci_step >> stmt_ci_step >> stmt_ci_step >>
  stmt_ci_step >> stmt_ci_step >> stmt_ci_step >> stmt_ci_step
QED

Resume first_emission_stmt_compilers[for]:
  ntac 8 gen_tac >> strip_tac >> first_x_assum kall_tac >>
  simp_tac bool_ss [compile_stmt_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- MATCH_ACCEPT_TAC (cj 1 first_emission_expr_compilers) >> gen_tac >>
  simp_tac bool_ss [stmt_comp_bind_return] >>
  qmatch_goalsub_abbrev_tac `if dyn then compile_ptr_load _ _ _ _ else _` >>
  qmatch_goalsub_abbrev_tac `Lit (n2w arr_count)` >>
  qmatch_goalsub_abbrev_tac `elem_size_in_location ce _ ety` >>
  map_every (fn p => qpat_x_assum p kall_tac)
    [`Abbrev (dyn = _)`, `Abbrev (arr_count = _)`, `Abbrev (ety = _)`] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- stmt_fe_with stmt_all_leaves >> gen_tac >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_no_code >> MATCH_ACCEPT_TAC stmt_declare_local_no_code) >>
  gen_tac >> ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- MATCH_ACCEPT_TAC stmt_first_emission_local_alloca >>
  ntac 5 (ho_match_mp_tac first_emission_bind >> conj_tac
    >- (ho_match_mp_tac first_emission_no_code >>
        MATCH_ACCEPT_TAC (cj 1 first_emission_counters)) >> gen_tac) >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- stmt_emit_tac >> stmt_ext_tac
QED

Resume first_emission_stmt_compilers[break]:
  ntac 4 gen_tac >> simp_tac bool_ss [compile_stmt_def] >> stmt_fe_tac
QED

Resume first_emission_stmt_compilers[continue]:
  ntac 4 gen_tac >> simp_tac bool_ss [compile_stmt_def] >> stmt_fe_tac
QED

Resume first_emission_stmt_compilers[continue_no_loop]:
  ntac 2 gen_tac >> simp_tac bool_ss [compile_stmt_def] >> stmt_fe_tac
QED

Resume first_emission_stmt_compilers[break_no_loop]:
  ntac 2 gen_tac >> simp_tac bool_ss [compile_stmt_def] >> stmt_fe_tac
QED

Resume first_emission_stmt_compilers[assert_custom_error]:
  ntac 5 gen_tac >> simp_tac bool_ss [compile_stmt_def] >> stmt_fe_tac
QED

Resume first_emission_stmt_compilers[raise_custom_error]:
  ntac 4 gen_tac >> simp_tac bool_ss [compile_stmt_def] >> stmt_fe_tac
QED

Resume first_emission_stmt_compilers[nil]:
  ntac 3 gen_tac >> simp_tac bool_ss [compile_stmt_def] >> stmt_fe_tac
QED

Resume first_emission_stmt_compilers[cons]:
  ntac 5 gen_tac >> strip_tac >>
  qpat_x_assum `!cs ce. _ ==> !a x b. compile_stmt _ _ _ _ _ = _ ==> _`
    (qspec_then `ARB with cs_current_insts := []`
      (assume_tac o SIMP_RULE bool_ss [block_is_terminated_def,
        compile_state_accfupds, combinTheory.K_THM, listTheory.list_case_def])) >>
  qpat_x_assum `!cs ce. _ ==> !a x b. compile_stmts _ _ _ _ _ = _ ==> _`
    (qspec_then `ARB with cs_current_insts := []`
      (assume_tac o SIMP_RULE bool_ss [block_is_terminated_def,
        compile_state_accfupds, combinTheory.K_THM, listTheory.list_case_def])) >>
  simp_tac bool_ss [compile_stmt_def] >> stmt_fe_with stmt_all_leaves
QED

Finalise first_emission_stmt_compilers
