(* First emissions of context operations precede their later control flow. *)
Theory contextFirstEmission
Ancestors
  entryConditionalFirstEmission compilerFirstEmission context contextProps
  fragExec compileEnv emitHelper venomInst

Theorem first_emission_imm_load:
  !a x b. compile_imm_load_word is_ctor imm off a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  Cases_on `is_ctor`
  >- (Cases_on `imm` >> simp_tac (srw_ss()) [compile_imm_load_word_def]
      >- (rpt gen_tac >> strip_tac >>
          drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac >>
      rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
  simp_tac (srw_ss()) [compile_imm_load_word_def] >> rpt gen_tac >> strip_tac >>
  drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]
QED

Theorem first_emission_imm_store:
  !a x b. compile_imm_store_word imm off v a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  Cases_on `imm` >> simp_tac bool_ss [compile_imm_store_word_def, optionTheory.option_case_def]
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 2 first_emission_emit_helpers) >> simp[]) >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pos (el 2)) (cj 2 first_emission_emit_helpers) >> simp[]
QED

Theorem first_emission_ptr_load:
  !a x b. compile_ptr_load is_ctor imm loc op a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  Cases_on `loc` >> simp_tac (srw_ss()) [compile_ptr_load_def]
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[])
  >- metis_tac[first_emission_imm_load] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]
QED

Theorem first_emission_ptr_store:
  !a x b. compile_ptr_store is_ctor imm loc dst v a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  Cases_on `loc` >> simp_tac bool_ss [compile_ptr_store_def]
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 2 first_emission_emit_helpers) >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 2 first_emission_emit_helpers) >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 2 first_emission_emit_helpers) >> simp[])
  >- (Cases_on `is_ctor` >> simp_tac bool_ss []
      >- metis_tac[first_emission_imm_store] >>
      rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 2 first_emission_emit_helpers) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pos (el 2)) (cj 2 first_emission_emit_helpers) >> simp[]
QED

Theorem first_emission_copy_memory:
  !a x b. compile_copy_memory dst src nbytes a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Cases_on `nbytes` >> simp_tac bool_ss [compile_copy_memory_def]
  >- metis_tac[first_emission_return] >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
  drule_at (Pos (el 2)) (cj 2 first_emission_emit_helpers) >> simp[]
QED

Theorem context_ptr_appends[local]:
  cs_appends (compile_ptr_load ctor imm loc addr) /\
  cs_appends (compile_ptr_store ctor imm loc addr v)
Proof
  simp[cs_appends_def] >> metis_tac[first_emission_ptr_load, first_emission_ptr_store]
QED

val context_append_simps =
  [cs_appends_prims, cs_appends_emit_helpers, cs_appends_return,
   context_ptr_appends, LET_THM];

fun context_append_tac g =
  (FIRST [FIRST_PROVE [simp_tac (srw_ss()) context_append_simps],
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- context_append_tac >> rpt gen_tac >> context_append_tac,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> context_append_tac,
    IF_CASES_TAC >> context_append_tac]) g;

Theorem first_emission_word_copy_loop:
  !a x b. compile_word_copy_loop src dst nw ll sl ctor a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_word_copy_loop_def, LET_THM] >>
  ho_match_mp_tac entry_first_emission_then_strong >> conj_tac
  >- (ho_match_mp_tac first_emission_no_code >> metis_tac[first_emission_counters]) >>
  gen_tac >> ho_match_mp_tac entry_first_emission_then_strong >> conj_tac
  >- (ho_match_mp_tac first_emission_no_code >> metis_tac[first_emission_counters]) >>
  gen_tac >> ho_match_mp_tac entry_first_emission_then_strong >> conj_tac
  >- (ho_match_mp_tac first_emission_no_code >> metis_tac[first_emission_counters]) >>
  gen_tac >> ho_match_mp_tac entry_first_emission_then_strong >> conj_tac
  >- (ho_match_mp_tac first_emission_no_code >> metis_tac[first_emission_fresh]) >>
  gen_tac >> ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 1 first_emission_emit_helpers) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
  `cs_appends tail` by (simp_tac bool_ss [Abbr `tail`] >> context_append_tac) >>
  fs[cs_appends_def]
QED

Theorem first_emission_byte_offset:
  !a x b. compile_with_byte_offset op off a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rewrite_tac[compile_with_byte_offset_def] >> IF_CASES_TAC
  >- metis_tac[first_emission_return] >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
  drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]
QED

Theorem first_emission_bytestring_length:
  !a x b. compile_bytestring_copy_len src a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_bytestring_copy_len_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
  `cs_appends tail` by (simp_tac bool_ss [Abbr `tail`] >> context_append_tac) >>
  fs[cs_appends_def]
QED

Theorem first_emission_store_bytestring:
  !a x b. compile_store_bytestring src dst a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rewrite_tac[compile_store_bytestring_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[first_emission_bytestring_length] >>
  metis_tac[cs_appends_emit_helpers, cs_appends_def]
QED

Theorem context_copy_appends[local]:
  cs_appends (compile_copy_memory dst src nbytes) /\
  cs_appends (compile_with_byte_offset op off) /\
  cs_appends (compile_store_bytestring src dst) /\
  cs_appends (compile_copy_memory_dynamic dst src len)
Proof
  rpt conj_tac
  >- (simp[cs_appends_def] >> metis_tac[first_emission_copy_memory])
  >- (simp[cs_appends_def] >> metis_tac[first_emission_byte_offset])
  >- (simp[cs_appends_def] >> metis_tac[first_emission_store_bytestring]) >>
  simp[compile_copy_memory_dynamic_def, cs_appends_emit_helpers]
QED

fun typed_append_tac g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss())
      (context_copy_appends :: context_append_simps)],
    first_assum (fn th => FIRST_PROVE [irule (SRULE [] th) >> simp[]]),
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- typed_append_tac >> rpt gen_tac >> typed_append_tac,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> typed_append_tac,
    IF_CASES_TAC >> gvs[] >> typed_append_tac]) g;

Theorem cs_appends_context_typed_copy:
  (!ce dst dt src st. cs_appends (compile_store_memory_typed ce dst dt src st)) /\
  (!ce dst src dt st doff soff.
    cs_appends (compile_typed_copy_fields ce dst src dt st doff soff)) /\
  (!ce dst dt src st nw. cs_appends (compile_copy_sarray_typed ce dst dt src st nw)) /\
  (!ce dst dt cap src st. cs_appends (compile_copy_dynarray_typed ce dst dt cap src st)) /\
  (!ce dst src df sf doff soff.
    cs_appends (compile_struct_typed_copy ce dst src df sf doff soff))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- simp[Once compile_store_memory_typed_def, cs_appends_return]
  >- simp[Once compile_store_memory_typed_def, cs_appends_return]
  >- suspend "fields"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- simp[Once compile_store_memory_typed_def, cs_appends_return]
  >> suspend "struct"
QED

Resume cs_appends_context_typed_copy[fields]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp_tac pure_ss [Once compile_store_memory_typed_def, LET_THM] >>
  BETA_TAC >> typed_append_tac
QED
Resume cs_appends_context_typed_copy[sarray]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp_tac pure_ss [Once compile_store_memory_typed_def, LET_THM] >>
  BETA_TAC >> typed_append_tac
QED
Resume cs_appends_context_typed_copy[dynarray]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp_tac pure_ss [Once compile_store_memory_typed_def, LET_THM] >>
  BETA_TAC >> typed_append_tac
QED
Resume cs_appends_context_typed_copy[struct]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp_tac pure_ss [Once compile_store_memory_typed_def, LET_THM] >>
  pairarg_tac >> gvs[] >> typed_append_tac
QED

Resume cs_appends_context_typed_copy[dispatch]:
  rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dt`
  >- (simp_tac bool_ss [Once compile_store_memory_typed_def] >> typed_append_tac) >>
  Cases_on `is_bytestring_type dt /\ is_bytestring_type st`
  >- simp[Once compile_store_memory_typed_def, context_copy_appends] >>
  Cases_on `acyclic_struct_metadata ce.ce_struct_fields`
  >- (Cases_on `dt` >> Cases_on `st` >>
      TRY (rename1 `compile_store_memory_typed ce dst (ArrayT de db) src (ArrayT se sb)` >>
           Cases_on `db` >> Cases_on `sb`) >> gvs[] >>
      simp[Once compile_store_memory_typed_def, LET_THM, context_copy_appends] >>
      metis_tac[]) >>
  simp[Once compile_store_memory_typed_def, cs_appends_emit_helpers]
QED

Finalise cs_appends_context_typed_copy

val context_fe_leaves =
  [first_emission_copy_memory, first_emission_byte_offset];

fun context_fe_leaf g =
  (FIRST [FIRST (map MATCH_ACCEPT_TAC context_fe_leaves),
    ho_match_mp_tac first_emission_no_code >>
      FIRST (map MATCH_ACCEPT_TAC
        [first_emission_return, first_emission_fresh,
         cj 1 first_emission_counters, cj 2 first_emission_counters]),
    ho_match_mp_tac first_emission_strong >>
      MATCH_ACCEPT_TAC first_emission_store_bytestring]) g;
fun context_tail_append_tac g =
  (FIRST [FIRST_PROVE [simp_tac (srw_ss())
      (cs_appends_context_typed_copy :: context_copy_appends :: context_append_simps)],
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- context_tail_append_tac >> rpt gen_tac >> context_tail_append_tac,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> context_tail_append_tac,
    IF_CASES_TAC >> context_tail_append_tac]) g;

fun context_ext_tac g =
  (rpt gen_tac >> strip_tac >>
   qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
   `cs_appends tail` by
     (simp_tac bool_ss [Abbr `tail`] >>
      context_tail_append_tac) >>
   fs[cs_appends_def]) g;

fun context_fe_tac g =
  (FIRST [context_fe_leaf,
    FIRST_PROVE [asm_simp_tac (srw_ss()) []],
    first_assum (fn th => FIRST_PROVE [MATCH_ACCEPT_TAC (SRULE [] th)]),
    ho_match_mp_tac first_emission_strong >>
      rpt gen_tac >> strip_tac >>
      FIRST (map (fn th => drule_at (Pos (el 2)) th >> simp[])
        [cj 1 first_emission_emit_helpers, cj 2 first_emission_emit_helpers,
         cj 3 first_emission_emit_helpers]),
    ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- (rpt gen_tac >> strip_tac >>
          FIRST (map (fn th => drule_at (Pos (el 2)) th >> simp[])
            [cj 1 first_emission_emit_helpers, cj 2 first_emission_emit_helpers,
             cj 3 first_emission_emit_helpers])) >> context_ext_tac,
    ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
      >- (rpt gen_tac >> strip_tac >>
          FIRST (map (fn th => drule_at (Pos (el 2)) th >> simp[])
            [cj 1 first_emission_emit_helpers, cj 2 first_emission_emit_helpers,
             cj 3 first_emission_emit_helpers])) >> context_ext_tac,
    ho_match_mp_tac first_emission_bind >> conj_tac
      >- context_fe_tac >> gen_tac >> context_fe_tac,
    ho_match_mp_tac first_emission_ignore_bind >> conj_tac >> context_fe_tac,
    IF_CASES_TAC >> rule_assum_tac (SRULE []) >>
      simp_tac bool_ss [] >> context_fe_tac]) g;

Theorem first_emission_context_typed_copy:
  (!ce dst dt src st a x b.
    compile_store_memory_typed ce dst dt src st a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ce dst src dt st doff soff a x b.
    compile_typed_copy_fields ce dst src dt st doff soff a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ce dst dt src st nw a x b.
    compile_copy_sarray_typed ce dst dt src st nw a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ce dst dt cap src st a x b.
    compile_copy_dynarray_typed ce dst dt cap src st a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ce dst src df sf doff soff a x b.
    compile_struct_typed_copy ce dst src df sf doff soff a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- (simp_tac bool_ss [Once compile_store_memory_typed_def] >> context_fe_tac)
  >- (simp_tac bool_ss [Once compile_store_memory_typed_def] >> context_fe_tac)
  >- suspend "fields"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- (simp_tac bool_ss [Once compile_store_memory_typed_def] >> context_fe_tac)
  >> suspend "struct"
QED

Resume first_emission_context_typed_copy[fields]:
  rpt gen_tac >> strip_tac >> rule_assum_tac (SRULE []) >>
  simp_tac pure_ss [Once compile_store_memory_typed_def, LET_THM] >>
  BETA_TAC >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_byte_offset >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_byte_offset >>
  gen_tac >> ho_match_mp_tac first_emission_ignore_bind >> conj_tac >>
  simp_tac (srw_ss()) [] >> metis_tac[]
QED
Resume first_emission_context_typed_copy[sarray]:
  rpt gen_tac >> strip_tac >> rule_assum_tac (SRULE []) >>
  simp_tac pure_ss [Once compile_store_memory_typed_def, LET_THM] >>
  BETA_TAC >> context_fe_tac
QED
Resume first_emission_context_typed_copy[dynarray]:
  rpt gen_tac >> strip_tac >> rule_assum_tac (SRULE []) >>
  simp_tac pure_ss [Once compile_store_memory_typed_def, LET_THM] >>
  BETA_TAC >> context_fe_tac
QED
Resume first_emission_context_typed_copy[struct]:
  rpt gen_tac >> strip_tac >> rule_assum_tac (SRULE []) >>
  simp_tac pure_ss [Once compile_store_memory_typed_def, LET_THM] >>
  pairarg_tac >> rule_assum_tac (SRULE []) >>
  asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF, pairTheory.FST, pairTheory.SND] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_byte_offset >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_byte_offset >>
  gen_tac >> ho_match_mp_tac first_emission_ignore_bind >> conj_tac >>
  simp_tac (srw_ss()) [] >> metis_tac[]
QED
Resume first_emission_context_typed_copy[dispatch]:
  rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dt`
  >- (rule_assum_tac (SRULE []) >>
      asm_simp_tac bool_ss [Once compile_store_memory_typed_def] >> context_fe_tac) >>
  Cases_on `is_bytestring_type dt /\ is_bytestring_type st`
  >- (asm_simp_tac bool_ss [Once compile_store_memory_typed_def] >> context_fe_tac) >>
  Cases_on `acyclic_struct_metadata ce.ce_struct_fields`
  >- (Cases_on `dt` >> Cases_on `st` >>
      TRY (rename1 `compile_store_memory_typed ce dst (ArrayT de db) src (ArrayT se sb)` >>
           Cases_on `db` >> Cases_on `sb`) >> gvs[] >>
      simp[Once compile_store_memory_typed_def, LET_THM] >>
      metis_tac[first_emission_copy_memory]) >>
  asm_simp_tac bool_ss [Once compile_store_memory_typed_def] >> context_fe_tac
QED

Finalise first_emission_context_typed_copy
