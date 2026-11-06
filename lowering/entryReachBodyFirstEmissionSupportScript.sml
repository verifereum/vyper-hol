(* First-emission boundaries for declaration and value support. *)
Theory entryReachBodyFirstEmissionSupport
Ancestors
  compilerFirstEmission stmtLowering exprLowering context compileEnv fragExec
  emitHelper venomInst finite_map externalEntryShape

Theorem first_emission_declare_local:
  declare_local ce id ty a = (x,b) ==>
  cs_extends a b /\ a.cs_blocks = b.cs_blocks /\
  a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts
Proof
  simp[declare_local_def] >> IF_CASES_TAC >>
  simp[comp_bind_def, comp_return_def, fresh_var_def] >> strip_tac >> gvs[] >>
  irule cs_extends_same_block >> simp[]
QED

Theorem first_emission_declare_stmt_local:
  declare_stmt_local ce s a = (x,b) ==>
  cs_extends a b /\ a.cs_blocks = b.cs_blocks /\
  a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts
Proof
  Cases_on `s` >> simp[declare_stmt_local_def, first_emission_declare_local,
    comp_return_def, cs_extends_refl] >>
  metis_tac[first_emission_declare_local]
QED

Theorem first_emission_alloc_buffer:
  compile_alloc_buffer n a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  Cases_on `emit_op ALLOCA [Lit (n2w n)] a` >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >> gvs[] >>
  drule_at Any (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]
QED

Theorem first_emission_local_alloca:
  !ce id a x b. emit_local_alloca ce id a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> simp[emit_local_alloca_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[]
  >- metis_tac[first_emission_return] >>
  rename1 `FLOOKUP ce.ce_vars id = SOME loc` >>
  Cases_on `loc` >> simp[comp_return_def, cs_extends_refl] >>
  rename1 `PtrVar op sz` >> Cases_on `op` >>
  simp[comp_return_def, cs_extends_refl] >> strip_tac >>
  drule_at Any (CONJUNCT1 first_emission_emit_helpers) >> simp[]
QED

Theorem first_emission_ptr_load:
  !ctor imm loc op a x b. compile_ptr_load ctor imm loc op a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >> Cases_on `loc` >> simp[compile_ptr_load_def]
  >~ [`compile_imm_load_word ctor imm op a = (x,b)`]
  >- (simp[compile_imm_load_word_def] >> reverse (Cases_on `ctor`) >> simp[]
  >- (strip_tac >> drule_at Any (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
  Cases_on `imm` >> simp[]
  >- (strip_tac >> drule_at Any (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac >>
  rpt strip_tac >>
  drule_at Any (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
  strip_tac >>
  drule_at Any (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]
QED


Theorem total_extends_appends[local]:
  (!s. cs_extends s (SND (m s))) ==> cs_appends m
Proof
  rw[cs_appends_def] >> first_x_assum (qspec_then `st` mp_tac) >> simp[]
QED

Theorem support_memory_appends[local]:
  (!ptr buf wc. cs_appends (compile_storage_to_memory ptr buf wc)) /\
  (!ptr buf wc. cs_appends (compile_transient_to_memory ptr buf wc)) /\
  (!ctor imm src dst wc off.
    cs_appends (compile_imm_copy_to_memory ctor imm src dst wc off)) /\
  (!n. cs_appends (compile_alloc_buffer n))
Proof
  rpt conj_tac >> rpt gen_tac >> irule total_extends_appends >>
  simp[compile_storage_to_memory_labels, compile_transient_to_memory_labels,
    compile_imm_copy_to_memory_labels, compile_alloc_buffer_labels]
QED

Theorem first_emission_ensure_in_memory:
  !ptr loc bytes wc ctor imm a x b.
  compile_ensure_in_memory ptr loc bytes wc ctor imm a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> Cases_on `loc` >>
  simp_tac (srw_ss()) [compile_ensure_in_memory_def]
  >- (simp[comp_return_def] >> strip_tac >> gvs[cs_extends_refl]) >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >>
  (conj_tac
   >- (rpt strip_tac >>
       FIRST [drule first_emission_alloc_buffer,
         drule_at Any (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers))] >> simp[]) >>
   gen_tac >> simp[LET_THM, GSYM cs_appends_def, ETA_THM] >>
      Cases_on `wc = 1` >> simp[] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      rpt (rpt gen_tac >> FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
           rpt gen_tac >> BETA_TAC >>
           simp[cs_appends_emit_helpers, cs_appends_return, support_memory_appends]))
QED

Theorem first_emission_unwrap_value:
  !ce vv a x b. unwrap_value ce vv a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> Cases_on `vv` >> simp[unwrap_value_def]
  >- (simp[comp_return_def] >> strip_tac >> gvs[cs_extends_refl]) >>
  IF_CASES_TAC
  >- (strip_tac >> drule first_emission_ptr_load >> simp[]) >>
  Cases_on `p.ptr_location` >> simp[] >>
  metis_tac[first_emission_return, first_emission_ensure_in_memory]
QED

Theorem first_emission_lower_value:
  (!a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. lower_value cfn ce ty e a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rewrite_tac[lower_value_def] >>
  ho_match_mp_tac first_emission_bind >>
  simp[] >> metis_tac[first_emission_unwrap_value]
QED

Theorem first_emission_mapping_subscript:
  !slot key a x b. compile_mapping_subscript slot key a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >> rewrite_tac[compile_mapping_subscript_def] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[first_emission_alloc_buffer] >>
  gen_tac >> simp[LET_THM, GSYM cs_appends_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  rpt (rpt gen_tac >> FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
       rpt gen_tac >> BETA_TAC >> simp[cs_appends_emit_helpers])
QED

Theorem first_emission_keccak256_key:
  !key is32 a x b. compile_keccak256_key key is32 a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >> simp[compile_keccak256_key_def] >>
  Cases_on `is32` >> simp[] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong_bind >>
  (conj_tac
   >- (rpt strip_tac >> FIRST [drule first_emission_alloc_buffer,
       drule_at Any (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers))] >> simp[]) >>
   gen_tac >> simp[LET_THM, GSYM cs_appends_def] >>
   CONV_TAC (DEPTH_CONV ETA_CONV) >>
   rpt (rpt gen_tac >> FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
        rpt gen_tac >> BETA_TAC >> simp[cs_appends_emit_helpers]))
QED

Theorem first_emission_array_subscript:
  (!a x b. loader base_op a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)) ==>
  !a x b. compile_array_subscript base_op idx dyn static_count scale sz signed loader a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  strip_tac >> Cases_on `dyn`
  >- (simp_tac (srw_ss()) [compile_array_subscript_def] >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- first_assum ACCEPT_TAC >>
      gen_tac >> Cases_on `signed` >>
      simp[LET_THM, GSYM cs_appends_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
      rpt (rpt gen_tac >> FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
           rpt gen_tac >> BETA_TAC >> simp[cs_appends_emit_helpers, cs_appends_return])) >>
  simp_tac (srw_ss()) [compile_array_subscript_def] >>
  simp[Once comp_bind_def, comp_return_def] >> Cases_on `signed` >> simp[]
  >- (ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- (rpt strip_tac >>
          drule_at Any (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
      gen_tac >> simp[LET_THM, GSYM cs_appends_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
      rpt (rpt gen_tac >> FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
           rpt gen_tac >> BETA_TAC >> simp[cs_appends_emit_helpers, cs_appends_return])) >>
  simp[Once comp_bind_def, comp_return_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt strip_tac >>
      drule_at Any (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
  gen_tac >> simp[LET_THM, GSYM cs_appends_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  rpt (rpt gen_tac >> FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
       rpt gen_tac >> BETA_TAC >> simp[cs_appends_emit_helpers, cs_appends_return])
QED

Theorem first_emission_get_target_ptr:
  (!ce ty e a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !ce tgt a x b. compile_get_target_ptr cfn ce tgt a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> gen_tac >> gen_tac >>
  measureInduct_on `base_assignment_target_size tgt` >>
  Cases_on `tgt` >> simp_tac (srw_ss()) [compile_get_target_ptr_def]
  >- (rpt CASE_TAC >> metis_tac[first_emission_return])
  >- (rpt CASE_TAC >> metis_tac[first_emission_return])
  >- (ho_match_mp_tac first_emission_bind >> conj_tac
      >- (first_x_assum (qspec_then `b` mp_tac) >> simp[]) >>
      gen_tac >> rename1 `FST result` >> PairCases_on `result` >>
      Cases_on `result2` >>
      FIRST [rename1 `SOME desc` >> Cases_on `desc`, all_tac] >>
      simp_tac (srw_ss()) [LET_THM] >>
      ho_match_mp_tac first_emission_bind >>
      (conj_tac
       >- (ho_match_mp_tac first_emission_lower_value >> metis_tac[]) >>
       gen_tac)
      >~ [`compile_keccak256_key`]
      >- (ho_match_mp_tac first_emission_bind >> conj_tac
          >- (IF_CASES_TAC >> simp[] >> rpt strip_tac >>
              metis_tac[first_emission_return, first_emission_keccak256_key]) >>
          gen_tac >> ho_match_mp_tac first_emission_strong >>
          ho_match_mp_tac first_emission_strong_bind >> conj_tac
          >- metis_tac[first_emission_mapping_subscript] >>
          simp[comp_return_def, cs_extends_refl]) >>
      ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >>
      (conj_tac
       >- (ho_match_mp_tac first_emission_array_subscript >>
           metis_tac[first_emission_ptr_load]) >>
       simp[comp_return_def, cs_extends_refl])) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (first_x_assum (qspec_then `b` mp_tac) >> simp[]) >>
  gen_tac >> simp_tac (srw_ss()) [LET_THM] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any
       (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
  simp[comp_return_def, cs_extends_refl]
QED
