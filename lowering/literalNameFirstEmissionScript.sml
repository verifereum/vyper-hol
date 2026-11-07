(* Literal/name entry prefixes and their named modular fast paths. *)
Theory literalNameFirstEmission
Ancestors
  compilerFirstEmission exprValueFirstEmission builtinScalarFirstEmission
  abiDecoderAppend exprLowering fragExec compileEnv emitHelper venomInst context

Theorem literal_store_chunks_appends[local]:
  !ptr bs off. cs_appends (compile_store_byte_chunks ptr bs off)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt strip_tac >>
  once_rewrite_tac[compile_store_byte_chunks_def] >>
  simp_tac (srw_ss()) [cs_appends_return, LET_THM] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >> gen_tac >>
  ho_match_mp_tac cs_appends_ignore_bind >>
  simp[cs_appends_emit_helpers] >>
  gvs[]
QED

Theorem literal_bytelike_first_emission[local]:
  !a x b. compile_bytelike_literal bs n a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_bytelike_literal_def, compile_alloc_buffer_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- (rpt gen_tac >> strip_tac >>
          drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
      simp[comp_return_def, cs_extends_refl]) >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `tail st0 = (y,c)` >>
  `cs_appends tail` by
    (simp_tac bool_ss [Abbr `tail`, LET_THM] >>
     ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
     >- simp[cs_appends_emit_helpers] >>
     ho_match_mp_tac cs_appends_ignore_bind >>
     simp[cs_appends_return, literal_store_chunks_appends]) >>
  fs[cs_appends_def]
QED

Theorem first_emission_name_vv:
  !a x b. compile_name_vv ce ty id a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Cases_on `FLOOKUP ce.ce_vars id` >> asm_simp_tac (srw_ss()) [compile_name_vv_def]
  >- (ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
      >- (rpt gen_tac >> strip_tac >>
          drule_at (Pos (el 2)) (cj 1 first_emission_emit_helpers) >> simp[]) >>
      simp[cs_extends_refl, comp_return_def]) >>
  rename1 `FLOOKUP _ _ = SOME loc` >>
  Cases_on `loc` >> simp_tac (srw_ss()) [] >>
  FIRST [simp[comp_return_def, cs_extends_refl] >> NO_TAC,
    ho_match_mp_tac first_emission_strong >>
    ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
    >- (rpt gen_tac >> strip_tac >>
        drule_at (Pos (el 2)) (cj 1 first_emission_emit_helpers) >> simp[]) >>
    simp[cs_extends_refl, comp_return_def]]
QED

Theorem first_emission_literal_vv:
  !a x b. compile_literal_vv ty lit a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Cases_on `lit`
  >~ [`compile_literal_vv _ (BoolL flag)`]
  >- (Cases_on `flag` >>
      simp[compile_literal_vv_def, comp_return_def, cs_extends_refl])
  >~ [`compile_literal_vv _ (IntL _)`]
  >- simp[compile_literal_vv_def, comp_return_def, cs_extends_refl]
  >~ [`compile_literal_vv _ (DecimalL _)`]
  >- simp[compile_literal_vv_def, comp_return_def, cs_extends_refl] >>
  simp_tac (srw_ss()) [compile_literal_vv_def] >>
  Cases_on `ty` >> simp_tac (srw_ss()) [] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >> simp_tac (srw_ss()) []) >>
  TRY (rename1 `BytesT sz` >> Cases_on `sz` >> simp_tac (srw_ss()) []) >>
  FIRST [simp[comp_return_def, cs_extends_refl] >> NO_TAC,
    ho_match_mp_tac first_emission_strong >>
    ho_match_mp_tac first_emission_strong_bind >> conj_tac
    >- MATCH_ACCEPT_TAC literal_bytelike_first_emission >>
    simp[comp_return_def, cs_extends_refl]]
QED

Theorem first_emission_addmod_names:
  !s x t. compile_addmod_names ce rt at an bt bn mt mn s = (x,t) ==>
    cs_extends s t /\
    ((s.cs_blocks = t.cs_blocks /\ s.cs_current_bb = t.cs_current_bb /\
      s.cs_current_insts = t.cs_current_insts) \/
     (!fn. fn_has_code s t fn ==>
       ?bb i. lookup_block s.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (s.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  simp_tac bool_ss [compile_addmod_names_def, LET_THM] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_name_vv >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_unwrap_value >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_name_vv >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_unwrap_value >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_name_vv >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_unwrap_value >>
  gen_tac >> rpt gen_tac >>
  simp_tac bool_ss [oneline as_stack_val_def] >>
  Cases_on `compile_addmod va vb vm st6` >>
  simp_tac (srw_ss()) [] >> strip_tac >> gvs[] >>
  drule first_emission_addmod >> simp[]
QED

Theorem first_emission_mulmod_names:
  !s x t. compile_mulmod_names ce rt at an bt bn mt mn s = (x,t) ==>
    cs_extends s t /\
    ((s.cs_blocks = t.cs_blocks /\ s.cs_current_bb = t.cs_current_bb /\
      s.cs_current_insts = t.cs_current_insts) \/
     (!fn. fn_has_code s t fn ==>
       ?bb i. lookup_block s.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (s.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  simp_tac bool_ss [compile_mulmod_names_def, LET_THM] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_name_vv >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_unwrap_value >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_name_vv >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_unwrap_value >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_name_vv >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_unwrap_value >>
  gen_tac >> rpt gen_tac >>
  simp_tac bool_ss [oneline as_stack_val_def] >>
  Cases_on `compile_mulmod va vb vm st6` >>
  simp_tac (srw_ss()) [] >> strip_tac >> gvs[] >>
  drule first_emission_mulmod >> simp[]
QED

Theorem first_emission_powmod256_names:
  !s x t. compile_powmod256_names ce rt at an bt bn s = (x,t) ==>
    cs_extends s t /\
    ((s.cs_blocks = t.cs_blocks /\ s.cs_current_bb = t.cs_current_bb /\
      s.cs_current_insts = t.cs_current_insts) \/
     (!fn. fn_has_code s t fn ==>
       ?bb i. lookup_block s.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (s.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  simp_tac bool_ss [compile_powmod256_names_def, LET_THM] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_name_vv >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_unwrap_value >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_name_vv >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_unwrap_value >>
  gen_tac >> rpt gen_tac >>
  simp_tac bool_ss [oneline as_stack_val_def] >>
  Cases_on `compile_pow_mod256 va vb st4` >>
  simp_tac (srw_ss()) [] >> strip_tac >> gvs[] >>
  drule first_emission_pow_mod256 >> simp[]
QED
