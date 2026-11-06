Theory entryReachBodyFirstEmissionExprSupport
Ancestors
  entryReachBodyFirstEmissionSupport compilerFirstEmission externalEntryShape
  exprLowering compileEnv fragExec emitHelper venomInst finite_map list

Theorem first_emission_bytelike_literal[local]:
  !bs n a x b. compile_bytelike_literal bs n a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [compile_bytelike_literal_def, LET_THM] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[first_emission_alloc_buffer] >>
  gen_tac >> simp[LET_THM, GSYM cs_appends_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule cs_appends_ignore_bind >> simp[cs_appends_emit_helpers] >>
  irule cs_appends_ignore_bind >> simp[cs_appends_return] >>
  rw[cs_appends_def] >>
  qspecl_then [`buf_alloc.buf_operand`, `bs`, `32`, `st`] mp_tac
    (cj 1 compile_store_byte_chunks_labels) >> simp[]
QED

Theorem first_emission_name_vv:
  !ce ty id a x b. compile_name_vv ce ty id a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> simp[compile_name_vv_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[]
  >- (map_every qid_spec_tac [`b`, `x`, `a`] >>
      ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
      >- (rpt strip_tac >> drule_at Any
           (CONJUNCT1 first_emission_emit_helpers) >> simp[]) >>
      simp[comp_return_def, cs_extends_refl]) >>
  rename1 `SOME loc` >> Cases_on `loc` >>
  simp[comp_return_def, cs_extends_refl] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_ignore_bind >>
  (conj_tac
   >- (rpt strip_tac >> drule_at Any
        (CONJUNCT1 first_emission_emit_helpers) >> simp[]) >>
   simp[comp_return_def, cs_extends_refl])
QED

Theorem first_emission_literal_vv:
  !ty lit a x b. compile_literal_vv ty lit a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> Cases_on `lit` >>
  simp[compile_literal_vv_def, comp_return_def, cs_extends_refl]
  >- (Cases_on `b'` >> simp[compile_literal_vv_def, comp_return_def, cs_extends_refl])
  >- (Cases_on `ty` >> simp[] >>
      map_every qid_spec_tac [`b`, `x`, `a`] >>
      ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >>
      (conj_tac
       >- metis_tac[first_emission_bytelike_literal] >>
       simp[comp_return_def, cs_extends_refl])) >>
  Cases_on `ty` >> simp[comp_return_def, cs_extends_refl] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[comp_return_def, cs_extends_refl] >> rename1 `BytesT bound` >>
  Cases_on `bound` >> simp[comp_return_def, cs_extends_refl] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[first_emission_bytelike_literal] >>
  simp[comp_return_def, cs_extends_refl]
QED

Theorem first_emission_as_stack_val:
  (!a v b. m a = (v,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. as_stack_val ty (m a) = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `m a` >>
  simp[as_stack_val_def] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem first_emission_mod_names:
  (!ce ty aty an bty bn mty mn a x b.
  compile_addmod_names ce ty aty an bty bn mty mn a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
  ) /\
  (!ce ty aty an bty bn mty mn a x b.
  compile_mulmod_names ce ty aty an bty bn mty mn a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)))
Proof
  conj_tac >> rpt gen_tac >>
  rewrite_tac[compile_addmod_names_def, compile_mulmod_names_def, LET_THM] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ntac 6 (ho_match_mp_tac first_emission_pair_let >> conj_tac
    >- metis_tac[first_emission_name_vv, first_emission_unwrap_value] >>
    gen_tac) >>
  ho_match_mp_tac first_emission_as_stack_val >>
  rewrite_tac[builtinMathTheory.compile_addmod_def, builtinMathTheory.compile_mulmod_def] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_ignore_bind >>
  (conj_tac
   >- (rpt strip_tac >> drule_at Any
        (CONJUNCT1 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
   rpt strip_tac >> drule_at Any
     (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[])
QED

Theorem first_emission_powmod256_names:
  !ce ty aty an bty bn a x b.
  compile_powmod256_names ce ty aty an bty bn a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> rewrite_tac[compile_powmod256_names_def, LET_THM] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ntac 4 (ho_match_mp_tac first_emission_pair_let >> conj_tac
    >- metis_tac[first_emission_name_vv, first_emission_unwrap_value] >>
    gen_tac) >>
  ho_match_mp_tac first_emission_as_stack_val >>
  rewrite_tac[builtinMathTheory.compile_pow_mod256_def] >>
  rpt strip_tac >> drule_at Any
    (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]
QED

Theorem first_emission_attribute:
  (!a x b. cfn ce ty base_e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_attribute cfn ce rt ty base_e fld a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rewrite_tac[compile_attribute_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- first_assum ACCEPT_TAC >>
  gen_tac >> simp_tac (srw_ss()) [LET_THM] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any
       (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
  simp[comp_return_def, cs_extends_refl]
QED

Theorem first_emission_subscript:
  (!ce ty e a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_subscript cfn ce rt ty base_e idx_e a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rewrite_tac[compile_subscript_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[] >>
  gen_tac >> Cases_on `place_type ce base_e` >>
  FIRST [rename1 `ValPT bt` >> Cases_on `bt`, all_tac] >>
  simp_tac (srw_ss()) [LET_THM, compile_tuple_subscript_def]
  >>~- ([`emit_op ADD`],
    ho_match_mp_tac first_emission_strong >>
    ho_match_mp_tac first_emission_strong_bind >> conj_tac
    >- (rpt strip_tac >> drule_at Any
         (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
    simp[comp_return_def, cs_extends_refl]) >>
  (ho_match_mp_tac first_emission_bind >>
   (conj_tac
    >- (ho_match_mp_tac first_emission_lower_value >> metis_tac[]) >>
    gen_tac))
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
   simp[comp_return_def, cs_extends_refl])
QED

Theorem first_emission_multi_vvs:
  !es ce.
  (!e a x b. MEM e es /\ cfn ce (expr_type e) e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_multi_vvs cfn ce es a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Induct_on `es`
  >- simp[compile_multi_vvs_def, comp_return_def, cs_extends_refl] >>
  rpt gen_tac >> strip_tac >> rewrite_tac[compile_multi_vvs_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[MEM] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (first_x_assum ho_match_mp_tac >> metis_tac[MEM]) >>
  metis_tac[first_emission_return]
QED
