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

Theorem first_emission_stage_intcall_args:
  !ce vals flags tys a x b.
  compile_stage_intcall_args ce vals flags tys a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ho_match_mp_tac compile_stage_intcall_args_ind >> rpt conj_tac
  >- simp[compile_stage_intcall_args_def, comp_return_def, cs_extends_refl] >>
  rpt gen_tac >> disch_tac >>
  once_rewrite_tac[compile_stage_intcall_args_def] >> simp_tac (srw_ss()) [LET_THM] >>
  ho_match_mp_tac first_emission_bind >>
  (conj_tac >- metis_tac[first_emission_unwrap_value] >> gen_tac)
  >~ [`compile_alloc_buffer`]
  >- (ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- metis_tac[first_emission_alloc_buffer] >>
      gen_tac >> simp[LET_THM, GSYM cs_appends_def] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule cs_appends_ignore_bind >> conj_tac
      >- (IF_CASES_TAC >> simp[cs_appends_emit_helpers] >>
          IF_CASES_TAC
          >- (irule cs_appends_ignore_bind >> simp[cs_appends_return] >>
              rw[cs_appends_def] >>
              qspecl_then [`val_op`, `buf_alloc.buf_operand`, `st`] mp_tac
                (cj 1 compile_store_bytestring_labels) >> simp[]) >>
          rw[cs_appends_def] >>
          qspecl_then [`ce`, `val_op`, `buf_alloc.buf_operand`, `ty`, `vv_type vv`, `st`]
            mp_tac (cj 1 compile_store_memory_labels) >> simp[]) >>
      irule cs_appends_bind >> simp[cs_appends_return] >>
      rw[cs_appends_def] >>
      qspecl_then [`ce`, `vals`, `flags`, `tys`, `st`] mp_tac
        (cj 1 compile_stage_intcall_args_labels) >> simp[]) >>
  ho_match_mp_tac first_emission_bind >>
  (conj_tac >- metis_tac[] >> metis_tac[first_emission_return])
QED

Theorem first_emission_materialize_vv[local]:
  !ce ty vv a x b. compile_materialize_vv ce ty vv a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >> rewrite_tac[compile_materialize_vv_def] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[first_emission_alloc_buffer] >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  irule cs_appends_bind >> reverse conj_tac
  >- (rw[cs_appends_def] >>
      qspecl_then [`ce`, `vv`, `st`] mp_tac (cj 1 unwrap_value_labels) >> simp[]) >>
  gen_tac >> BETA_TAC >> irule cs_appends_ignore_bind >> simp[cs_appends_return] >>
  rw[cs_appends_def] >>
  qspecl_then [`ce`, `a`, `tmp.buf_operand`, `ty`, `ty`, `st`]
    mp_tac (cj 1 compile_store_memory_labels) >> simp[]
QED

Theorem first_emission_ext_call_kwarg:
  (!ce ty e a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_ext_call_kwarg cfn ce rt k e a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rewrite_tac[compile_ext_call_kwarg_def] >>
  IF_CASES_TAC >> simp_tac (srw_ss()) [LET_THM] >>
  ho_match_mp_tac first_emission_bind
  >- (conj_tac >- metis_tac[] >> gen_tac >>
      ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- metis_tac[first_emission_materialize_vv] >>
      simp[comp_return_def, cs_extends_refl]) >>
  conj_tac
  >- (ho_match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  metis_tac[first_emission_return]
QED

Theorem first_emission_ext_call_kwargs:
  (!ce ty e a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !ks es ce rt a x b. compile_ext_call_kwargs cfn ce rt ks es a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> Induct_on `ks` >> Cases_on `es` >> rpt gen_tac >>
  once_rewrite_tac[compile_ext_call_kwargs_def] >>
  simp_tac (srw_ss()) [comp_return_def, cs_extends_refl] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_ext_call_kwarg >> metis_tac[]) >>
  gen_tac >> PairCases_on `x` >> simp_tac (srw_ss()) [] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[] >>
  gen_tac >> PairCases_on `x` >> simp_tac (srw_ss()) [] >>
  metis_tac[first_emission_return]
QED

Theorem first_emission_fresh_vars[local]:
  !n a x b. fresh_vars n a = (x,b) ==>
  cs_extends a b /\ a.cs_blocks = b.cs_blocks /\
  a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts
Proof
  Induct_on `n` >> simp[fresh_vars_def, comp_return_def, cs_extends_refl] >>
  rpt gen_tac >> simp[comp_bind_def, LET_THM] >>
  Cases_on `fresh_var a` >> simp[] >>
  rename1 `fresh_var a = (v,mid)` >>
  Cases_on `fresh_vars n mid` >> simp[] >> strip_tac >> gvs[] >>
  drule first_emission_fresh >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[comp_return_def] >>
  metis_tac[cs_extends_trans]
QED

Theorem first_emission_emit_multi_op[local]:
  !opc ops n a x b. emit_multi_op opc ops n a = (x,b) /\ opc <> PHI ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >> rewrite_tac[emit_multi_op_def, comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `fresh_vars n a` >> simp[LET_THM] >>
  rename1 `fresh_vars n a = (outs,mid)` >>
  Cases_on `emit_inst opc ops outs mid` >> simp[LET_THM, comp_return_def] >>
  strip_tac >> gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  drule first_emission_fresh_vars >> strip_tac >>
  drule_at Any (CONJUNCT1 first_emission_emit_helpers) >> simp[] >>
  disch_then drule >> strip_tac >> conj_tac >- metis_tac[cs_extends_trans] >>
  gvs[] >> rpt strip_tac >> drule_all fn_has_code_split >>
  strip_tac >> metis_tac[]
QED

Theorem first_emission_intcall:
  (!ce ty e a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !ce rt ty fid args dr a x b.
  compile_call cfn ce rt ty (IntCall fid) args dr a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `ce.ce_func_info (nsid_to_string fid)` >>
  rename1 `ce.ce_func_info _ = (n,p)` >> PairCases_on `p` >>
  simp[Once compile_call_def, LET_THM] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_multi_vvs >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (Cases_on `n > 0` >> simp[]
      >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
          >- metis_tac[first_emission_alloc_buffer] >>
          simp[cs_extends_refl]) >>
      Cases_on `p0 > 0` >> simp[cs_extends_refl] >>
      ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- metis_tac[first_emission_alloc_buffer] >> simp[cs_extends_refl]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- metis_tac[first_emission_stage_intcall_args] >>
  gen_tac >> Cases_on `n > 0` >> simp[]
  >- (Cases_on `return_buf` >> simp_tac (srw_ss()) [LET_THM]
      >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
          >- (rpt strip_tac >> drule_at Any
               (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
          simp[cs_extends_refl]) >>
      rewrite_tac[state_pair_let_bind] >>
      ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- (rpt strip_tac >> drule_at Any first_emission_emit_multi_op >> simp[]) >>
      gen_tac >> rpt gen_tac >>
      simp_tac (srw_ss()) [comp_bind_def, LET_THM] >>
      Cases_on `store_multi_results x.buf_operand results 0 st4` >>
      simp[] >> strip_tac >> gvs[] >>
      qspecl_then [`x.buf_operand`, `results`, `0`, `st4`] mp_tac
        (cj 1 store_multi_results_labels) >> simp[]) >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (rpt strip_tac >> drule_at Any
       (CONJUNCT1 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
  gen_tac >> Cases_on `return_buf` >> simp[cs_extends_refl]
QED

Theorem first_emission_send:
  (!ce ty e a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !ce rt ty hg args dr a x b.
  compile_call cfn ce rt ty (Send hg) args dr a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `args` >>
  simp[Once compile_call_def, LET_THM]
  >- (map_every qid_spec_tac [`b`, `x`, `a`] >>
      ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (rpt strip_tac >> drule_at Any
           (CONJUNCT1 first_emission_emit_helpers) >> simp[]) >> simp[cs_extends_refl]) >>
  Cases_on `t` >> simp[Once compile_call_def, LET_THM]
  >- (map_every qid_spec_tac [`b`, `x`, `a`] >>
      ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (rpt strip_tac >> drule_at Any
           (CONJUNCT1 first_emission_emit_helpers) >> simp[]) >> simp[cs_extends_refl]) >>
  IF_CASES_TAC
  >- (map_every qid_spec_tac [`b`, `x`, `a`] >>
      ntac 2 (ho_match_mp_tac first_emission_pair_let >> conj_tac
        >- (ho_match_mp_tac first_emission_lower_value >> metis_tac[]) >> gen_tac) >>
      ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (Cases_on `t'` >> simp[cs_extends_refl] >>
          Cases_on `t` >> simp[cs_extends_refl] >>
          ho_match_mp_tac first_emission_lower_value >> metis_tac[]) >>
      gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (rpt strip_tac >> drule_at Any
           (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
      gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (rpt strip_tac >> drule_at Any
           (CONJUNCT1 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
      simp[cs_extends_refl]) >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (rpt strip_tac >> drule_at Any
       (CONJUNCT1 first_emission_emit_helpers) >> simp[]) >> simp[cs_extends_refl]
QED

Theorem first_emission_invalid_call:
  !ct cfn ce rt ty args dr a x b.
  MEM ct [RawLog; RawRevert; SelfDestructTarget] /\
  compile_call cfn ce rt ty ct args dr a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [MEM] >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_call _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [compile_call_def, LET_THM] >>
  Cases_on `emit_inst INVALID [] [] a` >> simp[] >> strip_tac >> gvs[] >>
  drule_at Any (CONJUNCT1 first_emission_emit_helpers) >> simp[]
QED

Theorem first_emission_external_call_kwargs[local]:
  !ce addr av ats ms az mid rz rmin rm stat cv gas skip hd dv rt dt ei di a x b.
  compile_external_call_kwargs ce addr av ats ms az mid rz rmin rm stat cv gas
    skip hd dv rt dt ei di a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [compile_external_call_kwargs_def, LET_THM] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[first_emission_alloc_buffer] >>
  gen_tac >> simp_tac (srw_ss()) [LET_THM] >>
  map_every qx_gen_tac [`a`, `x`, `b`] >>
  qmatch_goalsub_abbrev_tac `tail a = (x,b)` >>
  `!s. cs_extends s (SND (tail s)) /\
       EVERY (isPREFIX "@") (added_labels s (SND (tail s)))` suffices_by
    (strip_tac >> strip_tac >> first_x_assum (qspec_then `a` mp_tac) >> simp[]) >>
  gen_tac >> simp_tac (srw_ss()) [Abbr `tail`] >>
  rpt (FIRST [irule fresh_label_bind_labels >> rpt gen_tac >> disch_tac,
              irule comp_bind_labels >> conj_tac >> rpt gen_tac,
              irule comp_ignore_bind_labels >> conj_tac >> rpt gen_tac] >>
       BETA_TAC >> simp[LET_THM, emit_op_labels, emit_inst_labels, emit_void_labels,
         compile_alloc_buffer_labels, compile_extcall_store_values_labels,
         compile_abi_encode_labels, compile_abi_decode_labels,
         compile_return_value_decode_labels, comp_return_labels])
  >~ [`new_block`] >- (irule new_block_action_labels >> simp[])
  >~ [`new_block`] >- (irule new_block_action_labels >> simp[]) >>
  IF_CASES_TAC >> simp[comp_return_labels, emit_op_labels,
                       compile_extcodesize_check_labels] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >> simp[LET_THM, compile_alloc_buffer_labels,
         compile_extcall_store_values_labels, emit_op_labels,
         compile_abi_encode_labels, comp_return_labels]) >>
  IF_CASES_TAC >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >> simp[compile_alloc_buffer_labels,
         compile_default_return_path_labels, compile_return_value_decode_labels,
         compile_abi_decode_labels, comp_return_labels])
QED

Theorem first_emission_extcall:
  (!ce ty e a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !ce rt ty stat skip sig opts args dr a x b.
  compile_call cfn ce rt ty (ExtCall stat skip sig opts) args dr a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >> PairCases_on `sig` >> Cases_on `args` >>
  simp[Once compile_call_def, LET_THM] >>
  map_every qid_spec_tac [`b`, `x`, `a`]
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (rpt strip_tac >> drule_at Any
           (CONJUNCT1 first_emission_emit_helpers) >> simp[]) >> simp[cs_extends_refl]) >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_multi_vvs >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (drule first_emission_ext_call_kwargs >> disch_then MATCH_ACCEPT_TAC) >>
  gen_tac >> PairCases_on `v` >> simp_tac (srw_ss()) [LET_THM] >>
  Cases_on `v2` >> simp_tac (srw_ss()) [LET_THM]
  >- suspend "extcall_tail" >>
  PairCases_on `x` >> simp_tac (srw_ss()) [LET_THM] >>
  suspend "extcall_tail"
QED

Resume first_emission_extcall[extcall_tail]:
  markerLib.RESUME_TAC >>
  (Cases_on `v1` >> simp_tac (srw_ss()) [LET_THM]
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (rpt strip_tac >> drule_at Any
            (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
      gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (rpt strip_tac >> drule first_emission_external_call_kwargs >> simp[]) >>
      rpt gen_tac >> IF_CASES_TAC >> simp[cs_extends_refl]) >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (rpt strip_tac >> drule first_emission_external_call_kwargs >> simp[]) >>
  rpt gen_tac >> IF_CASES_TAC >> simp[cs_extends_refl])
QED

Finalise first_emission_extcall

Theorem first_emission_raw_call_outbuf[local]:
  !n a x b. compile_raw_call_outbuf n a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  gen_tac >> simp_tac (srw_ss()) [builtinSystemTheory.compile_raw_call_outbuf_def, LET_THM] >>
  Cases_on `n > 0` >> simp[] >>
  (ho_match_mp_tac first_emission_strong_bind >> conj_tac
   >- metis_tac[first_emission_alloc_buffer] >>
   rpt gen_tac >> simp_tac (srw_ss()) [LET_THM, comp_bind_def, comp_return_def] >>
   rpt strip_tac >> gvs[cs_extends_refl] >>
   Cases_on `emit_op ADD [buf_alloc.buf_operand; Lit 32w] b` >> gvs[] >>
   drule_at Any (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[])
QED

Theorem first_emission_raw_calldata:
  (!ce ty e a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !ce rt ty rcf args dr a x b.
  compile_call cfn ce rt ty (RawCallCalldataTarget rcf) args dr a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `args` >>
  simp[Once compile_call_def, LET_THM] >>
  map_every qid_spec_tac [`b`, `x`, `a`]
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (rpt strip_tac >> drule_at Any
           (CONJUNCT1 first_emission_emit_helpers) >> simp[]) >> simp[cs_extends_refl]) >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (drule first_emission_ext_call_kwargs >> disch_then MATCH_ACCEPT_TAC) >>
  gen_tac >> PairCases_on `v` >> simp_tac (srw_ss()) [LET_THM] >>
  Cases_on `v1` >> simp_tac (srw_ss()) [LET_THM]
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (rpt strip_tac >> drule_at Any
           (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
      gen_tac >> suspend "raw_calldata_outbuf") >>
  suspend "raw_calldata_outbuf"
QED

Resume first_emission_raw_calldata[raw_calldata_outbuf]:
  markerLib.RESUME_TAC >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[first_emission_raw_call_outbuf] >>
  qx_gen_tac `out` >> PairCases_on `out` >> simp_tac (srw_ss()) [LET_THM] >>
  map_every qx_gen_tac [`a`, `res`, `b`] >>
  qmatch_goalsub_abbrev_tac `tail a = (res,b)` >>
  `!s. cs_extends s (SND (tail s)) /\
       EVERY (isPREFIX "@") (added_labels s (SND (tail s)))` suffices_by
    (strip_tac >> strip_tac >> first_x_assum (qspec_then `a` mp_tac) >> simp[]) >>
  gen_tac >> simp_tac (srw_ss()) [Abbr `tail`] >>
  irule comp_bind_labels >> reverse conj_tac
  >- simp[compile_msg_data_to_memory_labels] >>
  map_every qx_gen_tac [`p`, `s`] >> PairCases_on `p` >> simp_tac (srw_ss()) [] >>
  irule comp_bind_labels >> reverse conj_tac
  >- simp[compile_raw_call_finish_labels] >>
  rpt gen_tac >> BETA_TAC >> irule comp_bind_labels >> reverse conj_tac
  >- simp[emit_void_labels] >>
  rpt gen_tac >> BETA_TAC >> IF_CASES_TAC >>
  simp[cs_extends_refl, loweringShapeDefsTheory.added_labels_def, DROP_LENGTH_TOO_LONG]
QED

Finalise first_emission_raw_calldata

Theorem first_emission_raw_call:
  (!ce ty e a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !ce rt ty rcf args dr a x b.
  compile_call cfn ce rt ty (RawCallTarget rcf) args dr a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `args` >>
  simp[Once compile_call_def, LET_THM] >>
  map_every qid_spec_tac [`b`, `x`, `a`]
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (rpt strip_tac >> drule_at Any
           (CONJUNCT1 first_emission_emit_helpers) >> simp[]) >> simp[cs_extends_refl]) >>
  Cases_on `t` >> simp[LET_THM]
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (rpt strip_tac >> drule_at Any
           (CONJUNCT1 first_emission_emit_helpers) >> simp[]) >> simp[cs_extends_refl]) >>
  ntac 2 (ho_match_mp_tac first_emission_pair_let >> conj_tac
    >- (ho_match_mp_tac first_emission_lower_value >> metis_tac[]) >> gen_tac) >>
  ntac 2 (ho_match_mp_tac first_emission_pair_let >> conj_tac
    >- (rpt strip_tac >> drule_at Any
         (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >> gen_tac) >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (drule first_emission_ext_call_kwargs >> disch_then MATCH_ACCEPT_TAC) >>
  gen_tac >> PairCases_on `v` >> simp_tac (srw_ss()) [LET_THM] >>
  Cases_on `v1` >> simp_tac (srw_ss()) [LET_THM]
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (rpt strip_tac >> drule_at Any
           (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
      gen_tac >> suspend "raw_call_outbuf") >>
  suspend "raw_call_outbuf"
QED

Resume first_emission_raw_call[raw_call_outbuf]:
  markerLib.RESUME_TAC >> rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[first_emission_raw_call_outbuf] >>
  qx_gen_tac `out` >> PairCases_on `out` >> simp_tac (srw_ss()) [LET_THM] >>
  map_every qx_gen_tac [`a`, `res`, `b`] >>
  qmatch_goalsub_abbrev_tac `tail a = (res,b)` >>
  `!s. cs_extends s (SND (tail s)) /\
       EVERY (isPREFIX "@") (added_labels s (SND (tail s)))` suffices_by
    (strip_tac >> strip_tac >> first_x_assum (qspec_then `a` mp_tac) >> simp[]) >>
  gen_tac >> simp_tac (srw_ss()) [Abbr `tail`] >>
  irule comp_bind_labels >> reverse conj_tac
  >- simp[compile_raw_call_finish_labels] >>
  rpt gen_tac >> BETA_TAC >> IF_CASES_TAC >>
  simp[cs_extends_refl, loweringShapeDefsTheory.added_labels_def, DROP_LENGTH_TOO_LONG]
QED

Finalise first_emission_raw_call

Theorem lower_value_extension_only[local]:
  (!ce ty e s. cs_extends s (SND (cfn ce ty e s))) ==>
  !ce ty e. cs_appends (lower_value cfn ce ty e)
Proof
  strip_tac >> rpt gen_tac >> rewrite_tac[lower_value_def] >>
  irule cs_appends_bind >> reverse conj_tac
  >- (rw[cs_appends_def] >> first_x_assum (qspecl_then [`ce`, `ty`, `e`, `st`] mp_tac) >> simp[]) >>
  qx_gen_tac `vv` >> rw[cs_appends_def] >>
  qspecl_then [`ce`, `vv`, `st`] mp_tac (cj 1 unwrap_value_labels) >> simp[]
QED

Theorem multi_vvs_extension_only[local]:
  (!ce ty e s. cs_extends s (SND (cfn ce ty e s))) ==>
  !es ce. cs_appends (compile_multi_vvs cfn ce es)
Proof
  strip_tac >> Induct >> rpt gen_tac >> rewrite_tac[compile_multi_vvs_def]
  >- simp[cs_appends_return] >>
  irule cs_appends_bind >> reverse conj_tac
  >- (rw[cs_appends_def] >> first_x_assum (qspecl_then [`ce`, `expr_type h`, `h`, `st`] mp_tac) >> simp[]) >>
  gen_tac >> BETA_TAC >> irule cs_appends_bind >> reverse conj_tac
  >- first_x_assum MATCH_ACCEPT_TAC >>
  simp[cs_appends_return]
QED

Theorem create_salt_extension_only[local]:
  (!ce ty e s. cs_extends s (SND (cfn ce ty e s))) ==>
  !ce se. cs_appends (compile_create_salt cfn ce se)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `se` >>
  rewrite_tac[compile_create_salt_def]
  >- simp[cs_appends_return] >>
  irule cs_appends_bind >> reverse conj_tac
  >- (irule lower_value_extension_only >> first_assum ACCEPT_TAC) >>
  simp[cs_appends_return]
QED

Theorem create_ctor_tuple_extension_only[local]:
  (!ce ty e s. cs_extends s (SND (cfn ce ty e s))) ==>
  !ce es. cs_appends (compile_create_ctor_tuple cfn ce es)
Proof
  strip_tac >> rpt gen_tac >> simp_tac (srw_ss()) [compile_create_ctor_tuple_def, LET_THM] >>
  irule cs_appends_bind >> reverse conj_tac
  >- (irule multi_vvs_extension_only >> first_assum ACCEPT_TAC) >>
  gen_tac >> BETA_TAC >> irule cs_appends_bind >> reverse conj_tac
  >- (rw[cs_appends_def] >>
      qspecl_then [`type_memory_bytes ce (TupleT (MAP expr_type es))`, `st`]
        mp_tac (cj 1 compile_alloc_buffer_labels) >> simp[]) >>
  gen_tac >> BETA_TAC >> irule cs_appends_ignore_bind >> conj_tac
  >- (rw[cs_appends_def] >>
      qspecl_then [`ce`, `ZIP (a,MAP expr_type es)`, `a'.buf_operand`, `0`, `st`]
        mp_tac (cj 1 compile_extcall_store_values_labels) >> simp[]) >>
  simp[cs_appends_return]
QED

Theorem create_blueprint_args_extension_only[local]:
  (!ce ty e s. cs_extends s (SND (cfn ce ty e s))) ==>
  !ce raw es. cs_appends (compile_create_blueprint_args cfn ce raw es)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `raw` >>
  simp_tac (srw_ss()) [compile_create_blueprint_args_def, LET_THM]
  >- (Cases_on `es` >> simp_tac (srw_ss()) []
      >- (irule cs_appends_ignore_bind >> simp[cs_appends_emit_helpers, cs_appends_return]) >>
      Cases_on `t` >> simp_tac (srw_ss()) []
      >- (irule cs_appends_bind >> reverse conj_tac
          >- (irule lower_value_extension_only >> first_assum ACCEPT_TAC) >>
          gen_tac >> BETA_TAC >> irule cs_appends_bind >> reverse conj_tac
          >- simp[cs_appends_emit_helpers] >>
          gen_tac >> BETA_TAC >> irule cs_appends_bind >> reverse conj_tac
          >- simp[cs_appends_emit_helpers] >> simp[cs_appends_return]) >>
      irule cs_appends_ignore_bind >> simp[cs_appends_emit_helpers, cs_appends_return]) >>
  Cases_on `es = []` >> simp[]
  >- simp[cs_appends_return] >>
  irule cs_appends_bind >> reverse conj_tac
  >- (rw[cs_appends_def] >> metis_tac[cj 1 compile_alloc_buffer_labels, pairTheory.SND]) >>
  gen_tac >> BETA_TAC >> irule cs_appends_bind >> reverse conj_tac
  >- (irule create_ctor_tuple_extension_only >> first_assum ACCEPT_TAC) >>
  gen_tac >> BETA_TAC >> irule cs_appends_bind >> reverse conj_tac
  >- (rw[cs_appends_def] >> metis_tac[cj 1 (CONJUNCT1 (CONJUNCT2 compile_abi_encode_labels)), pairTheory.SND]) >>
  simp[cs_appends_return]
QED

Theorem raw_create_suffix_extension_only[local]:
  (!ce ty e s. cs_extends s (SND (cfn ce ty e s))) ==>
  !ce bytecode value es salt rof maxlen abi_size enc.
  cs_appends
    (do value <- lower_value cfn ce (expr_type value) value;
        len <- emit_op MLOAD [bytecode];
        data <- emit_op ADD [bytecode; Lit 32w];
        (ptr,total) <-
          (if es = [] then return (data,len)
           else do buf <- compile_alloc_buffer (maxlen + abi_size);
                   compile_copy_memory_dynamic buf.buf_operand data len;
                   src <- compile_create_ctor_tuple cfn ce es;
                   dst <- emit_op ADD [buf.buf_operand; len];
                   args_len <- compile_abi_encode_to_buf dst src enc;
                   total <- emit_op ADD [len; args_len];
                   return (buf.buf_operand,total)
                od);
        salt <- compile_create_salt cfn ce salt;
        compile_create_dispatch ptr total value salt rof
     od)
Proof
  strip_tac >> rpt gen_tac >>
  irule cs_appends_bind >> reverse conj_tac
  >- (irule lower_value_extension_only >> first_assum ACCEPT_TAC) >>
  ntac 2 (gen_tac >> BETA_TAC >> irule cs_appends_bind >> reverse conj_tac
    >- simp[cs_appends_emit_helpers]) >>
  gen_tac >> BETA_TAC >> irule cs_appends_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[cs_appends_return] >>
      irule cs_appends_bind >> reverse conj_tac
      >- (rw[cs_appends_def] >> metis_tac[cj 1 compile_alloc_buffer_labels, pairTheory.SND]) >>
      gen_tac >> BETA_TAC >> irule cs_appends_ignore_bind >> conj_tac
      >- (rw[cs_appends_def] >> metis_tac[cj 1 compile_copy_memory_dynamic_labels, pairTheory.SND]) >>
      irule cs_appends_bind >> reverse conj_tac
      >- (irule create_ctor_tuple_extension_only >> first_assum ACCEPT_TAC) >>
      gen_tac >> BETA_TAC >> irule cs_appends_bind >> reverse conj_tac
      >- simp[cs_appends_emit_helpers] >>
      gen_tac >> BETA_TAC >> irule cs_appends_bind >> reverse conj_tac
      >- (rw[cs_appends_def] >> metis_tac[cj 1 (CONJUNCT1 (CONJUNCT2 compile_abi_encode_labels)), pairTheory.SND]) >>
      gen_tac >> BETA_TAC >> irule cs_appends_bind >>
      simp[cs_appends_emit_helpers, cs_appends_return]) >>
  qx_gen_tac `pl` >> PairCases_on `pl` >> simp_tac (srw_ss()) [] >>
  irule cs_appends_bind >> reverse conj_tac
  >- (irule create_salt_extension_only >> first_assum ACCEPT_TAC) >>
  gen_tac >> BETA_TAC >> rw[cs_appends_def] >>
  metis_tac[cj 1 compile_create_dispatch_labels, pairTheory.SND]
QED

Theorem raw_create_extension_only[local]:
  (!ce ty e s. cs_extends s (SND (cfn ce ty e s))) ==>
  !ce bytecode value es salt rof.
    cs_appends (compile_raw_create cfn ce bytecode value es salt rof)
Proof
  strip_tac >> rpt gen_tac >>
  simp_tac (srw_ss()) [compile_raw_create_def, LET_THM] >>
  irule cs_appends_bind >> reverse conj_tac
  >- (rw[cs_appends_def] >> metis_tac[pairTheory.SND]) >>
  gen_tac >> BETA_TAC >> irule cs_appends_bind >> reverse conj_tac
  >- (rw[cs_appends_def] >> metis_tac[cj 1 compile_create_snapshot_labels, pairTheory.SND]) >>
  gen_tac >> BETA_TAC >> irule raw_create_suffix_extension_only >> first_assum ACCEPT_TAC
QED

Theorem create_call_extension_only[local]:
  (!ce ty e s. cs_extends s (SND (cfn ce ty e s))) ==>
  !ce ck salt rof es. cs_appends (compile_create_call cfn ce ck salt rof es)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `es`
  >- (simp[compile_create_call_def] >> irule cs_appends_ignore_bind >>
      simp[cs_appends_emit_helpers, cs_appends_return]) >>
  Cases_on `t`
  >- (simp[compile_create_call_def] >> irule cs_appends_ignore_bind >>
      simp[cs_appends_emit_helpers, cs_appends_return]) >>
  simp_tac (srw_ss()) [compile_create_call_def] >> IF_CASES_TAC
  >- (irule cs_appends_ignore_bind >> simp[cs_appends_emit_helpers, cs_appends_return]) >>
  Cases_on `ck` >> simp_tac (srw_ss()) [LET_THM]
  >~ [`cs_appends (compile_raw_create _ _ _ _ _ _ _)`]
  >- (irule raw_create_extension_only >> first_assum ACCEPT_TAC) >>
  ntac 2 (irule cs_appends_bind >> reverse conj_tac
    >- (irule lower_value_extension_only >> first_assum ACCEPT_TAC) >>
    gen_tac >> BETA_TAC)
  >~ [`cs_appends (comp_bind (compile_create_proxy_buf _) _)`]
  >- (irule cs_appends_bind >> reverse conj_tac
      >- (rw[cs_appends_def] >> metis_tac[cj 1 compile_create_proxy_buf_labels, pairTheory.SND]) >>
      gen_tac >> BETA_TAC >> irule cs_appends_bind >> reverse conj_tac
      >- (irule create_salt_extension_only >> first_assum ACCEPT_TAC) >>
      gen_tac >> BETA_TAC >> rw[cs_appends_def] >>
      metis_tac[cj 1 compile_create_dispatch_labels, pairTheory.SND])
  >~ [`cs_appends (comp_bind _ (\salt. compile_create_copy _ _ salt _))`]
  >- (irule cs_appends_bind >> reverse conj_tac
      >- (irule create_salt_extension_only >> first_assum ACCEPT_TAC) >>
      gen_tac >> BETA_TAC >> rw[cs_appends_def] >>
      metis_tac[cj 1 compile_create_copy_labels, pairTheory.SND]) >>
  irule cs_appends_bind >> reverse conj_tac
  >- (irule create_salt_extension_only >> first_assum ACCEPT_TAC) >>
  gen_tac >> BETA_TAC >> irule cs_appends_bind >> reverse conj_tac
  >- (irule lower_value_extension_only >> first_assum ACCEPT_TAC) >>
  gen_tac >> BETA_TAC >> irule cs_appends_bind >> reverse conj_tac
  >- (rw[cs_appends_def] >> metis_tac[cj 1 compile_create_blueprint_check_labels, pairTheory.SND]) >>
  gen_tac >> BETA_TAC >> irule cs_appends_bind >> reverse conj_tac
  >- (irule create_blueprint_args_extension_only >> first_assum ACCEPT_TAC) >>
  qx_gen_tac `pl` >> PairCases_on `pl` >> simp_tac (srw_ss()) [] >>
  rw[cs_appends_def] >> metis_tac[cj 1 compile_create_blueprint_append_labels, pairTheory.SND]
QED


Theorem first_emission_create_snapshot[local]:
  !ce vv ty a x b. compile_create_snapshot ce vv ty a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [compile_create_snapshot_def, LET_THM] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[first_emission_alloc_buffer] >>
  gen_tac >> map_every qx_gen_tac [`a`, `x`, `b`] >>
  qmatch_goalsub_abbrev_tac `tail a = (x,b)` >>
  `!s. cs_extends s (SND (tail s)) /\
       EVERY (isPREFIX "@") (added_labels s (SND (tail s)))` suffices_by
    (strip_tac >> strip_tac >> first_x_assum (qspec_then `a` mp_tac) >> simp[]) >>
  gen_tac >> simp_tac (srw_ss()) [Abbr `tail`] >>
  irule comp_ignore_bind_labels >> reverse conj_tac
  >- simp[comp_return_labels] >>
  Cases_on `vv_location vv` >> simp_tac (srw_ss()) []
  >- (rpt (irule comp_bind_labels >> conj_tac >> rpt gen_tac >> BETA_TAC >>
           simp[emit_op_labels, compile_copy_memory_dynamic_labels])) >>
  rename1 `vv_location vv = SOME loc` >> Cases_on `loc` >> simp_tac (srw_ss()) [] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[contextTheory.compile_slot_to_memory_def, compile_word_copy_loop_labels,
            compile_imm_copy_to_memory_labels, emit_op_labels,
            compile_copy_memory_dynamic_labels, comp_return_labels])
QED

Theorem first_emission_raw_create:
  (!ce ty e a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !ce bytecode value es salt rof a x b.
  compile_raw_create cfn ce bytecode value es salt rof a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >>
  `!ce ty e s. cs_extends s (SND (cfn ce ty e s))` by
    (rpt gen_tac >> Cases_on `cfn ce ty e s` >>
     first_x_assum drule >> simp[]) >>
  rpt gen_tac >> simp_tac (srw_ss()) [compile_raw_create_def, LET_THM] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[] >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[first_emission_create_snapshot] >>
  gen_tac >> BETA_TAC >> map_every qx_gen_tac [`a`, `res`, `b`] >>
  qmatch_goalsub_abbrev_tac `tail a = (res,b)` >>
  `cs_appends tail` by
    (simp_tac (srw_ss()) [Abbr `tail`] >>
     irule raw_create_suffix_extension_only >> first_assum ACCEPT_TAC) >>
  gvs[cs_appends_def]
QED

Theorem first_emission_create_proxy_buf[local]:
  !target a x b. compile_create_proxy_buf target a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >> rewrite_tac[builtinCreateTheory.compile_create_proxy_buf_def] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[first_emission_alloc_buffer] >>
  gen_tac >> map_every qx_gen_tac [`a`, `x`, `b`] >>
  qmatch_goalsub_abbrev_tac `tail a = (x,b)` >>
  `!s. cs_extends s (SND (tail s)) /\
       EVERY (isPREFIX "@") (added_labels s (SND (tail s)))` suffices_by
    (strip_tac >> strip_tac >> first_x_assum (qspec_then `a` mp_tac) >> simp[]) >>
  gen_tac >> simp_tac (srw_ss()) [Abbr `tail`] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_void_labels])
QED

Theorem first_emission_create_copy[local]:
  !target value salt rof a x b. compile_create_copy target value salt rof a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [builtinCreateTheory.compile_create_copy_def, LET_THM] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any
       (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
  gen_tac >> map_every qx_gen_tac [`a`, `x`, `b`] >>
  qmatch_goalsub_abbrev_tac `tail a = (x,b)` >>
  `!s. cs_extends s (SND (tail s)) /\
       EVERY (isPREFIX "@") (added_labels s (SND (tail s)))` suffices_by
    (strip_tac >> strip_tac >> first_x_assum (qspec_then `a` mp_tac) >> simp[]) >>
  gen_tac >> Cases_on `salt` >> Cases_on `rof` >>
  simp_tac (srw_ss()) [Abbr `tail`] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_void_labels,
            compile_alloc_dynamic_labels, compile_check_create_result_labels])
QED

Theorem first_emission_create_blueprint_check[local]:
  !target offset a x b. compile_create_blueprint_check target offset a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >> rewrite_tac[builtinCreateTheory.compile_create_blueprint_check_def] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any
       (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
  gen_tac >> map_every qx_gen_tac [`a`, `x`, `b`] >>
  qmatch_goalsub_abbrev_tac `tail a = (x,b)` >>
  `!s. cs_extends s (SND (tail s)) /\
       EVERY (isPREFIX "@") (added_labels s (SND (tail s)))` suffices_by
    (strip_tac >> strip_tac >> first_x_assum (qspec_then `a` mp_tac) >> simp[]) >>
  gen_tac >> simp_tac (srw_ss()) [Abbr `tail`] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_void_labels])
QED

Theorem first_emission_create_salt[local]:
  (!ce ty e a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !ce se a x b. compile_create_salt cfn ce se a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> map_every qx_gen_tac [`ce`, `se`] >> Cases_on `se`
  >- simp[compile_create_salt_def, comp_return_def, cs_extends_refl] >>
  rewrite_tac[compile_create_salt_def] >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  simp[comp_return_def, cs_extends_refl]
QED

Theorem first_emission_create_call:
  (!ce ty e a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !ce ck salt rof es a x b. compile_create_call cfn ce ck salt rof es a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >>
  `!ce ty e s. cs_extends s (SND (cfn ce ty e s))` by
    (rpt gen_tac >> Cases_on `cfn ce ty e s` >> first_x_assum drule >> simp[]) >>
  map_every qx_gen_tac [`ce`, `ck`, `salt`, `rof`, `es`] >> Cases_on `es`
  >- (simp_tac (srw_ss()) [compile_create_call_def] >> suspend "invalid_create") >>
  Cases_on `t`
  >- (simp_tac (srw_ss()) [compile_create_call_def] >> suspend "invalid_create") >>
  simp_tac (srw_ss()) [compile_create_call_def] >> IF_CASES_TAC
  >- suspend "invalid_create" >>
  Cases_on `ck` >> simp_tac (srw_ss()) [LET_THM]
  >~ [`compile_raw_create`]
  >- (drule first_emission_raw_create >> disch_then MATCH_ACCEPT_TAC) >>
  ntac 2 (ho_match_mp_tac first_emission_bind >> conj_tac
    >- (ho_match_mp_tac first_emission_lower_value >> metis_tac[]) >>
    gen_tac >> BETA_TAC)
  >~ [`compile_create_proxy_buf`] >- suspend "proxy"
  >~ [`compile_create_copy`] >- suspend "copy" >>
  suspend "blueprint"
QED

Resume first_emission_create_call[invalid_create]:
  markerLib.RESUME_TAC >> (
  rewrite_tac[comp_ignore_bind_def] >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any
       (CONJUNCT1 first_emission_emit_helpers) >> simp[]) >>
  simp[comp_return_def, cs_extends_refl])
QED

Resume first_emission_create_call[proxy]:
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[first_emission_create_proxy_buf] >>
  gen_tac >> BETA_TAC >> map_every qx_gen_tac [`a`, `res`, `b`] >>
  qmatch_goalsub_abbrev_tac `tail a = (res,b)` >>
  `cs_appends tail` by
    (simp_tac (srw_ss()) [Abbr `tail`] >> irule cs_appends_bind >> reverse conj_tac
     >- (irule create_salt_extension_only >> first_assum ACCEPT_TAC) >>
     gen_tac >> BETA_TAC >> rw[cs_appends_def] >>
     metis_tac[cj 1 compile_create_dispatch_labels, pairTheory.SND]) >>
  gvs[cs_appends_def]
QED

Resume first_emission_create_call[copy]:
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (drule first_emission_create_salt >> disch_then MATCH_ACCEPT_TAC) >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_strong >>
  metis_tac[first_emission_create_copy]
QED

Resume first_emission_create_call[blueprint]:
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (drule first_emission_create_salt >> disch_then MATCH_ACCEPT_TAC) >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[first_emission_create_blueprint_check] >>
  gen_tac >> BETA_TAC >> map_every qx_gen_tac [`a`, `res`, `last`] >>
  qmatch_goalsub_abbrev_tac `tail a = (res,last)` >>
  `cs_appends tail` by
    (simp_tac (srw_ss()) [Abbr `tail`] >> irule cs_appends_bind >> reverse conj_tac
     >- (irule create_blueprint_args_extension_only >> first_assum ACCEPT_TAC) >>
     qx_gen_tac `pl` >> PairCases_on `pl` >> simp_tac (srw_ss()) [] >>
     rw[cs_appends_def] >> metis_tac[cj 1 compile_create_blueprint_append_labels, pairTheory.SND]) >>
  gvs[cs_appends_def]
QED

Finalise first_emission_create_call

Theorem first_emission_call:
  (!ce ty e a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !ce rt ty target es dr a x b. compile_call cfn ce rt ty target es dr a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> map_every qx_gen_tac [`ce`, `rt`, `ty`, `target`, `es`, `dr`] >>
  Cases_on `target`
  >- (drule first_emission_intcall >> disch_then MATCH_ACCEPT_TAC)
  >- (drule first_emission_extcall >> disch_then MATCH_ACCEPT_TAC)
  >- (drule first_emission_send >> disch_then MATCH_ACCEPT_TAC)
  >- (drule first_emission_raw_call >> disch_then MATCH_ACCEPT_TAC)
  >- (drule first_emission_raw_calldata >> disch_then MATCH_ACCEPT_TAC)
  >- (rpt gen_tac >> strip_tac >> drule_at Any first_emission_invalid_call >>
      simp[MEM] >> strip_tac >> simp[])
  >- (rpt gen_tac >> strip_tac >> drule_at Any first_emission_invalid_call >>
      simp[MEM] >> strip_tac >> simp[])
  >- (rpt gen_tac >> strip_tac >> drule_at Any first_emission_invalid_call >>
      simp[MEM] >> strip_tac >> simp[]) >>
  simp_tac (srw_ss()) [compile_call_def] >>
  ho_match_mp_tac first_emission_as_stack_val >>
  drule first_emission_create_call >> disch_then MATCH_ACCEPT_TAC
QED

Theorem first_emission_env_var[local]:
  !item a x b. compile_env_var item a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  gen_tac >> Cases_on `item`
  >~ [`compile_env_var PrevHash`]
  >- (rewrite_tac[compile_env_var_def] >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- (rpt strip_tac >> drule_at Any
           (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
      gen_tac >> simp[GSYM cs_appends_def] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule cs_appends_bind >> simp[cs_appends_emit_helpers]) >>
  rewrite_tac[compile_env_var_def] >>
  rpt strip_tac >> drule_at Any
    (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]
QED

Theorem first_emission_builtin_environment:
  !cfn ce ret_ty ty bi args a x b.
  ((?item. bi = Env item) \/ bi = CalldataLen) /\
  compile_builtin_dispatch_body cfn ce ret_ty ty bi args a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 strip_assume_tac mp_tac) >>
  gvs[compile_builtin_dispatch_body_def] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_as_stack_val
  >- metis_tac[first_emission_env_var] >>
  rewrite_tac[builtinSimpleTheory.compile_builtin_calldatasize_def] >>
  rpt strip_tac >> drule_at Any
    (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]
QED

Theorem first_emission_invert[local]:
  !v ty ce a x b. compile_invert v ty ce a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >> Cases_on `ty` >> rewrite_tac[compile_invert_def, LET_THM] >>
  metis_tac[
    SRULE [] (Q.SPEC `NOT` (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers))),
    SRULE [] (Q.SPEC `XOR` (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)))]
QED

Theorem first_emission_neg[local]:
  !v ty a x b. compile_neg v ty a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [compile_neg_def, LET_THM, pairTheory.UNCURRY] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any
       (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
  gen_tac >> simp[GSYM cs_appends_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule cs_appends_ignore_bind >> simp[cs_appends_emit_helpers]
QED

Theorem first_emission_abs[local]:
  !v a x b. compile_builtin_abs v a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  gen_tac >> rewrite_tac[builtinSimpleTheory.compile_builtin_abs_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any
       (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
  gen_tac >> simp[GSYM cs_appends_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  ntac 4 (irule cs_appends_bind >> simp[cs_appends_emit_helpers] >> gen_tac) >>
  irule cs_appends_ignore_bind >> simp[cs_appends_emit_helpers] >>
  simp[cs_appends_def] >> rpt strip_tac >>
  mp_tac (Q.SPECL [`a`, `neg_val`, `v`, `st`] (cj 1 compile_select_labels)) >>
  simp[]
QED

Theorem first_emission_builtin_unary:
  (!ce ty e a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !ce ret_ty ty bi args a x b.
  (bi = Not \/ bi = Neg \/ bi = Abs) /\
  compile_builtin_dispatch_body cfn ce ret_ty ty bi args a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 strip_assume_tac mp_tac) >>
  gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_pair_let >>
  (conj_tac
   >- (ho_match_mp_tac first_emission_lower_value >> metis_tac[]) >> gen_tac)
  >- (Cases_on `expr_type (HD args) = BaseT BoolT` >> simp[] >>
      ho_match_mp_tac first_emission_as_stack_val
      >- (rpt strip_tac >> drule_at Any
           (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
      metis_tac[first_emission_invert])
  >- (ho_match_mp_tac first_emission_as_stack_val >> metis_tac[first_emission_neg]) >>
  ho_match_mp_tac first_emission_as_stack_val >> metis_tac[first_emission_abs]
QED

Theorem first_emission_acc[local]:
  (!a x b. cfn ce (BaseT AddressT) e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !item a x b. compile_acc cfn ce e item a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> gen_tac >> Cases_on `item`
  >~ [`compile_acc cfn ce e Address`]
  >- (rewrite_tac[compile_acc_def] >> ho_match_mp_tac first_emission_lower_value >> simp[])
  >~ [`compile_acc cfn ce e Code`]
  >- (rewrite_tac[compile_acc_def, LET_THM] >>
      ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (rpt strip_tac >> drule_at Any
           (CONJUNCT1 first_emission_emit_helpers) >> simp[]) >>
      simp[cs_extends_refl]) >>
  rewrite_tac[compile_acc_def, LET_THM] >>
  ho_match_mp_tac first_emission_pair_let >>
  (conj_tac >- (ho_match_mp_tac first_emission_lower_value >> simp[]) >> gen_tac)
  >~ [`(\(cs_op,st2). emit_op GT [cs_op; Lit 0w] st2) _`]
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (rpt strip_tac >> drule_at Any
           (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
      gen_tac >> rpt strip_tac >> drule_at Any
        (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
  rpt strip_tac >> drule_at Any
    (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]
QED

Theorem first_emission_builtin_accessor:
  (!ce ty e a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !ce ret_ty ty bi args a x b.
  ((?item. bi = Acc item) \/ bi = Len) /\
  compile_builtin_dispatch_body cfn ce ret_ty ty bi args a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 strip_assume_tac mp_tac) >>
  gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  map_every qid_spec_tac [`b`, `x`, `a`]
  >- (ho_match_mp_tac first_emission_as_stack_val >>
      qid_spec_tac `item` >>
      ho_match_mp_tac first_emission_acc >> metis_tac[]) >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- metis_tac[] >> gen_tac >>
  ho_match_mp_tac first_emission_as_stack_val >>
  rewrite_tac[builtinSimpleTheory.compile_builtin_len_def] >>
  metis_tac[first_emission_ptr_load]
QED
