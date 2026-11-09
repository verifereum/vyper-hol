Theory exprSimAbiEncodeArgsEntryPlace
Ancestors
  exprSimAbiEncodeArgsEntryValue exprSimAbiEncodeArgsEntryPrim
  exprSimAbiEncodeArgsEntry externalEntryShape exprLowering compileEnv
  context emitHelper vyperAST
Libs
  BasicProvers

Theorem abi_args_entry_mapping_subscript:
  compile_mapping_subscript ptr_op key a = (x,b) ==>
  cs_extends a b /\
  (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  simp[compile_mapping_subscript_def] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- metis_tac[abi_args_entry_alloc_buffer] >>
  rpt (FIRST
    [irule abi_args_entry_extends_bind >> conj_tac,
     irule abi_args_entry_extends_ignore_bind >> conj_tac,
     gen_tac] >> simp[emit_op_labels, emit_void_labels])
QED

Theorem abi_args_entry_keccak_key:
  compile_keccak256_key key is32 a = (x,b) ==>
  cs_extends a b /\
  (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  Cases_on `is32` >> simp[compile_keccak256_key_def] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- metis_tac[abi_args_entry_alloc_buffer]
  >- (rpt (FIRST
       [irule abi_args_entry_extends_bind >> conj_tac,
        irule abi_args_entry_extends_ignore_bind >> conj_tac,
        gen_tac] >> simp[emit_op_labels, emit_void_labels]))
  >- (rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  rpt (FIRST
    [irule abi_args_entry_extends_bind >> conj_tac,
     irule abi_args_entry_extends_ignore_bind >> conj_tac,
     gen_tac] >> simp[emit_op_labels, emit_void_labels])
QED

Theorem abi_args_entry_array_subscript:
  (!ptr_op a x b. loader ptr_op a = (x,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !a x b. compile_array_subscript ptr_op idx dyn static_n ws sz signed loader a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> simp[compile_array_subscript_def] >>
  ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac
  >- (Cases_on `dyn` >> simp[] >> metis_tac[abi_args_entry_safe_return]) >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac
  >- (Cases_on `signed` >> simp[]
      >- (rpt gen_tac >> strip_tac >>
          `SLT <> PHI` by simp[] >>
          drule_all abi_args_entry_emit_op >>
          metis_tac[abi_args_entry_safe_def]) >>
      metis_tac[abi_args_entry_safe_return]) >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  rpt (FIRST
    [irule abi_args_entry_extends_bind >> conj_tac,
     irule abi_args_entry_extends_ignore_bind >> conj_tac,
     gen_tac, IF_CASES_TAC] >>
    simp[emit_op_labels, emit_void_labels, comp_return_def, cs_extends_refl])
QED

Theorem abi_args_entry_tuple_subscript:
  compile_tuple_subscript ptr_op off a = (x,b) ==>
  cs_extends a b /\
  (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  simp[compile_tuple_subscript_def] >> strip_tac >>
  irule abi_args_entry_emit_op >> simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_args_entry_subscript:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty e idx_e a x b.
    compile_subscript cfn ce rt ty e idx_e a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> rpt gen_tac >> simp[compile_subscript_def] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac
  >- metis_tac[] >> gen_tac >>
  reverse (Cases_on `place_type ce e`)
  >- (rename1 `ValPT bt` >> Cases_on `bt` >> simp[] >>
      FIRST
       [ho_match_mp_tac abi_args_entry_emitted_bind >> conj_tac >-
          metis_tac[abi_args_entry_tuple_subscript] >>
          simp[comp_return_def, cs_extends_refl],
        ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac >-
          metis_tac[abi_args_entry_lower_value] >>
          gen_tac >> ho_match_mp_tac abi_args_entry_emitted_bind >> conj_tac >-
          (ho_match_mp_tac abi_args_entry_array_subscript >>
           metis_tac[abi_args_entry_ptr_load, abi_args_entry_safe_def]) >>
          simp[comp_return_def, cs_extends_refl]]) >>
  simp[] >> ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac
  >- metis_tac[abi_args_entry_lower_value] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[] >>
      metis_tac[abi_args_entry_keccak_key, abi_args_entry_safe_def,
                abi_args_entry_safe_return]) >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_bind >> conj_tac
  >- metis_tac[abi_args_entry_mapping_subscript] >>
  simp[comp_return_def, cs_extends_refl]
QED

Theorem abi_args_entry_safe_array_subscript:
  (!ptr_op a x b. loader ptr_op a = (x,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !a x b. compile_array_subscript ptr_op idx dyn static_n ws sz signed loader a = (x,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all abi_args_entry_array_subscript >>
  metis_tac[abi_args_entry_safe_def]
QED

Theorem abi_args_entry_get_target_ptr:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !tgt ce a x b. compile_get_target_ptr cfn ce tgt a = (x,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b
Proof
  strip_tac >> measureInduct_on `base_assignment_target_size tgt` >>
  Cases_on `tgt` >> gen_tac
  >- (simp[compile_get_target_ptr_def] >>
      TOP_CASE_TAC >> simp[comp_return_def, cs_extends_refl] >>
      TOP_CASE_TAC >> simp[comp_return_def, cs_extends_refl])
  >- (simp[compile_get_target_ptr_def] >>
      TOP_CASE_TAC >> simp[comp_return_def, cs_extends_refl] >>
      TOP_CASE_TAC >> simp[comp_return_def, cs_extends_refl])
  >- (simp[compile_get_target_ptr_def] >>
      ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
      >- (rpt gen_tac >> strip_tac >> first_x_assum irule >>
          simp[] >> goal_assum (drule_at Any) >> simp[]) >> gen_tac >>
      Cases_on `SND (SND result)` >> simp[]
      >- (ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
          >- metis_tac[abi_args_entry_lower_value] >>
          gen_tac >> ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
          >- (ho_match_mp_tac abi_args_entry_safe_array_subscript >>
              metis_tac[abi_args_entry_ptr_load, abi_args_entry_safe_def]) >>
          simp[comp_return_def, cs_extends_refl]) >>
      Cases_on `x` >> simp[]
      >- (ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
          >- metis_tac[abi_args_entry_lower_value] >>
          gen_tac >> ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
          >- (IF_CASES_TAC >> simp[] >>
              metis_tac[abi_args_entry_keccak_key, abi_args_entry_safe_def,
                        abi_args_entry_safe_return]) >>
          gen_tac >> ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
          >- metis_tac[abi_args_entry_mapping_subscript, abi_args_entry_safe_def] >>
          simp[comp_return_def, cs_extends_refl]) >>
      ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
      >- metis_tac[abi_args_entry_lower_value] >>
      gen_tac >> ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
      >- (ho_match_mp_tac abi_args_entry_safe_array_subscript >>
          metis_tac[abi_args_entry_ptr_load, abi_args_entry_safe_def]) >>
      simp[comp_return_def, cs_extends_refl]) >>
  simp[compile_get_target_ptr_def] >>
  ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> first_x_assum irule >>
          simp[] >> goal_assum (drule_at Any) >> simp[]) >> gen_tac >>
  ho_match_mp_tac abi_args_entry_safe_emitted_prefix >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  simp[comp_return_def, cs_extends_refl]
QED
