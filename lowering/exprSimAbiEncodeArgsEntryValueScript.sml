Theory exprSimAbiEncodeArgsEntryValue
Ancestors
  exprSimAbiEncodeArgsEntryPrim exprSimAbiEncodeArgsEntry
  compileEnv context emitHelper exprLowering externalEntryShape exprSimUnwrap

(* Sequencing interfaces keep administrative changes separate from code. *)
Theorem abi_args_entry_safe_bind:
  (!a x b. m a = (x,b) ==> cs_extends a b /\ abi_args_entry_safe a b) /\
  (!x b y c. k x b = (y,c) ==> cs_extends b c /\ abi_args_entry_safe b c) ==>
  !a y c. compileEnv$comp_bind m k a = (y,c) ==>
    cs_extends a c /\ abi_args_entry_safe a c
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> Cases_on `m a` >>
  simp[comp_bind_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >>
  metis_tac[abi_args_entry_safe_trans, cs_extends_trans]
QED

Theorem abi_args_entry_emitted_bind:
  (!a x b. m a = (x,b) ==> cs_extends a b /\
     (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)) /\
  (!x b y c. k x b = (y,c) ==> cs_extends b c) ==>
  !a y c. compileEnv$comp_bind m k a = (y,c) ==>
    cs_extends a c /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a c)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> Cases_on `m a` >>
  simp[comp_bind_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >>
  metis_tac[abi_args_entry_emitted_mono, cs_extends_trans]
QED

Theorem abi_args_entry_safe_return:
  comp_return x a = (y,b) ==> cs_extends a b /\ abi_args_entry_safe a b
Proof
  simp[comp_return_def] >> rw[] >> simp[cs_extends_refl]
QED

Theorem abi_args_entry_alloc_buffer:
  compile_alloc_buffer sz a = (x,b) ==> cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  simp[compile_alloc_buffer_def, emit_op_def, emit_inst_def,
       fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rw[] >> simp[cs_extends_def, abi_args_entry_emitted_def,
              venomInstTheory.mk_inst_def] >> metis_tac[]
QED

Theorem abi_args_entry_emit_op:
  op <> PHI /\ emit_op op args a = (x,b) ==> cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  simp[emit_op_def, emit_inst_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rw[] >> simp[cs_extends_def, abi_args_entry_emitted_def,
              venomInstTheory.mk_inst_def] >> metis_tac[]
QED

Theorem abi_args_entry_imm_load:
  compile_imm_load_word ic imm off a = (x,b) ==> cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  simp[compile_imm_load_word_def, emit_op_def, emit_inst_def,
       fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `ic` >> Cases_on `imm` >>
  rw[emit_op_def, emit_inst_def, fresh_var_def, fresh_id_def, emit_def,
     comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[cs_extends_def, abi_args_entry_emitted_def,
       venomInstTheory.mk_inst_def] >>
  metis_tac[rich_listTheory.IS_PREFIX_APPEND, listTheory.APPEND_ASSOC]
QED

Theorem abi_args_entry_ptr_load:
  compile_ptr_load ic imm loc off a = (x,b) ==> cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  Cases_on `loc` >> simp[compile_ptr_load_def] >> strip_tac
  >- (irule abi_args_entry_emit_op >> simp[] >> goal_assum (drule_at Any) >> simp[])
  >- (irule abi_args_entry_emit_op >> simp[] >> goal_assum (drule_at Any) >> simp[])
  >- (irule abi_args_entry_emit_op >> simp[] >> goal_assum (drule_at Any) >> simp[])
  >- metis_tac[abi_args_entry_imm_load]
  >> irule abi_args_entry_emit_op >> simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_args_entry_safe_prefix_bind:
  (!a x b. m a = (x,b) ==> cs_extends a b /\
     (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)) /\
  (!x b y c. k x b = (y,c) ==> cs_extends b c) ==>
  !a y c. compileEnv$comp_bind m k a = (y,c) ==> abi_args_entry_safe a c
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> Cases_on `m a` >>
  simp[comp_bind_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >>
  metis_tac[abi_args_entry_emitted_mono, abi_args_entry_safe_def]
QED

Theorem abi_args_entry_extends_bind:
  (!s. cs_extends s (SND (m s))) /\
  (!x s. cs_extends s (SND (k x s))) ==>
  !s. cs_extends s (SND (compileEnv$comp_bind m k s))
Proof
  strip_tac >> gen_tac >> simp[comp_bind_def, pairTheory.UNCURRY] >>
  irule cs_extends_trans >> qexists_tac `SND (m s)` >> simp[]
QED

Theorem abi_args_entry_extends_ignore_bind:
  (!s. cs_extends s (SND (m s))) /\
  (!s. cs_extends s (SND (n s))) ==>
  !s. cs_extends s (SND (comp_ignore_bind m n s))
Proof
  simp[comp_ignore_bind_def, abi_args_entry_extends_bind]
QED

Theorem abi_args_entry_safe_prefix:
  (!a x b. m a = (x,b) ==> cs_extends a b /\
     (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)) /\
  (!x b. cs_extends b (SND (k x b))) ==>
  !a y c. compileEnv$comp_bind m k a = (y,c) ==> abi_args_entry_safe a c
Proof
  strip_tac >> ho_match_mp_tac abi_args_entry_safe_prefix_bind >>
  simp[] >> metis_tac[pairTheory.SND]
QED

Theorem abi_args_entry_ensure_in_memory:
  compile_ensure_in_memory ptr_op loc mem_bytes wc ic imm a = (x,b) ==>
  cs_extends a b /\ abi_args_entry_safe a b
Proof
  strip_tac >> conj_tac
  >- metis_tac[compile_ensure_in_memory_extends] >>
  Cases_on `loc` >> fs[compile_ensure_in_memory_def]
  >- gvs[comp_return_def]
  >- (qpat_x_assum `_ a = (x,b)` mp_tac >>
      map_every qid_spec_tac [`b`, `x`, `a`] >>
      ho_match_mp_tac abi_args_entry_safe_prefix >>
      reverse conj_tac >-
        (gen_tac >> rpt (FIRST
          [irule abi_args_entry_extends_bind >> conj_tac,
           irule abi_args_entry_extends_ignore_bind >> conj_tac,
           gen_tac, IF_CASES_TAC] >>
          simp[comp_return_def, cs_extends_refl, emit_op_labels,
               emit_void_labels, compile_alloc_buffer_labels,
               compile_storage_to_memory_labels, compile_transient_to_memory_labels,
               compile_imm_copy_to_memory_labels])) >> metis_tac[abi_args_entry_alloc_buffer])
  >- (qpat_x_assum `_ a = (x,b)` mp_tac >>
      map_every qid_spec_tac [`b`, `x`, `a`] >>
      ho_match_mp_tac abi_args_entry_safe_prefix >>
      reverse conj_tac >-
        (gen_tac >> rpt (FIRST
          [irule abi_args_entry_extends_bind >> conj_tac,
           irule abi_args_entry_extends_ignore_bind >> conj_tac,
           gen_tac, IF_CASES_TAC] >>
          simp[comp_return_def, cs_extends_refl, emit_op_labels,
               emit_void_labels, compile_alloc_buffer_labels,
               compile_storage_to_memory_labels, compile_transient_to_memory_labels,
               compile_imm_copy_to_memory_labels])) >> metis_tac[abi_args_entry_alloc_buffer])
  >- (qpat_x_assum `_ a = (x,b)` mp_tac >>
      map_every qid_spec_tac [`b`, `x`, `a`] >>
      ho_match_mp_tac abi_args_entry_safe_prefix >>
      reverse conj_tac >-
        (gen_tac >> rpt (FIRST
          [irule abi_args_entry_extends_bind >> conj_tac,
           irule abi_args_entry_extends_ignore_bind >> conj_tac,
           gen_tac, IF_CASES_TAC] >>
          simp[comp_return_def, cs_extends_refl, emit_op_labels,
               emit_void_labels, compile_alloc_buffer_labels,
               compile_storage_to_memory_labels, compile_transient_to_memory_labels,
               compile_imm_copy_to_memory_labels])) >> metis_tac[abi_args_entry_alloc_buffer])
  >> qpat_x_assum `_ a = (x,b)` mp_tac >>
      map_every qid_spec_tac [`b`, `x`, `a`] >>
      ho_match_mp_tac abi_args_entry_safe_prefix >>
     reverse conj_tac >-
        (gen_tac >> rpt (FIRST
          [irule abi_args_entry_extends_bind >> conj_tac,
           irule abi_args_entry_extends_ignore_bind >> conj_tac,
           gen_tac, IF_CASES_TAC] >>
          simp[comp_return_def, cs_extends_refl, emit_op_labels,
               emit_void_labels, compile_alloc_buffer_labels,
               compile_storage_to_memory_labels, compile_transient_to_memory_labels,
               compile_imm_copy_to_memory_labels])) >>
     rpt gen_tac >> strip_tac >>
     `CALLDATALOAD <> PHI` by simp[] >>
     drule_all abi_args_entry_emit_op >> simp[]
QED

Theorem abi_args_entry_unwrap_value:
  unwrap_value ce vv a = (x,b) ==>
  cs_extends a b /\ abi_args_entry_safe a b
Proof
  Cases_on `vv` >> simp[unwrap_value_def] >>
  rpt IF_CASES_TAC >> simp[]
  >- metis_tac[abi_args_entry_safe_return]
  >- metis_tac[abi_args_entry_ptr_load, abi_args_entry_safe_def] >>
  Cases_on `p.ptr_location` >> simp[] >>
  metis_tac[abi_args_entry_safe_return, abi_args_entry_ensure_in_memory]
QED

Theorem abi_args_entry_lower_value:
  (!a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !a x b. lower_value cfn ce ty e a = (x,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b
Proof
  strip_tac >> simp[lower_value_def] >>
  ho_match_mp_tac abi_args_entry_safe_bind >>
  metis_tac[abi_args_entry_unwrap_value]
QED

Theorem abi_args_entry_materialize_vv:
  compile_materialize_vv ce ty vv a = (x,b) ==>
  cs_extends a b /\
  (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  simp[compile_materialize_vv_def] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac abi_args_entry_emitted_bind >> conj_tac
  >- metis_tac[abi_args_entry_alloc_buffer] >>
  rpt gen_tac >> simp[comp_bind_def] >> pairarg_tac >> simp[] >>
  simp[comp_ignore_bind_def, comp_return_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule abi_args_entry_unwrap_value >> strip_tac >>
  irule cs_extends_trans >> goal_assum (drule_at Any) >>
  metis_tac[compile_store_memory_labels, pairTheory.SND]
QED

Theorem abi_args_entry_emitted_suffix_bind:
  (!a x b. m a = (x,b) ==> cs_extends a b /\ abi_args_entry_safe a b) /\
  (!x b y c. k x b = (y,c) ==> cs_extends b c /\
    (b.cs_current_insts = [] ==> abi_args_entry_emitted b c)) ==>
  !a y c. compileEnv$comp_bind m k a = (y,c) ==>
    cs_extends a c /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a c)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> Cases_on `m a` >>
  simp[comp_bind_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >>
  fs[abi_args_entry_safe_def] >>
  metis_tac[abi_args_entry_emitted_mono, abi_args_entry_emitted_code_eq,
            cs_extends_trans]
QED

Theorem abi_args_entry_attribute:
  (!a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !a x b. compile_attribute cfn ce rt ty e fld a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> simp[compile_attribute_def] >>
  ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac
  >- simp[] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  simp[comp_return_def, cs_extends_refl]
QED

Theorem abi_args_entry_emitted_prefix:
  (!a x b. m a = (x,b) ==> cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)) /\
  (!x b. cs_extends b (SND (k x b))) ==>
  !a y c. compileEnv$comp_bind m k a = (y,c) ==>
    cs_extends a c /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a c)
Proof
  strip_tac >> ho_match_mp_tac abi_args_entry_emitted_bind >>
  simp[] >> metis_tac[pairTheory.SND]
QED

Theorem abi_args_entry_dynarray_pop:
  compile_dynarray_pop ptr_op ws sz ic imm loc a = (x,b) ==>
  cs_extends a b /\
  (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  simp[compile_dynarray_pop_def] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- metis_tac[abi_args_entry_ptr_load] >>
  rpt (FIRST
    [irule abi_args_entry_extends_bind >> conj_tac,
     irule abi_args_entry_extends_ignore_bind >> conj_tac,
     gen_tac] >>
    simp[emit_op_labels, emit_void_labels, compile_ptr_store_labels])
QED

Theorem abi_args_entry_extends_result:
  (!a x b. m a = (x,b) ==> cs_extends a b) ==>
  !a. cs_extends a (SND (m a))
Proof
  strip_tac >> gen_tac >> Cases_on `m a` >> metis_tac[pairTheory.SND]
QED

Theorem abi_args_entry_safe_emitted_prefix:
  (!a x b. m a = (x,b) ==> cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)) /\
  (!x b. cs_extends b (SND (k x b))) ==>
  !a y c. compileEnv$comp_bind m k a = (y,c) ==>
    cs_extends a c /\ abi_args_entry_safe a c
Proof
  strip_tac >> drule abi_args_entry_emitted_prefix >>
  metis_tac[abi_args_entry_safe_def]
QED

Theorem abi_args_entry_struct_lit:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !fields ce ty buf off a x b.
    compile_struct_lit cfn ce ty fields buf off a = (x,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b
Proof
  strip_tac >> Induct >> rpt gen_tac
  >- simp[compile_struct_lit_def, comp_return_def, cs_extends_refl] >>
  PairCases_on `h` >> simp[compile_struct_lit_def] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
  >- metis_tac[] >>
  gen_tac >>
  `(!a x b. emit_op ADD [buf; Lit (n2w off)] a = (x,b) ==>
      cs_extends a b /\
      (a.cs_current_insts = [] ==> abi_args_entry_emitted a b))` by
    (rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
     simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  ho_match_mp_tac abi_args_entry_safe_emitted_prefix >> conj_tac
  >- simp[] >>
  rpt (FIRST
    [irule abi_args_entry_extends_bind >> conj_tac,
     irule abi_args_entry_extends_ignore_bind >> conj_tac,
     gen_tac] >> simp[compile_store_memory_labels]) >>
  irule abi_args_entry_extends_result >> metis_tac[abi_args_entry_unwrap_value]
QED

Theorem abi_args_entry_struct_lit_emitted:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce ty fld fields buf off a x b.
    compile_struct_lit cfn ce ty (fld::fields) buf off a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> rpt gen_tac >> PairCases_on `fld` >>
  simp[compile_struct_lit_def] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac
  >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  rpt (FIRST
    [irule abi_args_entry_extends_bind >> conj_tac,
     irule abi_args_entry_extends_ignore_bind >> conj_tac,
     gen_tac] >> simp[compile_store_memory_labels]) >>
  irule abi_args_entry_extends_result >>
  metis_tac[abi_args_entry_unwrap_value, abi_args_entry_struct_lit]
QED
