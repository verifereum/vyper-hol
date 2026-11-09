Theory exprSimAbiEncodeArgsEntryCall
Ancestors
  exprSimAbiEncodeArgsEntryValue exprSimAbiEncodeArgsEntryPrim
  exprLowering compileEnv context emitHelper exprSimAbiEncodeArgsEntry

Theorem abi_args_entry_multi_vvs:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !es ce a vs b. compile_multi_vvs cfn ce es a = (vs,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b
Proof
  strip_tac >> Induct >> simp[compile_multi_vvs_def]
  >- metis_tac[abi_args_entry_safe_return] >>
  ntac 2 gen_tac >> ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
  >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_safe_bind >>
  metis_tac[abi_args_entry_safe_return]
QED

Theorem abi_args_entry_multi_exprs:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !es ce a vs b. compile_multi_exprs cfn ce es a = (vs,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b
Proof
  strip_tac >> Induct >> simp[compile_multi_exprs_def]
  >- metis_tac[abi_args_entry_safe_return] >>
  ntac 2 gen_tac >> ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
  >- (ho_match_mp_tac abi_args_entry_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac abi_args_entry_safe_bind >>
  metis_tac[abi_args_entry_safe_return]
QED

Theorem abi_args_entry_ext_call_kwarg:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt k e a x b. compile_ext_call_kwarg cfn ce rt k e a = (x,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b
Proof
  strip_tac >> ntac 4 gen_tac >> simp[compile_ext_call_kwarg_def] >>
  IF_CASES_TAC >> simp[] >>
  ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
  >- metis_tac[]
  >- (gen_tac >> ho_match_mp_tac abi_args_entry_safe_bind >>
      metis_tac[abi_args_entry_materialize_vv, abi_args_entry_safe_def,
                abi_args_entry_safe_return])
  >- (ho_match_mp_tac abi_args_entry_lower_value >> metis_tac[]) >>
  metis_tac[abi_args_entry_safe_return]
QED

Theorem abi_args_entry_ext_call_kwargs:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ks es ce rt a x b. compile_ext_call_kwargs cfn ce rt ks es a = (x,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b
Proof
  strip_tac >> Induct
  >- (simp[compile_ext_call_kwargs_def] >>
      metis_tac[abi_args_entry_safe_return]) >>
  gen_tac >> Cases_on `es` >> simp[compile_ext_call_kwargs_def]
  >- metis_tac[abi_args_entry_safe_return] >>
  ntac 2 gen_tac >> ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
  >- metis_tac[abi_args_entry_ext_call_kwarg] >>
  Cases >> simp[] >> ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
  >- metis_tac[] >>
  qx_gen_tac `kw_result` >> PairCases_on `kw_result` >> simp[] >>
  metis_tac[abi_args_entry_safe_return]
QED

Theorem abi_args_entry_lower_value_emitted:
  (!a vv b. cfn ce ty e a = (vv,b) ==> cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)) ==>
  !a x b. lower_value cfn ce ty e a = (x,b) ==> cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> simp[lower_value_def] >>
  ho_match_mp_tac abi_args_entry_emitted_bind >> conj_tac
  >- metis_tac[] >> metis_tac[abi_args_entry_unwrap_value]
QED

Theorem abi_args_entry_multi_vvs_emitted:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) /\
  (!ce e a vv b. P e /\ cfn ce (expr_type e) e a = (vv,b) /\
    a.cs_current_insts = [] ==> abi_args_entry_emitted a b) ==>
  !es ce a vs b. EXISTS P es /\ compile_multi_vvs cfn ce es a = (vs,b) /\
    a.cs_current_insts = [] ==> abi_args_entry_emitted a b
Proof
  strip_tac >> Induct >> simp[compile_multi_vvs_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ a = (vs,b)` mp_tac >>
  simp[comp_bind_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `cfn ce (expr_type h) h a = (vv,sm)` >>
  `cs_extends a sm /\ abi_args_entry_safe a sm` by metis_tac[] >>
  `cs_extends sm b /\ abi_args_entry_safe sm b` by
    metis_tac[abi_args_entry_multi_vvs] >>
  Cases_on `P h`
  >- metis_tac[abi_args_entry_emitted_mono] >>
  gvs[abi_args_entry_safe_def] >>
  metis_tac[abi_args_entry_emitted_mono, abi_args_entry_emitted_code_eq]
QED

Theorem abi_args_entry_multi_exprs_emitted:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) /\
  (!ce e a vv b. P e /\ cfn ce (expr_type e) e a = (vv,b) /\
    a.cs_current_insts = [] ==> abi_args_entry_emitted a b) ==>
  !es ce a vs b. EXISTS P es /\ compile_multi_exprs cfn ce es a = (vs,b) /\
    a.cs_current_insts = [] ==> abi_args_entry_emitted a b
Proof
  strip_tac >> Induct >> simp[compile_multi_exprs_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ a = (vs,b)` mp_tac >>
  simp[comp_bind_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `lower_value cfn ce (expr_type h) h a = (v,sm)` >>
  `cs_extends a sm /\ abi_args_entry_safe a sm` by
    metis_tac[abi_args_entry_lower_value] >>
  `cs_extends sm b /\ abi_args_entry_safe sm b` by
    metis_tac[abi_args_entry_multi_exprs] >>
  Cases_on `P h`
  >- (`abi_args_entry_emitted a sm` suffices_by
        metis_tac[abi_args_entry_emitted_mono] >>
      qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
      simp[lower_value_def, comp_bind_def] >> pairarg_tac >> simp[] >>
      strip_tac >> drule abi_args_entry_unwrap_value >> strip_tac >>
      metis_tac[abi_args_entry_emitted_mono]) >>
  gvs[abi_args_entry_safe_def] >>
  metis_tac[abi_args_entry_emitted_mono, abi_args_entry_emitted_code_eq]
QED

Theorem abi_args_entry_stage_intcall_args:
  !vals ce flags tys a ops b.
    compile_stage_intcall_args ce vals flags tys a = (ops,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b
Proof
  Induct >> simp[compile_stage_intcall_args_def]
  >- metis_tac[abi_args_entry_safe_return] >>
  ntac 2 gen_tac >> namedCases_on `flags` ["", "flag flags"]
  >- (simp[compile_stage_intcall_args_def] >>
      ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
      >- metis_tac[abi_args_entry_unwrap_value] >>
      gen_tac >> ho_match_mp_tac abi_args_entry_safe_bind >>
      metis_tac[abi_args_entry_safe_return]) >>
  namedCases_on `tys` ["", "ty tys"]
  >- (simp[compile_stage_intcall_args_def] >>
      ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
      >- metis_tac[abi_args_entry_unwrap_value] >>
      gen_tac >> ho_match_mp_tac abi_args_entry_safe_bind >>
      metis_tac[abi_args_entry_safe_return]) >>
  Cases_on `flag` >> simp[compile_stage_intcall_args_def] >>
  ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
  >- metis_tac[abi_args_entry_unwrap_value]
  >- (gen_tac >> ho_match_mp_tac abi_args_entry_safe_bind >>
      metis_tac[abi_args_entry_safe_return])
  >- metis_tac[abi_args_entry_unwrap_value] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_safe_emitted_prefix >> conj_tac
  >- metis_tac[abi_args_entry_alloc_buffer] >>
  rpt (FIRST [irule abi_args_entry_extends_bind >> conj_tac,
              irule abi_args_entry_extends_ignore_bind >> conj_tac,
              gen_tac, IF_CASES_TAC] >>
       simp[comp_return_def, cs_extends_refl,
            externalEntryShapeTheory.emit_void_labels,
            externalEntryShapeTheory.compile_store_bytestring_labels,
            externalEntryShapeTheory.compile_store_memory_labels,
            externalEntryShapeTheory.compile_stage_intcall_args_labels])
QED

Theorem abi_args_entry_emit_void:
  op <> PHI /\ emit_void op args a = (x,b) ==> cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  simp[emit_void_def, fresh_id_def, emit_def, comp_bind_def] >>
  rw[] >> simp[cs_extends_def, abi_args_entry_emitted_def,
               venomInstTheory.mk_inst_def] >> metis_tac[]
QED

Theorem abi_args_entry_fresh_vars:
  !n a xs b. fresh_vars n a = (xs,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b
Proof
  Induct >> simp[fresh_vars_def]
  >- metis_tac[abi_args_entry_safe_return] >>
  ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
  >- (rpt gen_tac >> simp[fresh_var_def] >> rw[] >>
      simp[cs_extends_def, abi_args_entry_safe_def]) >>
  gen_tac >> ho_match_mp_tac abi_args_entry_safe_bind >>
  metis_tac[abi_args_entry_safe_return]
QED

Theorem abi_args_entry_emit_multi_op:
  op <> PHI ==> !a xs b. emit_multi_op op args n a = (xs,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> simp[emit_multi_op_def, comp_ignore_bind_def] >>
  ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac
  >- metis_tac[abi_args_entry_fresh_vars] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_bind >> conj_tac
  >- metis_tac[fragExecTheory.cs_extends_emit_inst, abi_args_entry_emit_inst] >>
  simp[comp_return_def, cs_extends_refl]
QED

Theorem abi_args_entry_intcall:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty fid es d a vv b.
    compile_call cfn ce rt ty (IntCall fid) es d a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> rpt gen_tac >> simp[compile_call_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `cs_extends a st1 /\ abi_args_entry_safe a st1` by
    metis_tac[abi_args_entry_multi_vvs] >>
  pairarg_tac >> simp[] >>
  `cs_extends st1 st2 /\ abi_args_entry_safe st1 st2` by
    (qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
     IF_CASES_TAC
     >- (simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
         metis_tac[abi_args_entry_alloc_buffer, abi_args_entry_safe_def]) >>
     IF_CASES_TAC
     >- (simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
         metis_tac[abi_args_entry_alloc_buffer, abi_args_entry_safe_def]) >>
     simp[] >> strip_tac >> gvs[] >> simp[cs_extends_refl]) >>
  pairarg_tac >> simp[] >>
  `cs_extends st2 st3 /\ abi_args_entry_safe st2 st3` by
    metis_tac[abi_args_entry_stage_intcall_args] >>
  `cs_extends a st3 /\ abi_args_entry_safe a st3` by
    metis_tac[cs_extends_trans, abi_args_entry_safe_trans] >>
  strip_tac >>
  `cs_extends st3 b /\
   (st3.cs_current_insts = [] ==> abi_args_entry_emitted st3 b)` suffices_by
    (strip_tac >> gvs[abi_args_entry_safe_def] >>
     metis_tac[cs_extends_trans, abi_args_entry_emitted_mono,
               abi_args_entry_emitted_code_eq]) >>
  qpat_x_assum `(if _ then _ else _) = (vv,b)` mp_tac >>
  IF_CASES_TAC >> Cases_on `return_buf` >> simp[] >>
  pairarg_tac >> simp[]
  >- (strip_tac >> gvs[] >> `INVOKE <> PHI` by simp[] >>
      metis_tac[abi_args_entry_emit_op])
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      `INVOKE <> PHI` by simp[] >>
      drule_all abi_args_entry_emit_multi_op >> strip_tac >>
      `cs_extends st4 b` by
        metis_tac[externalEntryShapeTheory.store_multi_results_labels,
                  pairTheory.SND] >>
      metis_tac[cs_extends_trans, abi_args_entry_emitted_mono])
  >- (strip_tac >> gvs[] >> `INVOKE <> PHI` by simp[] >>
      metis_tac[abi_args_entry_emit_void]) >>
  strip_tac >> gvs[] >> `INVOKE <> PHI` by simp[] >>
  metis_tac[abi_args_entry_emit_void]
QED
