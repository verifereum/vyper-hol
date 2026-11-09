Theory exprSimAbiEncodeArgsEntryCall
Ancestors
  exprSimAbiEncodeArgsEntryValue exprSimAbiEncodeArgsEntryPrim
  exprLowering compileEnv context emitHelper exprSimAbiEncodeArgsEntry
  exprSimAbiEncodeArgsEntryCallbacks externalEntryShape

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

Theorem abi_args_entry_send:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty has_gas es d a vv b.
    compile_call cfn ce rt ty (Send has_gas) es d a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> ntac 4 gen_tac >> Cases
  >- (simp[compile_call_def] >> rpt gen_tac >> pairarg_tac >> simp[] >>
      strip_tac >> gvs[] >> `INVALID <> PHI` by simp[] >>
      metis_tac[fragExecTheory.cs_extends_emit_inst, abi_args_entry_emit_inst]) >>
  rename1 `addr_e::remaining` >> Cases_on `remaining`
  >- (simp[compile_call_def] >> rpt gen_tac >> pairarg_tac >> simp[] >>
      strip_tac >> gvs[] >> `INVALID <> PHI` by simp[] >>
      metis_tac[fragExecTheory.cs_extends_emit_inst, abi_args_entry_emit_inst]) >>
  rename1 `addr_e::val_e::gas_es` >> rpt gen_tac >> simp[compile_call_def] >>
  IF_CASES_TAC
  >- (pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
      `!ce ty e a x b. lower_value cfn ce ty e a = (x,b) ==>
         cs_extends a b /\ abi_args_entry_safe a b` by
        (rpt gen_tac >> metis_tac[abi_args_entry_lower_value]) >>
      `cs_extends a st1 /\ abi_args_entry_safe a st1` by metis_tac[] >>
      `cs_extends st1 st2 /\ abi_args_entry_safe st1 st2` by metis_tac[] >>
      `cs_extends a st2 /\ abi_args_entry_safe a st2` by
        metis_tac[cs_extends_trans, abi_args_entry_safe_trans] >>
      pairarg_tac >> simp[] >>
      `cs_extends st2 st2' /\ abi_args_entry_safe st2 st2'` by
        (Cases_on `gas_es` >> gvs[]
         >- simp[cs_extends_refl] >>
         Cases_on `t`
         >- (gvs[] >> metis_tac[]) >>
         Cases_on `has_gas` >> gvs[]) >>
      pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      `CALL <> PHI /\ ASSERT <> PHI` by simp[] >>
      drule_all abi_args_entry_emit_op >> strip_tac >>
      drule_all abi_args_entry_emit_void >> strip_tac >>
      gvs[abi_args_entry_safe_def] >>
      metis_tac[cs_extends_trans, abi_args_entry_emitted_mono,
                abi_args_entry_emitted_code_eq]) >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `INVALID <> PHI` by simp[] >>
  metis_tac[fragExecTheory.cs_extends_emit_inst, abi_args_entry_emit_inst]
QED

Theorem abi_args_entry_raw_revert_backend:
  !data a x b. compile_raw_revert data a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  gen_tac >> rewrite_tac[builtinSystemTheory.compile_raw_revert_def] >>
  ho_match_mp_tac abi_args_entry_emitted_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  gen_tac >> rpt gen_tac >> simp[comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  `ADD <> PHI` by simp[] >>
  drule_all abi_args_entry_emit_op >> strip_tac >>
  metis_tac[fragExecTheory.cs_extends_emit_inst, cs_extends_trans]
QED

Theorem abi_args_entry_raw_revert:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty es d a vv b.
    compile_call cfn ce rt ty RawRevert es d a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> ntac 3 gen_tac >> Cases
  >- (simp[compile_call_def] >> rpt gen_tac >> pairarg_tac >> simp[] >>
      strip_tac >> gvs[] >> `INVALID <> PHI` by simp[] >>
      metis_tac[fragExecTheory.cs_extends_emit_inst, abi_args_entry_emit_inst]) >>
  rename1 `data_e::rest` >> Cases_on `rest`
  >- (rpt gen_tac >> simp[compile_call_def] >> pairarg_tac >> simp[] >>
      `cs_extends a st1 /\ abi_args_entry_safe a st1` by
        metis_tac[abi_args_entry_lower_value] >>
      pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      drule abi_args_entry_raw_revert_backend >> strip_tac >>
      gvs[abi_args_entry_safe_def] >>
      metis_tac[cs_extends_trans, abi_args_entry_emitted_mono,
                abi_args_entry_emitted_code_eq]) >>
  simp[compile_call_def] >> rpt gen_tac >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> `INVALID <> PHI` by simp[] >>
  metis_tac[fragExecTheory.cs_extends_emit_inst, abi_args_entry_emit_inst]
QED

Theorem abi_args_entry_raw_log:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty es d a vv b.
    compile_call cfn ce rt ty RawLog es d a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> ntac 3 gen_tac >> Cases
  >- (simp[compile_call_def] >> rpt gen_tac >> pairarg_tac >> simp[] >>
      strip_tac >> gvs[] >> `INVALID <> PHI` by simp[] >>
      metis_tac[fragExecTheory.cs_extends_emit_inst, abi_args_entry_emit_inst]) >>
  rename1 `topics_e::rest` >> Cases_on `rest`
  >- (simp[compile_call_def] >> rpt gen_tac >> pairarg_tac >> simp[] >>
      strip_tac >> gvs[] >> `INVALID <> PHI` by simp[] >>
      metis_tac[fragExecTheory.cs_extends_emit_inst, abi_args_entry_emit_inst]) >>
  rename1 `topics_e::data_e::rest` >> Cases_on `rest`
  >- (rpt gen_tac >> simp[compile_call_def] >> pairarg_tac >> simp[] >>
      `cs_extends a st1 /\ abi_args_entry_safe a st1` by
        metis_tac[abi_args_entry_multi_exprs] >>
      `!ce ty e a x b. lower_value cfn ce ty e a = (x,b) ==>
         cs_extends a b /\ abi_args_entry_safe a b` by
        (rpt gen_tac >> metis_tac[abi_args_entry_lower_value]) >>
      IF_CASES_TAC >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
      pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[]
      >- (`cs_extends st1 st2 /\ abi_args_entry_safe st1 st2` by
            metis_tac[abi_args_entry_alloc_buffer, abi_args_entry_safe_def] >>
          `cs_extends st2 st3 /\ abi_args_entry_safe st2 st3` by metis_tac[] >>
          `MSTORE <> PHI` by simp[] >>
          drule_all abi_args_entry_emit_void >> strip_tac >>
          `cs_extends a st4 /\ abi_args_entry_safe a st4` by
            metis_tac[cs_extends_trans, abi_args_entry_safe_trans,
                      abi_args_entry_safe_def] >>
          `LOG <> PHI` by simp[] >>
          `st4.cs_current_insts = [] ==> abi_args_entry_emitted st4 b` by
            metis_tac[abi_args_entry_emit_inst] >>
          `cs_extends st4 b` by metis_tac[fragExecTheory.cs_extends_emit_inst] >>
          gvs[abi_args_entry_safe_def] >>
          metis_tac[cs_extends_trans, abi_args_entry_emitted_mono,
                    abi_args_entry_emitted_code_eq]) >>
      `cs_extends st1 st2 /\ abi_args_entry_safe st1 st2` by metis_tac[] >>
      `MLOAD <> PHI /\ ADD <> PHI` by simp[] >>
      `cs_extends st2 st3 /\
       (st2.cs_current_insts = [] ==> abi_args_entry_emitted st2 st3)` by
        metis_tac[abi_args_entry_emit_op] >>
      `cs_extends st3 st4 /\
       (st3.cs_current_insts = [] ==> abi_args_entry_emitted st3 st4)` by
        metis_tac[abi_args_entry_emit_op] >>
      `cs_extends a st4 /\ abi_args_entry_safe a st4` by
        metis_tac[cs_extends_trans, abi_args_entry_safe_trans,
                  abi_args_entry_safe_def] >>
      `LOG <> PHI` by simp[] >>
      `st4.cs_current_insts = [] ==> abi_args_entry_emitted st4 b` by
            metis_tac[abi_args_entry_emit_inst] >>
      `cs_extends st4 b` by metis_tac[fragExecTheory.cs_extends_emit_inst] >>
      gvs[abi_args_entry_safe_def] >>
      metis_tac[cs_extends_trans, abi_args_entry_emitted_mono,
                abi_args_entry_emitted_code_eq]) >>
  simp[compile_call_def] >> rpt gen_tac >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> `INVALID <> PHI` by simp[] >>
  metis_tac[fragExecTheory.cs_extends_emit_inst, abi_args_entry_emit_inst]
QED

Theorem abi_args_entry_raw_call:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty flags es d a vv b.
    compile_call cfn ce rt ty (RawCallTarget flags) es d a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> ntac 4 gen_tac >> Cases
  >- (simp[compile_call_def] >> rpt gen_tac >> pairarg_tac >> simp[] >>
      strip_tac >> gvs[] >> `INVALID <> PHI` by simp[] >>
      metis_tac[fragExecTheory.cs_extends_emit_inst, abi_args_entry_emit_inst]) >>
  rename1 `addr_e::rest` >> Cases_on `rest`
  >- (simp[compile_call_def] >> rpt gen_tac >> pairarg_tac >> simp[] >>
      strip_tac >> gvs[] >> `INVALID <> PHI` by simp[] >>
      metis_tac[fragExecTheory.cs_extends_emit_inst, abi_args_entry_emit_inst]) >>
  rename1 `addr_e::data_e::kw_es` >> rpt gen_tac >> simp[compile_call_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `!ce ty e a x b. lower_value cfn ce ty e a = (x,b) ==>
     cs_extends a b /\ abi_args_entry_safe a b` by
    (rpt gen_tac >> metis_tac[abi_args_entry_lower_value]) >>
  `cs_extends a st1 /\ abi_args_entry_safe a st1` by metis_tac[] >>
  `cs_extends st1 st2 /\ abi_args_entry_safe st1 st2` by metis_tac[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `cs_extends st4 st5` by metis_tac[abi_args_entry_ext_call_kwargs] >>
  pairarg_tac >> simp[] >>
  `cs_extends st5 st6` by
    (Cases_on `gas_opt` >> gvs[cs_extends_refl] >>
     `GAS <> PHI` by simp[] >> metis_tac[abi_args_entry_emit_op]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> Cases_on `flags.rcf_max_outsize = 0` >> gvs[] >>
  `cs_extends st6 st7` by
    metis_tac[externalEntryShapeTheory.compile_raw_call_outbuf_labels, pairTheory.SND] >>
  `cs_extends st7 b` by
    metis_tac[externalEntryShapeTheory.compile_raw_call_finish_labels, pairTheory.SND] >>
  `MLOAD <> PHI /\ ADD <> PHI` by simp[] >>
  `cs_extends st2 st3 /\
   (st2.cs_current_insts = [] ==> abi_args_entry_emitted st2 st3)` by
    metis_tac[abi_args_entry_emit_op] >>
  `cs_extends st3 st4` by metis_tac[abi_args_entry_emit_op] >>
  `cs_extends st3 b` by metis_tac[cs_extends_trans] >>
  `cs_extends a st2 /\ abi_args_entry_safe a st2` by
    metis_tac[cs_extends_trans, abi_args_entry_safe_trans] >>
  gvs[abi_args_entry_safe_def] >>
  metis_tac[cs_extends_trans, abi_args_entry_emitted_mono,
            abi_args_entry_emitted_code_eq]
QED

Theorem abi_args_entry_msg_data:
  !a x b. compile_msg_data_to_memory a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  rewrite_tac[builtinSystemTheory.compile_msg_data_to_memory_def] >>
  ho_match_mp_tac abi_args_entry_emitted_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  rpt gen_tac >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `cs_extends b cs'` by
    metis_tac[externalEntryShapeTheory.compile_alloc_dynamic_labels, pairTheory.SND] >>
  `CALLDATACOPY <> PHI` by simp[] >>
  drule_all abi_args_entry_emit_void >> strip_tac >>
  metis_tac[cs_extends_trans]
QED

Theorem abi_args_entry_raw_outbuf:
  !n a x b. compile_raw_call_outbuf n a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  gen_tac >> rewrite_tac[builtinSystemTheory.compile_raw_call_outbuf_def] >>
  IF_CASES_TAC >> simp[LET_THM] >>
  ho_match_mp_tac abi_args_entry_emitted_bind >>
  (conj_tac >- metis_tac[abi_args_entry_alloc_buffer]) >>
  rpt gen_tac >> simp[comp_bind_def, comp_return_def, cs_extends_refl] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `ADD <> PHI` by simp[] >> metis_tac[abi_args_entry_emit_op]
QED

Theorem abi_args_entry_raw_call_calldata:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty flags es d a vv b.
    compile_call cfn ce rt ty (RawCallCalldataTarget flags) es d a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> ntac 4 gen_tac >> Cases
  >- (simp[compile_call_def] >> rpt gen_tac >> pairarg_tac >> simp[] >>
      strip_tac >> gvs[] >> `INVALID <> PHI` by simp[] >>
      metis_tac[fragExecTheory.cs_extends_emit_inst, abi_args_entry_emit_inst]) >>
  rename1 `addr_e::kw_es` >> rpt gen_tac >> simp[compile_call_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `cs_extends a st1 /\ abi_args_entry_safe a st1` by
    metis_tac[abi_args_entry_lower_value] >>
  `cs_extends st1 st2 /\ abi_args_entry_safe st1 st2` by
    metis_tac[abi_args_entry_ext_call_kwargs] >>
  pairarg_tac >> simp[] >>
  `cs_extends st2 st3 /\ abi_args_entry_safe st2 st3` by
    (Cases_on `gas_opt` >> gvs[cs_extends_refl] >>
     `GAS <> PHI` by simp[] >>
     metis_tac[abi_args_entry_emit_op, abi_args_entry_safe_def]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> Cases_on `flags.rcf_max_outsize = 0` >> gvs[] >>
  `cs_extends st3 st4 /\
   (st3.cs_current_insts = [] ==> abi_args_entry_emitted st3 st4)` by
    metis_tac[abi_args_entry_raw_outbuf] >>
  `cs_extends st4 st5` by metis_tac[abi_args_entry_msg_data] >>
  `cs_extends st5 st6` by
    metis_tac[externalEntryShapeTheory.compile_raw_call_finish_labels, pairTheory.SND] >>
  `SETFMP <> PHI` by simp[] >>
  drule_all abi_args_entry_emit_void >> strip_tac >>
  `cs_extends st4 b` by metis_tac[cs_extends_trans] >>
  `cs_extends a st3 /\ abi_args_entry_safe a st3` by
    metis_tac[cs_extends_trans, abi_args_entry_safe_trans] >>
  gvs[abi_args_entry_safe_def] >>
  metis_tac[cs_extends_trans, abi_args_entry_emitted_mono,
            abi_args_entry_emitted_code_eq]
QED

Theorem abi_args_entry_external_backend:
  !ce addr vals tys memsz abisz mid retsz minsz retmem static value gas
   skip default defop rett def_ty enc dec a x b.
    compile_external_call_kwargs ce addr vals tys memsz abisz mid retsz minsz
      retmem static value gas skip default defop rett def_ty enc dec a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  ntac 20 gen_tac >> simp[compile_external_call_kwargs_def, LET_THM] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- metis_tac[abi_args_entry_alloc_buffer] >>
  rpt gen_tac >> qmatch_goalsub_abbrev_tac `SND (suffix b)` >>
  `cs_extends b (SND (suffix b)) /\
   EVERY (isPREFIX "@") (added_labels b (SND (suffix b)))` suffices_by simp[] >>
  simp[Abbr `suffix`] >>
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

Theorem abi_args_entry_extcall:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty static skip fname argtys rett opts es d a vv b.
    compile_call cfn ce rt ty (ExtCall static skip (fname,argtys,rett) opts)
      es d a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> ntac 9 gen_tac >> Cases
  >- (simp[compile_call_def] >> rpt gen_tac >> pairarg_tac >> simp[] >>
      strip_tac >> gvs[] >> `INVALID <> PHI` by simp[] >>
      metis_tac[fragExecTheory.cs_extends_emit_inst, abi_args_entry_emit_inst]) >>
  rename1 `addr_e::rest` >> rpt gen_tac >> simp[compile_call_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `cs_extends a st1 /\ abi_args_entry_safe a st1` by
    metis_tac[abi_args_entry_lower_value] >>
  `cs_extends st1 st2 /\ abi_args_entry_safe st1 st2` by
    metis_tac[abi_args_entry_multi_vvs] >>
  `cs_extends st2 st3 /\ abi_args_entry_safe st2 st3` by
    metis_tac[abi_args_entry_ext_call_kwargs] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `cs_extends st3 st5 /\ abi_args_entry_safe st3 st5` by
    (Cases_on `gas_opt` >> gvs[cs_extends_refl] >>
     `GAS <> PHI` by simp[] >>
     metis_tac[abi_args_entry_emit_op, abi_args_entry_safe_def]) >>
  pairarg_tac >> simp[] >> strip_tac >> Cases_on `rett = NoneT` >> gvs[] >>
  drule abi_args_entry_external_backend >> strip_tac >>
  `cs_extends a st5 /\ abi_args_entry_safe a st5` by
    metis_tac[cs_extends_trans, abi_args_entry_safe_trans] >>
  gvs[abi_args_entry_safe_def] >>
  metis_tac[cs_extends_trans, abi_args_entry_emitted_mono,
            abi_args_entry_emitted_code_eq]
QED

Theorem abi_args_entry_create_salt:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce opt a x b. compile_create_salt cfn ce opt a = (x,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b
Proof
  strip_tac >> gen_tac >> Cases >> simp[compile_create_salt_def]
  >- metis_tac[abi_args_entry_safe_return] >>
  ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
  >- metis_tac[abi_args_entry_lower_value] >>
  metis_tac[abi_args_entry_safe_return]
QED

Theorem abi_args_entry_create_ctor_tuple:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce es a x b. compile_create_ctor_tuple cfn ce es a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> ntac 2 gen_tac >> simp[compile_create_ctor_tuple_def] >>
  ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac
  >- metis_tac[abi_args_entry_multi_vvs] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- metis_tac[abi_args_entry_alloc_buffer] >>
  rpt gen_tac >> simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >>
  metis_tac[compile_extcall_store_values_labels, pairTheory.SND]
QED
