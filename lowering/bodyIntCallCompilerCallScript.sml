Theory bodyIntCallCompilerCall
Ancestors
  bodyIntCallCompilerAggregate bodyIntCallCompilerUniversalAggregate
  bodyIntCallCompilerCallRoots
  bodyIntCallCompilerExternal bodyIntCallCompilerRawSystem
  bodyIntCallCompilerCreatePipeline bodyIntCallCompilerStaging
  bodyIntCallCompilerUniversal bodyIntCallCompilerContext
  bodyIntCallCompilerFloor bodyIntCallCompilerEmit bodyIntCallCompilerInterval
  exprLowering compileEnv

Theorem intcall_interval_call_internal:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_call cfn ce rt ty (IntCall fid) es dflt a))
Proof
  strip_tac >> Cases_on `ce.ce_func_info (nsid_to_string fid)` >>
  rename1 `(_, finfo)` >> PairCases_on `finfo` >>
  simp[compile_call_def, comp_ignore_bind_def] >>
  irule intcall_interval_pair_bind_floor >> simp[intcall_interval_multi_vvs_floor] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> simp[] >>
  rpt (ho_match_mp_tac intcall_interval_pair_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_stage_intcall_args,
            intcall_interval_emit_multi_op, intcall_interval_emit_void,
            intcall_interval_store_multi_results] >>
       rpt strip_tac >> simp[intcall_compiler_interval_refl]) >>
  Cases_on `return_buf` >> simp[] >>
  rpt (ho_match_mp_tac intcall_interval_pair_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_emit_op,
            intcall_interval_emit_multi_op, intcall_interval_store_multi_results] >>
       rpt strip_tac >> simp[intcall_compiler_interval_refl]) >>
  simp[intcall_compiler_interval_refl]
QED

Theorem intcall_interval_call_external:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_call cfn ce rt ty (ExtCall sta skip sig opts) es dflt a))
Proof
  strip_tac >> PairCases_on `sig` >> Cases_on `es` >>
  simp[compile_call_def, intcall_interval_emit_inst] >>
  rpt (ho_match_mp_tac intcall_interval_pair_bind_floor >>
       simp[intcall_interval_emit_inst, intcall_compiler_interval_refl,
            intcall_interval_lower_value, intcall_interval_multi_vvs_floor,
            bodyIntCallCompilerExtOperandsTheory.intcall_interval_ext_call_kwargs,
            pairTheory.FORALL_PROD] >> rpt strip_tac >> simp[]) >>
  rename1 `case default_opt of NONE => (F,Lit 0w,_) | SOME (d,dt) => (T,d,dt)` >>
  Cases_on `default_opt`
  >- (simp[] >>
      qmatch_goalsub_rename_tac `case gas_opt of NONE => emit_op GAS [] _ | SOME g => (g,_)` >>
      Cases_on `gas_opt` >> simp[] >>
      rpt (ho_match_mp_tac intcall_interval_pair_bind_floor >>
           simp[intcall_interval_emit_op, intcall_interval_external_call_kwargs] >>
           rpt strip_tac >> simp[]) >>
      IF_CASES_TAC >> simp[intcall_compiler_interval_refl]) >>
  rename1 `SOME dp` >> PairCases_on `dp` >> simp[] >>
  qmatch_goalsub_rename_tac `case gas_opt of NONE => emit_op GAS [] _ | SOME g => (g,_)` >>
  Cases_on `gas_opt` >> simp[] >>
  rpt (ho_match_mp_tac intcall_interval_pair_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_external_call_kwargs] >>
       rpt strip_tac >> simp[]) >>
  IF_CASES_TAC >> simp[intcall_compiler_interval_refl]
QED

Theorem intcall_interval_call_raw:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_call cfn ce rt ty (RawCallTarget rcf) es dflt a))
Proof
  strip_tac >> namedCases_on `es` ["", "addr_e rest"]
  >- (simp[compile_call_def] >> ho_match_mp_tac intcall_interval_pair_bind_floor >>
      simp[intcall_interval_emit_inst, intcall_compiler_interval_refl]) >>
  Cases_on `rest` >> simp[compile_call_def] >>
  rpt (ho_match_mp_tac intcall_interval_pair_bind_floor >>
       simp[intcall_interval_emit_inst, intcall_compiler_interval_refl,
            intcall_interval_lower_value, intcall_interval_emit_op,
            bodyIntCallCompilerExtOperandsTheory.intcall_interval_ext_call_kwargs,
            pairTheory.FORALL_PROD] >> rpt strip_tac >> simp[]) >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[intcall_interval_emit_op,
       intcall_interval_raw_call_outbuf, intcall_interval_raw_call_finish,
       intcall_compiler_interval_refl, pairTheory.FORALL_PROD] >>
       rpt (ho_match_mp_tac intcall_interval_pair_bind_floor >>
            simp[intcall_interval_raw_call_outbuf, intcall_interval_raw_call_finish,
                 intcall_interval_emit_op, pairTheory.FORALL_PROD] >>
            rpt strip_tac >> simp[intcall_compiler_interval_refl])) >>
  simp[intcall_interval_raw_call_outbuf]
QED

Theorem intcall_interval_call_calldata:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_call cfn ce rt ty (RawCallCalldataTarget rcf) es dflt a))
Proof
  strip_tac >> Cases_on `es` >> simp[compile_call_def] >>
  rpt (ho_match_mp_tac intcall_interval_pair_bind_floor >>
       simp[intcall_interval_emit_inst, intcall_compiler_interval_refl,
            intcall_interval_lower_value,
            bodyIntCallCompilerExtOperandsTheory.intcall_interval_ext_call_kwargs,
            pairTheory.FORALL_PROD] >> rpt strip_tac >> simp[]) >>
  simp[intcall_interval_raw_call_outbuf, intcall_interval_raw_call_finish,
       intcall_interval_msg_data_to_memory, intcall_interval_emit_void] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[intcall_interval_emit_op,
       intcall_interval_raw_call_outbuf, intcall_interval_raw_call_finish,
       intcall_interval_msg_data_to_memory, intcall_interval_emit_void,
       intcall_compiler_interval_refl, pairTheory.FORALL_PROD] >>
       rpt (ho_match_mp_tac intcall_interval_pair_bind_floor >>
            simp[intcall_interval_raw_call_outbuf, intcall_interval_raw_call_finish,
                 intcall_interval_msg_data_to_memory, intcall_interval_emit_void,
                 intcall_interval_emit_op, pairTheory.FORALL_PROD] >>
            rpt strip_tac >> simp[intcall_compiler_interval_refl])) >>
  simp[intcall_interval_raw_call_outbuf, intcall_interval_msg_data_to_memory,
       intcall_interval_emit_void, intcall_interval_raw_call_finish]

QED
