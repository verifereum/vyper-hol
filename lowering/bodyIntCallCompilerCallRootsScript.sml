Theory bodyIntCallCompilerCallRoots
Ancestors
  bodyIntCallCompilerUniversalAggregate bodyIntCallCompilerAggregate
  bodyIntCallCompilerContext bodyIntCallCompilerFloor bodyIntCallCompilerEmit
  bodyIntCallCompilerInterval emitHelper exprLowering compileEnv

Theorem intcall_interval_emit_multi_op:
  opc <> ALLOCA /\ k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (emit_multi_op opc ops n a))
Proof
  strip_tac >> simp[emit_multi_op_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_fresh_vars, intcall_interval_emit_inst,
            intcall_interval_return])
QED

Theorem intcall_interval_store_multi_results:
  !ops off a. k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (store_multi_results buf ops off a))
Proof
  Induct >> simp[store_multi_results_def, intcall_interval_return] >>
  rpt strip_tac >> simp[comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void])
QED

Theorem intcall_interval_dynarray_pop:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_dynarray_pop bop ws sz ctor imm loc a))
Proof
  strip_tac >> simp[compile_dynarray_pop_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_ptr_load, intcall_interval_ptr_store,
            intcall_interval_emit_op, intcall_interval_emit_void])
QED

Theorem intcall_interval_get_target_ptr_all:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !bt a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (compile_get_target_ptr cfn cenv bt a))
Proof
  strip_tac >> measureInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> rpt strip_tac >>
  simp[Once compile_get_target_ptr_def]
  >- (rename1 `FLOOKUP cenv.ce_vars id` >>
      Cases_on `FLOOKUP cenv.ce_vars id` >> simp[intcall_interval_return] >>
      rename1 `FLOOKUP cenv.ce_vars id = SOME vl` >>
      Cases_on `vl` >> simp[intcall_interval_return])
  >- (rename1 `FLOOKUP cenv.ce_module_vars nsid` >>
      Cases_on `FLOOKUP cenv.ce_module_vars nsid` >> simp[intcall_interval_return] >>
      rename1 `FLOOKUP cenv.ce_module_vars nsid = SOME vl` >>
      Cases_on `vl` >> simp[intcall_interval_return]) >>
  irule intcall_interval_bind_floor >> reverse conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  simp[pairTheory.FORALL_PROD] >>
  map_every qx_gen_tac [`bop`, `locopt`, `ptopt`, `a'`] >> strip_tac
  >~ [`emit_op ADD _`]
  >- (rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
           simp[intcall_interval_emit_op, intcall_interval_return])) >>
  namedCases_on `ptopt` ["", "pt"] >> simp[]
  >- (rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
           simp[intcall_interval_lower_value, intcall_interval_array_subscript,
                intcall_interval_ptr_load, intcall_interval_return])) >>
  Cases_on `pt` >> simp[]
  >- (rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
           simp[intcall_interval_lower_value, intcall_interval_mapping_subscript,
                intcall_interval_return]) >>
      IF_CASES_TAC >> simp[intcall_interval_keccak_key, intcall_interval_return] >>
      rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
           simp[intcall_interval_mapping_subscript, intcall_interval_return])) >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_lower_value, intcall_interval_array_subscript,
            intcall_interval_ptr_load, intcall_interval_return])
QED
