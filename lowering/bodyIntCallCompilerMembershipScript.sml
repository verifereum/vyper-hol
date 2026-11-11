Theory bodyIntCallCompilerMembership
Ancestors
  bodyIntCallCompilerContext bodyIntCallCompilerFloor bodyIntCallCompilerEmit
  bodyIntCallCompilerInterval exprLowering compileEnv

Theorem intcall_interval_membership_in:
  !needle es k a. k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_list_membership_in needle es a))
Proof
  ho_match_mp_tac compile_list_membership_in_ind >> rpt conj_tac >>
  rpt gen_tac >> rpt strip_tac >>
  simp[Once compile_list_membership_in_def, intcall_interval_return,
       intcall_interval_emit_op] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op])
QED

Theorem intcall_interval_membership_notin:
  !needle es k a. k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_list_membership_notin needle es a))
Proof
  ho_match_mp_tac compile_list_membership_notin_ind >> rpt conj_tac >>
  rpt gen_tac >> rpt strip_tac >>
  simp[Once compile_list_membership_notin_def, intcall_interval_return] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op])
QED

Theorem intcall_interval_membership_loop:
  (!v a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (loader v a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_array_membership_loop needle arr len sz off loader isin a))
Proof
  strip_tac >> Cases_on `off > 0` >> Cases_on `isin` >>
  simp[compile_array_membership_loop_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_inst,
            intcall_interval_new_block, intcall_interval_fresh_var,
            intcall_interval_fresh_label, intcall_interval_return])
QED

Theorem intcall_interval_var_membership:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_var_array_membership cenv needle vv ty isin a))
Proof
  strip_tac >> Cases_on `ty` >>
  simp[compile_var_array_membership_def, comp_ignore_bind_def,
       intcall_interval_membership_loop, intcall_interval_ptr_load,
       intcall_interval_return] >>
  rpt (rpt strip_tac >>
       simp[intcall_interval_return, intcall_interval_ptr_load,
            intcall_interval_membership_loop, intcall_interval_emit_op,
            intcall_interval_emit_inst] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_membership_loop, intcall_interval_ptr_load,
            intcall_interval_emit_op, intcall_interval_emit_inst,
            intcall_interval_return]) >>
  rename1 `case bnd of Fixed _ => _ | Dynamic _ => _` >>
  Cases_on `bnd` >> simp[] >>
  rpt (rpt strip_tac >>
       simp[intcall_interval_return, intcall_interval_ptr_load,
            intcall_interval_membership_loop, intcall_interval_emit_op,
            intcall_interval_emit_inst] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_membership_loop, intcall_interval_ptr_load,
            intcall_interval_emit_op, intcall_interval_emit_inst,
            intcall_interval_return])
QED
