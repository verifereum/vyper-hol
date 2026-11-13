Theory ctorDeployMemoryRunMemEntryPhaseAdapters
Ancestors
  ctorDeployMemoryRunMemEntryEntryPhi ctorDeployMemoryRunMemEntryEndpoint
  ctorDeployMemoryRunMemEntryLabel abiDecoderPhi ctorRegisterArgs fragExec
  context emitHelper compilerFirstEmission rich_list list compileEnv
  venomInst venomExecSemantics compileVyper vyperCompiler
  ctorDeployMemoryRunMemPrefixLayout

Theorem ctor_phase_pay_appends[local]:
  cs_appends (if pay then comp_return () else
    comp_bind (emit_op CALLVALUE []) (\cv.
      comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv])))
Proof
  Cases_on `pay` >> simp[cs_appends_return] >>
  irule cs_appends_bind >> simp[cs_appends_emit_helpers] >> gen_tac >>
  irule cs_appends_bind >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_phase_extends:
  (if pay then comp_return () else
    comp_bind (emit_op CALLVALUE []) (\cv.
      comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv])))
    (initial_compile_state "__deploy") = ((),st_pay) /\
  (if cap > 0 then comp_bind (compile_fixed_region_with_id cap)
    (\r. comp_return (SND r).buf_operand) else comp_return (Lit 0w))
    st_pay = (imm,st1) /\
  compile_register_constructor_args ce args 0 0 st1 = (ce1,st2) /\
  (if nr then compile_nonreentrant_lock nkey ut F else comp_return ()) st2 = ((),st3) /\
  fresh_label "ctor_exit" st3 = (exit_lbl,sa) ==>
  cs_extends (initial_compile_state "__deploy") st_pay /\
  cs_extends st_pay st1 /\ cs_extends st1 st2 /\
  cs_extends st2 st3 /\ cs_extends st3 sa
Proof
  strip_tac >> rpt conj_tac
  >- metis_tac[ctor_phase_pay_appends, cs_appends_def]
  >- (Cases_on `cap > 0` >> gvs[comp_return_def, cs_extends_refl] >>
      qpat_x_assum `comp_bind _ _ st_pay = _` mp_tac >>
      simp[comp_bind_def, comp_return_def] >> pairarg_tac >> simp[] >>
      metis_tac[ctor_prefix_fixed_appends, cs_appends_def])
  >- metis_tac[ctor_registration_extends]
  >- (Cases_on `nr` >> gvs[comp_return_def] >>
      metis_tac[ctor_prefix_lock_appends, cs_appends_def, cs_extends_refl]) >>
  metis_tac[cs_appends_prims, cs_appends_def]
QED

Theorem ctor_phase_code_split:
  cs_extends initial st_pay /\ cs_extends st_pay st1 /\
  cs_extends st1 st2 /\ cs_extends st2 st3 /\ cs_extends st3 sa /\
  fn_has_code initial sa func ==>
  fn_has_code initial st_pay func /\ fn_has_code st_pay st1 func /\
  fn_has_code st1 st2 func /\ fn_has_code st2 st3 func /\
  fn_has_code st2 sa func
Proof
  strip_tac >>
  `cs_extends st2 sa` by metis_tac[cs_extends_trans] >>
  `cs_extends st1 sa` by metis_tac[cs_extends_trans] >>
  `cs_extends st_pay sa` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  `fn_has_code st_pay sa func` by metis_tac[fn_has_code_split] >>
  `fn_has_code st1 sa func` by metis_tac[fn_has_code_split] >>
  `fn_has_code st2 sa func` by metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]
QED

Theorem ctor_phase_lock_phi:
  !nkey ut st. abi_decoder_phi st (SND (compile_nonreentrant_lock nkey ut F st))
Proof
  rpt gen_tac >> simp[compile_nonreentrant_lock_def] >>
  Cases_on `ut` >> simp[] >>
  rpt (ho_match_mp_tac abi_decoder_phi_bind >> conj_tac
    >- simp[abi_decoder_phi_emit_op] >> rpt gen_tac) >>
  ho_match_mp_tac abi_decoder_phi_ignore_bind >> conj_tac
  >- simp[abi_decoder_phi_emit_void] >> simp[abi_decoder_phi_emit_void]
QED

Theorem ctor_phase_phi_backwards:
  cs_extends st last /\ abi_decoder_phi st last /\
  phi_prefix_length st.cs_current_insts = 0 /\ fn_has_code st last func /\
  (!bb. lookup_block last.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  !bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  `abi_decoder_phi_safe st.cs_blocks st` by
    (simp[abi_decoder_phi_safe_def] >> qexists `[]` >> simp[]) >>
  `abi_decoder_phi_safe st.cs_blocks last` by
    metis_tac[abi_decoder_phi_def] >>
  gvs[cs_extends_def, abi_decoder_phi_safe_def] >>
  Cases_on `new = []` >> gvs[] >>
  `emitted_blocks st last = new` by
    (irule emitted_blocks_append >> simp[]) >>
  gvs[fn_has_code_def, EVERY_MEM] >> rpt strip_tac >>
  `MEM (LAST (emitted_blocks st last)) (emitted_blocks st last)` by
    simp[MEM_LAST_NOT_NIL] >>
  metis_tac[optionTheory.SOME_11]
QED

Theorem ctor_phase_fresh_label_cursor:
  fresh_label "ctor_exit" st3 = (exit_lbl,sa) ==>
  st3.cs_current_bb = sa.cs_current_bb /\
  LENGTH st3.cs_current_insts = LENGTH sa.cs_current_insts
Proof
  simp[fresh_label_def, comp_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem ctor_phase_registration_phi:
  (if nr then compile_nonreentrant_lock nkey ut F else comp_return ()) st2 = ((),st3) /\
  fresh_label "ctor_exit" st3 = (exit_lbl,sa) /\
  cs_extends st2 st3 /\ cs_extends st3 sa /\
  phi_prefix_length st2.cs_current_insts = 0 /\ fn_has_code st2 sa func /\
  (!bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  !bb. lookup_block st2.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  `abi_decoder_phi st2 st3` by
    (Cases_on `nr` >> gvs[comp_return_def] >>
     metis_tac[ctor_phase_lock_phi, abi_decoder_phi_refl, pairTheory.SND]) >>
  `abi_decoder_phi st3 sa` by
    metis_tac[abi_decoder_phi_fresh_label, pairTheory.SND] >>
  `cs_extends st2 sa` by metis_tac[cs_extends_trans] >>
  `abi_decoder_phi st2 sa` by metis_tac[abi_decoder_phi_trans] >>
  metis_tac[ctor_phase_phi_backwards]
QED

Theorem ctor_phase_fixed_phi[local]:
  !cap st. abi_decoder_phi st (SND (compile_fixed_region_with_id cap st))
Proof
  simp[compile_fixed_region_with_id_def, comp_bind_def, comp_ignore_bind_def,
    fresh_id_def, fresh_var_def, comp_return_def, emit_def,
    abi_decoder_phi_def, abi_decoder_phi_safe_def] >> rpt strip_tac >>
  irule abi_decoder_phi_append >> simp[phi_prefix_length_def, mk_inst_def]
QED

Theorem ctor_phase_pay_phi[local]:
  !pay st. abi_decoder_phi st
    (SND ((if pay then comp_return () else
      comp_bind (emit_op CALLVALUE []) (\cv.
        comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv]))) st))
Proof
  rpt gen_tac >> Cases_on `pay` >> simp[abi_decoder_phi_return] >>
  ho_match_mp_tac abi_decoder_phi_bind >> conj_tac
  >- simp[abi_decoder_phi_emit_op] >> rpt gen_tac >>
  ho_match_mp_tac abi_decoder_phi_bind >> conj_tac
  >- simp[abi_decoder_phi_emit_op] >> simp[abi_decoder_phi_emit_void]
QED

Theorem ctor_phase_imm_phi[local]:
  !cap st. abi_decoder_phi st
    (SND ((if cap > 0 then comp_bind (compile_fixed_region_with_id cap)
      (\r. comp_return (SND r).buf_operand) else comp_return (Lit 0w)) st))
Proof
  rpt gen_tac >> IF_CASES_TAC >> simp[abi_decoder_phi_return] >>
  ho_match_mp_tac abi_decoder_phi_bind >>
  simp[ctor_phase_fixed_phi, abi_decoder_phi_return]
QED

Theorem ctor_phase_registration_head_phi:
  (if pay then comp_return () else
    comp_bind (emit_op CALLVALUE []) (\cv.
      comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv])))
    (initial_compile_state "__deploy") = ((),st_pay) /\
  (if cap > 0 then comp_bind (compile_fixed_region_with_id cap)
    (\r. comp_return (SND r).buf_operand) else comp_return (Lit 0w))
    st_pay = (imm,st1) /\
  compile_register_constructor_args ce args 0 0 st1 = (ce1,st2) ==>
  phi_prefix_length st2.cs_current_insts = 0
Proof
  strip_tac >>
  `abi_decoder_phi (initial_compile_state "__deploy") st_pay` by
    metis_tac[ctor_phase_pay_phi, pairTheory.SND] >>
  `abi_decoder_phi st_pay st1` by metis_tac[ctor_phase_imm_phi, pairTheory.SND] >>
  `abi_decoder_phi st1 st2` by metis_tac[ctor_registration_phi, pairTheory.SND] >>
  `abi_decoder_phi (initial_compile_state "__deploy") st2` by
    metis_tac[abi_decoder_phi_trans] >>
  irule abi_decoder_phi_safe_head >>
  qexists_tac `initial_compile_state "__deploy"` >>
  fs[abi_decoder_phi_def, initial_compile_state_def, phi_prefix_length_def]
QED

Theorem ctor_phase_code_phi_contracts:
  (if pay then comp_return () else
    comp_bind (emit_op CALLVALUE []) (\cv.
      comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv])))
    (initial_compile_state "__deploy") = ((),st_pay) /\
  (if cap > 0 then comp_bind (compile_fixed_region_with_id cap)
    (\r. comp_return (SND r).buf_operand) else comp_return (Lit 0w))
    st_pay = (imm,st1) /\
  compile_register_constructor_args ce args 0 0 st1 = (ce1,st2) /\
  (if nr then compile_nonreentrant_lock nkey ut F else comp_return ()) st2 = ((),st3) /\
  fresh_label "ctor_exit" st3 = (exit_lbl,sa) /\
  fn_has_code (initial_compile_state "__deploy") sa func /\
  (!bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  fn_has_code (initial_compile_state "__deploy") st_pay func /\
  fn_has_code st_pay st1 func /\ fn_has_code st1 st2 func /\
  fn_has_code st2 st3 func /\
  (!bb. lookup_block st2.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  st3.cs_current_bb = sa.cs_current_bb /\
  LENGTH st3.cs_current_insts = LENGTH sa.cs_current_insts
Proof
  strip_tac >> drule_all ctor_phase_extends >> strip_tac >>
  drule_all ctor_phase_code_split >> strip_tac >>
  `phi_prefix_length st2.cs_current_insts = 0` by
    metis_tac[ctor_phase_registration_head_phi] >>
  `!bb. lookup_block st2.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[ctor_phase_registration_phi] >>
  drule ctor_phase_fresh_label_cursor >> simp[]
QED
