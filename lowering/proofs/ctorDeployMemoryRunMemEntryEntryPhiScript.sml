Theory ctorDeployMemoryRunMemEntryEntryPhi
Ancestors
  ctorDeployMemoryRunMemEntryEndpoint ctorDeployMemoryRunMemEntryLabel
  abiDecoderPhi ctorRegisterArgs fragExec context emitHelper venomInst
  compilerFirstEmission rich_list list compileEnv venomExecSemantics ctorDeployLoweringDefs
  ctorDeployMemoryRunMemPrefixLayout ctorDeployMemoryRunMemEntryBoundary compileVyper vyperCompiler

Theorem ctor_entry_lock_phi[local]:
  !nkey ut st. abi_decoder_phi st (SND (compile_nonreentrant_lock nkey ut F st))
Proof
  rpt gen_tac >> simp[compile_nonreentrant_lock_def] >>
  Cases_on `ut` >> simp[] >>
  rpt (ho_match_mp_tac abi_decoder_phi_bind >> conj_tac
    >- simp[abi_decoder_phi_emit_op] >> rpt gen_tac) >>
  ho_match_mp_tac abi_decoder_phi_ignore_bind >> conj_tac
  >- simp[abi_decoder_phi_emit_void] >> simp[abi_decoder_phi_emit_void]
QED

Theorem ctor_entry_fixed_phi[local]:
  !cap st. abi_decoder_phi st (SND (compile_fixed_region_with_id cap st))
Proof
  simp[compile_fixed_region_with_id_def, comp_bind_def, comp_ignore_bind_def,
    fresh_id_def, fresh_var_def, comp_return_def, emit_def,
    abi_decoder_phi_def, abi_decoder_phi_safe_def] >> rpt strip_tac >>
  irule abi_decoder_phi_append >> simp[phi_prefix_length_def, mk_inst_def]
QED

Theorem ctor_entry_pay_phi[local]:
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

Theorem ctor_entry_imm_phi[local]:
  !cap st. abi_decoder_phi st
    (SND ((if cap > 0 then comp_bind (compile_fixed_region_with_id cap)
      (\r. comp_return (SND r).buf_operand) else comp_return (Lit 0w)) st))
Proof
  rpt gen_tac >> IF_CASES_TAC >> simp[abi_decoder_phi_return] >>
  ho_match_mp_tac abi_decoder_phi_bind >>
  simp[ctor_entry_fixed_phi, abi_decoder_phi_return]
QED

Theorem ctor_deploy_prefix_phi:
  !tops rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl sa sb sj
   st_exit st_epilogue st_final func.
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) ==>
  abi_decoder_phi (initial_compile_state "__deploy") sa
Proof
  simp_tac bool_ss [deploy_ctor_code_def] >> rpt strip_tac >>
  `abi_decoder_phi (initial_compile_state "__deploy") st_pay` by
    metis_tac[ctor_entry_pay_phi, pairTheory.SND] >>
  `abi_decoder_phi st_pay st1` by
    metis_tac[ctor_entry_imm_phi, pairTheory.SND] >>
  `abi_decoder_phi st1 st2` by
    metis_tac[ctor_registration_phi, pairTheory.SND] >>
  `abi_decoder_phi st2 st3` by
    (Cases_on `nr` >> gvs[comp_return_def] >>
     metis_tac[ctor_entry_lock_phi, abi_decoder_phi_refl, pairTheory.SND]) >>
  `abi_decoder_phi st3 sa` by
    metis_tac[abi_decoder_phi_fresh_label, pairTheory.SND] >>
  metis_tac[abi_decoder_phi_trans]
QED

Theorem ctor_entry_pay_appends[local]:
  cs_appends (if pay then comp_return () else
    comp_bind (emit_op CALLVALUE []) (\cv.
      comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv])))
Proof
  Cases_on `pay` >> simp[cs_appends_return] >>
  irule cs_appends_bind >> simp[cs_appends_emit_helpers] >> gen_tac >>
  irule cs_appends_bind >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_deploy_prefix_extends:
  !tops rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl sa sb sj
   st_exit st_epilogue st_final func.
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) ==>
  cs_extends (initial_compile_state "__deploy") sa
Proof
  simp_tac bool_ss [deploy_ctor_code_def] >> rpt strip_tac >>
  `cs_extends (initial_compile_state "__deploy") st_pay` by
    metis_tac[ctor_entry_pay_appends, cs_appends_def] >>
  `cs_extends st_pay st1` by
    (Cases_on `imm_len tops > 0` >> gvs[comp_return_def, cs_extends_refl] >>
     qpat_x_assum `comp_bind _ _ st_pay = _` mp_tac >>
     simp[comp_bind_def, comp_return_def] >> pairarg_tac >> simp[] >>
     metis_tac[ctor_prefix_fixed_appends, cs_appends_def]) >>
  `cs_extends st1 st2` by metis_tac[ctor_registration_extends] >>
  `cs_extends st2 st3` by
    (Cases_on `nr` >> gvs[comp_return_def] >>
     metis_tac[ctor_prefix_lock_appends, cs_appends_def, cs_extends_refl]) >>
  `cs_extends st3 sa` by metis_tac[cs_appends_prims, cs_appends_def] >>
  metis_tac[cs_extends_trans]
QED

Theorem ctor_entry_phi_backwards[local]:
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

Theorem ctor_deploy_initial_block_phi:
  !tops rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl sa sb sj
   st_exit st_epilogue st_final func.
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) ==>
  ?bb. lookup_block (initial_compile_state "__deploy").cs_current_bb
      func.fn_blocks = SOME bb /\ phi_prefix_length bb.bb_instructions = 0
Proof
  rpt gen_tac >> strip_tac >>
  drule ctor_deploy_prefix_phi >> strip_tac >>
  drule ctor_deploy_prefix_extends >> strip_tac >>
  `fn_has_code (initial_compile_state "__deploy") sa func` by
    fs[deploy_ctor_code_def] >>
  `phi_prefix_length sa.cs_current_insts = 0` by
    (irule abi_decoder_phi_safe_head >>
     qexists `initial_compile_state "__deploy"` >>
     fs[abi_decoder_phi_def, initial_compile_state_def, phi_prefix_length_def]) >>
  `!bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[ctor_deploy_endpoint_phi] >>
  `!bb. lookup_block (initial_compile_state "__deploy").cs_current_bb
      func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule ctor_entry_phi_backwards >>
     qexistsl [`func`, `sa`, `initial_compile_state "__deploy"`] >>
     simp[initial_compile_state_def, phi_prefix_length_def]) >>
  metis_tac[fn_has_code_start]
QED

Theorem ctor_checked_task_entry_phi:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func fn lbl.
  deploy_phases policy tops (deploy_bc,runtime_bc)
    (rpolicy,dunit,dout,prog,cplan) /\
  deploy_source_ok tops am tx /\
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  ?bb. lookup_block lbl fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ctor_checked_task_entry_cursor >> strip_tac >>
  drule_all ctor_checked_code_lookup_identity >> strip_tac >>
  drule ctor_deploy_initial_block_phi >> gvs[]
QED
