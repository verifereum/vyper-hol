Theory ctorDeployMemoryRunMemEntryEndpoint
Ancestors
  ctorDeployLoweringDefs ctorRegisterArgs abiDecoderPhi fragExec
  ctorDeployMemoryRunMemEntryStmtFirstEmission
  compilerFirstEmission rich_list venomExecSemantics context emitHelper venomInst compileEnv

Theorem ctor_endpoint_nonempty_prefix_phi:
  fn_has_code first last func /\
  last.cs_current_insts <> [] /\
  phi_prefix_length last.cs_current_insts = 0 ==>
  !bb. lookup_block last.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  simp[fn_has_code_def] >> rpt strip_tac >> gvs[] >>
  fs[IS_PREFIX_APPEND] >>
  Cases_on `last.cs_current_insts` >> gvs[phi_prefix_length_def] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[phi_prefix_length_def]
QED

(* The payable, no-immutables, no-arguments, unlocked constructor has an
   empty body-start current list. Prefix PHI preservation alone cannot
   constrain the first instruction subsequently supplied by the body. *)
Theorem ctor_empty_prefix_cursor_probe:
  comp_return () (initial_compile_state "__deploy") =
    ((), initial_compile_state "__deploy") /\
  comp_return (Lit 0w) (initial_compile_state "__deploy") =
    (Lit 0w, initial_compile_state "__deploy") /\
  compile_register_constructor_args ce [] 0 0
    (initial_compile_state "__deploy") =
    (ce, initial_compile_state "__deploy") /\
  (SND (fresh_label "ctor_exit" (initial_compile_state "__deploy"))).cs_current_insts = []
Proof
  EVAL_TAC
QED

Theorem ctor_endpoint_first_emission_fallthrough:
  a.cs_current_insts = [] /\ cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!f. fn_has_code a b f ==>
     ?bb i. lookup_block a.cs_current_bb f.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI)) /\
  (if block_is_terminated b then comp_return ()
   else emit_inst JMP [Label lbl] []) b = ((), c) /\
  fn_has_code a b fn /\ fn_has_code b c fn ==>
  !bb. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac
  >- (gvs[block_is_terminated_def] >>
      gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def,
          comp_return_def, fn_has_code_def, mk_inst_def] >>
      rpt strip_tac >> gvs[] >>
      Cases_on `bb.bb_instructions` >> gvs[phi_prefix_length_def, mk_inst_def]) >>
  metis_tac[first_emission_empty_phi]
QED

Theorem ctor_deploy_endpoint_empty_phi:
  !tops rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl sa sb sj
   st_exit st_epilogue st_final func bb.
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) /\
  sa.cs_current_insts = [] /\
  lookup_block sa.cs_current_bb func.fn_blocks = SOME bb ==>
  phi_prefix_length bb.bb_instructions = 0
Proof
  simp_tac bool_ss [deploy_ctor_code_def] >> rpt strip_tac >>
  drule ctor_compile_stmts_first_emission >> strip_tac >>
  irule ctor_endpoint_first_emission_fallthrough >>
  metis_tac[]
QED

Theorem ctor_deploy_endpoint_phi:
  !tops rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl sa sb sj
   st_exit st_epilogue st_final func bb.
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) /\
  phi_prefix_length sa.cs_current_insts = 0 /\
  lookup_block sa.cs_current_bb func.fn_blocks = SOME bb ==>
  phi_prefix_length bb.bb_instructions = 0
Proof
  rpt gen_tac >> strip_tac >> Cases_on `sa.cs_current_insts = []`
  >- metis_tac[ctor_deploy_endpoint_empty_phi] >>
  fs[deploy_ctor_code_def] >>
  drule_at (Pos last) ctor_endpoint_nonempty_prefix_phi >>
  metis_tac[]
QED

Theorem ctor_deploy_body_endpoint_guard:
  !tops rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl sa sb sj
   st_exit st_epilogue st_final func s0.
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
    (s0.vs_inst_idx = 0 ==> phi_prefix_length bb.bb_instructions = 0)
Proof
  rpt gen_tac >> strip_tac >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb` by
    (fs[deploy_ctor_code_def, fn_has_code_def] >> metis_tac[]) >>
  qexists `bb` >> simp[] >> strip_tac >>
  irule ctor_deploy_endpoint_empty_phi >>
  metis_tac[LENGTH_NIL]
QED
