(* Compiler interval facts for the selected decode arm. *)
Theory extcallReturnDefaultIntervals
Ancestors
  extcallReturnDefaultRouting abiDecoderAppend exprLoweringProps
  emitHelper emitHelperProps fragExec compileEnv venomInst venomState
  venomExecSemantics exprLowering arithmetic list rich_list

Theorem intervals_mono_trans[local]:
  ci_mono a b /\ ci_mono b c ==> ci_mono a c
Proof
  simp[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]
QED

Theorem return_default_decode_intervals:
  emit_op RETURNDATASIZE [] a = (rds,a1) /\
  emit_op ISZERO [rds] a1 = (iz,a2) /\
  fresh_label "extcall_default" a2 = (dl,a3) /\
  fresh_label "extcall_decode" a3 = (cl,a4) /\
  fresh_label "extcall_exit" a4 = (xl,a5) /\
  emit_inst JNZ [iz; Label dl; Label cl] [] a5 = ((),a6) /\
  new_block dl a6 = (old1,ds) /\
  compile_store_memory ce dop dst rt dt ds = ((),de) /\
  (if skip then comp_return () else compile_extcodesize_check addr) de = ((),ck) /\
  emit_inst JMP [Label xl] [] ck = ((),dj) /\
  new_block cl dj = (old2,cs) /\
  compile_return_value_decode lo cap cs = (hi,hs) /\
  compile_abi_decode_to_buf dst (Lit 0w) MLOAD base_op hi info hs = ((),he) /\
  emit_inst JMP [Label xl] [] he = ((),cj) /\
  new_block xl cj = (old3,b) /\ fn_has_code a b func ==>
  cs.cs_current_bb = cl /\ cs.cs_current_insts = [] /\
  ci_mono a cs /\ ci_mono cs hs /\ ci_mono hs he /\
  fn_has_code cs he func /\
  (he.cs_current_insts <> [] \/
   !bb. lookup_block he.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >>
  `ci_mono a a1 /\ ci_mono a1 a2` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono a2 a3 /\ ci_mono a3 a4 /\ ci_mono a4 a5` by
    metis_tac[ci_mono_fresh_label, pairTheory.SND] >>
  `ci_mono a5 a6 /\ ci_mono ck dj /\ ci_mono he cj` by
    metis_tac[ci_mono_emit_inst, pairTheory.SND] >>
  `ci_mono a6 ds /\ ci_mono dj cs /\ ci_mono cj b` by
    metis_tac[ci_mono_new_block, pairTheory.SND] >>
  `ci_mono ds de` by
    metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `ci_mono de ck` by
    (Cases_on `skip` >- gvs[comp_return_def, ci_mono_def, cs_extends_refl] >>
     gvs[compile_extcodesize_check_def, comp_bind_def] >>
     pairarg_tac >> gvs[] >>
     `ci_mono de cs'` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
     `ci_mono cs' ck` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
     fs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `ci_mono cs hs /\ ci_mono hs he` by
    metis_tac[ci_mono_compile_return_value_decode,
      cj 1 ci_mono_compile_abi_decode, pairTheory.SND] >>
  `ci_mono a cs` by
    (irule intervals_mono_trans >> qexists_tac `a1` >> simp[] >>
     irule intervals_mono_trans >> qexists_tac `a2` >> simp[] >>
     irule intervals_mono_trans >> qexists_tac `a3` >> simp[] >>
     irule intervals_mono_trans >> qexists_tac `a4` >> simp[] >>
     irule intervals_mono_trans >> qexists_tac `a5` >> simp[] >>
     irule intervals_mono_trans >> qexists_tac `a6` >> simp[] >>
     irule intervals_mono_trans >> qexists_tac `ds` >> simp[] >>
     irule intervals_mono_trans >> qexists_tac `de` >> simp[] >>
     irule intervals_mono_trans >> qexists_tac `ck` >> simp[] >>
     irule intervals_mono_trans >> qexists_tac `dj` >> simp[]) >>
  `fn_has_code cs he func /\ fn_has_code he cj func` by
    (drule_all return_default_intervals_code >> strip_tac >>
     `cs_extends cs hs /\ cs_extends hs he` by fs[ci_mono_def] >>
     metis_tac[fn_has_code_split, cs_extends_trans, fn_has_code_mid,
       ci_mono_def]) >>
  `cs.cs_current_bb = cl /\ cs.cs_current_insts = []` by
    (qpat_x_assum `new_block cl dj = _` mp_tac >> simp[new_block_def] >> strip_tac >> gvs[]) >>
  simp[] >> Cases_on `he.cs_current_insts = []` >> simp[] >>
  `?bb. lookup_block he.cs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX [mk_inst he.cs_next_id JMP [Label xl] []] bb.bb_instructions` by
    (qpat_x_assum `fn_has_code he cj func` mp_tac >>
     qpat_x_assum `emit_inst JMP [Label xl] [] he = _` mp_tac >>
     simp[emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
       comp_return_def, fn_has_code_def] >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >> Cases_on `bb.bb_instructions` >>
  gvs[phi_prefix_length_def, mk_inst_def]
QED
