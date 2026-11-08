(* Opcode-independent append interfaces for runtime entry wrappers. *)
Theory entryCompileIntervals
Ancestors
  moduleLowering compileEnv context fragExec stmtLoweringMono abiDecoderAppend
  abiDecoderCounters exprLoweringProps

Theorem cs_appends_decode_args:
  !xs ce off opc hi adj. cs_appends (compile_decode_args ce xs off opc hi adj)
Proof
  Induct >> simp[compile_decode_args_def, cs_appends_return] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_decode_args_def] >>
  rpt (FIRST [CHANGED_TAC (simp[cs_appends_emit_helpers,
    cs_appends_abi_clamp, cj 1 cs_appends_abi_decode_mutual, cs_appends_return]),
    gen_tac, irule cs_appends_bind, irule cs_appends_ignore_bind,
    conj_tac, IF_CASES_TAC]) >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[cs_appends_return] >>
  rename1 `SOME loc` >> Cases_on `var_location_decode_operand loc` >>
  simp[cs_appends_return, cs_appends_emit_helpers] >>
  rpt (FIRST [CHANGED_TAC (simp[cs_appends_emit_helpers,
    cj 1 cs_appends_abi_decode_mutual]), gen_tac,
    irule cs_appends_bind, irule cs_appends_ignore_bind, conj_tac])
QED

Theorem cs_appends_register_positional_args:
  !xs ce off. cs_appends (compile_register_positional_args ce xs off)
Proof
  Induct >> simp[compile_register_positional_args_def, cs_appends_return] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_register_positional_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  rename1 `SOME loc` >> Cases_on `var_location_memory_size loc` >> simp[] >>
  rpt (FIRST [CHANGED_TAC (simp[cs_appends_abi_alloc_buffer,
    cs_appends_decode_args, cs_appends_return]), gen_tac,
    irule cs_appends_bind, irule cs_appends_ignore_bind, conj_tac])
QED

Theorem cs_appends_nonreentrant:
  cs_appends (compile_nonreentrant_lock key trans view) /\
  cs_appends (compile_nonreentrant_unlock key trans view)
Proof
  simp[compile_nonreentrant_lock_def, compile_nonreentrant_unlock_def] >>
  rpt (FIRST [CHANGED_TAC (simp[cs_appends_emit_helpers, cs_appends_return]),
    gen_tac, irule cs_appends_bind, irule cs_appends_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem cs_appends_comp_get:
  cs_appends comp_get
Proof
  simp[cs_appends_def, comp_get_def, cs_extends_refl]
QED

Theorem cs_appends_stmts:
  cs_appends (compile_stmts ce lc ty stmts)
Proof
  metis_tac[cs_appends_def, cs_mono_def, cj 2 compile_stmt_cs_mono]
QED

Theorem cs_appends_guarded_body:
  cs_appends (compile_guarded_body ce nr key trans view stmts rt)
Proof
  simp[compile_guarded_body_def] >>
  rpt (FIRST [CHANGED_TAC (simp[cs_appends_nonreentrant, cs_appends_stmts,
    cs_appends_comp_get, cs_appends_emit_helpers, cs_appends_return]),
    gen_tac, irule cs_appends_bind, irule cs_appends_ignore_bind,
    conj_tac, IF_CASES_TAC]) >> Cases_on `rt` >> simp[cs_appends_emit_helpers]
QED

Theorem cs_appends_external_function_body:
  cs_appends (compile_external_function_body ce args nr key trans view stmts rt)
Proof
  simp[compile_external_function_body_def] >> irule cs_appends_bind >>
  simp[cs_appends_register_positional_args, cs_appends_guarded_body]
QED

Theorem cs_appends_fallback_body:
  cs_appends (compile_fallback_body ce pay nr key trans view stmts rt)
Proof
  simp[compile_fallback_body_def] >>
  rpt (FIRST [CHANGED_TAC (simp[cs_appends_guarded_body,
    cs_appends_emit_helpers, cs_appends_return]), gen_tac,
    irule cs_appends_bind, irule cs_appends_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem cs_appends_entry_checks:
  cs_appends (compile_entry_checks mc pay)
Proof
  simp[compile_entry_checks_def] >>
  rpt (FIRST [CHANGED_TAC (simp[cs_appends_emit_helpers, cs_appends_return]),
    gen_tac, irule cs_appends_bind, irule cs_appends_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem cs_appends_external_fn_bodies:
  !xs. cs_appends (compile_external_fn_bodies xs)
Proof
  Induct >> simp[compile_external_fn_bodies_def, cs_appends_return] >>
  gen_tac >> PairCases_on `h` >> simp[compile_external_fn_bodies_def] >>
  rpt (FIRST [CHANGED_TAC (simp[cs_appends_prims, cs_appends_entry_checks,
    cs_appends_external_function_body]), gen_tac, irule cs_appends_bind,
    irule cs_appends_ignore_bind, conj_tac])
QED

Theorem vars_mono_decode_args[local]:
  !xs ce off opc hi adj. abi_decoder_vars_mono (compile_decode_args ce xs off opc hi adj)
Proof
  Induct >> simp[compile_decode_args_def, abi_decoder_vars_mono_return] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_decode_args_def] >>
  rpt (FIRST [CHANGED_TAC (simp[abi_decoder_vars_mono_prims,
    abi_decoder_vars_mono_abi_clamp, cj 1 abi_decoder_vars_mono_mutual,
    abi_decoder_vars_mono_return]),
    gen_tac, irule abi_decoder_vars_mono_bind,
    irule abi_decoder_vars_mono_ignore_bind, conj_tac, IF_CASES_TAC]) >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[abi_decoder_vars_mono_return] >>
  rename1 `SOME loc` >> Cases_on `var_location_decode_operand loc` >>
  simp[abi_decoder_vars_mono_return, abi_decoder_vars_mono_prims] >>
  rpt (FIRST [CHANGED_TAC (simp[abi_decoder_vars_mono_prims,
    cj 1 abi_decoder_vars_mono_mutual]), gen_tac,
    irule abi_decoder_vars_mono_bind, irule abi_decoder_vars_mono_ignore_bind, conj_tac])
QED

Theorem vars_mono_register_positional_args[local]:
  !xs ce off. abi_decoder_vars_mono (compile_register_positional_args ce xs off)
Proof
  Induct >> simp[compile_register_positional_args_def, abi_decoder_vars_mono_return] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_register_positional_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  rename1 `SOME loc` >> Cases_on `var_location_memory_size loc` >> simp[] >>
  rpt (FIRST [CHANGED_TAC (simp[abi_decoder_vars_mono_abi_alloc_buffer,
    vars_mono_decode_args, abi_decoder_vars_mono_return]), gen_tac,
    irule abi_decoder_vars_mono_bind, irule abi_decoder_vars_mono_ignore_bind, conj_tac])
QED

Theorem vars_mono_nonreentrant[local]:
  abi_decoder_vars_mono (compile_nonreentrant_lock key trans view) /\
  abi_decoder_vars_mono (compile_nonreentrant_unlock key trans view)
Proof
  simp[compile_nonreentrant_lock_def, compile_nonreentrant_unlock_def] >>
  rpt (FIRST [CHANGED_TAC (simp[abi_decoder_vars_mono_prims, abi_decoder_vars_mono_return]),
    gen_tac, irule abi_decoder_vars_mono_bind, irule abi_decoder_vars_mono_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem vars_mono_stmts[local]:
  abi_decoder_vars_mono (compile_stmts ce lc ty stmts)
Proof
  simp[abi_decoder_vars_mono_def] >>
  metis_tac[ci_mono_def, cj 2 compile_stmt_ci_mono]
QED

Theorem vars_mono_comp_get[local]:
  abi_decoder_vars_mono comp_get
Proof
  simp[abi_decoder_vars_mono_def, comp_get_def]
QED

Theorem vars_mono_guarded_body[local]:
  abi_decoder_vars_mono (compile_guarded_body ce nr key trans view stmts rt)
Proof
  simp[compile_guarded_body_def] >>
  rpt (FIRST [CHANGED_TAC (simp[vars_mono_nonreentrant, vars_mono_stmts,
    vars_mono_comp_get, abi_decoder_vars_mono_prims, abi_decoder_vars_mono_return]),
    gen_tac, irule abi_decoder_vars_mono_bind, irule abi_decoder_vars_mono_ignore_bind,
    conj_tac, IF_CASES_TAC]) >> Cases_on `rt` >> simp[abi_decoder_vars_mono_prims]
QED

Theorem vars_mono_external_function_body[local]:
  abi_decoder_vars_mono (compile_external_function_body ce args nr key trans view stmts rt)
Proof
  simp[compile_external_function_body_def] >> irule abi_decoder_vars_mono_bind >>
  simp[vars_mono_register_positional_args, vars_mono_guarded_body]
QED

Theorem vars_mono_entry_checks[local]:
  abi_decoder_vars_mono (compile_entry_checks mc pay)
Proof
  simp[compile_entry_checks_def] >>
  rpt (FIRST [CHANGED_TAC (simp[abi_decoder_vars_mono_prims, abi_decoder_vars_mono_return]),
    gen_tac, irule abi_decoder_vars_mono_bind, irule abi_decoder_vars_mono_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem external_prefix_counter_growth[local]:
  (compile_entry_checks mc pay sa = ((),sb) ==> sa.cs_next_var <= sb.cs_next_var) /\
  (compile_external_function_body ce args nr key trans view stmts rt sa = ((),sb) ==>
    sa.cs_next_var <= sb.cs_next_var) /\
  (new_block lbl sa = (v,sb) ==> sa.cs_next_var <= sb.cs_next_var)
Proof
  rpt conj_tac >> strip_tac
  >- (mp_tac vars_mono_entry_checks >>
      simp[abi_decoder_vars_mono_def] >> metis_tac[pairTheory.SND])
  >- (mp_tac vars_mono_external_function_body >>
      simp[abi_decoder_vars_mono_def] >> metis_tac[pairTheory.SND]) >>
  gvs[new_block_def]
QED

Theorem external_fn_selected_check_intervals:
  !fns sa sx.
    MEM (lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt) fns /\
    compile_external_fn_bodies fns sa = ((),sx) ==>
    ?sc sd cenv sb se. compile_entry_checks mc pay sc = ((),sd) /\
      sc.cs_current_bb = lbl /\ sc.cs_current_insts = [] /\
      cs_extends sa sc /\ cs_extends sc sd /\ cs_extends sd sx /\
      sa.cs_next_var <= sc.cs_next_var /\
      compile_register_positional_args ce pa 4 sd = (cenv,sb) /\
      compile_guarded_body cenv nr key tr view stmts rt sb = ((),se) /\
      cs_extends sb se /\ cs_extends se sx
Proof
  Induct >> simp[compile_external_fn_bodies_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_external_fn_bodies_def, comp_ignore_bind_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac external_prefix_counter_growth >>
  drule (SRULE [cs_appends_def] (cj 2 cs_appends_prims)) >> strip_tac >>
  drule (SRULE [cs_appends_def] cs_appends_entry_checks) >> strip_tac >>
  drule (SRULE [cs_appends_def] cs_appends_external_function_body) >> strip_tac >>
  drule (SRULE [cs_appends_def] cs_appends_external_fn_bodies) >> strip_tac >>
  gvs[]
  >- (qpat_x_assum `compile_external_function_body _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      simp[compile_external_function_body_def, comp_bind_def] >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >>
      drule (SRULE [cs_appends_def] cs_appends_guarded_body) >> strip_tac >>
      qexistsl_tac [`cs'`, `cs''`] >> simp[] >>
      rpt (goal_assum (drule_at Any)) >>
      gvs[new_block_def] >> metis_tac[cs_extends_trans]) >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`sc`, `sd`, `cenv`, `sb`, `se`] >> simp[] >>
  metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem cs_appends_runtime_fallback_suffix:
  cs_appends (comp_ignore_bind (new_block lbl)
    (case fb of
       NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
     | SOME (ce,pay,nr,key,tr,view,stmts,rt) =>
         compile_fallback_body ce pay nr key tr view stmts rt))
Proof
  irule cs_appends_ignore_bind >> simp[cs_appends_prims] >>
  namedCases_on `fb` ["", "desc"] >> simp[cs_appends_emit_helpers] >>
  PairCases_on `desc` >> simp[cs_appends_fallback_body]
QED
