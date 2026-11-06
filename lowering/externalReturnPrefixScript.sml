(* A valued return's code starts with the code of its value. *)
Theory externalReturnPrefix
Ancestors
  stmtLoweringMono exprLoweringProps loweringPosts stmtLowering exprLowering
  compileEnv entryHaltMem fragExecMem fragExec entryStateRel bodySim compileVyper moduleLowering

(* Sequence ci_mono through binds, lets, conditionals and case splits,
   down to the operations named in rws (as in stmtLoweringMono). *)
fun ci_mono_chain_tac rws =
  let val close =
        FIRST (map MATCH_ACCEPT_TAC
                 (List.concat (map BODY_CONJUNCTS (ci_mono_comp_return :: rws))))
  in
    rpt gen_tac >>
    rpt (FIRST [MATCH_MP_TAC ci_mono_bind, MATCH_MP_TAC ci_mono_ignore_bind,
                close, FIRST_ASSUM MATCH_ACCEPT_TAC,
                IF_CASES_TAC, BasicProvers.TOP_CASE_TAC] >>
         rpt conj_tac >> rpt gen_tac >> PURE_REWRITE_TAC[LET_THM] >>
         BETA_TAC) >>
    simp (ci_mono_comp_return :: rws)
  end;

Theorem ci_mono_bind_after[local]:
  (!v s. ci_mono s (SND (k v s))) /\ m sa = (op, s1) ==>
  ci_mono s1 (SND (comp_bind m k sa))
Proof
  rw[comp_bind_def]
QED

Theorem return_value_code_prefix:
  stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv', sb) /\
  lower_value compile_expr cenv ty e sa = (op, s1) ==> cs_extends s1 sb
Proof
  strip_tac >>
  `ci_mono s1 sb` suffices_by simp[ci_mono_def] >>
  `sb = SND (compile_stmt cenv lctx ty (Return (SOME e)) sa)` by
    (qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, pairTheory.UNCURRY]) >>
  pop_assum SUBST1_TAC >> simp[Once compile_stmt_def] >>
  irule ci_mono_bind_after >> simp[] >>
  ci_mono_chain_tac
    [ci_mono_return_helpers, ci_mono_emit_op, ci_mono_compile_alloc_buffer,
     cj 1 ci_mono_typed_memory_family]
QED

Theorem update_cenv_ret_abi_frame[local]:
  (update_cenv_ret_abi cenv rt).ce_return_pc = cenv.ce_return_pc /\
  (update_cenv_ret_abi cenv rt).ce_ctor_exit_label = cenv.ce_ctor_exit_label
Proof
  simp[update_cenv_ret_abi_def]
QED

Theorem build_compile_env_external_frame[local]:
  (build_compile_env tops External mut fname fargs fret fbody ut).ce_return_pc =
    NONE /\
  (build_compile_env tops External mut fname fargs fret fbody ut).ce_ctor_exit_label =
    NONE
Proof
  simp[build_compile_env_def, pairTheory.UNCURRY]
QED

(* The selected external function's frame returns through the external
   branch, with no nonreentrant unlock. *)
Theorem external_package_frame_exit:
  set_external_package_target tgt
    (package_external_fn tops ut0 nkm
       (mut, F, rr, fname, fargs, dflts, fret, fbody)) =
    (lbl, cenv0, pos_args, min_cds, is_payable, nr, nkey, ut, iv, fbody', rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv, sa) /\
  same_frame cenv cenv' ==>
  cenv'.ce_return_pc = NONE /\ cenv'.ce_ctor_exit_label = NONE /\
  FST cenv'.ce_nonreentrant = F
Proof
  strip_tac >>
  `cenv0.ce_return_pc = NONE /\ cenv0.ce_ctor_exit_label = NONE /\
   FST cenv0.ce_nonreentrant = F` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[package_external_fn_def, set_external_package_target_def] >>
     strip_tac >> gvs[update_cenv_nonreentrant_def] >>
     rw[update_cenv_ret_abi_frame, build_compile_env_external_frame]) >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `same_frame _ _`
    (strip_assume_tac o REWRITE_RULE [same_frame_def]) >>
  `cenv'.ce_return_pc = cenv.ce_return_pc /\
   cenv'.ce_ctor_exit_label = cenv.ce_ctor_exit_label /\
   cenv'.ce_nonreentrant = cenv.ce_nonreentrant` by
    (qpat_x_assum `_ with <| ce_vars := _; ce_var_type := _;
                             ce_dynarray_capacity := _ |> = _`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `cenv.ce_return_pc = cenv0.ce_return_pc /\
   cenv.ce_ctor_exit_label = cenv0.ce_ctor_exit_label /\
   cenv.ce_nonreentrant = cenv0.ce_nonreentrant` by
    (qpat_x_assum `cenv = _` SUBST1_TAC >> simp[]) >>
  simp[]
QED

(* Return NONE in such a frame is STOP: it exits, memory-safely. *)
Theorem return_none_external_run_mem:
  stmt_env cenv lctx ty (Return NONE) sa = (cenv'', sb) /\
  cenv.ce_return_pc = NONE /\ cenv.ce_ctor_exit_label = NONE /\
  FST cenv.ce_nonreentrant = F /\
  fn_has_code sa sb func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?fuel r. run_from fuel ctx func s0 = r /\ exit_result r /\
           mem_safe_run fuel ctx func s0
Proof
  strip_tac >>
  `?x. compile_stmt cenv lctx ty (Return NONE) sa = (x, sb)` by
    (qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, pairTheory.UNCURRY] >>
     Cases_on `compile_stmt cenv lctx ty (Return NONE) sa` >> rw[] >>
     gvs[oneTheory.one]) >>
  Cases_on `cenv.ce_nonreentrant` >> rename1 `_ = (nr0, rest)` >>
  PairCases_on `rest` >> gvs[] >>
  `frag_exec_mem ctx sa sb (\t. t = s0) (\t. F) (\r. T)` by
    (irule compile_return_none_external_frag_mem >> simp[] >>
     metis_tac[]) >>
  gvs[frag_exec_mem_def] >>
  first_x_assum (qspecl_then [`func`, `s0`] mp_tac) >> simp[]
QED
