(* Raw list states carry no program-counter discipline.  Only the proof
   certificate is normalized; variable equations are transported directly. *)
Theory acMergeRuntimeProofs
Ancestors
  acMergeRuntimeDefs acMergeCursorDefs acRuntimeInvariantDefs
  acRuntimeInvariantProofs acRuntimeStepProofs acChainProofs acBaseProofs
  assertCombinerDefs venomWf venomWfProps venomExecProofs venomExecProps
  venomExecSemantics venomState venomInst dfgDefs dfgAnalysisProps
  basePtrProofs simplifyCfgAvailability finite_map list rich_list

Theorem ac_merge_runtime_raw:
  ac_merge_runtime fn bb offset n s <=>
    MEM bb fn.fn_blocks /\ n+offset <= LENGTH bb.bb_instructions /\
    fn_reachable fn bb.bb_label /\
    ac_dfg_inv_local (dfg_build_function fn) (ac_def_before fn bb (n+offset)) s /\
    (!inst v. ac_def_before fn bb (n+offset) inst /\ MEM v inst.inst_outputs ==>
      IS_SOME (lookup_var v s))
Proof
  `!op. eval_operand op
      (s with <|vs_current_bb := bb.bb_label; vs_inst_idx := n+offset|>) =
      eval_operand op s` by (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  simp[ac_merge_runtime_def, ac_cursor_inv_def, ac_dfg_inv_local_def,
       lookup_var_def]
QED

Theorem ac_merge_runtime_raw_step:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  ac_merge_runtime fn bb offset n s /\ n+offset < LENGTH bb.bb_instructions /\
  (EL (n+offset) bb.bb_instructions).inst_opcode <> PHI /\
  step_inst fuel ctx (EL (n+offset) bb.bb_instructions) s = OK t ==>
  ac_merge_runtime fn bb offset (SUC n) t
Proof
  rpt strip_tac >> fs[ac_merge_runtime_raw] >>
  `ac_dfg_inv_local (dfg_build_function fn)
      (ac_def_before fn bb (n+offset)) t` by
    (irule ac_old_equations_step_frame >> metis_tac[]) >>
  `ac_dfg_inv_local (dfg_build_function fn)
      (\di. di = EL (n+offset) bb.bb_instructions) t` by
    (irule ac_cursor_current_equations_step >> metis_tac[]) >>
  `offset + SUC n = SUC (n+offset)` by decide_tac >>
  simp[ac_merge_runtime_raw] >> reverse conj_tac
  >- (rpt strip_tac >>
      `ac_def_before fn bb (n+offset) inst \/
       inst = EL (n+offset) bb.bb_instructions` by metis_tac[ac_def_before_suc] >>
      gvs[]
      >- (`lookup_var v t = lookup_var v s` by
            (irule step_inst_preserves_lookup >>
             metis_tac[ac_def_before_output_not_current]) >>
          metis_tac[]) >>
      irule scfg_step_outputs_defined >> metis_tac[fn_inst_wf_def, EL_MEM]) >>
  `!di. ac_def_before fn bb (SUC (n+offset)) di <=>
    ac_def_before fn bb (n+offset) di \/ di = EL (n+offset) bb.bb_instructions`
    by metis_tac[ac_def_before_suc] >>
  fs[ac_dfg_inv_local_def] >>
  rpt conj_tac >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ac_merge_runtime_skip_assert:
  wf_function fn /\ fn_inst_wf fn /\
  ac_merge_runtime fn bb offset n s /\ n+offset < LENGTH bb.bb_instructions /\
  (EL (n+offset) bb.bb_instructions).inst_opcode = ASSERT ==>
  ac_merge_runtime fn bb offset (SUC n) s
Proof
  simp[ac_merge_runtime_def] >> rpt strip_tac >>
  drule_all ac_cursor_skip_assert >>
  simp[arithmeticTheory.ADD_CLAUSES, venom_state_component_equality]
QED

Theorem ac_merge_runtime_use_defined:
  wf_function fn /\ wf_ssa fn /\ ac_merge_runtime fn bb offset n s /\
  n+offset < LENGTH bb.bb_instructions /\
  (EL (n+offset) bb.bb_instructions).inst_opcode <> PHI /\
  MEM (Var v) (EL (n+offset) bb.bb_instructions).inst_operands ==>
  IS_SOME (lookup_var v s)
Proof
  simp[ac_merge_runtime_def] >> rpt strip_tac >>
  drule_all ac_cursor_use_defined >> simp[lookup_var_def]
QED

Theorem ac_merge_runtime_query:
  wf_function fn /\ wf_ssa fn /\ ac_merge_runtime fn bb offset n s /\
  n+offset < LENGTH bb.bb_instructions /\
  (EL (n+offset) bb.bb_instructions).inst_opcode = ASSERT /\
  (EL (n+offset) bb.bb_instructions).inst_operands = [c] /\
  ac_get_iszero_operand (dfg_build_function fn) {} c = SOME p ==>
  ?w. eval_operand p s = SOME w /\
      eval_operand c s = SOME (bool_to_word (w = 0w))
Proof
  rpt strip_tac >>
  `IS_SOME (eval_operand c s)` by
    (Cases_on `c` >> gvs[eval_operand_def]
     >- (irule ac_merge_runtime_use_defined >>
         qexistsl [`bb`, `fn`, `n`, `offset`] >> simp[]) >>
     gvs[Once ac_get_iszero_operand_def]) >>
  `!op. eval_operand op
      (s with <|vs_current_bb := bb.bb_label; vs_inst_idx := n+offset|>) =
      eval_operand op s` by (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  fs[ac_merge_runtime_def] >>
  drule_at (Pat `ac_cursor_inv _ _ _ _`) ac_cursor_iszero_bridge >>
  simp[] >> disch_then irule >> simp[] >> metis_tac[]
QED

Theorem ac_merge_runtime_safe_total:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  ac_merge_runtime_cert fn bb offset n s /\ n+offset < LENGTH bb.bb_instructions /\
  ac_is_safe_between (EL (n+offset) bb.bb_instructions) ==>
  ?t. step_inst fuel ctx (EL (n+offset) bb.bb_instructions) s = OK t
Proof
  rpt strip_tac >> fs[ac_merge_runtime_cert_def] >>
  `MEM bb fn.fn_blocks` by fs[ac_merge_runtime_raw] >>
  irule safe_between_wf_step_ok >> simp[] >> reverse conj_tac
  >- metis_tac[fn_inst_wf_def, EL_MEM] >>
  Cases >> simp[eval_operand_def]
  >- (strip_tac >> irule ac_merge_runtime_use_defined >>
      fs[ac_is_safe_between_def] >> metis_tac[]) >>
  `MEM (EL (n+offset) bb.bb_instructions) (fn_insts fn)` by
    (simp[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
     metis_tac[EL_MEM]) >>
  strip_tac >>
  `s' IN FDOM s.vs_labels` by
    (fs[ac_merge_safe_labels_def] >> metis_tac[]) >>
  simp[FLOOKUP_DEF]
QED

Theorem ac_merge_runtime_prior_operand:
  wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  a < n /\ n < LENGTH (DROP offset bb.bb_instructions) /\
  (EL a (DROP offset bb.bb_instructions)).inst_opcode = ASSERT /\
  (EL a (DROP offset bb.bb_instructions)).inst_operands = [c] /\
  ac_get_iszero_operand (dfg_build_function fn) {} c = SOME p /\
  step_inst fuel ctx (EL n (DROP offset bb.bb_instructions)) s = OK t ==>
  eval_operand p t = eval_operand p s
Proof
  rpt strip_tac >> fs[LENGTH_DROP] >>
  `a+offset < LENGTH bb.bb_instructions /\
   a+offset <= n+offset /\ n+offset < LENGTH bb.bb_instructions` by decide_tac >>
  fs[listTheory.EL_DROP] >>
  drule_at (Pat `step_inst _ _ _ _ = _`) ac_query_predicate_step >>
  disch_then irule >> simp[] >>
  qexistsl [`a+offset`, `fn`, `c`, `{}`] >> simp[]
QED

Theorem ac_merge_runtime_cert_step:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  ac_merge_runtime_cert fn bb offset n s /\ n+offset < LENGTH bb.bb_instructions /\
  (EL (n+offset) bb.bb_instructions).inst_opcode <> PHI /\
  step_inst fuel ctx (EL (n+offset) bb.bb_instructions) s = OK t ==>
  ac_merge_runtime_cert fn bb offset (SUC n) t
Proof
  simp[ac_merge_runtime_cert_def] >> rpt strip_tac
  >- metis_tac[ac_merge_runtime_raw_step] >>
  drule venomExecProofsTheory.step_inst_preserves_labels_always >>
  metis_tac[ac_merge_safe_labels_frame]
QED

Theorem ac_merge_runtime_cert_skip_assert:
  wf_function fn /\ fn_inst_wf fn /\
  ac_merge_runtime_cert fn bb offset n s /\ n+offset < LENGTH bb.bb_instructions /\
  (EL (n+offset) bb.bb_instructions).inst_opcode = ASSERT ==>
  ac_merge_runtime_cert fn bb offset (SUC n) s
Proof
  simp[ac_merge_runtime_cert_def] >> metis_tac[ac_merge_runtime_skip_assert]
QED

Theorem ac_merge_runtime_cert_laws:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
  offset <= LENGTH bb.bb_instructions /\
  EVERY (\i. i.inst_opcode <> PHI) (DROP offset bb.bb_instructions) ==>
  ac_merge_runtime_laws (DROP offset bb.bb_instructions) (dfg_build_function fn)
    fuel ctx (ac_merge_runtime_cert fn bb offset)
Proof
  rpt strip_tac >> simp[ac_merge_runtime_laws_def] >> rpt conj_tac
  >- (rpt strip_tac >> fs[LENGTH_DROP, EVERY_EL] >>
      `n+offset < LENGTH bb.bb_instructions` by decide_tac >>
      fs[listTheory.EL_DROP] >> irule ac_merge_runtime_cert_step >> simp[] >>
      first_x_assum (qspec_then `n` mp_tac) >>
      simp[listTheory.EL_DROP] >> metis_tac[]) 
  >- (rpt strip_tac >> fs[LENGTH_DROP] >>
      `n+offset < LENGTH bb.bb_instructions` by decide_tac >>
      fs[listTheory.EL_DROP] >> metis_tac[ac_merge_runtime_cert_skip_assert])
  >- (rpt strip_tac >> fs[LENGTH_DROP] >>
      `n+offset < LENGTH bb.bb_instructions` by decide_tac >>
      fs[listTheory.EL_DROP] >> metis_tac[ac_merge_runtime_safe_total])
  >- (rpt strip_tac >> fs[LENGTH_DROP, ac_merge_runtime_cert_def] >>
      `n+offset < LENGTH bb.bb_instructions` by decide_tac >>
      fs[listTheory.EL_DROP] >> metis_tac[ac_merge_runtime_query]) >>
  rpt strip_tac >> irule ac_merge_runtime_prior_operand >>
  simp[LENGTH_DROP] >> metis_tac[]
QED
