Theory phiPrefixExecution
Ancestors
  phiOriginValues phiTransform instIdxIndep rich_list
  dftIndexedExec simplifyCfgAvailability
  venomInst venomExecSemantics venomState list arithmetic

Definition prefix_eval_def:
  (prefix_eval [] s = OK s) /\
  (prefix_eval (i::is) s =
    case step_inst_base i s of
      OK t => prefix_eval is t
    | other => other)
End

Theorem prefix_eval_append:
  !xs ys s.
    prefix_eval (xs ++ ys) s =
    case prefix_eval xs s of
      OK t => prefix_eval ys t
    | other => other
Proof
  Induct >> simp[prefix_eval_def] >> rpt gen_tac >>
  Cases_on `step_inst_base h s` >> simp[prefix_eval_def]
QED

Theorem prefix_opcode_nonterminator[local]:
  is_param_opcode op \/ op = ASSIGN ==>
  ~is_terminator op /\ op <> INVOKE
Proof
  simp[is_param_opcode_iff] >> strip_tac >>
  gvs[is_terminator_def]
QED

Theorem prefix_eval_inst_idx:
  !xs s n. EVERY (\i. is_param_opcode i.inst_opcode \/
                          i.inst_opcode = ASSIGN) xs ==>
  prefix_eval xs (s with vs_inst_idx := n) =
  exec_result_map (\t. t with vs_inst_idx := n) (prefix_eval xs s)
Proof
  Induct >> simp[prefix_eval_def, exec_result_map_def] >>
  rpt gen_tac >> strip_tac >>
  `~is_terminator h.inst_opcode` by
    metis_tac[prefix_opcode_nonterminator] >>
  simp[prefix_eval_def, step_inst_inst_idx_indep] >>
  Cases_on `step_inst_base h s` >> simp[exec_result_map_def]
QED

Theorem prefix_step_range[local]:
  is_param_opcode i.inst_opcode \/ i.inst_opcode = ASSIGN ==>
  (?t. step_inst_base i s = OK t) \/
  (?e. step_inst_base i s = Error e)
Proof
  simp[is_param_opcode_iff] >> strip_tac >>
  once_rewrite_tac[step_inst_base_def] >>
  pure_asm_rewrite_tac[opcode_case_def] >>
  namedCases_on `i.inst_operands` ["", "a args"] >> simp[] >>
  Cases_on `args` >> simp[] >>
  Cases_on `a` >> simp[] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >> simp[]
  >- metis_tac[] >>
  Cases_on `outs` >> simp[] >>
  simp[AllCaseEqs()] >> metis_tac[optionTheory.option_nchotomy]
QED

Theorem prefix_eval_range:
  !xs s. EVERY (\i. is_param_opcode i.inst_opcode \/
                        i.inst_opcode = ASSIGN) xs ==>
  (?t. prefix_eval xs s = OK t) \/
  (?e. prefix_eval xs s = Error e)
Proof
  Induct >> simp[prefix_eval_def] >> rpt gen_tac >> strip_tac >>
  `(?t. step_inst_base h s = OK t) \/
   (?e. step_inst_base h s = Error e)` by
    (irule prefix_step_range >> simp[]) >>
  simp[prefix_eval_def]
QED

Theorem prefix_eval_exec_block_drop:
  !xs s k bb tail fuel ctx.
    EVERY (\i. is_param_opcode i.inst_opcode \/ i.inst_opcode = ASSIGN) xs /\
    DROP k bb.bb_instructions = xs ++ tail ==>
    exec_block fuel ctx bb (s with vs_inst_idx := k) =
    case prefix_eval xs s of
      OK t => exec_block fuel ctx bb (t with vs_inst_idx := k + LENGTH xs)
    | other => other
Proof
  Induct >> simp[prefix_eval_def] >> rpt gen_tac >> strip_tac >>
  `k < LENGTH bb.bb_instructions` by
    (CCONTR_TAC >> `DROP k bb.bb_instructions = []` by
       (irule DROP_LENGTH_TOO_LONG >> decide_tac) >> gvs[]) >>
  `EL k bb.bb_instructions = h` by metis_tac[HD_DROP, HD] >>
  `~is_terminator h.inst_opcode /\ h.inst_opcode <> INVOKE` by
    metis_tac[prefix_opcode_nonterminator] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def, step_inst_non_invoke,
       step_inst_inst_idx_indep] >>
  `(?t. step_inst_base h s = OK t) \/
   (?e. step_inst_base h s = Error e)` by
    (irule prefix_step_range >> simp[]) >>
  simp[prefix_eval_def, exec_result_map_def] >>
  `DROP (SUC k) bb.bb_instructions = xs ++ tail` by
    simp[DROP_SUC, TL] >>
  first_x_assum (qspecl_then [`t`, `SUC k`, `bb`, `tail`, `fuel`, `ctx`] mp_tac) >>
  simp[ADD_CLAUSES]
QED

Theorem prefix_eval_exec_block:
  bb.bb_instructions = pre ++ xs ++ tail /\
  EVERY (\i. is_param_opcode i.inst_opcode \/ i.inst_opcode = ASSIGN) xs ==>
  exec_block fuel ctx bb (s with vs_inst_idx := LENGTH pre) =
  case prefix_eval xs s of
    OK t => exec_block fuel ctx bb
              (t with vs_inst_idx := LENGTH pre + LENGTH xs)
  | other => other
Proof
  strip_tac >> irule prefix_eval_exec_block_drop >>
  simp[DROP_APPEND]
QED

Theorem selected_copy_step[local]:
  phi_single_origin d i = SOME root /\ i.inst_outputs = [out] ==>
  step_inst_base (transform_inst d i) s =
    case lookup_var root s of
      SOME v => OK (update_var out v s)
    | NONE => Error "undefined operand"
Proof
  strip_tac >> simp[transform_inst_def] >>
  once_rewrite_tac[step_inst_base_def] >>
  simp[eval_operand_def]
QED

Theorem selected_copies_update_var[local]:
  !xs d x w s.
    (!i. MEM i xs ==> ?root out.
      phi_single_origin d i = SOME root /\ i.inst_outputs = [out] /\
      root <> x /\ out <> x) ==>
    prefix_eval (MAP (transform_inst d) xs) (update_var x w s) =
    exec_result_map (update_var x w) (prefix_eval (MAP (transform_inst d) xs) s)
Proof
  Induct >> simp[prefix_eval_def, exec_result_map_def] >>
  rpt gen_tac >> strip_tac >>
  `?root out. phi_single_origin d h = SOME root /\
      h.inst_outputs = [out] /\ root <> x /\ out <> x` by metis_tac[] >>
  `lookup_var root (update_var x w s) = lookup_var root s` by
    simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `!u. step_inst_base (transform_inst d h) u =
    case lookup_var root u of
      SOME v => OK (update_var out v u)
    | NONE => Error "undefined operand"` by
    (gen_tac >> irule selected_copy_step >> simp[]) >>
  simp[prefix_eval_def] >>
  namedCases_on `lookup_var root s` ["", "value"] >>
  simp[exec_result_map_def] >>
  `update_var out value (update_var x w s) =
   update_var x w (update_var out value s)` by
    metis_tac[dftCommutationTheory.update_var_commutes] >>
  metis_tac[]
QED

Theorem eval_phis_selected_copies[local]:
  !xs d s.
    EVERY (\i. i.inst_opcode = PHI) xs /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) xs)) /\
    (!i root. MEM i xs /\ phi_single_origin d i = SOME root ==>
      (?out v. i.inst_outputs = [out] /\ lookup_var root s = SOME v /\
        eval_one_phi s i = SOME (out,v)) /\
      (!j. MEM j xs ==> ~MEM root j.inst_outputs)) ==>
    eval_phis s xs =
    case eval_phis s (FILTER (\i. phi_single_origin d i = NONE) xs) of
      OK t => prefix_eval (MAP (transform_inst d)
                (FILTER (\i. ?r. phi_single_origin d i = SOME r) xs)) t
    | other => other
Proof
  Induct >> simp[eval_phis_def, prefix_eval_def] >>
  rpt gen_tac >> strip_tac >>
  `eval_phis s xs =
    case eval_phis s (FILTER (\i. phi_single_origin d i = NONE) xs) of
      OK t => prefix_eval (MAP (transform_inst d)
                (FILTER (\i. ?r. phi_single_origin d i = SOME r) xs)) t
    | other => other` by (first_x_assum irule >> fs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  Cases_on `phi_single_origin d h`
  >- (simp[eval_phis_def] >>
      namedCases_on `eval_one_phi s h` ["", "pair"] >> simp[] >>
      PairCases_on `pair` >> simp[] >>
      `h.inst_outputs = [pair0]` by
        fs[eval_one_phi_def, AllCaseEqs()] >>
      `!u. prefix_eval (MAP (transform_inst d)
              (FILTER (\i. ?r. phi_single_origin d i = SOME r) xs))
              (update_var pair0 pair1 u) =
            exec_result_map (update_var pair0 pair1)
              (prefix_eval (MAP (transform_inst d)
                (FILTER (\i. ?r. phi_single_origin d i = SOME r) xs)) u)` by
        (gen_tac >> irule selected_copies_update_var >>
         fs[MEM_FILTER, ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >>
         metis_tac[MEM]) >>
      Cases_on `eval_phis s (FILTER (\i. phi_single_origin d i = NONE) xs)` >>
      simp[exec_result_map_def] >>
      `(?u. eval_phis s xs = OK u) \/ (?e. eval_phis s xs = Error e)` by
        metis_tac[eval_phis_ok_or_error_defs] >>
      CASE_TAC >> gvs[exec_result_map_def]) >>
  `?out value. h.inst_outputs = [out] /\ lookup_var x s = SOME value /\
     eval_one_phi s h = SOME (out,value)` by metis_tac[] >>
  `!u. step_inst_base (transform_inst d h) u =
    case lookup_var x u of SOME v => OK (update_var out v u)
      | NONE => Error "undefined operand"` by
    (gen_tac >> irule selected_copy_step >> simp[]) >>
  `!u. prefix_eval (MAP (transform_inst d)
          (FILTER (\i. ?r. phi_single_origin d i = SOME r) xs))
          (update_var out value u) =
        exec_result_map (update_var out value)
          (prefix_eval (MAP (transform_inst d)
            (FILTER (\i. ?r. phi_single_origin d i = SOME r) xs)) u)` by
    (gen_tac >> irule selected_copies_update_var >>
     fs[MEM_FILTER, ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >> metis_tac[MEM]) >>
  Cases_on `eval_phis s (FILTER (\i. phi_single_origin d i = NONE) xs)` >>
  simp[prefix_eval_def] >>
  `lookup_var x v = lookup_var x s` by
    (
     irule venomExecPropsTheory.eval_phis_lookup_frame >>
     qexists `FILTER (\i. phi_single_origin d i = NONE) xs` >>
     simp[] >> rpt strip_tac >>
     drule venomExecPropsTheory.phi_prefix_mem >> simp[MEM_FILTER] >> metis_tac[]) >>
  simp[] >>
  `(?u. eval_phis s xs = OK u) \/ (?e. eval_phis s xs = Error e)` by
    metis_tac[eval_phis_ok_or_error_defs] >>
  CASE_TAC >> gvs[exec_result_map_def]
QED

Theorem phi_parallel_selected_copies:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  fn_entry_label fn = SOME s0.vs_current_bb /\ s0.vs_vars = FEMPTY /\
  source_entry_reachable ctx fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  eval_phis s (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) =
  case eval_phis s (FILTER (\i. phi_single_origin (dfg_build_function fn) i = NONE)
          (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) of
    OK t => prefix_eval (MAP (transform_inst (dfg_build_function fn))
      (FILTER (\i. ?r. phi_single_origin (dfg_build_function fn) i = SOME r)
        (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions))) t
  | other => other
Proof
  strip_tac >> irule eval_phis_selected_copies >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label] >>
  `fn_reachable fn bb.bb_label` by
    metis_tac[source_entry_reachable_inv, source_entry_inv_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> disch_tac >>
      `MEM i bb.bb_instructions /\ i.inst_opcode = PHI` by
        metis_tac[venomExecPropsTheory.phi_prefix_mem] >>
      conj_tac >- (irule phi_single_origin_incoming_value >> metis_tac[]) >>
      rpt strip_tac >> drule venomExecPropsTheory.phi_prefix_mem >> strip_tac >>
      metis_tac[phi_single_origin_block_frame])
  >- (`ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))` by
        metis_tac[venomWfPropsTheory.ssa_form_block_outputs_distinct, venomWfTheory.wf_ssa_def] >>
      qpat_x_assum `ALL_DISTINCT _` mp_tac >>
      qspecl_then [`phi_prefix_length bb.bb_instructions`, `bb.bb_instructions`] mp_tac TAKE_DROP >>
      metis_tac[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]) >>
  simp[EVERY_MEM] >> metis_tac[venomExecPropsTheory.phi_prefix_mem]
QED

Theorem selected_copies_success[local]:
  !xs d s.
    (!i. MEM i xs ==> ?root out value.
      phi_single_origin d i = SOME root /\ i.inst_outputs = [out] /\
      lookup_var root s = SOME value /\
      (!j. MEM j xs ==> ~MEM root j.inst_outputs)) ==>
    ?t. prefix_eval (MAP (transform_inst d) xs) s = OK t
Proof
  Induct >> simp[prefix_eval_def] >> rpt gen_tac >> strip_tac >>
  `?root out value. phi_single_origin d h = SOME root /\
     h.inst_outputs = [out] /\ lookup_var root s = SOME value` by metis_tac[] >>
  `step_inst_base (transform_inst d h) s = OK (update_var out value s)` by
    (drule_all selected_copy_step >> simp[]) >>
  simp[prefix_eval_def] >> first_x_assum irule >>
  rpt strip_tac >>
  `?r dst v. phi_single_origin d i = SOME r /\ i.inst_outputs = [dst] /\
     lookup_var r s = SOME v /\
     (!j. j = h \/ MEM j xs ==> ~MEM r j.inst_outputs)` by metis_tac[] >>
  qexistsl [`r`, `dst`, `v`] >>
  simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[MEM, lookup_var_def]
QED

Theorem phi_selected_copies_success:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  fn_entry_label fn = SOME s0.vs_current_bb /\ s0.vs_vars = FEMPTY /\
  source_entry_reachable ctx fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s (FILTER (\i. phi_single_origin (dfg_build_function fn) i = NONE)
    (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) = OK t ==>
  ?u. prefix_eval (MAP (transform_inst (dfg_build_function fn))
    (FILTER (\i. ?r. phi_single_origin (dfg_build_function fn) i = SOME r)
      (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions))) t = OK u
Proof
  strip_tac >> irule selected_copies_success >>
  simp[MEM_FILTER] >> rpt strip_tac >>
  `MEM i bb.bb_instructions /\ i.inst_opcode = PHI` by
    metis_tac[venomExecPropsTheory.phi_prefix_mem] >>
  drule_all phi_single_origin_incoming_value >> strip_tac >>
  qexistsl [`r`, `out`, `value`] >> simp[] >> conj_tac
  >- (`!j. MEM j (FILTER (\i. phi_single_origin (dfg_build_function fn) i = NONE)
          (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) ==>
          MEM j bb.bb_instructions` by
        (simp[MEM_FILTER] >> metis_tac[venomExecPropsTheory.phi_prefix_mem]) >>
      metis_tac[phi_single_origin_eval_phis_frame]) >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label] >>
  `fn_reachable fn bb.bb_label` by
    metis_tac[source_entry_reachable_inv, source_entry_inv_def] >>
  rpt strip_tac >>
  `MEM j bb.bb_instructions` by metis_tac[venomExecPropsTheory.phi_prefix_mem] >>
  metis_tac[phi_single_origin_block_frame]
QED

Theorem param_step_update_var[local]:
  is_param_opcode i.inst_opcode /\ ~MEM x i.inst_outputs ==>
  step_inst_base i (update_var x w s) =
  exec_result_map (update_var x w) (step_inst_base i s)
Proof
  simp[is_param_opcode_iff] >> strip_tac >>
  once_rewrite_tac[step_inst_base_def] >>
  pure_asm_rewrite_tac[opcode_case_def] >>
  namedCases_on `i.inst_operands` ["", "a args"] >> simp[exec_result_map_def] >>
  Cases_on `args` >> simp[exec_result_map_def] >>
  Cases_on `a` >> simp[exec_result_map_def] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >>
  simp[exec_result_map_def, COND_RAND, COND_RATOR] >>
  Cases_on `outs` >> simp[exec_result_map_def, COND_RAND, COND_RATOR] >>
  `out <> x` by fs[] >>
  simp[dftCommutationTheory.update_var_commutes] >>
  simp[update_var_def]
QED

Theorem param_prefix_update_var[local]:
  !xs x w s.
    EVERY (\i. is_param_opcode i.inst_opcode /\ ~MEM x i.inst_outputs) xs ==>
    prefix_eval xs (update_var x w s) =
    exec_result_map (update_var x w) (prefix_eval xs s)
Proof
  Induct >> simp[prefix_eval_def, exec_result_map_def] >>
  rpt gen_tac >> strip_tac >>
  `step_inst_base h (update_var x w s) =
    exec_result_map (update_var x w) (step_inst_base h s)` by
    (irule param_step_update_var >> simp[]) >>
  `(?t. step_inst_base h s = OK t) \/ (?e. step_inst_base h s = Error e)` by
    (irule prefix_step_range >> simp[]) >>
  simp[prefix_eval_def, exec_result_map_def]
QED

Theorem param_prefix_lookup_frame[local]:
  !xs s t x.
    EVERY (\i. is_param_opcode i.inst_opcode /\ ~MEM x i.inst_outputs) xs /\
    prefix_eval xs s = OK t ==> lookup_var x t = lookup_var x s
Proof
  Induct >> simp[prefix_eval_def] >> rpt gen_tac >> strip_tac >>
  `(?u. step_inst_base h s = OK u) \/ (?e. step_inst_base h s = Error e)` by
    (irule prefix_step_range >> simp[]) >> gvs[] >>
  `~is_terminator h.inst_opcode` by metis_tac[prefix_opcode_nonterminator] >>
  `lookup_var x u = lookup_var x s` by
    (drule_all venomInstProofs1Theory.step_inst_base_preserves_all >>
     simp[]) >>
  metis_tac[]
QED

Theorem selected_copies_param_commute[local]:
  !xs qs d s.
    EVERY (\j. is_param_opcode j.inst_opcode) qs /\
    (!i. MEM i xs ==> ?root out v.
      phi_single_origin d i = SOME root /\ i.inst_outputs = [out] /\
      lookup_var root s = SOME v /\
      (!j. MEM j xs ==> ~MEM root j.inst_outputs) /\
      (!j. MEM j qs ==> ~MEM root j.inst_outputs /\ ~MEM out j.inst_outputs)) ==>
    prefix_eval (MAP (transform_inst d) xs ++ qs) s =
    prefix_eval (qs ++ MAP (transform_inst d) xs) s
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  `?root out value. phi_single_origin d h = SOME root /\
    h.inst_outputs = [out] /\ lookup_var root s = SOME value /\
    (!j. MEM j qs ==> ~MEM root j.inst_outputs /\ ~MEM out j.inst_outputs)` by metis_tac[] >>
  `!u. step_inst_base (transform_inst d h) u =
    case lookup_var root u of SOME v => OK (update_var out v u)
      | NONE => Error "undefined operand"` by
    (gen_tac >> irule selected_copy_step >> simp[]) >>
  `prefix_eval (MAP (transform_inst d) xs ++ qs) (update_var out value s) =
   prefix_eval (qs ++ MAP (transform_inst d) xs) (update_var out value s)` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     `?r dst v. phi_single_origin d i = SOME r /\ i.inst_outputs = [dst] /\
       lookup_var r s = SOME v /\
       (!j. j = h \/ MEM j xs ==> ~MEM r j.inst_outputs) /\
       (!j. MEM j qs ==> ~MEM r j.inst_outputs /\ ~MEM dst j.inst_outputs)` by metis_tac[] >>
     qexistsl [`r`, `dst`, `v`] >>
     simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     metis_tac[MEM, lookup_var_def]) >>
  `prefix_eval qs (update_var out value s) =
    exec_result_map (update_var out value) (prefix_eval qs s)` by
    (irule param_prefix_update_var >> fs[EVERY_MEM]) >>
  `(?t. prefix_eval qs s = OK t) \/ (?e. prefix_eval qs s = Error e)` by
    (irule prefix_eval_range >> fs[EVERY_MEM]) >>
  simp[prefix_eval_def] >>
  qpat_x_assum `prefix_eval (MAP _ xs ++ qs) _ = _` (fn th => rewrite_tac[th]) >>
  simp[prefix_eval_append, exec_result_map_def] >>
  `lookup_var root t = lookup_var root s` by
    (irule param_prefix_lookup_frame >> qexists `qs` >> fs[EVERY_MEM]) >>
  simp[prefix_eval_def]
QED

Theorem phi_selected_copies_param_commute[local]:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  fn_entry_label fn = SOME s0.vs_current_bb /\ s0.vs_vars = FEMPTY /\
  source_entry_reachable ctx fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s (FILTER (\i. phi_single_origin (dfg_build_function fn) i = NONE)
    (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) = OK t ==>
  prefix_eval (MAP (transform_inst (dfg_build_function fn))
    (FILTER (\i. ?r. phi_single_origin (dfg_build_function fn) i = SOME r)
      (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) ++
    FILTER (\i. is_param_opcode i.inst_opcode) bb.bb_instructions) t =
  prefix_eval (FILTER (\i. is_param_opcode i.inst_opcode) bb.bb_instructions ++
    MAP (transform_inst (dfg_build_function fn))
    (FILTER (\i. ?r. phi_single_origin (dfg_build_function fn) i = SOME r)
      (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions))) t
Proof
  strip_tac >> irule selected_copies_param_commute >>
  simp[EVERY_FILTER, MEM_FILTER] >> rpt strip_tac >>
  `MEM i bb.bb_instructions /\ i.inst_opcode = PHI` by
    metis_tac[venomExecPropsTheory.phi_prefix_mem] >>
  drule_all phi_single_origin_incoming_value >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label] >>
  `fn_reachable fn bb.bb_label` by
    metis_tac[source_entry_reachable_inv, source_entry_inv_def] >>
  `!j. MEM j bb.bb_instructions ==> ~MEM r j.inst_outputs` by
    metis_tac[phi_single_origin_block_frame] >>
  qexistsl [`r`, `out`, `value`] >> simp[] >> conj_tac
  >- (`!j. MEM j (FILTER (\i. phi_single_origin (dfg_build_function fn) i = NONE)
          (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) ==>
          MEM j bb.bb_instructions` by
        (simp[MEM_FILTER] >> metis_tac[venomExecPropsTheory.phi_prefix_mem]) >>
      metis_tac[phi_single_origin_eval_phis_frame]) >>
  conj_tac
  >- metis_tac[venomExecPropsTheory.phi_prefix_mem] >>
  rpt strip_tac >> simp[] >>
  `i = j` by
    (irule venomWfPropsTheory.ssa_outputs_same_inst >>
     conj_tac
     >- (qexists `fn` >> fs[venomWfTheory.wf_ssa_def] >>
         metis_tac[venomInstTheory.fmp_fn_insts_blocks_intro]) >>
     qexists `out` >> simp[]) >>
  gvs[is_param_opcode_iff]
QED

Theorem phi_complete_prefix_result:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  fn_entry_label fn = SOME s0.vs_current_bb /\ s0.vs_vars = FEMPTY /\
  source_entry_reachable ctx fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  (case eval_phis s (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) of
     OK p => prefix_eval (FILTER (\i. is_param_opcode i.inst_opcode) bb.bb_instructions) p
   | other => other) =
  (case eval_phis s (FILTER (\i. phi_single_origin (dfg_build_function fn) i = NONE)
      (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) of
     OK k => prefix_eval
       (FILTER (\i. is_param_opcode i.inst_opcode) bb.bb_instructions ++
        MAP (transform_inst (dfg_build_function fn))
          (FILTER (\i. ?r. phi_single_origin (dfg_build_function fn) i = SOME r)
            (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions))) k
   | other => other)
Proof
  strip_tac >>
  drule_all phi_parallel_selected_copies >> disch_then SUBST1_TAC >>
  `(?t. eval_phis s (FILTER (\i. phi_single_origin (dfg_build_function fn) i = NONE)
      (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) = OK t) \/
   (?e. eval_phis s (FILTER (\i. phi_single_origin (dfg_build_function fn) i = NONE)
      (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) = Error e)` by
    metis_tac[eval_phis_ok_or_error_defs] >> simp[] >>
  drule_all phi_selected_copies_success >> strip_tac >> simp[] >>
  drule_all phi_selected_copies_param_commute >>
  simp[prefix_eval_append]
QED

Theorem run_block_prefix_eval:
  bb.bb_instructions = phis ++ xs ++ rest /\
  EVERY (\i. i.inst_opcode = PHI) phis /\
  EVERY (\i. is_param_opcode i.inst_opcode \/ i.inst_opcode = ASSIGN) xs /\
  EVERY (\i. i.inst_opcode <> PHI) rest ==>
  run_block fuel ctx bb s =
  case (case eval_phis s phis of
          OK p => prefix_eval xs p | other => other) of
    OK t => exec_block fuel ctx bb
              (t with vs_inst_idx := LENGTH phis + LENGTH xs)
  | other => other
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) (xs ++ rest)` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     `is_param_opcode i.inst_opcode \/ i.inst_opcode = ASSIGN` by metis_tac[] >>
     gvs[is_param_opcode_iff]) >>
  `phi_prefix_length bb.bb_instructions = LENGTH phis` by
    gvs[dft_phi_prefix_append, simplifyCfgAvailabilityTheory.scfg_phi_prefix_length] >>
  `eval_phis s bb.bb_instructions = eval_phis s phis` by
    gvs[dft_eval_phis_append] >>
  simp[run_block_def] >>
  `(?p. eval_phis s phis = OK p) \/ (?e. eval_phis s phis = Error e)` by
    metis_tac[eval_phis_ok_or_error_defs] >> simp[] >>
  irule prefix_eval_exec_block >> metis_tac[]
QED

Theorem phi_run_block_correct:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  fn_entry_label fn = SOME s0.vs_current_bb /\ s0.vs_vars = FEMPTY /\
  source_entry_reachable ctx fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\ pseudos_prefix bb ==>
  run_block fuel ctx bb s = run_block fuel ctx (transform_block (dfg_build_function fn) bb) s
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `bb_well_formed bb` by fs[venomWfTheory.wf_function_def] >>
  drule_all phi_complete_prefix_result >>
  qabbrev_tac `ps = TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions` >>
  qabbrev_tac `qs = FILTER (\i. is_param_opcode i.inst_opcode) bb.bb_instructions` >>
  qabbrev_tac `ks = FILTER (\i. phi_single_origin (dfg_build_function fn) i = NONE) ps` >>
  qabbrev_tac `cs = MAP (transform_inst (dfg_build_function fn))
    (FILTER (\i. ?r. phi_single_origin (dfg_build_function fn) i = SOME r) ps)` >>
  qabbrev_tac `rest = DROP (LENGTH ps + LENGTH qs) bb.bb_instructions` >>
  disch_tac >>
  `bb.bb_instructions = ps ++ qs ++ rest /\
   EVERY (\i. i.inst_opcode = PHI) ps /\
   EVERY (\i. is_param_opcode i.inst_opcode) qs /\
   EVERY (\i. ~is_pseudo i.inst_opcode) rest` by
    (drule_all bb_pseudo_prefix_layout >> simp[LET_THM, Abbr `ps`, Abbr `qs`, Abbr `rest`]) >>
  `EVERY (\i. i.inst_opcode = PHI) ks` by fs[Abbr `ks`, EVERY_FILTER, EVERY_MEM] >>
  `EVERY (\i. is_param_opcode i.inst_opcode \/ i.inst_opcode = ASSIGN) (qs ++ cs)` by
    (fs[EVERY_MEM, Abbr `cs`, MEM_MAP, MEM_FILTER] >> rpt strip_tac >>
     simp[transform_inst_def] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> PHI) rest` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i rest ==> ~is_pseudo _` (qspec_then `i` mp_tac) >>
     simp[venomInstTheory.is_pseudo_def]) >>
  `(transform_block (dfg_build_function fn) bb).bb_instructions = ks ++ (qs ++ cs) ++ rest` by
    (drule_all transform_insts_pseudo_prefix_layout >>
     simp[transform_block_def, LET_THM, Abbr `ks`, Abbr `cs`, Abbr `ps`, Abbr `qs`, Abbr `rest`]) >>
  `LENGTH ks + LENGTH (qs ++ cs) = LENGTH ps + LENGTH qs` by
    (mp_tac (Q.SPECL [`dfg_build_function fn`, `ps`] transform_phi_prefix_lengths) >>
     simp[Abbr `ks`, Abbr `cs`] >> decide_tac) >>
  `run_block fuel ctx bb s =
   case (case eval_phis s ps of OK p => prefix_eval qs p | other => other) of
     OK t => exec_block fuel ctx bb (t with vs_inst_idx := LENGTH ps + LENGTH qs)
   | other => other` by
    (irule run_block_prefix_eval >> gvs[]) >>
  `run_block fuel ctx (transform_block (dfg_build_function fn) bb) s =
   case (case eval_phis s ks of OK k => prefix_eval (qs ++ cs) k | other => other) of
     OK t => exec_block fuel ctx (transform_block (dfg_build_function fn) bb)
       (t with vs_inst_idx := LENGTH ks + LENGTH (qs ++ cs))
   | other => other` by
    (irule run_block_prefix_eval >> gvs[]) >>
  `!t. exec_block fuel ctx bb (t with vs_inst_idx := LENGTH ps + LENGTH qs) =
       exec_block fuel ctx (transform_block (dfg_build_function fn) bb)
         (t with vs_inst_idx := LENGTH ps + LENGTH qs)` by
    (gen_tac >> irule venomExecProofsTheory.exec_block_same_suffix >>
     simp[] >> gvs[DROP_APPEND, APPEND_ASSOC]) >>
  simp[]
QED
