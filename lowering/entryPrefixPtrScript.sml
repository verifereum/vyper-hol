(* Actual endpoint transport for the external entry prefix. *)
Theory entryPrefixPtr
Ancestors entryDispatchPtr ptrSafeRun ptrDiscipline moduleLoweringProps
  moduleLowering fragExec venomExecSemantics venomInst venomState list
  finite_map words contextCodegenRel codegenRel compileEnv emitHelperProps
  exprLoweringProps typedCopyArrayPtr

Theorem ptr_safe_jump_exact_continuation:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ptr_safe_blocks D lo fuel ctx fn PG
    (entry_prov fn (jump_to lbl s) G)
    (entry_taint_vars fn (jump_to lbl s) tn) (jump_to lbl s) ==>
  ptr_safe_run D lo fuel ctx fn PG G tn s
Proof
  strip_tac >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def] >>
  conj_tac
  >- (simp[ptr_safe_step_def, ptr_inst_ok_def] >>
      simp[access_ok_def, taint_ok_def] >>
      simp[source_memory_write_ranges_def, source_memory_read_ranges_def,
           step_inst_non_invoke, step_inst_base_def, mk_inst_def,
           jump_to_def, op_taint_def]) >>
  simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
       is_terminator_def]
QED

Theorem entry_taint_vars_frame:
  (entry_taint_vars fn s tn).t_mem = tn.t_mem /\
  (entry_taint_vars fn s tn).t_stor = tn.t_stor /\
  (entry_taint_vars fn s tn).t_trans = tn.t_trans /\
  (entry_taint_vars fn s tn).t_imm = tn.t_imm
Proof
  simp[entry_taint_vars_def, AllCaseEqs()] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[]
QED

Theorem dispatch_scalar_taint_frame:
  MEM opc [CALLDATASIZE; CALLDATALOAD; LT; EQ; ISZERO; SHR] /\
  vars_pc_only s t ==>
  (step_taint (mk_inst id opc ops outs) s t tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id opc ops outs) s t tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc ops outs) s t tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id opc ops outs) s t tn).t_imm = tn.t_imm
Proof
  strip_tac >> fs[vars_pc_only_def, venom_state_component_equality, MEM] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, written_taint_def, mk_inst_def,
       source_memory_write_ranges_def, adopt_reset_def,
       store_taint_def, imm_taint_def, range_bytes_def, FLOOKUP_DEF,
       pred_setTheory.EXTENSION, SF CONJ_ss] >>
  namedCases_on `ops` ["", "a rest"] >> simp[] >>
  namedCases_on `rest` ["", "b more"] >> simp[] >>
  namedCases_on `more` ["", "c tail"] >> simp[] >>
  Cases_on `tail` >> simp[]
QED

Theorem compile_selector_checks_ptr_endpoint:
  !sels mid st st'.
    compile_selector_checks mid sels st = ((), st') ==>
    !ctx fn ss m lo PG G tn.
      fn_has_code st st' fn /\ eval_operand mid ss = SOME m /\
      fresh_vars_wrt st ss /\ ~ss.vs_halted /\
      ss.vs_current_bb = st.cs_current_bb /\
      ss.vs_inst_idx = LENGTH st.cs_current_insts /\
      allocas_from lo ss /\ (ctx_has_dalloca ctx ==> allocas_below_fmp ss) /\
      op_taint tn mid = {} /\
      (st'.cs_current_insts = [] ==>
        ?bb. lookup_block st'.cs_current_bb fn.fn_blocks = SOME bb /\
             phi_prefix_length bb.bb_instructions = 0) ==>
      ?tt G' tn'.
        vars_pc_only ss tt /\ fresh_vars_wrt st' tt /\ ~tt.vs_halted /\
        tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
        tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
        (case selector_hit m sels of
           SOME lbl => tt.vs_current_bb = lbl /\ tt.vs_inst_idx = 0
         | NONE => tt.vs_current_bb = st'.cs_current_bb /\
                   tt.vs_inst_idx = LENGTH st'.cs_current_insts) /\
        !D. (!fuel. case selector_hit m sels of
           SOME lbl => ptr_safe_blocks D lo fuel ctx fn PG G' tn' tt
         | NONE => ptr_safe_run D lo fuel ctx fn PG G' tn' tt) ==>
          !fuel. ptr_safe_run D lo fuel ctx fn PG G tn ss
Proof
  Induct
  >- (simp[compile_selector_checks_def, comp_return_def, selector_hit_def] >>
      rpt strip_tac >> qexistsl_tac [`ss`, `G`, `tn`] >>
      simp[vars_pc_only_refl]) >>
  Cases >> rename1 `(sel, lbl)` >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  drule_all compile_selector_checks_cons_layout >> strip_tac >>
  qpat_x_assum `compile_selector_checks mid ((sel,lbl)::sels) _ = _` kall_tac >>
  qpat_x_assum `fn_has_code st st' fn` kall_tac >>
  qabbrev_tac `out = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `v = bool_to_word (m = n2w sel)` >>
  qabbrev_tac `u = update_var out v ss with vs_inst_idx := SUC ss.vs_inst_idx` >>
  `mid <> Var out` by
    (simp[Abbr `out`] >> strip_tac >> gvs[] >>
     qpat_x_assum `fresh_vars_wrt st ss`
       (qspec_then `st.cs_next_var` mp_tac o REWRITE_RULE [fresh_vars_wrt_def]) >>
     gvs[eval_operand_def, lookup_var_def, TO_FLOOKUP]) >>
  `vars_pc_only ss u` by
    simp[Abbr `u`, vars_pc_only_inst_idx, vars_pc_only_update_var,
         vars_pc_only_refl] >>
  `fresh_vars_wrt tail u` by
    (simp[Abbr `u`, control_moves_keep_vars] >>
     irule fresh_vars_wrt_advance >>
     qexistsl_tac [`st.cs_next_var`, `st`] >> simp[Abbr `out`]) >>
  `eval_operand mid u = SOME m` by
    (simp[Abbr `u`, control_moves_keep_vars] >>
     irule eval_operand_update_fresh >> simp[] >>
     qexistsl_tac [`st.cs_next_var`, `st`] >> simp[Abbr `out`]) >>
  `?nb. lookup_block next fn.fn_blocks = SOME nb /\
        phi_prefix_length nb.bb_instructions = 0` by
    (drule_all compile_selector_checks_phi_free >> simp[]) >>
  qmatch_asmsub_abbrev_tac `get_instruction bb (LENGTH _) = SOME eqi` >>
  qabbrev_tac `G1 = step_prov PG G eqi (update_var out v ss)` >>
  qabbrev_tac `tn1 = step_taint eqi ss (update_var out v ss) tn` >>
  `op_taint tn1 (Var out) = {}` by
    (simp[Abbr `tn1`, Abbr `eqi`] >>
     irule dispatch_scalar_output_clean >> simp[op_taint_def]) >>
  `op_taint tn1 mid = {}` by
    simp[Abbr `tn1`, Abbr `eqi`, Abbr `out`,
         step_taint_single_output_preserves_other_operand] >>
  `tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by
    (simp[Abbr `tn1`, Abbr `eqi`] >>
     irule dispatch_scalar_taint_frame >>
     simp[vars_pc_only_update_var, vars_pc_only_refl]) >>
  `u.vs_current_bb = st.cs_current_bb /\
   u.vs_inst_idx = SUC (LENGTH st.cs_current_insts) /\
   eval_operand (Var out) u = SOME v /\ ~u.vs_halted /\
   allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (fs[Abbr `u`, update_var_def, eval_operand_def, lookup_var_def,
        FLOOKUP_UPDATE, allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `!D fuel. ptr_safe_blocks D lo fuel ctx fn PG
      (entry_prov fn (jump_to (if v <> 0w then match else next) u) G1)
      (entry_taint_vars fn (jump_to (if v <> 0w then match else next) u) tn1)
      (jump_to (if v <> 0w then match else next) u) ==>
      ptr_safe_run D lo fuel ctx fn PG G tn ss` by
    (rpt strip_tac >>
     `step_inst fuel ctx eqi ss = OK (update_var out v ss)` by
       simp[Abbr `eqi`, Abbr `v`, step_inst_non_invoke, mk_inst_def,
            step_inst_base_def, exec_pure2_def, eval_operand_def] >>
     irule ptr_safe_run_scalar_continuation >>
     qexistsl_tac [`bb`, `eqi`, `update_var out v ss`] >>
     simp[Abbr `eqi`, is_terminator_def, mk_inst_def, update_var_def] >>
     reverse conj_tac
     >- (irule (REWRITE_RULE [mk_inst_def] ptr_safe_dispatch_scalar_step) >>
         simp[MEM, op_taint_def] >> qexists_tac `update_var out v ss` >>
         gvs[mk_inst_def, update_var_def]) >>
     `ptr_safe_run D lo fuel ctx fn PG G1 tn1 u` suffices_by
       simp[] >>
     irule ptr_safe_cond_jump_continuation >> simp[] >>
     qexistsl_tac [`st.cs_next_id + 1`, `next`, `Var out`, `v`, `match`] >> simp[]) >>
  Cases_on `m = n2w sel`
  >- (suspend "hit") >>
  suspend "miss"
QED

Resume compile_selector_checks_ptr_endpoint[hit]:
  qpat_x_assum `!mid st st'. _` kall_tac >>
  `entry_prov fn (jump_to match u) G1 = G1 /\
   entry_taint_vars fn (jump_to match u) tn1 = tn1` by
    (irule entry_ghost_no_phi >>
     simp[jump_to_def, phi_prefix_length_def, mk_inst_def]) >>
  qabbrev_tac `tt = jump_to lbl (jump_to match u)` >>
  qexistsl_tac [`tt`, `entry_prov fn tt G1`, `entry_taint_vars fn tt tn1`] >>
  simp[entry_taint_vars_frame, selector_hit_def] >>
  `vars_pc_only ss tt` by
    simp[Abbr `tt`, vars_pc_only_jump_to] >>
  `fresh_vars_wrt st' tt` by
    (simp[Abbr `tt`, control_moves_keep_vars] >>
     irule fresh_vars_wrt_mono >> qexists_tac `tail` >> simp[] >>
     drule compile_selector_checks_next_var >> simp[]) >>
  simp[Abbr `tt`, jump_to_def] >>
  rpt strip_tac >>
  qpat_x_assum `!D fuel. _ ==> ptr_safe_run _ _ _ _ _ _ _ _ ss`
    (qspecl_then [`D`, `fuel`] irule) >>
  simp[Abbr `v`, bool_to_word_def] >>
  irule ptr_safe_blocks_from_phi_free_run >>
  reverse conj_tac >- simp[jump_to_def, phi_prefix_length_def, mk_inst_def] >>
  gen_tac >> irule ptr_safe_jump_exact_continuation >>
  simp[jump_to_def] >>
  conj_tac >- (rpt strip_tac >> fs[allocas_below_fmp_def] >> metis_tac[]) >>
  conj_tac >- (fs[allocas_from_def] >> metis_tac[]) >>
  qexistsl_tac [`st.cs_next_id + 2`, `lbl`] >>
  simp[get_instruction_def]
QED

Resume compile_selector_checks_ptr_endpoint[miss]:
  `entry_prov fn (jump_to next u) G1 = G1 /\
   entry_taint_vars fn (jump_to next u) tn1 = tn1` by
    (irule entry_ghost_no_phi >> simp[jump_to_def] >> metis_tac[]) >>
  qpat_x_assum `!mid st st'. _` (drule_then mp_tac) >>
  disch_then (qspecl_then [`ctx`, `fn`, `jump_to next u`, `m`, `lo`, `PG`, `G1`, `tn1`] mp_tac) >>
  impl_tac
  >- (simp[jump_to_def, control_moves_keep_vars] >>
      fs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  strip_tac >>
  qexistsl_tac [`tt`, `G'`, `tn'`] >>
  `vars_pc_only ss tt` by
    (irule vars_pc_only_trans >> qexists_tac `jump_to next u` >>
     simp[vars_pc_only_jump_to]) >>
  simp[selector_hit_def] >>
  rpt strip_tac >>
  qpat_x_assum `!D fuel. _ ==> ptr_safe_run _ _ _ _ _ _ _ _ ss`
    (qspecl_then [`D`, `fuel`] irule) >>
  simp[Abbr `v`, bool_to_word_def] >>
  irule ptr_safe_blocks_from_phi_free_run >>
  reverse conj_tac >- simp[jump_to_def] >>
  qpat_x_assum `!D. _` (qspec_then `D` irule) >> simp[]
QED

Finalise compile_selector_checks_ptr_endpoint

Theorem dispatch_scalar_update_ptr_endpoint:
  (!fuel. step_inst fuel ctx (mk_inst id opc ops [out]) s =
     OK (update_var out value s)) ==>
  !fn bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) ==>
  !st st_next lo PG G tn.
  MEM opc [CALLDATASIZE; CALLDATALOAD; LT; EQ; ISZERO; SHR] /\
  EVERY (\op. op_taint tn op = {}) ops /\
  (!a b. ops <> [Var a; Var b]) /\
  out = STRING #"%" (toString st.cs_next_var) /\
  st_next.cs_next_var = SUC st.cs_next_var /\
  fresh_vars_wrt st s /\ ~s.vs_halted /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?u G' tn'.
    u = (update_var out value s with vs_inst_idx := SUC s.vs_inst_idx) /\
    G' = step_prov PG G (mk_inst id opc ops [out]) (update_var out value s) /\
    tn' = step_taint (mk_inst id opc ops [out]) s (update_var out value s) tn /\
    vars_pc_only s u /\ fresh_vars_wrt st_next u /\ ~u.vs_halted /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = SUC s.vs_inst_idx /\
    eval_operand (Var out) u = SOME value /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    op_taint tn' (Var out) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!D fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' u ==>
              ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qexistsl_tac [`update_var out value s with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G (mk_inst id opc ops [out]) (update_var out value s)`,
    `step_taint (mk_inst id opc ops [out]) s (update_var out value s) tn`] >>
  `vars_pc_only s (update_var out value s)` by
    simp[vars_pc_only_update_var, vars_pc_only_refl] >>
  `fresh_vars_wrt st_next (update_var out value s)` by
    (irule fresh_vars_wrt_advance >> qexistsl_tac [`st.cs_next_var`, `st`] >> simp[]) >>
  `op_taint (step_taint (mk_inst id opc ops [out]) s (update_var out value s) tn) (Var out) = {}` by
    metis_tac[dispatch_scalar_output_clean] >>
  `(step_taint (mk_inst id opc ops [out]) s (update_var out value s) tn).t_mem = tn.t_mem /\
   (step_taint (mk_inst id opc ops [out]) s (update_var out value s) tn).t_stor = tn.t_stor /\
   (step_taint (mk_inst id opc ops [out]) s (update_var out value s) tn).t_trans = tn.t_trans /\
   (step_taint (mk_inst id opc ops [out]) s (update_var out value s) tn).t_imm = tn.t_imm` by
    metis_tac[dispatch_scalar_taint_frame] >>
  simp[vars_pc_only_inst_idx, control_moves_keep_vars, update_var_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
       allocas_from_def, allocas_below_fmp_def] >>
  conj_tac >- (fs[allocas_from_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> fs[allocas_below_fmp_def] >> metis_tac[]) >>
  rpt strip_tac >>
  irule ptr_safe_run_scalar_continuation >>
  qexistsl_tac [`bb`, `mk_inst id opc ops [out]`, `update_var out value s`] >>
  simp[update_var_def] >>
  conj_tac
  >- (gvs[mk_inst_def, MEM, is_terminator_def]) >>
  gvs[ptr_safe_dispatch_scalar_step]
QED


