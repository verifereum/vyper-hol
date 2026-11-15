(* Checked joint prefixes retain their actual instruction history and ghosts. *)
Theory loweringJointPrefixHistory
Ancestors
  loweringOriginHistory loweringBudgetRunHistory loweringTerminalHistory
  loweringCallBudgetHistory fragGasOriginPtr fragGasFocus fragExec
  typedCopyArrayPtr
  entryReachBodyFmp vyperLoweringCorrect vyperCompiler
  ptrSafeRun ptrDiscipline memSafeRun gasEvents
  contextCodegenRel contextCodegenRelProps venomExecSemantics venomExecProofs
  venomInstProofs venomInst venomState finite_map list arithmetic

Theorem gas_origin_ptr_focus_certificate:
  !D lo explicit ctx root marks leaf leaf_pg leaf_g leaf_tn finish following.
    MEM root.bp_fn ctx.ctx_functions /\
    (!fn. MEM fn ctx.ctx_functions ==>
      ALL_DISTINCT (fn_labels fn) /\
      !bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    gas_origin_ptr_focus (D,lo,explicit,ctx,root.bp_fn,root.bp_params)
      (root.bp_state,root.bp_prov,root.bp_taint) marks
      (leaf,leaf_pg,leaf_g,leaf_tn,finish) /\
    active_inst leaf following finish ==>
    ?history. lower_budget_certificate (D,lo,explicit,ctx) root history marks
      (INL (leaf,leaf_pg,leaf_g,leaf_tn,finish))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all gas_origin_ptr_focus_start >> strip_tac >>
  `lower_budget_path T (D,lo,explicit,ctx) root [] [] root` by
    (irule lower_budget_path_entry >> simp[] >> metis_tac[]) >>
  drule gas_origin_ptr_focus_history >>
  disch_then (qspecl_then [`root`, `[]`, `[]`, `root`, `following`] mp_tac) >>
  impl_tac >- metis_tac[] >> simp[] >> strip_tac >>
  rename1 `lower_budget_path T (D,lo,explicit,ctx) root history marks endpoint` >>
  qexists_tac `history` >> simp[lower_budget_certificate_def] >> metis_tac[]
QED

(* Only this runtime supplier uses the current compiler's shape restriction. *)
Theorem lower_vyper_runtime_unit_recorder_shape:
  !tops rpolicy unit.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops ==>
    !fn. MEM fn unit.cu_context.ctx_functions ==>
      ALL_DISTINCT (fn_labels fn) /\
      !bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0
Proof
  rpt gen_tac >> strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  `~ctx_has_dalloca unit.cu_context` by metis_tac[entry_runtime_no_dalloca] >>
  rpt gen_tac >> strip_tac >>
  rename1 `MEM func unit.cu_context.ctx_functions` >> conj_tac
  >- fs[lowering_context_ok_def, EVERY_MEM] >>
  rpt gen_tac >> strip_tac >> irule no_phis_phi_prefix_length_zero >>
  qsuff_tac `EVERY (\inst. inst.inst_opcode <> PHI) (fn_insts func)`
  >- (rewrite_tac[fn_insts_def, EVERY_fn_insts_blocks] >>
      simp[EVERY_MEM] >> metis_tac[]) >>
  fs[lowering_context_ok_def, ptr_ok_check_def, ctx_has_dalloca_def,
     EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED

Theorem lower_vyper_runtime_unit_focus_certificate:
  !tops rpolicy unit D explicit fn vs marks leaf leaf_pg leaf_g leaf_tn finish following.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    gas_origin_ptr_focus (D,0,explicit,unit.cu_context,fn,[])
      ((vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                   vs_inst_idx := 0 |>),FEMPTY,entry_taint)
      marks (leaf,leaf_pg,leaf_g,leaf_tn,finish) /\
    active_inst leaf following finish ==>
    ?p history.
      p = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
        bp_taint := entry_taint; bp_fn := fn;
        bp_state := vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                               vs_inst_idx := 0 |> |> /\
      lower_budget_certificate (D,0,explicit,unit.cu_context) p history marks
        (INL (leaf,leaf_pg,leaf_g,leaf_tn,finish))
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `active_inst leaf following end_state` >>
  `MEM fn unit.cu_context.ctx_functions` by metis_tac[lookup_function_MEM] >>
  qspecl_then [`tops`, `rpolicy`, `unit`] mp_tac lower_vyper_runtime_unit_recorder_shape >>
  impl_tac >- simp[] >> disch_tac >>
  qabbrev_tac `p = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
    bp_taint := entry_taint; bp_fn := fn;
    bp_state := vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                           vs_inst_idx := 0 |> |>` >>
  qexists_tac `p` >> simp[] >>
  qspecl_then [`D`, `0`, `explicit`, `unit.cu_context`, `p`, `marks`,
    `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `end_state`, `following`]
    mp_tac gas_origin_ptr_focus_certificate >> simp[Abbr`p`] >> metis_tac[]
QED
