(*
 * DFT's facts toward its O1 stage contract (o1ContractDft's pieces), in
 * the gas form.
 *
 * Each function of C' is dft_fn of its function in C (ctx_pass_stage_dft).
 * Under the run's pre (fallible instructions kept in order) and row 7
 * (SSA, no ALLOCA), each is a DFT schedule in the sense of dftRunRel
 * (dft_fn_rel), so:
 *   - DFT may move a GAS read past another GAS read or an INVOKE, so C'
 *     consumes the gas readings in another order than C.  The run of C'
 *     from vs' fixes the readings each GAS instruction gets; C, run from
 *     the gas variant of vs' holding those readings in C's order, takes
 *     the same path, ends alike, and every state C' reaches has a
 *     counterpart C reaches, which carries the memory invariant to C'
 *     (dft_ctx_sim_gas);
 *   - the schedule is SSA (dft_block_rel_wf_ssa), for row 8.
 * An instruction reading a label as a value (LowerDload's
 * ADD [_; Label "code_end"]) has it bound by code_layout_valid
 * (dft_ctx_labels_bound), so it cannot error where the original did not.
 *)
Theory dftContractGas
Ancestors
  dftGasOracleFromList dftGasOracleToList dftGasOracleSim dftGasOracleInv
  dftGasOracleDefs venomRetProps contextRawReachable ptrDiscipline passSimulationDefs
  o1ContractCfgNorm gasOracleReplay dftWf dftCorrectnessFinal stackPlanGen contextCodegenRel
  o1DftStep dftSsaPreserve dftRunRel dftScheduleOrder dftDefs o1PassLift
  o1PassContract unitMemInv unitShapeDefs lowerDloadDefs venomPassDispatcher
  venomExecSemantics venomWf venomInst venomState list
  dftGasMask gasEvents gasCount crossBlockSimProofs dftGasFromListRestore venomWfProps

Theorem ctx_pass_stage_dft:
  ctx_pass_stage rpolicy (CFP_Simple VP_DFT) view C C' ==>
  C'.ctx_entry = C.ctx_entry /\
  C'.ctx_global_reserved = C.ctx_global_reserved /\
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions
Proof
  rw[ctx_pass_stage_def] >>
  irule LIST_REL_mono >> goal_assum (drule_at Any) >>
  rw[fn_pass_step_def] >> gvs[]
QED

(* label_positions_ok leaves one value use of a label outside jumps,
   PHIs, INVOKE and CODECOPY: LowerDload's ADD [_; Label "code_end"],
   which code_layout_valid binds. *)
Triviality label_positions_value_label:
  label_positions_ok inst /\ MEM (Label l) inst.inst_operands /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> CODECOPY /\
  ~is_terminator inst.inst_opcode /\ ~is_pseudo inst.inst_opcode ==>
  l = "code_end"
Proof
  rpt strip_tac >> fs[label_positions_ok_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_pseudo_def, EVERY_MEM] >>
  res_tac >> fs[stackPlanTypesTheory.is_label_operand_def] >>
  (* only ADD [op; Label "code_end"] is left *)
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[stackPlanTypesTheory.is_label_operand_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[stackPlanTypesTheory.is_label_operand_def] >>
  first_x_assum (qspec_then `Label l` mp_tac) >>
  simp[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem dft_ctx_labels_bound:
  o1_ctx_shape C /\ code_layout_valid vs ==> ctx_labels_bound C vs.vs_labels
Proof
  rw[ctx_labels_bound_def] >>
  `o1_fn_shape C fn` by fs[o1_ctx_shape_def, EVERY_MEM] >>
  `inst_shape_ok inst` by fs[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >>
  `l = "code_end"` by
    (fs[inst_shape_ok_def] >> metis_tac[label_positions_value_label]) >>
  gvs[code_layout_valid_def, finite_mapTheory.FLOOKUP_DEF]
QED

Theorem dft_fn_rel_stage:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\
  EVERY (\fn. wf_ssa fn /\ EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn))
    C.ctx_functions /\
  EVERY fn_pseudos_prefix C.ctx_functions /\
  LIST_REL dft_fallible_order_kept C.ctx_functions C'.ctx_functions ==>
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions
Proof
  rw[LIST_REL_EL_EQN] >>
  `EL n C'.ctx_functions = dft_fn (EL n C.ctx_functions) /\
   dft_fallible_order_kept (EL n C.ctx_functions) (EL n C'.ctx_functions)`
    by metis_tac[] >>
  `MEM (EL n C.ctx_functions) C.ctx_functions` by metis_tac[EL_MEM] >>
  qabbrev_tac `f = EL n C.ctx_functions` >>
  `o1_fn_shape C f /\ wf_ssa f /\ EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts f) /\
   fn_pseudos_prefix f` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `wf_function f /\ fn_inst_wf f` by fs[o1_fn_shape_def] >>
  drule_all dftScheduleOrderTheory.dft_fn_block_rel >> strip_tac >>
  gvs[dft_fn_rel_def]
QED

(* ===== Assembly helpers ===== *)

Theorem dft_ctx_block_ids_distinct:
  !fs gs. LIST_REL dft_fn_rel fs gs ==>
  EVERY (\fn. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
                fn.fn_blocks) gs
Proof
  Induct_on `LIST_REL` >> rw[] >> rename1 `dft_fn_rel f g` >>
  rw[EVERY_MEM] >> rename1 `MEM bb' g.fn_blocks` >>
  `LIST_REL dftScheduleOrder$dft_block_rel f.fn_blocks g.fn_blocks /\
   wf_function f` by fs[dft_fn_rel_def] >>
  `?bb. MEM bb f.fn_blocks /\ dftScheduleOrder$dft_block_rel bb bb'` by
    (fs[LIST_REL_EL_EQN, MEM_EL] >> metis_tac[]) >>
  metis_tac[wf_fn_block_inst_ids_distinct, dft_block_rel_ids_distinct]
QED

Theorem dft_ctx_functions_map:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions ==>
  C'.ctx_functions = MAP dft_fn C.ctx_functions
Proof
  rw[LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP]
QED

Theorem dft_fn_name_eom[simp]:
  (dft_fn fn).fn_name = fn.fn_name /\ (dft_fn fn).fn_eom = fn.fn_eom
Proof
  simp[dft_fn_def] >> pairarg_tac >> simp[]
QED

Theorem collect_fn_eoms_dft:
  !fs. collect_fn_eoms (MAP dft_fn fs) = collect_fn_eoms fs
Proof
  Induct >> simp[collect_fn_eoms_def]
QED

Theorem dead_result_rel_halt_readings[local]:
  dead_result_rel D (Halt s) (Halt (s with vs_gas_readings := w))
Proof
  simp[dead_result_rel_def, accounts_agree_except_def,
       transient_agree_except_def, imms_agree_except_def,
       storage_agree_except_def, word_agree_except_def,
       vfmStateTheory.account_state_component_equality] >>
  irule EVERY2_refl >>
  simp[request_agree_except_def, accounts_agree_except_def,
       transient_agree_except_def, storage_agree_except_def,
       word_agree_except_def, vfmStateTheory.account_state_component_equality,
       extCallOracleTheory.call_request_component_equality]
QED

Theorem dead_result_rel_gas_halt:
  gas_variant a c /\ gas_variant b c ==> dead_result_rel D (Halt a) (Halt b)
Proof
  rw[gas_variant_def] >>
  `b = a with vs_gas_readings := b.vs_gas_readings` by
    fs[venom_state_component_equality] >>
  pop_assum SUBST1_TAC >> simp[dead_result_rel_halt_readings]
QED

Theorem gas_dft_dead_result:
  gas_res_rel r e /\ dft_res_rel e e' /\ gas_res_rel r' e' /\
  terminates r /\ (!v t. r <> IntRet v t) /\ (!t. r <> OK t) ==>
  dead_result_rel D r r'
Proof
  Cases_on `r` >> Cases_on `e` >>
  simp[gas_res_rel_def, terminates_def, dft_res_rel_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `r'` >> gvs[gas_res_rel_def]
  >~ [`dead_result_rel _ (Halt _) (Halt _)`]
  >- metis_tac[dead_result_rel_gas_halt] >>
  gvs[dead_result_rel_def]
QED

Theorem lookup_function_name[local]:
  !fns. lookup_function name fns = SOME fn ==> fn.fn_name = name
Proof
  Induct >> rw[lookup_function_def, FIND_thm] >> gvs[lookup_function_def]
QED

(* o1_fn_shape: the entry function has no RET, RETFMP or DRET. *)
Theorem o1_ctx_shape_run_context_no_intret:
  o1_ctx_shape C ==> run_context fuel C vs <> IntRet vals t
Proof
  strip_tac >> irule run_context_not_int_ret >> rpt strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `fn.fn_name = name` by metis_tac[lookup_function_name] >>
  `o1_fn_shape C fn` by gvs[o1_ctx_shape_def, EVERY_MEM] >>
  gvs[o1_fn_shape_def, entry_fn_no_return_def]
QED

Theorem o1_ctx_shape_wf_functions:
  o1_ctx_shape C ==> EVERY wf_function C.ctx_functions
Proof
  rw[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM]
QED

(* dft_fn keeps wf_function on o1-shaped functions (dft_fn_wf_function). *)
Theorem dft_ctx_wf_functions:
  o1_ctx_shape C /\ C'.ctx_functions = MAP dft_fn C.ctx_functions ==>
  EVERY wf_function C'.ctx_functions
Proof
  rw[EVERY_MEM, MEM_MAP] >> irule dftLiftingTheory.dft_fn_wf_function >>
  gvs[o1_ctx_shape_def, EVERY_MEM] >> first_x_assum drule >>
  simp[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM]
QED

Theorem gas_res_rel_terminates:
  gas_res_rel r e /\ terminates r ==> terminates e
Proof
  Cases_on `r` >> Cases_on `e` >> simp[gas_res_rel_def, terminates_def]
QED

Theorem lowered_mem_fact_gas_readings[simp]:
  lowered_mem_fact eom ctx fn inst (t with vs_gas_readings := ws) <=>
  lowered_mem_fact eom ctx fn inst t
Proof
  `inst_mem_ranges inst (t with vs_gas_readings := ws) = inst_mem_ranges inst t` by
    (irule supply_inst_mem_ranges_cong >> simp[]) >>
  simp[lowered_mem_fact_def, lowered_mem_ok_def, in_revert_forward_def]
QED

(* The witness vs holds the readings C' consumes from vs', reordered to
   the order C reads them in.  Through the oracle semantics
   (dftGasOracleDefs): gas_oracle_from_list turns the run of C' from vs'
   into an oracle run, gas_oracle_to_list turns the oracle run of C into a
   list run from vs' with readings W, and the two oracle runs agree
   (dft_ev_context_sim) and carry the memory fact (dft_ev_lowered_inv); vs
   is vs' with readings W and fuel' is fuel.  The entry function returns
   no internal value (o1_fn_shape; venomRetProps' run_context_not_int_ret),
   so the context's run never ends in IntRet.  lowered_mem_fact reads
   operands, memory ranges and vs_initial_fmp, not vs_gas_readings, and
   dft_fn keeps fn_eom, so max_live_eom C' = max_live_eom C. *)
Theorem dft_ctx_sim_gas:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ C'.ctx_global_reserved = C.ctx_global_reserved /\
  o1_ctx_shape C /\
  ctx_labels_bound C vs'.vs_labels /\ o1_run_state_ok vs' ==>
  ?vs. gas_variant vs vs' /\ ctx_sim D C C' vs vs' /\
       (o1_lowered_inv C vs ==> o1_lowered_inv C' vs')
Proof
  strip_tac >>
  `C'.ctx_functions = MAP dft_fn C.ctx_functions` by
    metis_tac[dft_ctx_functions_map] >>
  drule dft_ctx_block_ids_distinct >> strip_tac >>
  drule_all o1_ctx_shape_wf_functions >> strip_tac >>
  drule_all dft_ctx_wf_functions >> strip_tac >>
  mp_tac (Q.INST [`ctx:venom_context` |-> `C'`, `s:venom_state` |-> `vs'`]
            gas_oracle_from_list) >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (Q.INST [`ctx:venom_context` |-> `C`, `s:venom_state` |-> `vs'`]
            gas_oracle_to_list) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_context _ C (vs' with vs_gas_readings := rds)` >>
  qexists_tac `vs' with vs_gas_readings := rds` >>
  conj_tac >- simp[gas_variant_def, venom_state_component_equality] >>
  conj_tac
  >- (rw[ctx_sim_def] >> qexists_tac `fuel` >>
      irule gas_dft_dead_result >>
      simp[run_context_not_ok, o1_ctx_shape_run_context_no_intret] >>
      qexistsl [`ev_context orc fuel C vs'`, `ev_context orc fuel C' vs'`] >>
      simp[] >> irule dft_ev_context_sim >> simp[] >>
      metis_tac[gas_res_rel_terminates]) >>
  rw[o1_lowered_inv_def] >> qexists_tac `eom` >>
  conj_tac >- gvs[max_live_eom_def, collect_fn_eoms_dft] >>
  gvs[mem_inv_raw_reachable] >>
  `!p d fn inst t. ev_reachable orc vs' C p d fn inst t ==>
     lowered_mem_fact eom C fn inst t` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  `!p d fn inst t. ev_reachable orc vs' C' p d fn inst t ==>
     lowered_mem_fact eom C' fn inst t` by
    (mp_tac (Q.INST [`s:venom_state` |-> `vs'`] dft_ev_lowered_inv) >>
     simp[] >> impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  conj_tac
  >- (simp[lookup_function_map, dft_fn_entry_label] >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem dft_out_wf_ssa:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions ==>
  EVERY wf_ssa C'.ctx_functions
Proof
  rw[LIST_REL_EL_EQN, EVERY_EL] >>
  `EL n C'.ctx_functions = dft_fn (EL n C.ctx_functions) /\
   dft_fn_rel (EL n C.ctx_functions) (EL n C'.ctx_functions)` by metis_tac[] >>
  qabbrev_tac `f = EL n C.ctx_functions` >>
  gvs[dft_fn_rel_def] >>
  `dft_fn f = f with fn_blocks := (dft_fn f).fn_blocks` by
    (rewrite_tac[dft_fn_def, LET_THM] >>
     CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >> simp[]) >>
  pop_assum (fn th => ONCE_REWRITE_TAC[th]) >>
  irule dftSsaPreserveTheory.dft_block_rel_wf_ssa >> simp[]
QED

(* The actual entry run of a context, as its entry function's block run. *)
Theorem run_context_entry_blocks:
  ctx.ctx_entry = SOME nm /\ lookup_function nm ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  run_context fuel ctx s =
  run_blocks fuel ctx fn
    (s with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
Proof
  simp[run_context_def, run_function_def]
QED

Theorem run_blocks_terminates_fuel_eq[local]:
  terminates (run_blocks f1 ctx fn s) /\ terminates (run_blocks f2 ctx fn s) ==>
  run_blocks f1 ctx fn s = run_blocks f2 ctx fn s
Proof
  rpt strip_tac >> Cases_on `f1 <= f2`
  >- (mp_tac (Q.SPECL [`f1`, `ctx`, `fn`, `s`] run_blocks_fuel_mono) >>
      simp[] >> disch_then (qspec_then `f2 - f1` mp_tac) >> simp[])
  >> mp_tac (Q.SPECL [`f2`, `ctx`, `fn`, `s`] run_blocks_fuel_mono) >>
  simp[] >> disch_then (qspec_then `f1 - f2` mp_tac) >> simp[]
QED

Theorem entry_gas_update_comm[local]:
  (s with <| vs_prev_bb := NONE; vs_current_bb := l; vs_inst_idx := 0 |>)
    with vs_gas_readings := g =
  s with <| vs_gas_readings := g; vs_prev_bb := NONE; vs_current_bb := l;
            vs_inst_idx := 0 |>
Proof
  simp[venom_state_component_equality]
QED

(* Same-witness fuel extension of dft_blocks_gas_mask: its statement, plus the
 * one raw-slot mask's sites covering the compatible source's events at every
 * fuel, not only at the target's terminating fuel.  A closed property, carried
 * as an explicit premise by the prefix lifts below until the DFT line proves
 * it; nothing here assumes it. *)
Definition dft_blocks_gas_prefix_def:
  dft_blocks_gas_prefix <=>
  !fuel C C' fn fn' s.
    LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
    LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
    o1_ctx_shape C /\ o1_ctx_shape C' /\
    MEM fn C.ctx_functions /\ fn' = dft_fn fn /\
    dft_fn_rel fn fn' /\ strict_dom_vars_defined fn s /\
    fn_reachable fn s.vs_current_bb /\
    ctx_labels_bound C s.vs_labels /\
    ctx_labels_bound C' s.vs_labels /\ ~s.vs_call_ctx.cc_static /\
    terminates (run_blocks fuel C' fn' s) /\
    gas_count_blocks fuel C' fn' s <= LENGTH s.vs_gas_readings
    ==>
    ?raw_slots sites unused.
      LENGTH raw_slots = LENGTH sites /\
      PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) s.vs_gas_readings /\
      (!t.
        (?ir. run_blocks fuel C' fn' s = IntRet ir t) ==>
        EVERY IS_SOME raw_slots /\ unused = t.vs_gas_readings) /\
      (!gobs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs ==>
        (?extra.
          sites = gas_events_blocks fuel C fn
            (s with vs_gas_readings := gobs ++ tail) ++ extra) /\
        ((?fuel_src. terminates
          (run_blocks fuel_src C fn (s with vs_gas_readings := gobs ++ tail)))
         ==>
        terminates
          (run_blocks fuel C fn (s with vs_gas_readings := gobs ++ tail)) /\
        dft_res_rel
          (restore_result []
            (run_blocks fuel C fn (s with vs_gas_readings := gobs ++ tail)))
          (restore_result [] (run_blocks fuel C' fn' s)) /\
        (!t.
          (?ir. run_blocks fuel C' fn' s = IntRet ir t) ==>
          gas_events_blocks fuel C fn
            (s with vs_gas_readings := gobs ++ tail) = sites /\
          residual_result tail (run_blocks fuel C' fn' s)
            (run_blocks fuel C fn (s with vs_gas_readings := gobs ++ tail))))) /\
      (!gobs tail f_src.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs ==>
        ?extra.
          sites = gas_events_blocks f_src C fn
            (s with vs_gas_readings := gobs ++ tail) ++ extra)
End

(* The context premises give the blocks premises at the actual entry. *)
Theorem dft_ctx_entry[local]:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ C'.ctx_global_reserved = C.ctx_global_reserved /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\
  ctx_labels_bound C vs'.vs_labels /\ o1_run_state_ok vs' /\
  C'.ctx_entry = SOME nm /\ lookup_function nm C'.ctx_functions = SOME fn' /\
  fn_entry_label fn' = SOME lbl /\
  terminates (run_context fuel C' vs') ==>
  ?fn. lookup_function nm C.ctx_functions = SOME fn /\ fn' = dft_fn fn /\
       fn_entry_label fn = SOME lbl /\ MEM fn C.ctx_functions /\
       dft_fn_rel fn fn' /\
       strict_dom_vars_defined fn
         (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>) /\
       fn_reachable fn lbl /\ ctx_labels_bound C' vs'.vs_labels /\
       ~vs'.vs_call_ctx.cc_static /\
       run_context fuel C' vs' =
       run_blocks fuel C' fn'
         (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>) /\
       terminates (run_blocks fuel C' fn'
         (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>))
Proof
  strip_tac >>
  `C'.ctx_functions = MAP dft_fn C.ctx_functions` by
    metis_tac[dft_ctx_functions_map] >>
  `?fn. lookup_function nm C.ctx_functions = SOME fn /\ fn' = dft_fn fn` by
    (qpat_x_assum `lookup_function nm C'.ctx_functions = _` mp_tac >>
     simp[lookup_function_map]) >>
  gvs[] >>
  `fn_entry_label fn = SOME lbl` by gvs[dft_fn_entry_label] >>
  `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `dft_fn_rel fn (dft_fn fn)` by
    (gvs[MEM_EL, LIST_REL_EL_EQN, EL_MAP] >> metis_tac[]) >>
  `ctx_labels_bound (C' : venom_context) vs'.vs_labels` by
    (irule dft_ctx_labels_bound >> gvs[o1_run_state_ok_def]) >>
  `~vs'.vs_call_ctx.cc_static` by gvs[o1_run_state_ok_def] >>
  `run_context fuel C' vs' =
   run_blocks fuel C' (dft_fn fn)
     (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)` by
    (irule run_context_entry_blocks >> simp[dft_fn_entry_label] >>
     qexists_tac `nm` >> gvs[]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[fn_reachable_def] >>
  irule venomWfPropsTheory.strict_dom_vars_defined_entry >> simp[]
QED

(* One filling's blocks facts at the entry give its context facts. *)
Theorem dft_ctx_of_blocks[local]:
  o1_ctx_shape C /\ C'.ctx_entry = C.ctx_entry /\ C'.ctx_entry = SOME nm /\
  lookup_function nm C.ctx_functions = SOME fn /\ fn_entry_label fn = SOME lbl /\
  terminates (run_context fuel C' vs') /\
  run_context fuel C' vs' =
  run_blocks fuel C' (dft_fn fn)
    (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>) /\
  (?extra. sites =
     gas_events_blocks fuel C fn
       ((vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
          with vs_gas_readings := gobs ++ tail) ++ extra) /\
  ((?fuel_src. terminates
     (run_blocks fuel_src C fn
       ((vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
          with vs_gas_readings := gobs ++ tail))) ==>
   terminates
     (run_blocks fuel C fn
       ((vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
          with vs_gas_readings := gobs ++ tail)) /\
   dft_res_rel
     (restore_result []
       (run_blocks fuel C fn
         ((vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
            with vs_gas_readings := gobs ++ tail)))
     (restore_result []
       (run_blocks fuel C' (dft_fn fn)
         (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)))) ==>
  (?extra. sites =
     gas_events_blocks fuel C fn
       (vs' with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                    vs_current_bb := lbl; vs_inst_idx := 0 |>) ++ extra) /\
  ((?fr. terminates
           (run_context fr C (vs' with vs_gas_readings := gobs ++ tail))) ==>
   terminates (run_context fuel C (vs' with vs_gas_readings := gobs ++ tail)) /\
   !D. ctx_sim D C C' (vs' with vs_gas_readings := gobs ++ tail) vs')
Proof
  strip_tac >>
  qabbrev_tac `es = (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                                 vs_inst_idx := 0 |>)
                      with vs_gas_readings := gobs ++ tail` >>
  conj_tac >- (qexists_tac `extra` >> qunabbrev_tac `es` >> fs[entry_gas_update_comm]) >>
  disch_then (qx_choose_then `fr` assume_tac) >>
  `!f. run_context f C (vs' with vs_gas_readings := gobs ++ tail) =
       run_blocks f C fn es` by
    (gen_tac >> qunabbrev_tac `es` >>
     `(vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
        with vs_gas_readings := gobs ++ tail =
      (vs' with vs_gas_readings := gobs ++ tail)
        with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>` by
       simp[venom_state_component_equality] >>
     pop_assum SUBST1_TAC >>
     irule run_context_entry_blocks >> simp[] >> qexists_tac `nm` >> gvs[]) >>
  `terminates (run_blocks fr C fn es)` by metis_tac[] >>
  qpat_x_assum `(?fuel_src. _) ==> _` mp_tac >>
  impl_tac >- (qexists_tac `fr` >> first_assum ACCEPT_TAC) >> strip_tac >>
  conj_tac >- metis_tac[] >>
  rw[ctx_sim_def] >> qexists_tac `fuel` >>
  `run_blocks fuel' C fn es = run_blocks fuel C fn es` by
    (irule run_blocks_terminates_fuel_eq >> metis_tac[]) >>
  irule gas_dft_dead_result >>
  `run_blocks fuel' C fn es =
   run_context fuel C (vs' with vs_gas_readings := gobs ++ tail)` by metis_tac[] >>
  pop_assum SUBST1_TAC >>
  rpt conj_tac
  >- metis_tac[o1_ctx_shape_run_context_no_intret]
  >- metis_tac[run_context_not_ok]
  >- metis_tac[] >>
  qexistsl [`restore_result [] (run_blocks fuel C fn es)`,
            `restore_result [] (run_blocks fuel C' (dft_fn fn)
               (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                            vs_inst_idx := 0 |>))`] >>
  gvs[restore_result_rel]
QED

(* One raw-slot mask, fixed before every filling of the target's readings,
 * covers the source events of each compatible filling at the actual entry.
 * Source fillings that terminate are simulated for every dead mask. *)
Theorem dft_ctx_gas_mask:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ C'.ctx_global_reserved = C.ctx_global_reserved /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\
  ctx_labels_bound C vs'.vs_labels /\ o1_run_state_ok vs' /\
  C'.ctx_entry = SOME nm /\ lookup_function nm C'.ctx_functions = SOME fn' /\
  fn_entry_label fn' = SOME lbl /\
  terminates (run_context fuel C' vs') /\
  gas_count_blocks fuel C' fn'
    (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>) <=
    LENGTH vs'.vs_gas_readings ==>
  ?fn raw_slots sites unused.
    lookup_function nm C.ctx_functions = SOME fn /\ fn_entry_label fn = SOME lbl /\
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) vs'.vs_gas_readings /\
    !gobs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs ==>
      (?extra. sites =
         gas_events_blocks fuel C fn
           (vs' with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                        vs_current_bb := lbl; vs_inst_idx := 0 |>) ++ extra) /\
      ((?fr. terminates
               (run_context fr C (vs' with vs_gas_readings := gobs ++ tail))) ==>
       terminates (run_context fuel C (vs' with vs_gas_readings := gobs ++ tail)) /\
       !D. ctx_sim D C C' (vs' with vs_gas_readings := gobs ++ tail) vs')
Proof
  strip_tac >> drule_all dft_ctx_entry >> strip_tac >>
  mp_tac (Q.SPECL [`fuel`, `C`, `C'`, `fn`, `fn'`,
     `vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>`]
     dft_blocks_gas_mask) >>
  impl_tac >- fs[] >> strip_tac >>
  qexistsl [`fn`, `raw_slots`, `sites`, `unused`] >>
  rpt (conj_tac >- fs[]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`gobs`, `tail`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  irule dft_ctx_of_blocks >> gvs[] >> metis_tac[]
QED

(* dft_ctx_gas_mask under the DFT prefix property: the same mask's sites also
 * cover every compatible filling's source events at every fuel. *)
Theorem dft_ctx_gas_mask_prefix:
  dft_blocks_gas_prefix /\
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ C'.ctx_global_reserved = C.ctx_global_reserved /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\
  ctx_labels_bound C vs'.vs_labels /\ o1_run_state_ok vs' /\
  C'.ctx_entry = SOME nm /\ lookup_function nm C'.ctx_functions = SOME fn' /\
  fn_entry_label fn' = SOME lbl /\
  terminates (run_context fuel C' vs') /\
  gas_count_blocks fuel C' fn'
    (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>) <=
    LENGTH vs'.vs_gas_readings ==>
  ?fn raw_slots sites unused.
    lookup_function nm C.ctx_functions = SOME fn /\ fn_entry_label fn = SOME lbl /\
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) vs'.vs_gas_readings /\
    !gobs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs ==>
      (?extra. sites =
         gas_events_blocks fuel C fn
           (vs' with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                        vs_current_bb := lbl; vs_inst_idx := 0 |>) ++ extra) /\
      ((?fr. terminates
               (run_context fr C (vs' with vs_gas_readings := gobs ++ tail))) ==>
       terminates (run_context fuel C (vs' with vs_gas_readings := gobs ++ tail)) /\
       !D. ctx_sim D C C' (vs' with vs_gas_readings := gobs ++ tail) vs') /\
      !f_src. ?extra. sites =
         gas_events_blocks f_src C fn
           (vs' with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                        vs_current_bb := lbl; vs_inst_idx := 0 |>) ++ extra
Proof
  strip_tac >> drule_all dft_ctx_entry >> strip_tac >>
  qpat_x_assum `dft_blocks_gas_prefix`
    (mp_tac o REWRITE_RULE [dft_blocks_gas_prefix_def]) >>
  disch_then (qspecl_then [`fuel`, `C`, `C'`, `fn`, `fn'`,
     `vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>`]
     mp_tac) >>
  impl_tac >- fs[] >> strip_tac >>
  qexistsl [`fn`, `raw_slots`, `sites`, `unused`] >>
  rpt (conj_tac >- fs[]) >>
  rpt gen_tac >> strip_tac >>
  `!f_src. ?extra. sites =
     gas_events_blocks f_src C fn
       (vs' with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                    vs_current_bb := lbl; vs_inst_idx := 0 |>) ++ extra` by
    (gen_tac >>
     first_x_assum (qspecl_then [`gobs`, `tail`, `f_src`] mp_tac) >>
     impl_tac >- simp[] >> simp[entry_gas_update_comm]) >>
  first_x_assum (qspecl_then [`gobs`, `tail`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  REWRITE_TAC [CONJ_ASSOC] >> conj_tac
  >- (irule dft_ctx_of_blocks >> gvs[] >> metis_tac[]) >>
  first_assum ACCEPT_TAC
QED
