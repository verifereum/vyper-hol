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
  dftGasFromListUnion dftGasToListAgreement dftGasFromListTraceNames
  dftGasToListTrace dftGasFromListReadings rich_list pair
  dftGasOracleDefs venomRetProps contextRawReachable ptrDiscipline passSimulationDefs
  o1ContractCfgNorm gasOracleReplay dftWf dftCorrectnessFinal stackPlanGen contextCodegenRel
  o1DftStep dftSsaPreserve dftRunRel dftScheduleOrder dftDefs o1PassLift
  o1PassContract unitMemInv unitShapeDefs lowerDloadDefs venomPassDispatcher
  venomExecSemantics venomWf venomInst venomState list

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
(* Input readings replay the output's actual instruction events in input
   order. Unrecorded output events read zero; the list has no arbitrary tail. *)
Definition dft_gas_replay_def:
  dft_gas_replay C C' vs vs' <=>
    gas_variant vs vs' /\
    ?j. vs.vs_gas_readings =
          MAP (list_oracle C' vs')
            (trace_events (dftGasToListTrace$trace_context
              (list_oracle C' vs') j C vs')) /\
        !fuel. agrees (list_oracle C' vs') vs.vs_gas_readings
          (trace_events (dftGasToListTrace$trace_context
            (list_oracle C' vs') fuel C vs'))
End

Theorem dft_gas_replay_variant:
  dft_gas_replay C C' vs vs' ==> gas_variant vs vs'
Proof
  simp[dft_gas_replay_def]
QED

Theorem oracle_trace_regions[local]:
  (!orc p d fuel ctx inst s.
    EVERY (block_region p d [inst.inst_id])
      (trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst s))) /\
  (!orc p d fuel ctx fn bb s.
    EVERY (block_region p d
      (MAP (\i. i.inst_id) (DROP s.vs_inst_idx bb.bb_instructions)))
      (trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s))) /\
  (!orc p d fuel ctx fn s.
    EVERY (later_region p d)
      (trace_events (dftGasToListTrace$trace_blocks orc p d fuel ctx fn s)))
Proof
  ho_match_mp_tac oracle_trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume oracle_trace_regions[step]:
  rpt gen_tac >> strip_tac >> simp[trace_step_eq] >>
  Cases_on `inst.inst_opcode = GAS`
  >- simp[trace_events_def, block_region_def] >>
  simp[] >> Cases_on `inst.inst_opcode = INVOKE` >> simp[trace_events_def] >>
  Cases_on `decode_invoke inst` >> simp[trace_events_def] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 ctx.ctx_functions` >> simp[trace_events_def] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> simp[trace_events_def] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >> simp[trace_events_def] >>
  rename1 `setup_callee _ _ _ = SOME cs` >>
  `EVERY (later_region ((d,inst.inst_id)::p) d)
    (trace_events (dftGasToListTrace$trace_blocks orc
      ((d,inst.inst_id)::p) d fuel ctx callee cs))` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
  PairCases_on `e` >> strip_tac >> irule below_call_region >>
  simp[] >> metis_tac[later_region_frame]
QED

Resume oracle_trace_regions[block]:
  rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once trace_block_eq, trace_events_def] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  drule remaining_ids_step >> strip_tac >>
  simp[Once trace_block_eq, trace_events_def, trace_events_append, EVERY_APPEND] >>
  conj_tac
  >- (`EVERY (block_region p d [inst.inst_id])
        (trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst s))` by
        (first_x_assum irule >> simp[]) >>
      gvs[EVERY_MEM] >> rpt strip_tac >> irule block_region_mono >>
      qexists_tac `[inst.inst_id]` >> simp[]) >>
  Cases_on `ev_step orc p d fuel ctx inst s` >> simp[trace_events_def] >>
  rename1 `ev_step _ _ _ _ _ _ _ = OK t` >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[trace_events_def] >> gvs[] >>
  `EVERY (block_region p d
      (MAP (\i. i.inst_id) (DROP (SUC s.vs_inst_idx) bb.bb_instructions)))
    (trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb
      (t with vs_inst_idx := SUC s.vs_inst_idx)))` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  gvs[EVERY_MEM] >> rpt strip_tac >> irule block_region_mono >>
  qexists_tac `MAP (\i. i.inst_id) (DROP (SUC s.vs_inst_idx) bb.bb_instructions)` >>
  simp[]
QED

Resume oracle_trace_regions[blocks]:
  rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >- simp[trace_blocks_zero, trace_events_def] >>
  rename1 `SUC k` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once trace_blocks_eq, trace_events_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[]
  >- (rename1 `eval_phis _ _ = OK sp` >>
      simp[Once trace_blocks_eq, trace_events_append, EVERY_APPEND] >> conj_tac
      >- (gvs[EVERY_MEM] >> rpt strip_tac >> irule block_region_later >>
          first_x_assum (qspec_then `e` mp_tac) >> simp[] >> metis_tac[]) >>
      Cases_on `ev_block orc p (SUC d) k ctx bb
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
      simp[trace_events_def] >> rename1 `ev_block _ _ _ _ _ _ _ = OK t` >>
      Cases_on `t.vs_halted` >> simp[trace_events_def] >> gvs[EVERY_MEM] >>
      rpt strip_tac >> irule later_region_mono >>
      qexists_tac `SUC d` >> simp[] >> metis_tac[]) >>
  simp[Once trace_blocks_eq, trace_events_def]
QED

Finalise oracle_trace_regions

Theorem oracle_trace_step_region[local]:
  MEM e (trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst s)) ==>
  block_region p d [inst.inst_id] e
Proof
  mp_tac (cj 1 oracle_trace_regions) >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem oracle_trace_block_region[local]:
  MEM e (trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s)) ==>
  block_region p d (MAP (\i. i.inst_id) (DROP s.vs_inst_idx bb.bb_instructions)) e
Proof
  mp_tac (cj 2 oracle_trace_regions) >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem oracle_trace_blocks_region[local]:
  MEM e (trace_events (dftGasToListTrace$trace_blocks orc p d fuel ctx fn s)) ==>
  later_region p d e
Proof
  mp_tac (cj 3 oracle_trace_regions) >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem oracle_trace_block_excludes[local]:
  ~MEM id (MAP (\i. i.inst_id) (DROP s.vs_inst_idx bb.bb_instructions)) ==>
  ~MEM (p,d,id)
    (trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s))
Proof
  rpt strip_tac >> drule oracle_trace_block_region >>
  simp[block_region_def] >>
  metis_tac[frame_not_below_self, frame_below_def]
QED

Theorem oracle_trace_step_block_disjoint[local]:
  ~MEM inst.inst_id (MAP (\i. i.inst_id) (DROP t.vs_inst_idx bb.bb_instructions)) ==>
  !e. MEM e (trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst s)) ==>
    ~MEM e (trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb t))
Proof
  rpt strip_tac >> drule oracle_trace_step_region >> strip_tac >>
  drule oracle_trace_block_region >> strip_tac >>
  metis_tac[block_regions_disjoint, MEM]
QED

Theorem oracle_trace_events_distinct[local]:
  (!orc p d fuel ctx inst s.
    EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
      f.fn_blocks) ctx.ctx_functions ==>
    ALL_DISTINCT (trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst s))) /\
  (!orc p d fuel ctx fn bb s.
    EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
      f.fn_blocks) ctx.ctx_functions /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
    ALL_DISTINCT (trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s))) /\
  (!orc p d fuel ctx fn s.
    EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
      f.fn_blocks) ctx.ctx_functions /\
    EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)) fn.fn_blocks ==>
    ALL_DISTINCT (trace_events (dftGasToListTrace$trace_blocks orc p d fuel ctx fn s)))
Proof
  ho_match_mp_tac oracle_trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume oracle_trace_events_distinct[step]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = GAS` >> simp[trace_step_eq, trace_events_def] >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[trace_events_def] >>
  Cases_on `decode_invoke inst` >> simp[trace_events_def] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 ctx.ctx_functions` >> simp[trace_events_def] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> simp[trace_events_def] >>
  Cases_on `setup_callee callee x s` >> simp[trace_events_def] >>
  first_x_assum irule >> simp[] >>
  gvs[EVERY_MEM] >> metis_tac[lookup_function_MEM]
QED

Resume oracle_trace_events_distinct[block]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once trace_block_eq, trace_events_def] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (DROP s.vs_inst_idx bb.bb_instructions))` by
    (rewrite_tac[MAP_DROP] >> irule ALL_DISTINCT_DROP >> simp[]) >>
  drule remaining_ids_step >> strip_tac >> gvs[] >>
  `ALL_DISTINCT (trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst s))` by
    (first_x_assum irule >> simp[]) >>
  simp[Once trace_block_eq, trace_events_def, trace_events_append, ALL_DISTINCT_APPEND] >>
  Cases_on `ev_step orc p d fuel ctx inst s` >> simp[trace_events_def] >>
  rename1 `ev_step _ _ _ _ _ _ _ = OK t` >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[trace_events_def] >>
  gen_tac >> disch_tac >> irule oracle_trace_step_block_disjoint >>
  simp[] >> metis_tac[]
QED

Resume oracle_trace_events_distinct[blocks]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `fuel` >- simp[trace_blocks_zero, trace_events_def] >> rename1 `SUC k` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once trace_blocks_eq, trace_events_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (gvs[EVERY_MEM] >> metis_tac[livenessTransferProofsTheory.lookup_block_mem]) >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[Once trace_blocks_eq, trace_events_def] >> rename1 `eval_phis _ _ = OK sp` >>
  simp[trace_events_append, ALL_DISTINCT_APPEND] >>
  Cases_on `ev_block orc p (SUC d) k ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[trace_events_def] >>
  rename1 `ev_block _ _ _ _ _ _ _ = OK t` >>
  Cases_on `t.vs_halted` >> simp[trace_events_def] >> rpt strip_tac >>
  drule oracle_trace_block_region >> strip_tac >>
  drule oracle_trace_blocks_region >> strip_tac >>
  metis_tac[block_later_disjoint]
QED

Finalise oracle_trace_events_distinct

Theorem oracle_context_events_distinct[local]:
  o1_ctx_shape C ==>
  ALL_DISTINCT (trace_events (dftGasToListTrace$trace_context orc fuel C s))
Proof
  strip_tac >>
  `EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
    f.fn_blocks) C.ctx_functions` by
    (drule o1_ctx_shape_wf_functions >> simp[EVERY_MEM] >>
     metis_tac[wf_fn_block_inst_ids_distinct]) >>
  simp[dftGasToListTraceTheory.trace_context_def, dftGasToListTraceTheory.trace_function_def] >>
  Cases_on `C.ctx_entry` >> simp[trace_events_def] >>
  Cases_on `lookup_function x C.ctx_functions` >> simp[trace_events_def] >>
  rename1 `lookup_function _ _ = SOME fn` >>
  Cases_on `fn_entry_label fn` >> simp[trace_events_def] >>
  irule (cj 3 oracle_trace_events_distinct) >> simp[] >>
  gvs[EVERY_MEM] >> metis_tac[lookup_function_MEM]
QED

Theorem list_oracle_nonzero_occurrence[local]:
  o1_ctx_shape C /\ list_oracle C s e <> 0w ==>
  ?k. k < LENGTH s.vs_gas_readings /\ indexed_event C s k = e /\
      EL k s.vs_gas_readings = list_oracle C s e
Proof
  strip_tac >>
  `recorded C s e (list_oracle C s e)` by
    (qpat_x_assum `list_oracle _ _ _ <> _` mp_tac >>
     simp[list_oracle_def] >> Cases_on `?w. recorded C s e w` >>
     simp[] >> metis_tac[SELECT_AX]) >>
  qpat_x_assum `recorded _ _ _ _` mp_tac >>
  simp[recorded_def, MEM_EL] >> strip_tac >>
  rename1 `k < LENGTH (trace_gas (dftGasFromListTraceDefs$trace_context n C s))` >>
  `k < LENGTH s.vs_gas_readings` by
    (irule trace_context_nonzero_bound >> qexistsl_tac [`C`,`n`] >>
     simp[] >> metis_tac[SND]) >>
  qexists_tac `k` >> simp[] >> conj_tac
  >- (drule indexed_event_eq >> simp[] >> metis_tac[FST]) >>
  mp_tac (Q.INST [`fuel:num` |-> `n`, `ctx:venom_context` |-> `C`]
    trace_context_readings) >>
  simp[gas_prefix_genlist, LIST_EQ_REWRITE] >>
  disch_then (qspec_then `k` mp_tac) >>
  simp[EL_MAP, EL_GENLIST] >> metis_tac[SND]
QED

Theorem distinct_indices_extract[local]:
  ALL_DISTINCT ks /\ (!k. MEM k ks ==> k < LENGTH ws) ==>
  ?unused. PERM (MAP (\k. EL k ws) ks ++ unused) ws
Proof
  strip_tac >>
  `PERM (ks ++ FILTER (\k. ~MEM k ks) (GENLIST I (LENGTH ws)))
    (GENLIST I (LENGTH ws))` by
    (irule sortingTheory.PERM_ALL_DISTINCT >>
     simp[ALL_DISTINCT_APPEND, FILTER_ALL_DISTINCT, ALL_DISTINCT_GENLIST,
          MEM_FILTER, MEM_GENLIST] >> metis_tac[]) >>
  drule (Q.ISPEC `\k. EL k ws` sortingTheory.PERM_MAP) >>
  simp[MAP_APPEND, MAP_GENLIST] >> metis_tac[GENLIST_ID]
QED

Theorem finite_occurrence_slots[local]:
  !es (f:'a -> bytes32) ws (key:num -> 'a).
  ALL_DISTINCT es /\
  (!e. MEM e es /\ f e <> 0w ==>
    ?k. k < LENGTH ws /\ key k = e /\ EL k ws = f e) ==>
  ?slots unused.
    MAP f es = MAP (\slot. case slot of NONE => 0w | SOME w => w) slots /\
    PERM (MAP THE (FILTER IS_SOME slots) ++ unused) ws
Proof
  rpt strip_tac >>
  `?idx. !e. MEM e es /\ f e <> 0w ==>
    idx e < LENGTH ws /\ key (idx e) = e /\ EL (idx e) ws = f e` by
    metis_tac[SKOLEM_THM] >>
  `ALL_DISTINCT (MAP idx (FILTER (\e. f e <> 0w) es))` by
    (irule ALL_DISTINCT_MAP_INJ >>
     simp[FILTER_ALL_DISTINCT, MEM_FILTER] >> metis_tac[]) >>
  `!k. MEM k (MAP idx (FILTER (\e. f e <> 0w) es)) ==> k < LENGTH ws` by
    (simp[MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  `?unused. PERM
    (MAP (\k. EL k ws) (MAP idx (FILTER (\e. f e <> 0w) es)) ++ unused) ws` by
    (irule distinct_indices_extract >> simp[]) >>
  qexistsl_tac [`MAP (\e. if f e = 0w then NONE else SOME (f e)) es`, `unused`] >>
  conj_tac
  >- (simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f] >>
      rpt strip_tac >> Cases_on `f e = 0w` >> simp[]) >>
  `MAP THE (FILTER IS_SOME (MAP (\e. if f e = 0w then NONE else SOME (f e)) es)) =
    MAP f (FILTER (\e. f e <> 0w) es)` by
    (rpt (pop_assum kall_tac) >> Induct_on `es` >> simp[] >>
     gen_tac >> Cases_on `f h = 0w` >> simp[]) >>
  `MAP (\k. EL k ws) (MAP idx (FILTER (\e. f e <> 0w) es)) =
    MAP f (FILTER (\e. f e <> 0w) es)` by
    (simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f, MEM_FILTER] >> metis_tac[]) >>
  gvs[]
QED

(* Canonical replay records each observed nonzero word with its target
   multiplicity. Missing events may contribute zero-filled slots. *)
Theorem dft_gas_replay_slots:
  !C C' si so.
    o1_ctx_shape C /\ o1_ctx_shape C' /\
    dft_gas_replay C C' si so ==>
    ?slots unused.
      si.vs_gas_readings =
        MAP (\slot. case slot of NONE => 0w | SOME w => w) slots /\
      PERM (MAP THE (FILTER IS_SOME slots) ++ unused) so.vs_gas_readings
Proof
  rpt strip_tac >> gvs[dft_gas_replay_def] >>
  irule finite_occurrence_slots >>
  reverse conj_tac >- simp[oracle_context_events_distinct] >>
  qexists_tac `indexed_event C' so` >>
  metis_tac[list_oracle_nonzero_occurrence]
QED

Theorem dft_ctx_sim_gas:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ C'.ctx_global_reserved = C.ctx_global_reserved /\
  o1_ctx_shape C /\
  ctx_labels_bound C vs'.vs_labels /\ o1_run_state_ok vs' ==>
  ?vs. dft_gas_replay C C' vs vs' /\ ctx_sim D C C' vs vs' /\
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
  qabbrev_tac `gas_orc = list_oracle C' vs'` >>
  qpat_x_assum `orc = _` SUBST_ALL_TAC >>
  qabbrev_tac `rds = MAP gas_orc (trace_events (trace_context gas_orc j C vs'))` >>
  qexists_tac `vs' with vs_gas_readings := rds` >>
  conj_tac
  >- (fs[dft_gas_replay_def, gas_variant_def, venom_state_component_equality,
         Abbr `gas_orc`, Abbr `rds`] >>
      metis_tac[]) >>
  conj_tac
  >- (rw[ctx_sim_def] >> qexists_tac `fuel` >>
      irule gas_dft_dead_result >>
      simp[run_context_not_ok, o1_ctx_shape_run_context_no_intret] >>
      qexistsl [`ev_context gas_orc fuel C vs'`, `ev_context gas_orc fuel C' vs'`] >>
      simp[] >> irule dft_ev_context_sim >> simp[] >>
      metis_tac[gas_res_rel_terminates]) >>
  rw[o1_lowered_inv_def] >> qexists_tac `eom` >>
  conj_tac >- gvs[max_live_eom_def, collect_fn_eoms_dft] >>
  gvs[mem_inv_raw_reachable] >>
  `!p d fn inst t. ev_reachable gas_orc vs' C p d fn inst t ==>
     lowered_mem_fact eom C fn inst t` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  `!p d fn inst t. ev_reachable gas_orc vs' C' p d fn inst t ==>
     lowered_mem_fact eom C' fn inst t` by
    (mp_tac (Q.INST [`s:venom_state` |-> `vs'`, `orc` |-> `gas_orc`]
      dft_ev_lowered_inv) >>
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
