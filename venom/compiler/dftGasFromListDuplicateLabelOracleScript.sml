Theory dftGasFromListDuplicateLabelOracle
Ancestors
  dftGasFromListDuplicateLabelAudit dftGasOracleDefs contextCodegenRel
  venomExecSemantics venomInst venomState finite_map words list

Theorem audit_active_cases:
  active_inst audit_fn inst s ==>
  (s.vs_inst_idx = 0 /\ (inst = audit_assign \/ inst = audit_first)) \/
  (s.vs_inst_idx = 1 /\ inst = audit_second) \/
  (s.vs_inst_idx = 2 /\ inst = audit_marker)
Proof
  simp[active_inst_def, audit_fn_def, mk_raw_function_def, audit_blocks_def,
       LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  Cases_on `s.vs_inst_idx`
  >- (simp[] >> metis_tac[]) >>
  rename1 `s.vs_inst_idx = SUC k` >> Cases_on `k`
  >- (simp[] >> metis_tac[]) >>
  rename1 `s.vs_inst_idx = SUC (SUC k)` >> Cases_on `k` >>
  simp[] >> metis_tac[]
QED

Theorem audit_opcodes:
  audit_assign.inst_opcode = ASSIGN /\ audit_first.inst_opcode = GAS /\
  audit_second.inst_opcode = GAS /\ audit_second.inst_id = 1 /\
  audit_second.inst_outputs = ["y"] /\ audit_marker.inst_opcode = STOP
Proof
  EVAL_TAC
QED

Theorem audit_marker_not_ok:
  ev_step orc p d fuel ctx audit_marker s <> OK t
Proof
  simp[ev_step_def, audit_marker_def, mk_inst_def, step_inst_base_def]
QED

Theorem audit_second_value:
  ev_step orc p d fuel ctx audit_second s = OK t ==>
  lookup_var "y" t = SOME (orc (p,d,1))
Proof
  simp[ev_step_def, ev_gas_def, audit_opcodes, lookup_var_def, update_var_def] >>
  strip_tac >> gvs[FLOOKUP_UPDATE]
QED

Theorem audit_oracle_invariant:
  !orc vs0 ctx p d fn inst u.
    ev_reachable orc vs0 ctx p d fn inst u ==>
    vs0 = audit_start /\ ctx = audit_ctx ==>
    fn = audit_fn /\ p = [] /\ d = 1 /\
    (u.vs_inst_idx = 2 ==> lookup_var "y" u = SOME (orc ([],1,1)))
Proof
  ho_match_mp_tac ev_reachable_ind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >> suspend "callee"
QED

Resume audit_oracle_invariant[entry]:
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `SOME _ = audit_ctx.ctx_entry` mp_tac >>
  simp[audit_ctx_def, mk_venom_context_def] >> strip_tac >>
  `fn = audit_fn` by metis_tac[audit_entry_facts, optionTheory.SOME_11] >> gvs[] >>
  `lbl = "entry"` by metis_tac[audit_entry_facts, optionTheory.SOME_11] >> gvs[] >>
  qpat_x_assum `enters_block _ _ _` mp_tac >>
  simp[enters_block_def, audit_fn_def, mk_raw_function_def, audit_blocks_def,
       lookup_block_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Resume audit_oracle_invariant[next]:
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  imp_res_tac audit_active_cases >> gvs[audit_indices] >>
  simp[lookup_var_def] >>
  drule audit_second_value >> simp[lookup_var_def]
QED

Resume audit_oracle_invariant[block]:
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  imp_res_tac audit_active_cases >>
  gvs[audit_opcodes, is_terminator_def] >>
  metis_tac[audit_marker_not_ok]
QED

Resume audit_oracle_invariant[callee]:
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  imp_res_tac audit_active_cases >> gvs[audit_opcodes]
QED

Finalise audit_oracle_invariant

Theorem audit_restored_value:
  ev_reachable orc audit_start audit_ctx p d audit_fn audit_marker
    ((audit_end w v readings) with vs_gas_readings := audit_start.vs_gas_readings) ==>
  v = orc ([],1,1)
Proof
  strip_tac >> drule audit_oracle_invariant >>
  simp[audit_indices, audit_end_def, audit_mid_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE]
QED

Theorem audit_no_common_oracle:
  ~(?orc. !fn inst t. raw_reachable audit_start audit_ctx fn inst t ==>
       ?p d. ev_reachable orc audit_start audit_ctx p d fn inst
         (t with vs_gas_readings := audit_start.vs_gas_readings))
Proof
  strip_tac >>
  `?p d. ev_reachable orc audit_start audit_ctx p d audit_fn audit_marker
      ((audit_end 0w 1w [1w;2w]) with vs_gas_readings := audit_start.vs_gas_readings)` by
    metis_tac[audit_raw_end] >>
  `?p d. ev_reachable orc audit_start audit_ctx p d audit_fn audit_marker
      ((audit_end 1w 2w [2w]) with vs_gas_readings := audit_start.vs_gas_readings)` by
    metis_tac[audit_raw_end] >>
  imp_res_tac audit_restored_value >>
  `(1w:bytes32) <> 2w` by (wordsLib.WORD_DECIDE_TAC) >> metis_tac[]
QED

(* The frozen obligation instantiated at the checked concrete context and state. *)
Theorem gas_oracle_from_list_counterexample:
  EVERY (\fn. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
                fn.fn_blocks) audit_ctx.ctx_functions /\
  ~(?orc. FINITE {e | orc e <> 0w} /\
      (!fuel. gas_res_rel (run_context fuel audit_ctx audit_start)
                          (ev_context orc fuel audit_ctx audit_start)) /\
      (!fn inst t. raw_reachable audit_start audit_ctx fn inst t ==>
         ?p d. ev_reachable orc audit_start audit_ctx p d fn inst
                 (t with vs_gas_readings := audit_start.vs_gas_readings)))
Proof
  simp[audit_distinct] >> metis_tac[audit_no_common_oracle]
QED
