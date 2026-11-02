(* Semantic classification and successful-pair boundaries for crossings. *)
Theory dftFramePair
Ancestors
  dftFramePrefix dftFrameSwap dftPermSim dftBlockSim venomEffects dftDefs
  unitShapeDefs venomInst venomExecSemantics venomWf venomState dftCommutation
  venomCallOracleDefs extCallOracle pred_set list finite_map venomInstProofs

Theorem dft_cross_effects:
  dft_cross a b ==> effects_independent a.inst_opcode b.inst_opcode
Proof
  simp[dft_cross_def, effects_independent_def, DISJOINT_UNION] >>
  metis_tac[DISJOINT_SYM]
QED

Theorem dft_cross_abort:
  dft_cross a b ==> abort_compatible a.inst_opcode b.inst_opcode
Proof
  simp[dft_cross_def, is_fallible_def] >> strip_tac >>
  gvs[abort_compatible_def, opcode_fail_class_def]
QED

Theorem dft_cross_not_two_invokes:
  dft_cross a b ==> ~(a.inst_opcode = INVOKE /\ b.inst_opcode = INVOKE)
Proof
  strip_tac >> drule dft_cross_effects >>
  rpt strip_tac >> gvs[effects_independent_def, read_effects_def, write_effects_def, all_effects_def]
QED

Theorem dft_cross_ext_independent:
  dft_cross a b /\ a.inst_opcode <> ALLOCA /\ b.inst_opcode <> ALLOCA /\
  ~is_ext_call_op a.inst_opcode /\ ~is_ext_call_op b.inst_opcode ==>
  ext_bi_independent a b
Proof
  strip_tac >> drule dft_cross_effects >> drule dft_cross_abort >>
  `~is_alloca_op a.inst_opcode /\ ~is_alloca_op b.inst_opcode` by
    (conj_tac >- (Cases_on `a.inst_opcode` >> gvs[is_alloca_op_def]) >>
     Cases_on `b.inst_opcode` >> gvs[is_alloca_op_def]) >>
  gvs[dft_cross_def, ext_bi_independent_def]
QED

Theorem dft_shape_external:
  inst_shape_ok e /\ is_ext_call_op e.inst_opcode ==>
  e.inst_opcode = CALL \/ e.inst_opcode = STATICCALL
Proof
  Cases_on `e.inst_opcode` >>
  simp[inst_shape_ok_def, is_ext_call_op_def]
QED

Theorem dft_external_observer:
  effects_independent e.inst_opcode p.inst_opcode /\
  (e.inst_opcode = CALL \/ e.inst_opcode = STATICCALL) ==>
  write_effects p.inst_opcode = {} /\
  p.inst_opcode <> INVOKE /\ ~is_ext_call_op p.inst_opcode /\
  DISJOINT (read_effects p.inst_opcode) (write_effects e.inst_opcode) /\
  (e.inst_opcode = CALL ==> read_effects p.inst_opcode = {})
Proof
  strip_tac >>
  gvs[effects_independent_def, DISJOINT_UNION, read_effects_def,
      write_effects_def] >>
  Cases_on `p.inst_opcode` >>
  fs[read_effects_def, write_effects_def, empty_effects_def,
     is_ext_call_op_def] >>
  fs[all_effects_def]
QED

Theorem dft_step_swap_two_fuels:
  ext_bi_independent a b /\
  ~(a.inst_opcode = INVOKE /\ b.inst_opcode = INVOKE) /\
  inst_wf a /\ inst_wf b /\
  step_inst fa C a s = OK sa /\ step_inst fb C b sa = OK t ==>
  ?sb. step_inst fb C b s = OK sb /\ step_inst fa C a sb = OK t
Proof
  strip_tac >> Cases_on `a.inst_opcode = INVOKE`
  >- (`b.inst_opcode <> INVOKE` by metis_tac[] >>
      `step_inst fa C b sa = OK t` by gvs[step_inst_non_invoke] >>
      drule_all step_swap_ok_ext >> strip_tac >>
      qexists_tac `sb` >> gvs[step_inst_non_invoke]) >>
  `step_inst fb C a s = OK sa` by gvs[step_inst_non_invoke] >>
  drule_all step_swap_ok_ext >> strip_tac >>
  qexists_tac `sb` >> gvs[step_inst_non_invoke]
QED

Theorem dft_step_frame_updates:
  !pairs s. i.inst_opcode <> INVOKE /\
    EVERY (\kv. (!y. MEM (Var y) i.inst_operands ==> FST kv <> y) /\
                ~MEM (FST kv) i.inst_outputs) pairs ==>
    step_inst fuel C i
      (FOLDL (\st (out,value). update_var out value st) s pairs) =
    map_result_state
      (\st. FOLDL (\st (out,value). update_var out value st) st pairs)
      (step_inst fuel C i s)
Proof
  Induct >- (rpt gen_tac >> Cases_on `step_inst fuel C i s` >>
             simp[map_result_state_def]) >>
  simp[] >> rpt gen_tac >>
  Cases_on `h` >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `update_var q r s` mp_tac) >>
  simp[] >> strip_tac >>
  `step_inst fuel C i (update_var q r s) =
     map_result_state (update_var q r) (step_inst fuel C i s)` by
    (irule step_inst_frame >> simp[]) >> simp[] >>
  Cases_on `step_inst fuel C i s` >> simp[map_result_state_def]
QED

Theorem dft_step_frame_updates_ok:
  i.inst_opcode <> INVOKE /\
  EVERY (\kv. (!y. MEM (Var y) i.inst_operands ==> FST kv <> y) /\
              ~MEM (FST kv) i.inst_outputs) pairs ==>
  (step_inst fuel C i
     (FOLDL (\st (out,value). update_var out value st) s pairs) = OK t <=>
   ?u. step_inst fuel C i s = OK u /\
       t = FOLDL (\st (out,value). update_var out value st) u pairs)
Proof
  strip_tac >> drule_all dft_step_frame_updates >>
  disch_then (qspecl_then [`fuel`, `C`, `s`] mp_tac) >>
  Cases_on `step_inst fuel C i s` >> simp[map_result_state_def] >>
  metis_tac[]
QED

(* Semantic reader families expose the same output update on two input states. *)
Theorem dft_read0_replay:
  f s = f u /\ exec_read0 f i s = OK t ==>
  ?out value. i.inst_outputs = [out] /\
    t = update_var out value s /\
    exec_read0 f i u = OK (update_var out value u)
Proof
  simp[exec_read0_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem dft_read1_replay:
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op u) /\
  (!v. f v s = f v u) /\ exec_read1 f i s = OK t ==>
  ?out value. i.inst_outputs = [out] /\
    t = update_var out value s /\
    exec_read1 f i u = OK (update_var out value u)
Proof
  simp[exec_read1_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem dft_static_read_observer:
  write_effects p.inst_opcode = {} /\
  DISJOINT (read_effects p.inst_opcode) {Eff_MEMORY; Eff_RETURNDATA} /\
  read_effects p.inst_opcode <> {} /\ ~is_terminator p.inst_opcode ==>
  p.inst_opcode = SLOAD \/ p.inst_opcode = TLOAD \/
  p.inst_opcode = BALANCE \/ p.inst_opcode = SELFBALANCE \/
  p.inst_opcode = EXTCODESIZE \/ p.inst_opcode = EXTCODEHASH \/
  p.inst_opcode = GETFMP \/ p.inst_opcode = INITIAL_FMP
Proof
  Cases_on `p.inst_opcode` >>
  simp[write_effects_def, read_effects_def, empty_effects_def,
       is_terminator_def, all_effects_def]
QED

Theorem dft_static_read_replay:
  (p.inst_opcode = SLOAD \/ p.inst_opcode = TLOAD \/
   p.inst_opcode = BALANCE \/ p.inst_opcode = SELFBALANCE \/
   p.inst_opcode = EXTCODESIZE \/ p.inst_opcode = EXTCODEHASH \/
   p.inst_opcode = GETFMP \/ p.inst_opcode = INITIAL_FMP) /\
  s.vs_accounts = u.vs_accounts /\ s.vs_transient = u.vs_transient /\
  s.vs_call_ctx = u.vs_call_ctx /\ s.vs_fmp = u.vs_fmp /\
  s.vs_initial_fmp = u.vs_initial_fmp /\
  (!op. MEM op p.inst_operands ==> eval_operand op s = eval_operand op u) /\
  step_inst_base p s = OK t ==>
  ?out value. p.inst_outputs = [out] /\
    t = update_var out value s /\
    step_inst_base p u = OK (update_var out value u)
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base p s = OK t` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >> strip_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  fs[sload_def, tload_def, contract_storage_def, contract_transient_def] >>
  gvs[exec_read0_def, exec_read1_def, AllCaseEqs()] >>
  rpt (qpat_x_assum `SOME _ = eval_operand _ _` (assume_tac o SYM)) >>
  simp[] >> qmatch_goalsub_abbrev_tac `update_var out value s` >>
  qexists_tac `value` >> simp[]
QED

Theorem dft_static_call_read_fields:
  exec_ext_call e s gas addr value ao az ro rz T = OK u ==>
  s.vs_accounts = u.vs_accounts /\ s.vs_transient = u.vs_transient /\
  s.vs_call_ctx = u.vs_call_ctx /\ s.vs_fmp = u.vs_fmp /\
  s.vs_initial_fmp = u.vs_initial_fmp
Proof
  simp[exec_ext_call_def, consume_call_outcome_eq] >> strip_tac >>
  gvs[AllCaseEqs(), update_var_def, adopt_outcome_def, venom_call_request_def]
QED

Theorem dft_static_step_read_fields:
  e.inst_opcode = STATICCALL /\ step_inst fuel C e s = OK u ==>
  s.vs_accounts = u.vs_accounts /\ s.vs_transient = u.vs_transient /\
  s.vs_call_ctx = u.vs_call_ctx /\ s.vs_fmp = u.vs_fmp /\
  s.vs_initial_fmp = u.vs_initial_fmp
Proof
  strip_tac >>
  qpat_x_assum `step_inst fuel C e s = OK u` mp_tac >>
  asm_rewrite_tac[step_inst_def] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >> strip_tac >>
  gvs[AllCaseEqs()] >> drule dft_static_call_read_fields >> simp[]
QED


Theorem dft_pure1_replay:
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op u) /\
  exec_pure1 f i s = OK t ==>
  ?out value. i.inst_outputs = [out] /\ t = update_var out value s /\
    exec_pure1 f i u = OK (update_var out value u)
Proof
  simp[exec_pure1_def] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  rpt (qpat_x_assum `SOME _ = eval_operand _ _` (assume_tac o SYM)) >>
  simp[] >> metis_tac[]
QED

Theorem dft_pure2_replay:
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op u) /\
  exec_pure2 f i s = OK t ==>
  ?out value. i.inst_outputs = [out] /\ t = update_var out value s /\
    exec_pure2 f i u = OK (update_var out value u)
Proof
  simp[exec_pure2_def] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  rpt (qpat_x_assum `SOME _ = eval_operand _ _` (assume_tac o SYM)) >>
  simp[] >> metis_tac[]
QED

Theorem dft_pure3_replay:
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op u) /\
  exec_pure3 f i s = OK t ==>
  ?out value. i.inst_outputs = [out] /\ t = update_var out value s /\
    exec_pure3 f i u = OK (update_var out value u)
Proof
  simp[exec_pure3_def] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  rpt (qpat_x_assum `SOME _ = eval_operand _ _` (assume_tac o SYM)) >>
  simp[] >> metis_tac[]
QED

val dft_opcode_eqs = CONJUNCTS step_inst_base_opcode_eqs;

Theorem dft_empty_read_replay:
  inst_wf p /\ inst_shape_ok p /\
  ~is_terminator p.inst_opcode /\ p.inst_opcode <> ALLOCA /\
  p.inst_opcode <> INVOKE /\ ~is_ext_call_op p.inst_opcode /\
  write_effects p.inst_opcode = {} /\ read_effects p.inst_opcode = {} /\
  (!op. MEM op p.inst_operands ==> eval_operand op s = eval_operand op u) /\
  s.vs_prev_bb = u.vs_prev_bb /\ s.vs_params = u.vs_params /\
  s.vs_return_pc_token = u.vs_return_pc_token /\
  s.vs_call_ctx = u.vs_call_ctx /\ s.vs_tx_ctx = u.vs_tx_ctx /\
  s.vs_block_ctx = u.vs_block_ctx /\ s.vs_data_section = u.vs_data_section /\
  s.vs_code = u.vs_code /\ s.vs_labels = u.vs_labels /\
  s.vs_prev_hashes = u.vs_prev_hashes /\
  step_inst_base p s = OK t ==>
  ?pairs. MAP FST pairs = p.inst_outputs /\
    t = FOLDL (\st (out,value). update_var out value st) s pairs /\
    step_inst_base p u =
      OK (FOLDL (\st (out,value). update_var out value st) u pairs)
Proof
  strip_tac >> Cases_on `p.inst_opcode` >>
  fs[write_effects_def, read_effects_def, empty_effects_def] >>
  fs[is_terminator_def, is_ext_call_op_def, inst_shape_ok_def] >>
  qpat_x_assum `step_inst_base p s = OK t` mp_tac >>
  asm_simp_tac bool_ss dft_opcode_eqs >> strip_tac
  >>~- ([`exec_pure1 _ p s = OK t`],
    drule_all dft_pure1_replay >> strip_tac >>
    qexists_tac `[(out,value)]` >> simp[])
  >>~- ([`exec_pure2 _ p s = OK t`],
    drule_all dft_pure2_replay >> strip_tac >>
    qexists_tac `[(out,value)]` >> simp[])
  >>~- ([`exec_pure3 _ p s = OK t`],
    drule_all dft_pure3_replay >> strip_tac >>
    qexists_tac `[(out,value)]` >> simp[])
  >>~- ([`exec_read0 _ p s = OK t`],
    drule_at (Pat `exec_read0 _ _ _ = OK _`) dft_read0_replay >>
    disch_then (qspec_then `u` mp_tac) >> simp[] >> strip_tac >> qexists_tac `[(out,value)]` >> simp[])
  >>~- ([`exec_read1 _ p s = OK t`],
    drule_at (Pat `exec_read1 _ _ _ = OK _`) dft_read1_replay >>
    disch_then (qspec_then `u` mp_tac) >> simp[] >> strip_tac >>
    qexists_tac `[(out,value)]` >> simp[]) >>
  gvs[AllCaseEqs()] >> fs[inst_wf_def] >>
  rpt (qpat_x_assum `SOME _ = eval_operand _ _` (assume_tac o SYM)) >>
  simp[] >> FIRST [
    qexists_tac `[]` >> simp[] >> NO_TAC,
    qmatch_goalsub_abbrev_tac `update_var out value s` >>
      qexists_tac `[(out,value)]` >> simp[] >> NO_TAC,
    qmatch_goalsub_abbrev_tac `update_var out2 value2 (update_var out1 value1 s)` >>
      qexists_tac `[(out1,value1); (out2,value2)]` >> simp[] >> NO_TAC]
QED

Theorem dft_external_step_metadata:
  (e.inst_opcode = CALL \/ e.inst_opcode = STATICCALL) /\
  step_inst fuel C e s = OK u ==>
  s.vs_prev_bb = u.vs_prev_bb /\ s.vs_params = u.vs_params /\
  s.vs_return_pc_token = u.vs_return_pc_token /\
  s.vs_call_ctx = u.vs_call_ctx /\ s.vs_tx_ctx = u.vs_tx_ctx /\
  s.vs_block_ctx = u.vs_block_ctx /\ s.vs_data_section = u.vs_data_section /\
  s.vs_code = u.vs_code /\ s.vs_labels = u.vs_labels /\
  s.vs_prev_hashes = u.vs_prev_hashes
Proof
  strip_tac >> qpat_x_assum `step_inst fuel C e s = OK u` mp_tac >>
  asm_rewrite_tac[step_inst_def] >>
  asm_simp_tac bool_ss dft_opcode_eqs >> strip_tac >>
  gvs[AllCaseEqs()] >>
  gvs[exec_ext_call_def, consume_call_outcome_eq, AllCaseEqs(), update_var_def]
QED

Theorem dft_step_operand_agreement:
  step_inst fuel C e s = OK u /\ ~is_terminator e.inst_opcode /\
  DISJOINT (set (inst_defs e)) (set (inst_uses p)) ==>
  !op. MEM op p.inst_operands ==> eval_operand op s = eval_operand op u
Proof
  strip_tac >> rpt strip_tac >>
  drule eval_operand_step_pres >>
  disch_then (qspec_then `op` mp_tac) >>
  simp[] >> impl_tac
  >- (rpt strip_tac >> gvs[inst_defs_def, inst_uses_def, DISJOINT_DEF,
                          EXTENSION] >> metis_tac[mem_var_operand_vars]) >>
  simp[]
QED

Theorem dft_external_replay:
  (e.inst_opcode = CALL \/ e.inst_opcode = STATICCALL) /\
  effects_independent e.inst_opcode p.inst_opcode /\
  DISJOINT (set (inst_defs e)) (set (inst_uses p)) /\
  inst_wf p /\ inst_shape_ok p /\
  ~is_terminator p.inst_opcode /\ p.inst_opcode <> ALLOCA /\
  (step_inst fe C e s = OK u \/ step_inst fe C e u = OK s) /\
  step_inst fp C p s = OK t ==>
  ?pairs. MAP FST pairs = p.inst_outputs /\
    t = FOLDL (\st (out,value). update_var out value st) s pairs /\
    step_inst fp C p u =
      OK (FOLDL (\st (out,value). update_var out value st) u pairs)
Proof
  strip_tac >>
  `~is_terminator e.inst_opcode` by gvs[is_terminator_def] >>
  drule dft_external_observer >> simp[] >> strip_tac >>
  `!op. MEM op p.inst_operands ==> eval_operand op s = eval_operand op u` by
    metis_tac[dft_step_operand_agreement] >>
  qpat_assum `step_inst fe C e _ = OK _`
    (mp_then (Pat `step_inst _ _ _ _ = OK _`) mp_tac dft_external_step_metadata) >>
  simp[] >> strip_tac >>
  (Cases_on `read_effects p.inst_opcode = {}`
  >- (gvs[step_inst_def] >> irule dft_empty_read_replay >> simp[]) >> gvs[] >>
  `e.inst_opcode = STATICCALL` by metis_tac[] >>
  `DISJOINT (read_effects p.inst_opcode) {Eff_MEMORY; Eff_RETURNDATA}` by
    gvs[write_effects_def] >>
  qpat_assum `step_inst fe C e _ = OK _`
    (mp_then (Pat `step_inst _ _ _ _ = OK _`) mp_tac dft_static_step_read_fields) >>
  simp[] >> strip_tac >>
  drule_all dft_static_read_observer >> strip_tac >>
  gvs[step_inst_def] >>
  qpat_assum `step_inst_base p s = OK t`
    (mp_then (Pat `step_inst_base _ _ = OK _`) mp_tac dft_static_read_replay) >>
  disch_then (qspec_then `u` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `[(out,value)]` >> simp[])
QED

Theorem dft_external_observer_updates:
  (e.inst_opcode = CALL \/ e.inst_opcode = STATICCALL) /\
  effects_independent e.inst_opcode p.inst_opcode /\
  inst_wf p /\ inst_shape_ok p /\
  ~is_terminator p.inst_opcode /\ p.inst_opcode <> ALLOCA /\
  step_inst fp C p s = OK t ==>
  ?pairs. MAP FST pairs = p.inst_outputs /\
    t = FOLDL (\st (out,value). update_var out value st) s pairs
Proof
  strip_tac >> drule dft_external_observer >> simp[] >> strip_tac >>
  (Cases_on `read_effects p.inst_opcode = {}`
  >- (gvs[step_inst_def] >>
      qpat_assum `step_inst_base p s = OK t`
        (mp_then (Pat `step_inst_base _ _ = OK _`) mp_tac dft_empty_read_replay) >>
      disch_then (qspec_then `s` mp_tac) >> simp[] >> metis_tac[]) >>
  `e.inst_opcode = STATICCALL` by metis_tac[] >>
  `DISJOINT (read_effects p.inst_opcode) {Eff_MEMORY; Eff_RETURNDATA}` by
    gvs[write_effects_def] >>
  drule_all dft_static_read_observer >> strip_tac >>
  gvs[step_inst_def] >>
  qpat_assum `step_inst_base p s = OK t`
    (mp_then (Pat `step_inst_base _ _ = OK _`) mp_tac dft_static_read_replay) >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `[(out,value)]` >> simp[])
QED

Theorem dft_updates_independent:
  MAP FST pairs = p.inst_outputs /\
  DISJOINT (set (inst_defs p)) (set (inst_uses e)) /\
  DISJOINT (set (inst_defs p)) (set (inst_defs e)) ==>
  EVERY (\kv. (!y. MEM (Var y) e.inst_operands ==> FST kv <> y) /\
              ~MEM (FST kv) e.inst_outputs) pairs
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM (FST kv) p.inst_outputs` by metis_tac[MEM_MAP] >>
  gvs[inst_defs_def, inst_uses_def, DISJOINT_DEF, EXTENSION] >>
  metis_tac[mem_var_operand_vars]
QED

Theorem dft_updates_vars:
  !pairs s. FOLDL (\st (out,value). update_var out value st) s pairs =
    s with vs_vars := FOLDL (\vs kv. vs |+ kv) s.vs_vars pairs
Proof
  Induct >> simp[] >> Cases_on `h` >>
  simp[update_var_def]
QED

Theorem dft_updates_lookup:
  !pairs s u k.
  FLOOKUP (FOLDL (\vs kv. vs |+ kv) s pairs) k =
    if MEM k (MAP FST pairs) then
      FLOOKUP (FOLDL (\vs kv. vs |+ kv) u pairs) k
    else FLOOKUP s k
Proof
  Induct >- simp[] >> Cases_on `h` >> rpt gen_tac >>
  simp[] >> first_assum (qspecl_then [`u |+ (q,r)`, `u |+ (q,r)`, `k`] mp_tac) >>
  first_x_assum (qspecl_then [`s |+ (q,r)`, `u |+ (q,r)`, `k`] mp_tac) >>
  Cases_on `MEM k (MAP FST pairs)` >> simp[] >>
  Cases_on `k = q` >> simp[FLOOKUP_UPDATE]
QED

Theorem dft_updates_transfer:
  MAP FST pairs = MAP FST pairs' /\
  FOLDL (\st (out,value). update_var out value st) s pairs =
  FOLDL (\st (out,value). update_var out value st) s pairs' ==>
  FOLDL (\st (out,value). update_var out value st) u pairs =
  FOLDL (\st (out,value). update_var out value st) u pairs'
Proof
  simp[dft_updates_vars] >> strip_tac >>
  `FOLDL (\vs kv. vs |+ kv) s.vs_vars pairs =
   FOLDL (\vs kv. vs |+ kv) s.vs_vars pairs'` by
    (qpat_x_assum `s with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\st. st.vs_vars`) >> simp[]) >>
  AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
  simp[FLOOKUP_EXT, FUN_EQ_THM] >> gen_tac >>
  qspec_then `pairs` (qspecl_then [`u.vs_vars`, `s.vs_vars`, `x`] mp_tac) dft_updates_lookup >>
  qspec_then `pairs'` (qspecl_then [`u.vs_vars`, `s.vs_vars`, `x`] mp_tac) dft_updates_lookup >>
  simp[]
QED

Theorem dft_external_pair:
  (e.inst_opcode = CALL \/ e.inst_opcode = STATICCALL) /\
  effects_independent e.inst_opcode p.inst_opcode /\
  DISJOINT (set (inst_defs e)) (set (inst_uses p)) /\
  DISJOINT (set (inst_defs p)) (set (inst_uses e)) /\
  DISJOINT (set (inst_defs p)) (set (inst_defs e)) /\
  inst_wf p /\ inst_shape_ok p /\
  ~is_terminator p.inst_opcode /\ p.inst_opcode <> ALLOCA ==>
  ((?se. step_inst fe C e s = OK se /\ step_inst fp C p se = OK t) <=>
   (?sp. step_inst fp C p s = OK sp /\ step_inst fe C e sp = OK t))
Proof
  strip_tac >> (`e.inst_opcode <> INVOKE` by gvs[] >> eq_tac
  >- (strip_tac >>
      qpat_assum `step_inst fp C p se = OK t`
        (mp_then (Pat `step_inst _ _ _ _ = OK _`) mp_tac dft_external_replay) >>
      disch_then (qspecl_then [`s`, `fe`, `e`] mp_tac) >> simp[] >>
      strip_tac >>
      `EVERY (\kv. (!y. MEM (Var y) e.inst_operands ==> FST kv <> y) /\
                    ~MEM (FST kv) e.inst_outputs) pairs` by
        (irule dft_updates_independent >> metis_tac[]) >>
      qexists_tac `FOLDL (\st (out,value). update_var out value st) s pairs` >>
      simp[] >> drule_all dft_step_frame_updates >>
      disch_then (qspecl_then [`fe`, `C`, `s`] mp_tac) >>
      simp[map_result_state_def]) >>
  strip_tac >>
  qpat_assum `step_inst fp C p s = OK sp`
    (mp_then (Pat `step_inst _ _ _ _ = OK _`) mp_tac dft_external_observer_updates) >>
  disch_then (qspec_then `e` mp_tac) >> simp[] >> strip_tac >>
  `EVERY (\kv. (!y. MEM (Var y) e.inst_operands ==> FST kv <> y) /\
                ~MEM (FST kv) e.inst_outputs) pairs` by
    (irule dft_updates_independent >> metis_tac[]) >>
  drule_all dft_step_frame_updates_ok >>
  disch_then (qspecl_then [`t`, `s`, `fe`, `C`] mp_tac) >>
  simp[] >> strip_tac >>
  `?u. step_inst fe C e s = OK u /\
       t = FOLDL (\st (out,value). update_var out value st) u pairs` by metis_tac[] >>
  qpat_assum `step_inst fp C p s = OK sp`
    (mp_then (Pat `step_inst _ _ _ _ = OK _`) mp_tac dft_external_replay) >>
  disch_then (qspecl_then [`u`, `fe`, `e`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `pairs'` strip_assume_tac) >>
  `FOLDL (\st (out,value). update_var out value st) u pairs' =
   FOLDL (\st (out,value). update_var out value st) u pairs` by
    (irule dft_updates_transfer >> metis_tac[]) >>
  simp[])
QED

Theorem dft_cross_pair:
  dft_cross a b /\ inst_wf a /\ inst_wf b /\
  inst_shape_ok a /\ inst_shape_ok b /\
  a.inst_opcode <> ALLOCA /\ b.inst_opcode <> ALLOCA ==>
  ((?sa. step_inst fa C a s = OK sa /\ step_inst fb C b sa = OK t) <=>
   (?sb. step_inst fb C b s = OK sb /\ step_inst fa C a sb = OK t))
Proof
  strip_tac >> drule dft_cross_effects >> strip_tac >>
  Cases_on `is_ext_call_op a.inst_opcode`
  >- (drule_all dft_shape_external >> strip_tac >>
      irule dft_external_pair >> gvs[dft_cross_def, DISJOINT_SYM]) >>
  Cases_on `is_ext_call_op b.inst_opcode`
  >- (drule_all dft_shape_external >> strip_tac >>
      ONCE_REWRITE_TAC[EQ_SYM_EQ] >> irule dft_external_pair >>
      gvs[dft_cross_def, effects_independent_def, DISJOINT_UNION, DISJOINT_SYM]) >>
  drule_all dft_cross_ext_independent >> strip_tac >>
  drule dft_cross_not_two_invokes >> strip_tac >>
  eq_tac >> strip_tac >> irule dft_step_swap_two_fuels >>
  metis_tac[ext_bi_independent_sym]
QED

Theorem dft_step_index_ok:
  ~is_terminator i.inst_opcode ==>
  (step_inst fuel C i (s with vs_inst_idx := n) = OK t <=>
   ?u. step_inst fuel C i s = OK u /\ t = u with vs_inst_idx := n)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >> drule_all step_preserves_control_flow >> simp[] >> strip_tac >>
      drule_all dft_step_index >> disch_then (qspec_then `s.vs_inst_idx` mp_tac) >>
      simp[] >> strip_tac >>
      qpat_x_assum `t.vs_inst_idx = n` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  strip_tac >> gvs[] >> irule dft_step_index >> simp[] >> metis_tac[]
QED

Theorem dft_prefix_pair_steps:
  ~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode ==>
  (dft_prefix C [a;b] s t <=>
   ?fa fb sa u. step_inst fa C a s = OK sa /\
     step_inst fb C b sa = OK u /\
     t = u with vs_inst_idx := s.vs_inst_idx + 2)
Proof
  strip_tac >> simp[dft_prefix_cons, dft_step_index_ok] >>
  `s.vs_inst_idx + 2 = SUC (SUC s.vs_inst_idx)` by decide_tac >>
  simp[SF DNF_ss] >> metis_tac[]
QED

Theorem dft_cross_prefix_pair:
  dft_cross a b /\ inst_wf a /\ inst_wf b /\
  inst_shape_ok a /\ inst_shape_ok b /\
  a.inst_opcode <> ALLOCA /\ b.inst_opcode <> ALLOCA ==>
  (dft_prefix C [a;b] s t <=> dft_prefix C [b;a] s t)
Proof
  strip_tac >>
  `~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode` by
    gvs[dft_cross_def] >>
  simp[dft_prefix_pair_steps] >>
  drule_all dft_cross_pair >>
  metis_tac[]
QED
