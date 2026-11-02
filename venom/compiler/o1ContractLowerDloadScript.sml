(*
 * LowerDload against the O1 pass contract: the step part.
 *
 * The dispatched transform is lower_dload_function_supply, which draws its
 * new variables and instruction ids from the IR supply.  The step part of
 * the contract asks that one run keeps the O1 function shape, takes fresh
 * ids, and maps no labels.  The run's input supply must be well formed
 * (ir_supply_inst_ok: every used id is below the next one) and cover the
 * observed unit; the schedule runner establishes both at its start and
 * every step's checks keep them, but fn_pass_step does not say so yet, so
 * they are hypotheses here.
 *
 * TOP-LEVEL:
 *   lower_dload_function_supply_wf_function  - well-formedness kept
 *   lower_dload_function_supply_ssa_form     - SSA kept
 *   lower_dload_step_shape                   - the step part of the contract
 *)
Theory o1ContractLowerDload
Ancestors
  o1PassContract lowerDloadDefs lowerDloadSupplyProofs venomPassDispatcher venomFnScheduleRunner
  unitShapeDefs venomWf irSupply venomInst stackPlanTypes list

(* Why these hold: the expansion of DLOAD/DLOADBYTES only inserts
   non-terminators (ALLOCA, ADD, CODECOPY, MLOAD) in place of a
   non-terminator, so block labels, terminators and successors are
   unchanged; the new ids come from fresh_inst_id, which under
   ir_supply_inst_ok returns ids above every used id, hence outside the
   function's ids when the supply covers it; the new variables come from
   fresh_ir_var, which avoids irs_used_vars.  The only label operand added
   is "code_end" as ADD's second operand, which label_positions_ok admits
   and which is reserved. *)

Theorem lower_dload_inst_supply_nonempty:
  lower_dload_inst_supply s i = (xs,t) ==> xs <> []
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      strip_tac >> gvs[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      strip_tac >> gvs[]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_inst_supply_special:
  ~MEM i.inst_opcode [DLOAD; DLOADBYTES] ==>
  lower_dload_inst_supply s i = ([i],s)
Proof
  simp[lower_dload_inst_supply_def]
QED

Theorem lower_dload_inst_supply_control:
  lower_dload_inst_supply s i = (xs,t) /\ MEM j xs /\
  (is_terminator j.inst_opcode \/ j.inst_opcode = PHI \/
   MEM j.inst_opcode [GAS; RETPC_PARAM; ASSIGN; PARAM; INVOKE; RET; STOP; RETURN]) ==>
  j = i
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[is_terminator_def]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[is_terminator_def]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_inst_supply_wf:
  lower_dload_inst_supply s i = (xs,t) /\ inst_wf i ==>
  EVERY inst_wf xs
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[inst_wf_def]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[inst_wf_def]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_inst_supply_shape:
  lower_dload_inst_supply s i = (xs,t) /\ inst_shape_ok i ==>
  EVERY inst_shape_ok xs
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >>
      gvs[inst_shape_ok_def, label_positions_ok_def, is_read0_opcode_def,
          is_label_operand_def]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >>
      gvs[inst_shape_ok_def, label_positions_ok_def, is_read0_opcode_def,
          is_label_operand_def]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_inst_supply_operand_provenance:
  lower_dload_inst_supply s i = (xs,t) /\ MEM j xs /\
  MEM op j.inst_operands ==>
  MEM op i.inst_operands \/
  (?v. op = Var v /\ MEM v (FLAT (MAP (\k. k.inst_outputs) xs))) \/
  op = Label "code_end" \/ op = Lit 32w
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_inst_supply_vars:
  lower_dload_inst_supply s i = (xs,t) /\
  EVERY (\v. MEM v s.irs_used_vars) i.inst_outputs /\
  ALL_DISTINCT i.inst_outputs ==>
  ALL_DISTINCT (FLAT (MAP (\k. k.inst_outputs) xs)) /\
  EVERY (\v. MEM v t.irs_used_vars) (FLAT (MAP (\k. k.inst_outputs) xs)) /\
  (!v. MEM v s.irs_used_vars ==> MEM v t.irs_used_vars) /\
  (!v. MEM v (FLAT (MAP (\k. k.inst_outputs) xs)) /\
       MEM v s.irs_used_vars ==> MEM v i.inst_outputs)
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> imp_res_tac fresh_ir_var_contract >> gvs[] >>
      metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> imp_res_tac fresh_ir_var_contract >> gvs[] >>
      metis_tac[]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_insts_supply_vars:
  !s xs t.
  lower_dload_insts_supply s ins = (xs,t) /\
  EVERY (\v. MEM v s.irs_used_vars) (FLAT (MAP (\k. k.inst_outputs) ins)) /\
  ALL_DISTINCT (FLAT (MAP (\k. k.inst_outputs) ins)) ==>
  ALL_DISTINCT (FLAT (MAP (\k. k.inst_outputs) xs)) /\
  EVERY (\v. MEM v t.irs_used_vars) (FLAT (MAP (\k. k.inst_outputs) xs)) /\
  (!v. MEM v s.irs_used_vars ==> MEM v t.irs_used_vars) /\
  (!v. MEM v (FLAT (MAP (\k. k.inst_outputs) xs)) /\
       MEM v s.irs_used_vars ==>
       MEM v (FLAT (MAP (\k. k.inst_outputs) ins)))
Proof
  Induct_on `ins`
  >- simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  strip_tac >>
  gvs[ALL_DISTINCT_APPEND] >>
  drule_all lower_dload_inst_supply_vars >> strip_tac >>
  `EVERY (\v. MEM v s1.irs_used_vars)
     (FLAT (MAP (\k. k.inst_outputs) ins))` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  simp[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND, EVERY_APPEND] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem lower_dload_blocks_supply_vars:
  !s bs t.
  lower_dload_blocks_supply s bbs = (bs,t) /\
  EVERY (\v. MEM v s.irs_used_vars)
    (FLAT (MAP (\b. FLAT (MAP (\k. k.inst_outputs) b.bb_instructions)) bbs)) /\
  ALL_DISTINCT
    (FLAT (MAP (\b. FLAT (MAP (\k. k.inst_outputs) b.bb_instructions)) bbs)) ==>
  ALL_DISTINCT (FLAT (MAP (\b. FLAT (MAP (\k. k.inst_outputs) b.bb_instructions)) bs)) /\
  EVERY (\v. MEM v t.irs_used_vars)
    (FLAT (MAP (\b. FLAT (MAP (\k. k.inst_outputs) b.bb_instructions)) bs)) /\
  (!v. MEM v s.irs_used_vars ==> MEM v t.irs_used_vars) /\
  (!v. MEM v (FLAT (MAP (\b. FLAT (MAP (\k. k.inst_outputs) b.bb_instructions)) bs)) /\
       MEM v s.irs_used_vars ==>
       MEM v (FLAT (MAP (\b. FLAT (MAP (\k. k.inst_outputs) b.bb_instructions)) bbs)))
Proof
  Induct_on `bbs`
  >- simp[lower_dload_blocks_supply_def] >>
  rpt gen_tac >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs()] >> strip_tac >>
  gvs[ALL_DISTINCT_APPEND] >>
  drule_all lower_dload_insts_supply_vars >> strip_tac >>
  `EVERY (\v. MEM v s1.irs_used_vars)
    (FLAT (MAP (\b. FLAT (MAP (\k. k.inst_outputs) b.bb_instructions)) bbs))` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  simp[ALL_DISTINCT_APPEND, EVERY_APPEND] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem lower_dload_outputs_blocks[local]:
  FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bs)) =
  FLAT (MAP (\b. FLAT (MAP (\i. i.inst_outputs) b.bb_instructions)) bs)
Proof
  Induct_on `bs` >> simp[fn_insts_blocks_def, MAP_APPEND, FLAT_APPEND]
QED

Theorem lower_dload_function_supply_outputs:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts f))) ==>
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts g)))
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs(), fn_insts_def,
       lower_dload_outputs_blocks] >> strip_tac >> gvs[] >>
  irule (cj 1 lower_dload_blocks_supply_vars) >>
  qexistsl [`f.fn_blocks`,`s`,`t`] >> simp[] >>
  rw[EVERY_MEM, MEM_FLAT, MEM_MAP] >>
  gvs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >>
  first_x_assum irule >>
  simp[fn_ir_vars_def, block_ir_vars_def, MEM_FLAT, MEM_MAP,
       PULL_EXISTS, inst_ir_vars_def] >>
  gvs[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem lower_dload_function_supply_distinct_ids:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_inst_ok s /\
  ir_supply_covers_fn s f /\ ALL_DISTINCT (fn_ir_inst_ids f) ==>
  ALL_DISTINCT (fn_ir_inst_ids g)
Proof
  strip_tac >>
  `EVERY (\id. MEM id s.irs_used_inst_ids) (fn_ir_inst_ids f)` by
    gvs[ir_supply_covers_fn_def, list_subset_def] >>
  drule_all lower_dload_function_supply_contract >>
  simp[ld_ids_supply_ok_def]
QED

Theorem lower_dload_function_supply_wf_function:
  !s fn fn' s'.
    wf_function fn /\ ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\
    lower_dload_function_supply s fn = (fn',s') ==>
    wf_function fn'
Proof
  cheat
QED

Theorem lower_dload_function_supply_ssa_form:
  !s fn fn' s'.
    ssa_form fn /\ ir_supply_covers_fn s fn /\
    lower_dload_function_supply s fn = (fn',s') ==>
    ssa_form fn'
Proof
  cheat
QED

Theorem lower_dload_step_shape:
  !rpolicy observed s fn out.
    fn_pass_step rpolicy (CFP_Simple VP_LowerDload) observed s fn out /\
    o1_ctx_shape observed.cu_context /\
    ir_supply_inst_ok s /\ ir_supply_covers_unit s observed ==>
    o1_fn_shape observed.cu_context out.fpo_function /\
    fresh_names_ok s fn out.fpo_function /\
    label_map_sources_ok fn out.fpo_function out.fpo_label_map
Proof
  cheat
QED
