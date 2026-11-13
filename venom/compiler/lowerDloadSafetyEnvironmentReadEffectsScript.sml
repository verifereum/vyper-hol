(* Zero-operand environment observations preserve the safety projection. *)
Theory lowerDloadSafetyEnvironmentReadEffects
Ancestors
  lowerDloadSafetyKernel lowerDloadSafetyReadSteps lowerDloadSafetyUpdates lowerDloadSafetyValues
  ptrDiscipline venomExecSemantics venomState venomInst unitShapeDefs
  codegenRel contextCodegenRel memLocDefs finite_map list pred_set words

Theorem ld_environment_read_vars[local]:
  ld_vars P A f /\ ld_nonghost tn f.lf_src f.lf_tgt /\
  MEM inst (fn_insts f.lf_fn) /\
  MEM inst.inst_opcode
    [CALLER;ADDRESS;CALLVALUE;ORIGIN;GASPRICE;CHAINID;COINBASE;
     TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;
     CALLDATASIZE;RETURNDATASIZE;CODESIZE] /\
  step_inst_base inst f.lf_tgt = OK ts ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := set_var_taint f.lf_tv inst.inst_outputs (out_taint tn inst f.lf_src) |> )
Proof
  strip_tac >>
  `!v. MEM v inst.inst_outputs ==> MEM v (fn_ir_vars f.lf_fn)` by
    metis_tac[ld_inst_output_ir] >>
  `f.lf_src.vs_call_ctx = f.lf_tgt.vs_call_ctx /\
   f.lf_src.vs_tx_ctx = f.lf_tgt.vs_tx_ctx /\
   f.lf_src.vs_block_ctx = f.lf_tgt.vs_block_ctx /\
   f.lf_src.vs_returndata = f.lf_tgt.vs_returndata /\
   f.lf_src.vs_code = f.lf_tgt.vs_code` by gvs[ld_nonghost_def] >>
  gvs[MEM] >>
  (qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
   pure_once_rewrite_tac[step_inst_base_def] >>
   asm_rewrite_tac[opcode_case_def] >> strip_tac >>
   pure_once_rewrite_tac[step_inst_base_def] >>
   asm_rewrite_tac[opcode_case_def] >>
   irule ld_vars_exec_read0 >> simp[word_agree_except_def])
QED

Theorem ld_environment_read_success[local]:
  MEM inst.inst_opcode
    [CALLER;ADDRESS;CALLVALUE;ORIGIN;GASPRICE;CHAINID;COINBASE;
     TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;
     CALLDATASIZE;RETURNDATASIZE;CODESIZE] /\
  step_inst_base inst s = OK s' ==>
  ?out x. inst.inst_outputs = [out] /\ s' = update_var out x s
Proof
  strip_tac >> gvs[MEM] >>
  (qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
   pure_once_rewrite_tac[step_inst_base_def] >>
   asm_rewrite_tac[opcode_case_def] >>
   simp[exec_read0_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[])
QED

Theorem ld_environment_read_taint[local]:
  MEM inst.inst_opcode
    [CALLER;ADDRESS;CALLVALUE;ORIGIN;GASPRICE;CHAINID;COINBASE;
     TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;
     CALLDATASIZE;RETURNDATASIZE;CODESIZE] ==>
  step_taint inst s (update_var v x s) tn =
    tn with t_var := set_var_taint tn.t_var inst.inst_outputs (out_taint tn inst s)
Proof
  strip_tac >>
  `written_taint tn inst s = {}` by
    (namedCases_on `inst.inst_operands` ["", "a rest"]
     >- gvs[MEM, written_taint_def] >>
     namedCases_on `rest` ["", "b tail"]
     >- gvs[MEM, written_taint_def] >>
     namedCases_on `tail` ["", "c more"]
     >- gvs[MEM, written_taint_def] >>
     Cases_on `more` >> gvs[MEM, written_taint_def]) >>
  gvs[MEM] >>
  (simp[step_taint_def, mem_taint_def, update_var_def,
        new_site_bytes_def, step_writes_def, range_bytes_def,
        source_memory_write_ranges_def, store_taint_def, adopt_reset_def,
        imm_taint_def, FLOOKUP_DEF, taint_component_equality] >> SET_TAC[])
QED

(* GAS pops the next reading, so its states differ from an environment
   read's by the remaining readings, which the two runs share. *)
Theorem ld_vars_same_vars[local]:
  ld_vars P A (f with <| lf_src := s; lf_tgt := t; lf_H := H; lf_tv := tv |>) /\
  s'.vs_vars = s.vs_vars /\ s'.vs_params = s.vs_params /\
  t'.vs_vars = t.vs_vars /\ t'.vs_params = t.vs_params ==>
  ld_vars P A (f with <| lf_src := s'; lf_tgt := t'; lf_H := H; lf_tv := tv |>)
Proof
  simp[lowerDloadSafetyRelationTheory.ld_vars_def]
QED

Theorem ld_gas_read_taint[local]:
  inst.inst_opcode = GAS ==>
  step_taint inst s (update_var v x (s with vs_gas_readings := g)) tn =
    tn with t_var := set_var_taint tn.t_var inst.inst_outputs (out_taint tn inst s)
Proof
  strip_tac >>
  `written_taint tn inst s = {}` by
    (simp[written_taint_def] >> BasicProvers.every_case_tac >> gvs[]) >>
  simp[step_taint_def, mem_taint_def, update_var_def,
       new_site_bytes_def, step_writes_def, range_bytes_def,
       source_memory_write_ranges_def, store_taint_def, adopt_reset_def,
       imm_taint_def, FLOOKUP_DEF, taint_component_equality] >> SET_TAC[]
QED

Theorem ld_gas_read_step[local]:
  inst.inst_opcode = GAS /\
  s.vs_gas_readings = t.vs_gas_readings /\
  step_inst_base inst t = OK ts ==>
  ?out r g. inst.inst_outputs = [out] /\
    ts = update_var out r (t with vs_gas_readings := g) /\
    step_inst_base inst s = OK (update_var out r (s with vs_gas_readings := g))
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst t = OK ts` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[exec_gas_def, AllCaseEqs()] >> strip_tac >>
  qexistsl_tac [`out`, `case t.vs_gas_readings of [] => 0w | r::_ => r`,
                `DROP 1 t.vs_gas_readings`] >>
  gvs[] >>
  Cases_on `t.vs_gas_readings` >>
  gvs[venom_state_component_equality, update_var_def]
QED

Theorem ld_environment_read_effect:
  ld_vars P A f /\ fn_ptr_ok P f.lf_fn /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ tn.t_var = f.lf_tv /\
  taint_ok f.lf_fn tn inst f.lf_src /\
  MEM inst.inst_opcode
    [CALLER;ADDRESS;CALLVALUE;GAS;ORIGIN;GASPRICE;CHAINID;COINBASE;
     TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;
     CALLDATASIZE;RETURNDATASIZE;CODESIZE] /\
  step_inst_base inst f.lf_tgt = OK ts /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\ ld_nonghost tn f.lf_src f.lf_tgt ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var |> ) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
    ld_erase A o_f set_prov f.lf_H inst.inst_outputs NONE =
      step_prov PG (ld_erase A o_f f.lf_H) inst ss /\
    ss.vs_allocas = f.lf_src.vs_allocas /\
    ss.vs_alloca_next = f.lf_src.vs_alloca_next /\
    ss.vs_params = f.lf_src.vs_params /\
    ss.vs_current_bb = f.lf_src.vs_current_bb /\
    ss.vs_prev_bb = f.lf_src.vs_prev_bb /\
    ss.vs_inst_idx = f.lf_src.vs_inst_idx /\
    ts.vs_allocas = f.lf_tgt.vs_allocas /\
    ts.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    ts.vs_params = f.lf_tgt.vs_params /\
    ts.vs_current_bb = f.lf_tgt.vs_current_bb /\
    ts.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
    ts.vs_inst_idx = f.lf_tgt.vs_inst_idx
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = GAS`
  >- (`f.lf_src.vs_gas_readings = f.lf_tgt.vs_gas_readings` by
        fs[ld_nonghost_def] >>
      `!v. MEM v inst.inst_outputs ==> MEM v (fn_ir_vars f.lf_fn)` by
        metis_tac[ld_inst_output_ir] >>
      drule_all ld_gas_read_step >> strip_tac >>
      `step_taint inst f.lf_src
         (update_var out r (f.lf_src with vs_gas_readings := g)) tn =
       tn with t_var := set_var_taint tn.t_var inst.inst_outputs
         (out_taint tn inst f.lf_src)` by
        (irule ld_gas_read_taint >> simp[]) >>
      `?ss0. exec_read0 (K r) inst f.lf_src = OK ss0 /\
         ld_vars P A (f with <|lf_src := ss0;
           lf_tgt := update_var out r f.lf_tgt;
           lf_H := set_prov f.lf_H inst.inst_outputs NONE;
           lf_tv := set_var_taint f.lf_tv inst.inst_outputs
                      (out_taint tn inst f.lf_src)|>)` by
        (irule ld_vars_exec_read0 >>
         gvs[exec_read0_def, word_agree_except_def]) >>
      qpat_x_assum `exec_read0 _ _ _ = _` mp_tac >>
      simp[exec_read0_def] >> strip_tac >> gvs[] >>
      rpt conj_tac
      >- (irule ld_vars_same_vars >>
          qexistsl_tac [`update_var out r f.lf_src`,
                        `update_var out r f.lf_tgt`] >>
          simp[update_var_def])
      >- (fs[ld_memory_def, update_var_def] >> metis_tac[])
      >- (fs[ld_nonghost_def, update_var_def] >> metis_tac[]) >>
      simp[ld_erase_set_prov, step_prov_def, out_prov_def, update_var_def]) >>
  `MEM inst.inst_opcode
    [CALLER;ADDRESS;CALLVALUE;ORIGIN;GASPRICE;CHAINID;COINBASE;
     TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;
     CALLDATASIZE;RETURNDATASIZE;CODESIZE]` by gvs[] >>
  drule_all ld_environment_read_vars >> strip_tac >>
  drule_all ld_environment_read_success >> strip_tac >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  strip_tac >> drule_all ld_environment_read_success >> strip_tac >> gvs[] >>
  `step_taint inst f.lf_src (update_var out x f.lf_src) tn =
     tn with t_var := set_var_taint tn.t_var inst.inst_outputs
       (out_taint tn inst f.lf_src)` by
    (irule ld_environment_read_taint >> simp[]) >>
  (simp[] >>
   conj_tac >- (irule ld_memory_update_var >> simp[]) >>
   conj_tac >- (irule ld_nonghost_update_var >> simp[]) >>
   simp[ld_erase_set_prov, step_prov_def, out_prov_def])
QED
