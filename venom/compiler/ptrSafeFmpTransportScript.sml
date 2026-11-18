(* Three-field FMP transport for the safety and ghost observations.
   Execution commutation is supplied by the caller, not re-proved here. *)
Theory ptrSafeFmpTransport
Ancestors
  ptrSafeRun memSafeRun ptrDiscipline unitTransformDefs
  venomExecSemantics venomState venomInst contextCodegenRel codegenRel
  list finite_map pred_set instIdxIndep rawFmpTransportDefs unitShapeDefs
  contextPlanEmissionProps venomExecProofs rawFmpTransport ctxLookupAgreeHelpers

Theorem eval_operands_fmp_fields[simp]:
  !ops. eval_operands ops (s with <|vs_fmp := p; vs_initial_fmp := i;
                                  vs_call_entry_fmp := e|>) = eval_operands ops s
Proof
  Induct >> simp[eval_operands_def]
QED

Theorem step_prov_fmp_fields[simp]:
  inst.inst_opcode <> DALLOCA ==>
  step_prov PG G inst (s with <|vs_fmp := p; vs_initial_fmp := i;
                               vs_call_entry_fmp := e|>) = step_prov PG G inst s
Proof
  simp[step_prov_def, out_prov_def]
QED

Theorem entry_prov_fmp_fields[simp]:
  entry_prov fn (s with <|vs_fmp := p; vs_initial_fmp := i;
                         vs_call_entry_fmp := e|>) G = entry_prov fn s G
Proof
  simp[entry_prov_def]
QED

Theorem entry_taint_vars_fmp_fields[simp]:
  entry_taint_vars fn (s with <|vs_fmp := p; vs_initial_fmp := i;
                               vs_call_entry_fmp := e|>) tn = entry_taint_vars fn s tn
Proof
  simp[entry_taint_vars_def]
QED

Theorem source_memory_read_ranges_fmp_fields[simp]:
  inst.inst_opcode <> DRET ==>
  source_memory_read_ranges inst
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
  source_memory_read_ranges inst s
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  asm_simp_tac (srw_ss()) [source_memory_read_ranges_def,
    memory_range_of_operands_def, eval_operand_fmp_update,
    eval_operands_fmp_fields] >> gvs[]
QED

Theorem source_memory_write_ranges_fmp_fields[simp]:
  inst.inst_opcode <> DRET ==>
  source_memory_write_ranges inst
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
  source_memory_write_ranges inst s
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  simp[source_memory_write_ranges_def, fixed_source_write_range_def,
       sized_source_write_range_def] >> gvs[]
QED

Theorem new_site_bytes_fmp_fields:
  t.vs_fmp = s.vs_fmp ==>
  new_site_bytes
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
    (t with <|vs_fmp := p; vs_initial_fmp := j; vs_call_entry_fmp := d|>) =
  new_site_bytes s t
Proof
  simp[new_site_bytes_def]
QED

Theorem step_taint_fmp_fields:
  inst.inst_opcode <> DRET /\ t.vs_fmp = s.vs_fmp ==>
  step_taint inst
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
    (t with <|vs_fmp := p; vs_initial_fmp := j; vs_call_entry_fmp := d|>) tn =
  step_taint inst s t tn
Proof
  strip_tac >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_fmp_fields,
       step_writes_def, written_taint_def, out_taint_def,
       store_taint_def, imm_taint_def]
QED

Theorem memory_checks_fmp_fields[simp]:
  inst.inst_opcode <> DRET ==>
  (inst_mem_below_frontier inst
     (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
   inst_mem_below_frontier inst s) /\
  (inst_dload_in_section inst
     (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
   inst_dload_in_section inst s)
Proof
  simp[inst_mem_below_frontier_def, inst_dload_in_section_def]
QED

Theorem access_ok_fmp_fields[simp]:
  inst.inst_opcode <> DRET ==>
  access_ok lo G fn inst
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
  access_ok lo G fn inst s
Proof
  simp[access_ok_def, in_revert_forward_def]
QED

Theorem taint_ok_fmp_fields[simp]:
  inst.inst_opcode <> DRET ==>
  taint_ok fn tn inst
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
  taint_ok fn tn inst s
Proof
  simp[taint_ok_def, about_to_revert_def, in_revert_forward_def,
       active_inst_def]
QED

Theorem ret_taint_fmp_fields[simp]:
  ret_taint tn inst
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
  ret_taint tn inst s
Proof
  simp[ret_taint_def]
QED

Theorem commuting_result_fmp_fixed:
  (!p i e. f (s with <|vs_fmp := p; vs_initial_fmp := i;
                       vs_call_entry_fmp := e|>) =
     exec_result_map
       (\t. t with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
       (f s)) /\
  (f s = OK t \/ f s = Halt t) ==> t.vs_fmp = s.vs_fmp
Proof
  strip_tac >>
  first_x_assum (qspecl_then
    [`s.vs_fmp`, `s.vs_initial_fmp`, `s.vs_call_entry_fmp`] mp_tac) >>
  simp[exec_result_map_def, venom_state_component_equality]
QED

Theorem ptr_inst_ok_fmp_fields_under_execution:
  ~ctx_has_dalloca ctx /\ inst.inst_opcode <> DRET /\
  (!p i e s. step_inst fuel ctx inst
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
    exec_result_map
      (\t. t with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
      (step_inst fuel ctx inst s)) ==>
  (ptr_inst_ok D lo fuel ctx fn G tn inst
     (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) <=>
   ptr_inst_ok D lo fuel ctx fn G tn inst s)
Proof
  strip_tac >> simp[ptr_inst_ok_def, allocas_from_def] >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
  `!t. step_inst fuel ctx inst s = Halt t ==> t.vs_fmp = s.vs_fmp` by
    (rpt strip_tac >> irule commuting_result_fmp_fixed >>
     qexists_tac `step_inst fuel ctx inst` >> simp[]) >>
  Cases_on `step_inst fuel ctx inst s` >>
  gvs[exec_result_map_def, SRULE [] step_taint_fmp_fields]
QED


(* H is only a statement abbreviation for the supplied execution interface. *)
Theorem ghost_defs_fmp_update_under_execution:
  (!fuel ctx PG G tn inst s.
    (EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
      inst.inst_opcode <> DALLOCA) (fn_insts fn)) ctx.ctx_functions /\
    (!fuel inst s p i e.
      raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA ==>
      raw_fmp_result_rel p i e (step_inst fuel ctx inst s)
        (step_inst fuel ctx inst
          (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
    (!fuel inst s p i e.
      raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA /\
      inst.inst_opcode <> INVOKE ==>
      step_inst fuel ctx inst
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      exec_result_map
        (\t. t with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
        (step_inst fuel ctx inst s)) /\
    (!s insts p i e.
      eval_phis (s with <|vs_fmp := p; vs_initial_fmp := i;
                         vs_call_entry_fmp := e|>) insts =
      exec_result_map
        (\t. t with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
        (eval_phis s insts)) /\
    (!callee args s p i e.
      setup_callee callee args
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      OPTION_MAP
        (\cs. cs with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := p|>)
        (setup_callee callee args s))) /\ raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA ==>
    !p i e. ghost_step fuel ctx PG G tn inst
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      ghost_step fuel ctx PG G tn inst s) /\
  (!fuel ctx fn PG G tn bb s.
    (EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
      inst.inst_opcode <> DALLOCA) (fn_insts fn)) ctx.ctx_functions /\
    (!fuel inst s p i e.
      raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA ==>
      raw_fmp_result_rel p i e (step_inst fuel ctx inst s)
        (step_inst fuel ctx inst
          (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
    (!fuel inst s p i e.
      raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA /\
      inst.inst_opcode <> INVOKE ==>
      step_inst fuel ctx inst
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      exec_result_map
        (\t. t with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
        (step_inst fuel ctx inst s)) /\
    (!s insts p i e.
      eval_phis (s with <|vs_fmp := p; vs_initial_fmp := i;
                         vs_call_entry_fmp := e|>) insts =
      exec_result_map
        (\t. t with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
        (eval_phis s insts)) /\
    (!callee args s p i e.
      setup_callee callee args
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      OPTION_MAP
        (\cs. cs with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := p|>)
        (setup_callee callee args s))) /\
    EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
      (fn_insts fn) /\
    EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
      bb.bb_instructions ==>
    !p i e. ghost_block fuel ctx fn PG G tn bb
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      ghost_block fuel ctx fn PG G tn bb s) /\
  (!fuel ctx fn PG G tn s.
    (EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
      inst.inst_opcode <> DALLOCA) (fn_insts fn)) ctx.ctx_functions /\
    (!fuel inst s p i e.
      raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA ==>
      raw_fmp_result_rel p i e (step_inst fuel ctx inst s)
        (step_inst fuel ctx inst
          (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
    (!fuel inst s p i e.
      raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA /\
      inst.inst_opcode <> INVOKE ==>
      step_inst fuel ctx inst
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      exec_result_map
        (\t. t with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
        (step_inst fuel ctx inst s)) /\
    (!s insts p i e.
      eval_phis (s with <|vs_fmp := p; vs_initial_fmp := i;
                         vs_call_entry_fmp := e|>) insts =
      exec_result_map
        (\t. t with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
        (eval_phis s insts)) /\
    (!callee args s p i e.
      setup_callee callee args
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      OPTION_MAP
        (\cs. cs with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := p|>)
        (setup_callee callee args s))) /\
    EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
      (fn_insts fn) ==>
    !p i e. ghost_blocks fuel ctx fn PG G tn
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      ghost_blocks fuel ctx fn PG G tn s)
Proof
  pure_rewrite_tac [LET_THM] >> BETA_TAC >> ho_match_mp_tac ghost_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
      fs[] >>
      `inst.inst_opcode <> DRET` by gvs[raw_opcode_ok_def] >>
      Cases_on `inst.inst_opcode = INVOKE`
      >- (once_rewrite_tac[ghost_step_def] >> simp[] >>
          Cases_on `decode_invoke inst` >> simp[] >>
          rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
          Cases_on `lookup_function pair0 ctx.ctx_functions` >> simp[] >>
          Cases_on `eval_operands pair1 s` >>
          simp[PURE_REWRITE_RULE [venom_state_fupdcanon] eval_operands_fmp_fields] >>
          rename1 `lookup_function pair0 ctx.ctx_functions = SOME callee` >>
          rename1 `eval_operands pair1 s = SOME args` >>
          Cases_on `setup_callee callee args s` >> simp[] >>
          `EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
             inst.inst_opcode <> DALLOCA) (fn_insts callee)` by
            (drule venomInstTheory.lookup_function_MEM >> strip_tac >>
             qpat_x_assum `EVERY _ ctx.ctx_functions` mp_tac >>
             simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
          first_x_assum drule_all >> simp[]) >>
      `!t. step_inst fuel ctx inst s = OK t ==> t.vs_fmp = s.vs_fmp` by
        (rpt strip_tac >> irule commuting_result_fmp_fixed >>
         qexists_tac `step_inst fuel ctx inst` >> simp[]) >>
      once_rewrite_tac[ghost_step_def] >> simp[] >>
      Cases_on `step_inst fuel ctx inst s` >>
      gvs[exec_result_map_def, SRULE [] step_taint_fmp_fields,
          PURE_REWRITE_RULE [venom_state_fupdcanon] step_prov_fmp_fields])
  >- (rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> fs[] >>
      once_rewrite_tac[ghost_block_def] >> simp[] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
      `raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA` by
        (drule_all EVERY_get_instruction >> simp[]) >>
      `raw_fmp_result_rel p i e (step_inst fuel ctx inst s)
        (step_inst fuel ctx inst
          (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))` by
        (pure_rewrite_tac[venom_state_fupdcanon] >> first_x_assum irule >> simp[]) >>
      Cases_on `step_inst fuel ctx inst s` >> gvs[] >>
      Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
      simp[PURE_REWRITE_RULE [venom_state_fupdcanon] entry_prov_fmp_fields,
           PURE_REWRITE_RULE [venom_state_fupdcanon] entry_taint_vars_fmp_fields])
  >> rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> fs[] >>
  Cases_on `fuel` >> once_rewrite_tac[ghost_blocks_def] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
    bb.bb_instructions` by
      (irule contextPlanEmissionPropsTheory.lookup_block_insts_every >>
       gvs[fn_insts_def] >> goal_assum drule >> simp[]) >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  gvs[exec_result_map_def]
QED

Theorem mem_safe_defs_fmp_update_under_execution:
  (!fuel ctx inst s.
    (EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
      inst.inst_opcode <> DALLOCA) (fn_insts fn)) ctx.ctx_functions /\
    (!fuel inst s p i e.
      raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA ==>
      raw_fmp_result_rel p i e (step_inst fuel ctx inst s)
        (step_inst fuel ctx inst
          (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
    (!fuel bb s p i e.
      EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
        bb.bb_instructions ==>
      raw_fmp_result_rel p i e (exec_block fuel ctx bb s)
        (exec_block fuel ctx bb
          (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
    (!s insts p i e.
      eval_phis (s with <|vs_fmp := p; vs_initial_fmp := i;
                         vs_call_entry_fmp := e|>) insts =
      exec_result_map
        (\t. t with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
        (eval_phis s insts)) /\
    (!callee args s p i e.
      setup_callee callee args
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      OPTION_MAP
        (\cs. cs with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := p|>)
        (setup_callee callee args s))) /\ raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA ==>
    !p i e. mem_safe_step fuel ctx inst
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      mem_safe_step fuel ctx inst s) /\
  (!fuel ctx bb s.
    (EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
      inst.inst_opcode <> DALLOCA) (fn_insts fn)) ctx.ctx_functions /\
    (!fuel inst s p i e.
      raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA ==>
      raw_fmp_result_rel p i e (step_inst fuel ctx inst s)
        (step_inst fuel ctx inst
          (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
    (!fuel bb s p i e.
      EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
        bb.bb_instructions ==>
      raw_fmp_result_rel p i e (exec_block fuel ctx bb s)
        (exec_block fuel ctx bb
          (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
    (!s insts p i e.
      eval_phis (s with <|vs_fmp := p; vs_initial_fmp := i;
                         vs_call_entry_fmp := e|>) insts =
      exec_result_map
        (\t. t with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
        (eval_phis s insts)) /\
    (!callee args s p i e.
      setup_callee callee args
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      OPTION_MAP
        (\cs. cs with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := p|>)
        (setup_callee callee args s))) /\
    EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
      bb.bb_instructions ==>
    !p i e. mem_safe_block fuel ctx bb
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      mem_safe_block fuel ctx bb s) /\
  (!fuel ctx fn s.
    (EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
      inst.inst_opcode <> DALLOCA) (fn_insts fn)) ctx.ctx_functions /\
    (!fuel inst s p i e.
      raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA ==>
      raw_fmp_result_rel p i e (step_inst fuel ctx inst s)
        (step_inst fuel ctx inst
          (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
    (!fuel bb s p i e.
      EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
        bb.bb_instructions ==>
      raw_fmp_result_rel p i e (exec_block fuel ctx bb s)
        (exec_block fuel ctx bb
          (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
    (!s insts p i e.
      eval_phis (s with <|vs_fmp := p; vs_initial_fmp := i;
                         vs_call_entry_fmp := e|>) insts =
      exec_result_map
        (\t. t with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
        (eval_phis s insts)) /\
    (!callee args s p i e.
      setup_callee callee args
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      OPTION_MAP
        (\cs. cs with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := p|>)
        (setup_callee callee args s))) /\
    EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
      (fn_insts fn) ==>
    !p i e. mem_safe_blocks fuel ctx fn
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      mem_safe_blocks fuel ctx fn s)
Proof
  pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  ho_match_mp_tac mem_safe_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
      fs[] >> `inst.inst_opcode <> DRET` by gvs[raw_opcode_ok_def] >>
      `~ctx_has_dalloca ctx` by
        (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
      simp[mem_safe_step_no_dalloca,
           PURE_REWRITE_RULE [venom_state_fupdcanon] memory_checks_fmp_fields] >>
      Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
      Cases_on `decode_invoke inst` >> simp[] >>
      rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
      Cases_on `lookup_function pair0 ctx.ctx_functions` >> simp[] >>
      Cases_on `eval_operands pair1 s` >>
      simp[PURE_REWRITE_RULE [venom_state_fupdcanon] eval_operands_fmp_fields] >>
      rename1 `lookup_function pair0 ctx.ctx_functions = SOME callee` >>
      rename1 `eval_operands pair1 s = SOME args` >>
      Cases_on `setup_callee callee args s` >> simp[] >>
      `EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
         inst.inst_opcode <> DALLOCA) (fn_insts callee)` by
        (drule venomInstTheory.lookup_function_MEM >> strip_tac >>
         qpat_x_assum `EVERY _ ctx.ctx_functions` mp_tac >>
         simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
      first_x_assum drule_all >> simp[])
  >- (rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> fs[] >>
      once_rewrite_tac[mem_safe_block_def] >> simp[] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
      `raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA` by
        (drule_all EVERY_get_instruction >> simp[]) >>
      `raw_fmp_result_rel p i e (step_inst fuel ctx inst s)
        (step_inst fuel ctx inst
          (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))` by simp[] >>
      Cases_on `step_inst fuel ctx inst s` >> gvs[] >>
      Cases_on `is_terminator inst.inst_opcode` >> gvs[])

  >> rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> fs[] >>
  Cases_on `fuel` >> once_rewrite_tac[mem_safe_blocks_def] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
    bb.bb_instructions` by
      (irule contextPlanEmissionPropsTheory.lookup_block_insts_every >>
       gvs[fn_insts_def] >> goal_assum drule >> simp[]) >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[exec_result_map_def] >>
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  `raw_fmp_result_rel p i e
    (exec_block n ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    (exec_block n ctx bb (sp with <|vs_inst_idx := phi_prefix_length bb.bb_instructions;
       vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))` by
      (qpat_x_assum `!fuel bb s p i e. _ ==> raw_fmp_result_rel _ _ _ _ _`
         (qspecl_then [`n`, `bb`,
           `sp with vs_inst_idx := phi_prefix_length bb.bb_instructions`] mp_tac) >>
       simp[] >> disch_then (qspecl_then [`p`, `i`, `e`] mp_tac) >> simp[]) >>
  Cases_on `exec_block n ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> gvs[] >>
  Cases_on `v.vs_halted` >> gvs[]
QED

Theorem ptr_safe_blocks_fmp_update_under_execution:
  (!D lo fuel ctx fn PG G tn inst s.
    (EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
      inst.inst_opcode <> DALLOCA) (fn_insts fn)) ctx.ctx_functions /\
    (!fuel inst s p i e.
      raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA ==>
      raw_fmp_result_rel p i e (step_inst fuel ctx inst s)
        (step_inst fuel ctx inst
          (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
    (!fuel inst s p i e.
      raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA /\
      inst.inst_opcode <> INVOKE ==>
      step_inst fuel ctx inst
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      exec_result_map
        (\t. t with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
        (step_inst fuel ctx inst s)) /\
    (!s insts p i e.
      eval_phis (s with <|vs_fmp := p; vs_initial_fmp := i;
                         vs_call_entry_fmp := e|>) insts =
      exec_result_map
        (\t. t with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
        (eval_phis s insts)) /\
    (!callee args s p i e.
      setup_callee callee args
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      OPTION_MAP
        (\cs. cs with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := p|>)
        (setup_callee callee args s))) /\ raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA ==>
    !p i e. ptr_safe_step D lo fuel ctx fn PG G tn inst
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      ptr_safe_step D lo fuel ctx fn PG G tn inst s) /\
  (!D lo fuel ctx fn PG G tn bb s.
    (EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
      inst.inst_opcode <> DALLOCA) (fn_insts fn)) ctx.ctx_functions /\
    (!fuel inst s p i e.
      raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA ==>
      raw_fmp_result_rel p i e (step_inst fuel ctx inst s)
        (step_inst fuel ctx inst
          (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
    (!fuel inst s p i e.
      raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA /\
      inst.inst_opcode <> INVOKE ==>
      step_inst fuel ctx inst
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      exec_result_map
        (\t. t with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
        (step_inst fuel ctx inst s)) /\
    (!s insts p i e.
      eval_phis (s with <|vs_fmp := p; vs_initial_fmp := i;
                         vs_call_entry_fmp := e|>) insts =
      exec_result_map
        (\t. t with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
        (eval_phis s insts)) /\
    (!callee args s p i e.
      setup_callee callee args
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      OPTION_MAP
        (\cs. cs with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := p|>)
        (setup_callee callee args s))) /\
    EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
      (fn_insts fn) /\
    EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
      bb.bb_instructions ==>
    !p i e. ptr_safe_block D lo fuel ctx fn PG G tn bb
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      ptr_safe_block D lo fuel ctx fn PG G tn bb s) /\
  (!D lo fuel ctx fn PG G tn s.
    (EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
      inst.inst_opcode <> DALLOCA) (fn_insts fn)) ctx.ctx_functions /\
    (!fuel inst s p i e.
      raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA ==>
      raw_fmp_result_rel p i e (step_inst fuel ctx inst s)
        (step_inst fuel ctx inst
          (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
    (!fuel inst s p i e.
      raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA /\
      inst.inst_opcode <> INVOKE ==>
      step_inst fuel ctx inst
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      exec_result_map
        (\t. t with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
        (step_inst fuel ctx inst s)) /\
    (!s insts p i e.
      eval_phis (s with <|vs_fmp := p; vs_initial_fmp := i;
                         vs_call_entry_fmp := e|>) insts =
      exec_result_map
        (\t. t with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
        (eval_phis s insts)) /\
    (!callee args s p i e.
      setup_callee callee args
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      OPTION_MAP
        (\cs. cs with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := p|>)
        (setup_callee callee args s))) /\
    EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
      (fn_insts fn) ==>
    !p i e. ptr_safe_blocks D lo fuel ctx fn PG G tn
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      ptr_safe_blocks D lo fuel ctx fn PG G tn s)
Proof
  pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  ho_match_mp_tac ptr_safe_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
      fs[] >> `inst.inst_opcode <> DRET` by gvs[raw_opcode_ok_def] >>
      `~ctx_has_dalloca ctx` by
        (simp[ctx_has_dalloca_def, EXISTS_MEM] >> rpt strip_tac >>
         qpat_x_assum `EVERY _ ctx.ctx_functions` mp_tac >>
         simp[EVERY_MEM] >> metis_tac[]) >>
      Cases_on `inst.inst_opcode = INVOKE`
      >- (once_rewrite_tac[ptr_safe_step_def] >>
          simp[ptr_inst_ok_def, allocas_from_def,
            PURE_REWRITE_RULE [venom_state_fupdcanon] access_ok_fmp_fields,
            PURE_REWRITE_RULE [venom_state_fupdcanon] taint_ok_fmp_fields] >>
          Cases_on `decode_invoke inst` >> simp[] >>
          rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
          Cases_on `lookup_function pair0 ctx.ctx_functions` >> simp[] >>
          Cases_on `eval_operands pair1 s` >>
          simp[PURE_REWRITE_RULE [venom_state_fupdcanon] eval_operands_fmp_fields] >>
          rename1 `lookup_function pair0 ctx.ctx_functions = SOME callee` >>
          rename1 `eval_operands pair1 s = SOME args` >>
          Cases_on `setup_callee callee args s` >> simp[] >>
          `EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
             inst.inst_opcode <> DALLOCA) (fn_insts callee)` by
            (drule venomInstTheory.lookup_function_MEM >> strip_tac >>
             qpat_x_assum `EVERY _ ctx.ctx_functions` mp_tac >>
             simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
          first_x_assum drule_all >> simp[]) >>
      once_rewrite_tac[ptr_safe_step_def] >> simp[] >>
      irule (PURE_REWRITE_RULE [venom_state_fupdcanon]
        ptr_inst_ok_fmp_fields_under_execution) >> simp[])
  >- (rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> fs[] >>
      once_rewrite_tac[ptr_safe_block_def] >> simp[] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
      `raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA` by
        (drule_all EVERY_get_instruction >> simp[]) >>
      `ghost_step fuel ctx PG G tn inst
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
        ghost_step fuel ctx PG G tn inst s` by
        (pure_rewrite_tac[venom_state_fupdcanon] >>
         irule (cj 1 (SRULE [LET_THM] ghost_defs_fmp_update_under_execution)) >> simp[]) >>
      `raw_fmp_result_rel p i e (step_inst fuel ctx inst s)
        (step_inst fuel ctx inst
          (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))` by simp[] >>
      Cases_on `step_inst fuel ctx inst s` >> gvs[] >>
      Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
      simp[PURE_REWRITE_RULE [venom_state_fupdcanon] entry_prov_fmp_fields,
           PURE_REWRITE_RULE [venom_state_fupdcanon] entry_taint_vars_fmp_fields])
  >> rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> fs[] >>
  Cases_on `fuel` >> once_rewrite_tac[ptr_safe_blocks_def] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
    bb.bb_instructions` by
      (irule contextPlanEmissionPropsTheory.lookup_block_insts_every >>
       gvs[fn_insts_def] >> goal_assum drule >> simp[]) >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[exec_result_map_def]
QED
