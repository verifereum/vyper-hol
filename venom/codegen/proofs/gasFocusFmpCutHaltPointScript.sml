(* Kept halting instructions at a restored FMP cursor. *)
Theory gasFocusFmpCutHaltPoint
Ancestors
  fmpStageControl fmpStagePointRanges fmpStageOpBase fmpStageRel
  concretizeLayoutCutSafe o1LowerDloadHaltResult o1LowerDloadRangeTransport
  o1LowerDloadShared lowerDloadOracleCallAssembly dftGasFromListLookup
  frameViewFacts frameViewScalar opcodeClass contextCodegenRel o1PassContract ptrStaticDiscipline
  ptrDiscipline pointerConfinedDefs memLocDefs memSafeRun
  venomWf venomExecProofs venomExecSemantics venomState venomInst
  passSimulationDefs words finite_map pred_set list

val halt_ops = ``[STOP; RETURN; REVERT; SINK; SELFDESTRUCT; INVALID]``;

Theorem cut_halt_fetch[local]:
  wf_function fn /\ active_inst fn inst s /\ MEM inst.inst_opcode ^halt_ops /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s cut u ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' ==>
  active_inst fn' inst u
Proof
  strip_tac >> gvs[fmp_stage_rel_def, fmp_frame_rel_def, active_inst_def] >>
  `lookup_block u.vs_current_bb fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  drule fmp_stage_kept_inst >> disch_then drule >> disch_then drule >>
  simp[pre_fmp_opcode_def] >>
  disch_then (qx_choose_then `bb'` strip_assume_tac) >>
  qexists `bb'` >> simp[] >> metis_tac[lookup_block_MEM, lookup_block_label]
QED

Theorem cut_halt_operand[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ opaque_use_ok fn /\
  active_inst fn inst s /\ MEM inst.inst_opcode ^halt_ops /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s cut u ts /\
  MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
  ?y. eval_operand op u = SOME y /\
      fmp_value_rel sm (op_prov G op) (op_taint tn op) x y
Proof
  strip_tac >> irule fmp_stage_operand_point >> simp[] >>
  goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `active_inst _ _ _`)) >>
  `inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> PHI /\
   inst.inst_opcode <> RET /\ inst.inst_opcode <> RETFMP /\ inst.inst_opcode <> DRET` by gvs[MEM] >>
  simp[] >> metis_tac[ordinary_operand_not_retpc, ld_active_inst_member]
QED

Theorem cut_halt_scalar_prov[local]:
  ptr_use_static_ok P pv inst /\ FDOM G SUBSET pv /\
  ((inst.inst_opcode = SELFDESTRUCT /\ MEM op inst.inst_operands) \/
   (inst.inst_opcode = RETURN /\ inst.inst_operands = [addr;op])) ==>
  op_prov G op = NONE
Proof
  strip_tac >> Cases_on `op` >> simp[op_prov_def] >>
  rename1 `FLOOKUP G v = NONE` >> Cases_on `FLOOKUP G v` >> simp[] >>
  `v IN pv` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  qpat_x_assum `ptr_use_static_ok _ _ _`
    (qspec_then `v` mp_tac o CONJUNCT2 o REWRITE_RULE [ptr_use_static_ok_def]) >>
  gvs[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def,
      Excl "FILTER"] >>
  simp[FILTER] >> rpt IF_CASES_TAC >> gvs[]
QED

Theorem cut_halt_scalar[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ opaque_use_ok fn /\ active_inst fn inst s /\
  ptr_use_static_ok P (fn_pv P fn) inst /\ FDOM G SUBSET fn_pv P fn /\ taint_ok fn tn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s cut u ts /\
  ((inst.inst_opcode = SELFDESTRUCT /\ MEM op inst.inst_operands) \/
   (inst.inst_opcode = RETURN /\ inst.inst_operands = [addr;op])) /\
  eval_operand op s = SOME x ==> eval_operand op u = SOME x
Proof
  strip_tac >>
  `op_prov G op = NONE` by (irule cut_halt_scalar_prov >> metis_tac[]) >>
  `MEM op inst.inst_operands /\ MEM inst.inst_opcode ^halt_ops` by simp[] >>
  `op_taint tn op = {}` by (gvs[taint_ok_def] >> metis_tac[]) >>
  drule_all cut_halt_operand >> strip_tac >> gvs[] >> metis_tac[fmp_mem_value_clean]
QED

Theorem cut_halt_stop_sink[local]:
  frame_reachable vs C stk PG G tn fn inst s /\ gas_cut n vs s /\
  taint_within_upto D n C vs /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s cut u ts /\
  (inst.inst_opcode = STOP \/ inst.inst_opcode = SINK) /\
  step_inst k C inst s = Halt s1 ==>
  ?u1. step_inst k C' inst u = Halt u1 /\ dead_result_rel D (Halt s1) (Halt u1)
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  drule_all taint_within_upto_halt >> strip_tac >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s u /\
   s.vs_returndata = u.vs_returndata` by fs[fmp_stage_rel_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >> strip_tac >> gvs[] >>
  (simp[step_inst_non_invoke] >>
   asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
   irule (Q.INST [`A` |-> `s.vs_call_ctx.cc_address`,
                  `tn` |-> `tn`, `R` |-> `{}`] ld_shared_halt_result) >>
   gvs[halt_state_def, set_returndata_def, step_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, ret_taint_def, ld_shared_agree_def] >>
   qexists_tac `tn` >> simp[])
QED

Theorem cut_halt_return_slice[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ opaque_use_ok fn /\ active_inst fn inst s /\
  ptr_use_static_ok P (fn_pv P fn) inst /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn inst s /\ access_ok eom G fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s cut u ts /\
  inst.inst_opcode = RETURN /\ inst.inst_operands = [addr;sz] /\
  eval_operand addr s = SOME p /\ eval_operand sz s = SOME len ==>
  ?q. eval_operand addr u = SOME q /\ eval_operand sz u = SOME len /\
    (!i. i < w2n len /\ i NOTIN ret_taint tn inst s ==>
      EL i (read_memory (w2n p) (w2n len) s) =
      EL i (read_memory (w2n q) (w2n len) u))
Proof
  strip_tac >>
  `eval_operand sz u = SOME len` by (irule cut_halt_scalar >> metis_tac[]) >>
  drule_all wf_active_lookup >> strip_tac >>
  `~in_revert_forward fn s` by
    (simp[in_revert_forward_def] >> rpt strip_tac >> gvs[] >>
     drule_all revert_forward_at_opcode >> simp[]) >>
  `!v. addr = Var v ==> ~retpc_var fn v` by
    (gen_tac >> disch_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> simp[] >> metis_tac[ld_active_inst_member]) >>
  `op_taint tn addr = {}` by (gvs[taint_ok_def] >> metis_tac[]) >>
  `?q. eval_operand addr u = SOME q /\
    (w2n len=0 \/ (w2n p=w2n q /\ w2n p+w2n len<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+w2n len<=z /\ w2n p=b+j /\ w2n q=c+j))` by
    (irule fmp_mem_read_operand_range_point >> simp[] >>
     goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `active_inst _ _ _`)) >>
     simp[mem_read_ops_def, source_memory_read_ranges_def, memory_range_of_operands_def]) >>
  qexists_tac `q` >> simp[] >> rpt strip_tac >>
  irule ld_memory_agree_slice_element >> simp[] >>
  qexistsl_tac [`eom`,`tn.t_mem`,`fmp_ld_sites sm`] >>
  gvs[ret_taint_def] >> fs[fmp_stage_rel_def] >> metis_tac[]
QED

Theorem cut_halt_return[local]:
  frame_reachable vs C stk PG G tn fn inst s /\ gas_cut n vs s /\
  taint_within_upto D n C vs /\
  wf_function fn /\ make_ssa_input_ok fn /\ opaque_use_ok fn /\ active_inst fn inst s /\
  ptr_use_static_ok P (fn_pv P fn) inst /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn inst s /\ access_ok eom G fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s cut u ts /\
  inst.inst_opcode = RETURN /\ step_inst k C inst s = Halt s1 ==>
  ?u1. step_inst k C' inst u = Halt u1 /\ dead_result_rel D (Halt s1) (Halt u1)
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  drule_all taint_within_upto_halt >> strip_tac >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s u` by fs[fmp_stage_rel_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all cut_halt_return_slice >> strip_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_def] >> simp[] >>
  irule ld_shared_halt_result >>
  gvs[halt_state_def, set_returndata_def, step_taint_def, store_taint_def,
      adopt_reset_def, imm_taint_def, ld_read_memory_length,
      GSYM read_memory_def] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`s.vs_call_ctx.cc_address`, `tn`] >> gvs[ld_shared_agree_def]
QED

Theorem cut_halt_selfdestruct[local]:
  frame_reachable vs C stk PG G tn fn inst s /\ gas_cut n vs s /\
  taint_within_upto D n C vs /\
  wf_function fn /\ make_ssa_input_ok fn /\ opaque_use_ok fn /\ active_inst fn inst s /\
  ptr_use_static_ok P (fn_pv P fn) inst /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s cut u ts /\
  inst.inst_opcode = SELFDESTRUCT /\ step_inst k C inst s = Halt s1 ==>
  ?u1. step_inst k C' inst u = Halt u1 /\ dead_result_rel D (Halt s1) (Halt u1)
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  drule_all taint_within_upto_halt >> strip_tac >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s u /\
   s.vs_call_ctx = u.vs_call_ctx` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  `?op x. inst.inst_operands = [op] /\ eval_operand op s = SOME x` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     strip_tac >> metis_tac[]) >>
  rename1 `inst.inst_operands = [addr]` >>
  rename1 `eval_operand addr s = SOME x` >>
  `eval_operand addr u = SOME x` by
    (irule cut_halt_scalar >> metis_tac[MEM]) >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op u` by simp[] >>
  drule_all ld_shared_selfdestruct_step >>
  disch_then (qspec_then `C'` strip_assume_tac) >>
  qexists_tac `t1` >> simp[] >>
  irule ld_shared_halt_result >> gvs[] >>
  conj_tac >- (qexists_tac `{}` >> simp[]) >>
  qexistsl_tac [`s1.vs_call_ctx.cc_address`, `step_taint inst s s1 tn`] >> simp[]
QED

Theorem cut_halt_abort[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ opaque_use_ok fn /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s cut u ts /\
  MEM inst.inst_opcode ^halt_ops /\ step_inst k C inst s = Abort ab s1 ==>
  ?u1. step_inst k C' inst u = Abort ab u1 /\
       dead_result_rel D (Abort ab s1) (Abort ab u1)
Proof
  strip_tac >>
  `s.vs_call_ctx = u.vs_call_ctx` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  `!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
          ?y. eval_operand op u = SOME y` by
    (rpt strip_tac >> drule_all cut_halt_operand >> metis_tac[]) >>
  `IS_SOME (eval_operands inst.inst_operands s) ==>
   IS_SOME (eval_operands inst.inst_operands u)` by
    (simp[eval_operands_IS_SOME_EVERY, EVERY_MEM] >> rpt strip_tac >>
     Cases_on `eval_operand op s` >> fs[] >> metis_tac[optionTheory.IS_SOME_DEF]) >>
  fs[MEM] >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[dead_result_rel_def] >>
  `?a. eval_operand off_op u = SOME a` by metis_tac[MEM] >>
  `?b. eval_operand sz_op u = SOME b` by metis_tac[MEM] >>
  simp[]
QED

(* Location is available even when the source step has not been taken. *)
Theorem focus_fmp_cut_halt_point:
  frame_reachable vs C stk PG G tn fn inst s /\ gas_cut n vs s /\
  taint_within_upto D n C vs /\
  wf_function fn /\ make_ssa_input_ok fn /\ opaque_use_ok fn /\
  active_inst fn inst s /\ ~s.vs_halted /\
  ptr_use_static_ok P (fn_pv P fn) inst /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn inst s /\ access_ok eom G fn inst s /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s cut u ts /\
  MEM inst.inst_opcode ^halt_ops ==>
  active_inst fn' inst u /\
  (step_inst k C inst s = r /\ terminates r ==>
   ?r'. step_inst k C' inst u = r' /\
    case r of
      OK s1 => s1.vs_halted /\
               ?u1. r' = OK u1 /\ u1.vs_halted /\
                    dead_result_rel D (Halt s1) (Halt u1)
    | Halt s1 => dead_result_rel D r r'
    | Abort ab s1 => dead_result_rel D r r'
    | _ => F)
Proof
  strip_tac >> conj_tac >- metis_tac[cut_halt_fetch] >>
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[MEM] >>
  qpat_x_assum `terminates r` mp_tac >>
  Cases_on `r` >> simp[terminates_def] >>
  rename1 `step_inst k C inst s = _`
  >- (`MEM inst.inst_opcode
          [RET; RETFMP; DRET; STOP; RETURN; REVERT; SINK; SELFDESTRUCT; INVALID; PHI]`
        by gvs[MEM] >>
      drule terminal_base_not_ok >> metis_tac[step_inst_non_invoke])
  >- (Cases_on `inst.inst_opcode = STOP \/ inst.inst_opcode = SINK`
      >- (drule_all cut_halt_stop_sink >> strip_tac >> simp[]) >>
      `inst.inst_opcode <> STOP /\ inst.inst_opcode <> SINK` by metis_tac[] >>
      drule step_inst_halt_opcodes >> simp[] >> strip_tac
      >- (drule_all cut_halt_return >> strip_tac >> simp[]) >>
      drule_all cut_halt_selfdestruct >> strip_tac >> simp[])
  >- (drule_all cut_halt_abort >> strip_tac >> simp[]) >>
  qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
  simp[step_inst_non_invoke] >>
  disch_then (mp_tac o MATCH_MP step_inst_base_intret_opcodes) >> gvs[MEM]
QED
