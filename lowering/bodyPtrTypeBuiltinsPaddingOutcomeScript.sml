(* Outcome-exclusion probes for the padding witness. *)
Theory bodyPtrTypeBuiltinsPaddingOutcome
Ancestors
  bodyPtrTypeBuiltinsPaddingFrame bodyPtrTypeBuiltinsPaddingTarget
  bodyPtrTypeBuiltinsPaddingWitness
  gasExemptCert vyperState vyperInterpreter words fragGasPathPtr
  venomExecSemantics venomExecProofs ptrSafeRun ptrDiscipline venomState
  venomInst finite_map list pred_set decoderGhostFramePtr codegenRel

Theorem padding_source_returns:
  bind (eval_expr padding_actual_context padding_expr)
    (read_result padding_actual_context) (padding_source with gas_obs := gs) =
  (INL (IntV 0), padding_source with gas_obs := gs)
Proof
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >> simp[] >> EVAL_TAC
QED

Theorem padding_no_exempt_cert:
  ~gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr padding_actual_context padding_expr)
                  (read_result padding_actual_context)) (return ()))
    (padding_source,s) marks (err,ee) (leaf,final_s)
Proof
  strip_tac >> drule gas_exempt_cert_execution >>
  simp[ignore_bind_def, bind_def, padding_source_returns, return_def]
QED

Theorem padding_straight_edge_inversion:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  step_inst_base i s = OK u /\
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' r ==>
  r = OK (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  G' = step_prov PG G i u /\ tn' = step_taint i s u tn
Proof
  strip_tac >>
  fs[gas_path_ptr_edge_def] >> gvs[step_inst_non_invoke] >>
  gvs[Once ghost_step_def, step_inst_non_invoke, fragExecTheory.exit_result_def]
QED

Theorem padding_path_first_edge:
  gas_path_ptr D lo ctx fn PG G tn s n G' tn' r ==>
  (r = OK s /\ G' = G /\ tn' = tn) \/
  (?k H tt u m.
    gas_path_ptr_edge D lo ctx fn PG G tn s k H tt (OK u) /\
    gas_path_ptr D lo ctx fn PG H tt u m G' tn' r) \/
  (?k. gas_path_ptr_edge D lo ctx fn PG G tn s k G' tn' r /\
       exit_result r)
Proof
  simp[Once gas_path_ptr_cases] >> metis_tac[]
QED

Theorem padding_path_blocked:
  (!n H tt r. ~gas_path_ptr_edge D lo ctx fn PG G tn s n H tt r) ==>
  !n G' tn' r. gas_path_ptr D lo ctx fn PG G tn s n G' tn' r ==>
    r = OK s
Proof
  rpt strip_tac >> drule padding_path_first_edge >> metis_tac[]
QED

Theorem padding_path_one_prefix:
  (!n H tt r. gas_path_ptr_edge D lo ctx fn PG G tn s n H tt r ==>
      r = OK u /\ H = Gu /\ tt = tu) /\
  (!n H tt r. gas_path_ptr D lo ctx fn PG Gu tu u n H tt r ==> P r) ==>
  !n H tt r. gas_path_ptr D lo ctx fn PG G tn s n H tt r ==>
    r = OK s \/ P r
Proof
  rpt strip_tac >> drule padding_path_first_edge >>
  strip_tac >> gvs[] >>
  first_x_assum (drule_then strip_assume_tac) >>
  gvs[fragExecTheory.exit_result_def] >> metis_tac[]
QED

(* Bounded concrete certificate abbreviation, not an alternative execution
   relation. The fallback branches are unused by the five checked steps. *)
Definition padding_prefix_def:
  (padding_prefix 0 =
    (padding_actual_machine, entry_taint with t_mem := {63})) /\
  (padding_prefix (SUC k) =
    if k < 5 then
      case padding_prefix k of (s,tn) =>
      case EL (k+3) (fn_insts padding_runtime_function) of i =>
      case step_inst_base i s of
        OK u => (u with vs_inst_idx := SUC s.vs_inst_idx,
                 step_taint i s u tn)
      | _ => (s,tn)
    else padding_prefix k)
End

Definition padding_prefix_machine_def:
  padding_prefix_machine k = FST (padding_prefix k)
End

Definition padding_prefix_taint_def:
  padding_prefix_taint k = SND (padding_prefix k)
End

Theorem padding_prefix_small:
  (!k. k < 5 ==>
    padding_prefix (k+1) =
      case padding_prefix k of (s,tn) =>
      case EL (k+3) (fn_insts padding_runtime_function) of i =>
      case step_inst_base i s of
        OK u => (u with vs_inst_idx := SUC s.vs_inst_idx,
                 step_taint i s u tn)
      | _ => (s,tn))
Proof
  gen_tac >> strip_tac >>
  pure_rewrite_tac[GSYM arithmeticTheory.ADD1, padding_prefix_def] >> simp[]
QED


Theorem padding_prefix_instructions:
  EL 3 (fn_insts padding_runtime_function) =
    <| inst_id := 11; inst_opcode := MLOAD;
       inst_operands := [Var "%5"]; inst_outputs := ["%8"] |> /\
  EL 4 (fn_insts padding_runtime_function) =
    <| inst_id := 12; inst_opcode := ADD;
       inst_operands := [Var "%5";Lit 32w]; inst_outputs := ["%9"] |> /\
  EL 5 (fn_insts padding_runtime_function) =
    <| inst_id := 13; inst_opcode := MLOAD;
       inst_operands := [Var "%9"]; inst_outputs := ["%10"] |> /\
  EL 6 (fn_insts padding_runtime_function) =
    <| inst_id := 14; inst_opcode := ISZERO;
       inst_operands := [Var "%8"]; inst_outputs := ["%11"] |> /\
  EL 7 (fn_insts padding_runtime_function) =
    <| inst_id := 15; inst_opcode := ISZERO;
       inst_operands := [Var "%11"]; inst_outputs := ["%12"] |>
Proof
  rewrite_tac[padding_runtime_function_equation] >> EVAL_TAC
QED

Theorem padding_actual_machine_projections:
  padding_actual_machine.vs_vars =
    FEMPTY |+ ("%5",0w) |+ ("%6",0w) |+ ("%7",64w) /\
  padding_actual_machine.vs_memory =
    REPLICATE 31 (0w:word8) ++ [1w;0w] ++ REPLICATE 31 0w /\
  padding_actual_machine.vs_current_bb = padding_runtime_label /\
  padding_actual_machine.vs_inst_idx = 3
Proof
  simp[padding_actual_machine_def, padding_machine_def]
QED

Theorem padding_prefix_zero:
  padding_prefix 0 = (padding_actual_machine, entry_taint with t_mem := {63})
Proof
  simp[padding_prefix_def]
QED

Theorem padding_first_load:
  step_inst_base (EL 3 (fn_insts padding_runtime_function))
    padding_actual_machine = OK (update_var "%8" 1w padding_actual_machine)
Proof
  rewrite_tac[padding_prefix_instructions] >>
  simp[Once step_inst_base_def, exec_read1_def, eval_operand_def,
       lookup_var_def, padding_actual_machine_projections] >> EVAL_TAC
QED

Theorem padding_prefix_success:
  !k u. k < 5 /\
  step_inst_base (EL (k+3) (fn_insts padding_runtime_function))
    (padding_prefix_machine k) = OK u ==>
  padding_prefix_machine (k+1) =
    (u with vs_inst_idx := SUC (padding_prefix_machine k).vs_inst_idx) /\
  padding_prefix_taint (k+1) =
    step_taint (EL (k+3) (fn_insts padding_runtime_function))
      (padding_prefix_machine k) u (padding_prefix_taint k)
Proof
  rpt strip_tac >> drule padding_prefix_small >>
  Cases_on `padding_prefix k` >>
  gvs[padding_prefix_machine_def, padding_prefix_taint_def]
QED

Theorem padding_prefix_machine_zero:
  padding_prefix_machine 0 = padding_actual_machine
Proof
  simp[padding_prefix_machine_def, padding_prefix_zero]
QED

Theorem padding_prefix_one:
  padding_prefix_machine 1 =
    (update_var "%8" 1w padding_actual_machine with vs_inst_idx := 4) /\
  padding_prefix_taint 1 =
    step_taint (EL 3 (fn_insts padding_runtime_function))
      padding_actual_machine (update_var "%8" 1w padding_actual_machine)
      (padding_prefix_taint 0)
Proof
  qspec_then `0` mp_tac padding_prefix_success >>
  simp[padding_prefix_machine_zero, padding_first_load,
       padding_actual_machine_projections]
QED

Theorem padding_second_add:
  step_inst_base (EL 4 (fn_insts padding_runtime_function))
    (padding_prefix_machine 1) =
    OK (update_var "%9" 32w (padding_prefix_machine 1))
Proof
  rewrite_tac[padding_prefix_instructions] >>
  simp[Once step_inst_base_def, exec_pure2_def, eval_operand_def,
       lookup_var_def, padding_prefix_one, update_var_def,
       padding_actual_machine_projections, FLOOKUP_UPDATE]
QED

Theorem padding_prefix_two:
  padding_prefix_machine 2 =
    (update_var "%9" 32w (padding_prefix_machine 1) with vs_inst_idx := 5) /\
  padding_prefix_taint 2 =
    step_taint (EL 4 (fn_insts padding_runtime_function))
      (padding_prefix_machine 1) (update_var "%9" 32w (padding_prefix_machine 1))
      (padding_prefix_taint 1)
Proof
  qspecl_then [`1`,`update_var "%9" 32w (padding_prefix_machine 1)`]
    mp_tac padding_prefix_success >>
  simp[padding_second_add] >> simp[padding_prefix_one, update_var_def]
QED

Theorem padding_third_load:
  step_inst_base (EL 5 (fn_insts padding_runtime_function))
    (padding_prefix_machine 2) =
    OK (update_var "%10" 0w (padding_prefix_machine 2))
Proof
  rewrite_tac[padding_prefix_instructions] >>
  rewrite_tac[cj 1 padding_prefix_two, cj 1 padding_prefix_one] >>
  simp[update_var_def, padding_actual_machine_projections] >>
  simp[Once step_inst_base_def, exec_read1_def, eval_operand_def,
       lookup_var_def, FLOOKUP_UPDATE] >>
  simp[mload_def, padding_actual_machine_projections] >> EVAL_TAC
QED

Theorem padding_prefix_three:
  padding_prefix_machine 3 =
    (update_var "%10" 0w (padding_prefix_machine 2) with vs_inst_idx := 6) /\
  padding_prefix_taint 3 =
    step_taint (EL 5 (fn_insts padding_runtime_function))
      (padding_prefix_machine 2) (update_var "%10" 0w (padding_prefix_machine 2))
      (padding_prefix_taint 2)
Proof
  qspecl_then [`2`,`update_var "%10" 0w (padding_prefix_machine 2)`]
    mp_tac padding_prefix_success >>
  simp[padding_third_load] >> simp[padding_prefix_two, update_var_def]
QED

Theorem padding_fourth_iszero:
  step_inst_base (EL 6 (fn_insts padding_runtime_function))
    (padding_prefix_machine 3) =
    OK (update_var "%11" 0w (padding_prefix_machine 3))
Proof
  rewrite_tac[padding_prefix_instructions, cj 1 padding_prefix_three,
              cj 1 padding_prefix_two, cj 1 padding_prefix_one] >>
  simp[update_var_def, padding_actual_machine_projections] >>
  simp[Once step_inst_base_def, exec_pure1_def, eval_operand_def,
       lookup_var_def, FLOOKUP_UPDATE, update_var_def, bool_to_word_def]
QED

Theorem padding_prefix_four:
  padding_prefix_machine 4 =
    (update_var "%11" 0w (padding_prefix_machine 3) with vs_inst_idx := 7) /\
  padding_prefix_taint 4 =
    step_taint (EL 6 (fn_insts padding_runtime_function))
      (padding_prefix_machine 3) (update_var "%11" 0w (padding_prefix_machine 3))
      (padding_prefix_taint 3)
Proof
  qspecl_then [`3`,`update_var "%11" 0w (padding_prefix_machine 3)`]
    mp_tac padding_prefix_success >>
  simp[padding_fourth_iszero] >> simp[padding_prefix_three, update_var_def]
QED

Theorem padding_fifth_iszero:
  step_inst_base (EL 7 (fn_insts padding_runtime_function))
    (padding_prefix_machine 4) =
    OK (update_var "%12" 1w (padding_prefix_machine 4))
Proof
  rewrite_tac[padding_prefix_instructions, cj 1 padding_prefix_four] >>
  simp[update_var_def] >>
  simp[Once step_inst_base_def, exec_pure1_def, eval_operand_def,
       lookup_var_def, FLOOKUP_UPDATE, update_var_def, bool_to_word_def]
QED

Theorem padding_prefix_five:
  padding_prefix_machine 5 =
    (update_var "%12" 1w (padding_prefix_machine 4) with vs_inst_idx := 8) /\
  padding_prefix_taint 5 =
    step_taint (EL 7 (fn_insts padding_runtime_function))
      (padding_prefix_machine 4) (update_var "%12" 1w (padding_prefix_machine 4))
      (padding_prefix_taint 4)
Proof
  qspecl_then [`4`,`update_var "%12" 1w (padding_prefix_machine 4)`]
    mp_tac padding_prefix_success >>
  simp[padding_fifth_iszero] >> simp[padding_prefix_four, update_var_def]
QED

Theorem padding_prefix_positions:
  !k. k <= 5 ==>
    (padding_prefix_machine k).vs_current_bb = padding_runtime_label /\
    (padding_prefix_machine k).vs_inst_idx = 3+k
Proof
  rpt strip_tac >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5` by decide_tac >>
  gvs[cj 1 padding_prefix_five, cj 1 padding_prefix_four,
      cj 1 padding_prefix_three, cj 1 padding_prefix_two,
      cj 1 padding_prefix_one, padding_prefix_machine_zero,
      update_var_def, padding_actual_machine_projections]
QED

Theorem padding_prefix_mem_taint:
  (padding_prefix_taint 2).t_mem = {63}
Proof
  rewrite_tac[cj 2 padding_prefix_two, cj 2 padding_prefix_one,
              padding_prefix_taint_def, padding_prefix_zero,
              padding_prefix_instructions] >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def,
       new_site_bytes_def, update_var_def, range_bytes_def,
       EXTENSION, FLOOKUP_DEF, SF CONJ_ss]
QED

Theorem padding_prefix_three_taint:
  op_taint (padding_prefix_taint 3) (Var "%10") = {31}
Proof
  rewrite_tac[cj 2 padding_prefix_three, padding_prefix_instructions] >>
  simp[step_taint_def, op_taint_def, set_var_taint_def, FLOOKUP_UPDATE,
       out_taint_def, eval_operand_def, lookup_var_def,
       cj 1 padding_prefix_two, update_var_def, FLOOKUP_UPDATE,
       padding_prefix_mem_taint, mem_word_taint_def, EXTENSION]
QED

Theorem padding_prefix_five_taint:
  op_taint (padding_prefix_taint 5) (Var "%10") <> {}
Proof
  rewrite_tac[cj 2 padding_prefix_five, cj 2 padding_prefix_four] >>
  simp[step_taint_other_output, padding_prefix_instructions,
       padding_prefix_three_taint]
QED

Theorem padding_prefix_fetch:
  !k. k < 5 ==>
    lookup_block (padding_prefix_machine k).vs_current_bb
      padding_runtime_function.fn_blocks =
      SOME (HD padding_runtime_function.fn_blocks) /\
    get_instruction (HD padding_runtime_function.fn_blocks)
      (padding_prefix_machine k).vs_inst_idx =
      SOME (EL (k+3) (fn_insts padding_runtime_function)) /\
    (EL (k+3) (fn_insts padding_runtime_function)).inst_opcode <> INVOKE /\
    ~is_terminator (EL (k+3) (fn_insts padding_runtime_function)).inst_opcode
Proof
  rpt strip_tac >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4` by decide_tac >>
  gvs[] >> simp[padding_prefix_positions, padding_runtime_function_equation,
    mk_raw_function_def, lookup_block_def, FIND_def, get_instruction_def,
    INDEX_FIND_def, fn_insts_def, fn_insts_blocks_def, is_terminator_def] >>
  gvs[padding_prefix_instructions, is_terminator_def]
QED

Theorem padding_prefix_steps_ok:
  !k. k < 5 ==>
    ?u. step_inst_base (EL (k+3) (fn_insts padding_runtime_function))
          (padding_prefix_machine k) = OK u
Proof
  rpt strip_tac >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4` by decide_tac >>
  gvs[padding_prefix_machine_zero] >>
  metis_tac[padding_first_load, padding_second_add, padding_third_load,
            padding_fourth_iszero, padding_fifth_iszero]
QED

Theorem padding_prefix_forced_edge:
  !k G n G' tn' r.
    k < 5 /\
    gas_path_ptr_edge D lo ctx padding_runtime_function PG G
      (padding_prefix_taint k) (padding_prefix_machine k) n G' tn' r ==>
    r = OK (padding_prefix_machine (k+1)) /\
    tn' = padding_prefix_taint (k+1)
Proof
  rpt strip_tac >>
  drule padding_prefix_fetch >> strip_tac >>
  drule padding_prefix_steps_ok >> strip_tac >>
  drule_all padding_straight_edge_inversion >> strip_tac >>
  drule_all padding_prefix_success >> strip_tac >> gvs[]
QED

Theorem padding_prefix_last_blocked:
  ~gas_path_ptr_edge D lo ctx padding_runtime_function PG G
    (padding_prefix_taint 5) (padding_prefix_machine 5) n G' tn' r
Proof
  irule padding_actual_mul_edge_forbidden >>
  simp[padding_prefix_positions, padding_prefix_five_taint]
QED

Theorem padding_prefix_paths:
  !d k G n G' tn' r.
    k+d = 5 /\
    gas_path_ptr D lo ctx padding_runtime_function PG G
      (padding_prefix_taint k) (padding_prefix_machine k) n G' tn' r ==>
    ?j. k <= j /\ j <= 5 /\ r = OK (padding_prefix_machine j)
Proof
  Induct_on `d`
  >- (rpt strip_tac >> `k = 5` by decide_tac >> gvs[] >>
      drule padding_path_first_edge >> strip_tac
      >- (qexists_tac `5` >> gvs[]) >>
      metis_tac[padding_prefix_last_blocked]) >>
  rpt strip_tac >> `k < 5` by decide_tac >>
  drule padding_path_first_edge >> strip_tac
  >- (qexists_tac `k` >> gvs[] >> decide_tac)
  >- (drule_all padding_prefix_forced_edge >> strip_tac >> gvs[] >>
      `k+1+d = 5` by decide_tac >>
      first_x_assum (qspec_then `k+1` mp_tac) >>
      simp[] >> disch_then drule >> strip_tac >>
      qexists_tac `j` >> simp[] >> decide_tac) >>
  drule_all padding_prefix_forced_edge >> strip_tac >>
  gvs[fragExecTheory.exit_result_def]
QED

Theorem padding_actual_paths_stop_early:
  gas_path_ptr D lo ctx padding_runtime_function PG G
    (entry_taint with t_mem := {63}) padding_actual_machine n G' tn' r ==>
  ?j. j <= 5 /\ r = OK (padding_prefix_machine j)
Proof
  strip_tac >>
  qspecl_then [`5`,`0`] mp_tac padding_prefix_paths >>
  simp[padding_prefix_machine_zero, padding_prefix_taint_def, padding_prefix_zero] >>
  disch_then drule >> simp[]
QED

Theorem padding_actual_no_pointer_outcome:
  (!res ee H tt t. Q res ee H tt t ==> t.vs_inst_idx = 12) ==>
  ~gas_outcome_ptr D tops (ctx,padding_runtime_function) PG
    (bind (eval_expr padding_actual_context padding_expr)
          (read_result padding_actual_context))
    (padding_source, padding_actual_machine, G, entry_taint with t_mem := {63}) Q R
Proof
  rpt strip_tac >>
  fs[gas_outcome_ptr_def, padding_no_exempt_cert, gas_summary_ptr_at_def] >>
  drule padding_actual_paths_stop_early >> strip_tac >>
  gvs[fragExecTheory.exit_result_def] >>
  first_x_assum drule >> strip_tac >>
  drule padding_prefix_positions >> simp[] >> decide_tac
QED
