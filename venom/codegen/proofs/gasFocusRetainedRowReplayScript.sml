(* Retained caller rows: closed child packets are consumed only at their
   immutable recorded call, with historical operand/setup agreement. *)
Theory gasFocusRetainedRowReplay
Ancestors dftGasFromListTraceDefs[qualified,ignore_grammar]
  dftGasPrefixProvider dftGasFromListReadings dftGasToListReplay
  dftGasFromListRestore dftRunRel removeUnusedGasProofs gasFocusRetainedRowTail
  gasEvents gasOracleReplay dftIndexedExec venomExecSemantics
  venomInst venomState stateEquiv list rich_list arithmetic finite_map

Theorem focus_retained_invoke_contribution[local]:
  c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME csf /\
  eval_operands ops b0 = SOME args /\
  setup_callee csf args b0 = SOME child_entry /\
  (!op. MEM op c.inst_operands ==> eval_operand op u = eval_operand op b0) /\
  (!callee argv. setup_callee callee argv
      (u with vs_gas_readings := b0.vs_gas_readings) =
      setup_callee callee argv b0) /\
  u.vs_gas_readings = g ++ tail /\
  (?extra. es = gas_events_blocks f C csf
      (child_entry with vs_gas_readings := g ++ tail) ++ extra) /\
  ((?fr. terminates (run_blocks fr C csf
      (child_entry with vs_gas_readings := g ++ tail))) ==>
    gas_events_blocks f C csf
      (child_entry with vs_gas_readings := g ++ tail) = es /\
    residual_result tail (IntRet ir child_out)
      (run_blocks f C csf (child_entry with vs_gas_readings := g ++ tail))) /\
  (!v. (run_blocks f C csf (child_entry with vs_gas_readings := g ++ tail) = OK v \/
        ?r. run_blocks f C csf (child_entry with vs_gas_readings := g ++ tail) = IntRet r v) ==>
    dftGasFromListTraceDefs$trace_gas
      (dftGasFromListTraceDefs$trace_blocks ((d,c.inst_id)::p) d f C csf
        (child_entry with vs_gas_readings := g ++ tail)) = ZIP (keys,g)) ==>
  (?extra. es = gas_events_step f C owner c u ++ extra) /\
  (!v. step_inst f C c u = OK v ==>
    gas_events_step f C owner c u = es /\ v.vs_gas_readings = tail /\
    dftGasFromListTraceDefs$trace_gas
      (dftGasFromListTraceDefs$trace_step p d f C sf c u) = ZIP (keys,g))
Proof
  strip_tac >>
  `!op. MEM op ops ==> eval_operand op u = eval_operand op b0` by
    (gvs[decode_invoke_def, AllCaseEqs()] >> metis_tac[MEM]) >>
  `eval_operands ops u = SOME args` by metis_tac[eval_operands_agree] >>
  `setup_callee csf args u =
      SOME (child_entry with vs_gas_readings := g ++ tail)` by
    (qpat_x_assum `!callee argv. _` (qspecl_then [`csf`, `args`] mp_tac) >>
     simp[gas_setup_callee] >> Cases_on `setup_callee csf args u` >>
     simp[] >> strip_tac >> drule gas_setup_callee_readings >>
     simp[venom_state_component_equality]) >>
  simp[gas_events_step_def, dftGasFromListTraceDefsTheory.trace_step_invoke] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[Once step_inst_def] >>
  Cases_on `run_blocks f C csf (child_entry with vs_gas_readings := g ++ tail)` >>
  simp[AllCaseEqs()] >> rpt strip_tac >>
  `?fr. terminates (run_blocks fr C csf
      (child_entry with vs_gas_readings := g ++ tail))` by
    (qexists_tac `f` >> simp[passSimulationDefsTheory.terminates_def]) >>
  qpat_x_assum `(?fr. _) ==> _` mp_tac >>
  (impl_tac >- metis_tac[]) >>
  strip_tac >> gvs[residual_result_def, lift_result_def] >>
  drule gas_bind_outputs_readings >>
  simp[Once (cj 1 dftGasFromListTraceDefsTheory.trace_defs)]
QED

Theorem focus_retained_row_replay:
  !fuel N d ms xs ess ks k sf p calls j C8 root_tf root_entry C7 be.
  (N:num) <= fuel /\ d <= fuel /\
  LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH xs /\ LENGTH ks = LENGTH xs /\
  LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
  LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\
  k <= LENGTH xs /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_pseudo i.inst_opcode) (TAKE k xs) /\
  (!q. q < k ==>
    ((EL q xs).inst_opcode = GAS ==>
      (?slot. EL q ms = [slot]) /\
      EL q ess = [(sf.fn_name,(EL q xs).inst_id)] /\
      EL q ks = [(p,d,(EL q xs).inst_id)]) /\
    ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
      EL q ms = [] /\ EL q ess = [] /\ EL q ks = [])) /\
  (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==>
    ?h b0 (done_at_call:num list) child_entry ir child_out caller_post
      tf nm ops args csf ctf.
      FLOOKUP calls (p,d,(EL q xs).inst_id) =
        SOME (q,h,b0,done_at_call,child_entry,SOME (ir,child_out,caller_post)) /\
      h < j /\
      EL h (dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry) =
        ((p,d,(EL q xs).inst_id),tf,EL q xs,b0) /\
      decode_invoke (EL q xs) = SOME (nm,ops) /\
      lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops b0 = SOME args /\
      setup_callee ctf args b0 = SOME child_entry /\
      run_blocks (fuel-d) C8 ctf child_entry = IntRet ir child_out /\
      bind_outputs (EL q xs).inst_outputs ir.iret_values
        (adopt_return_fmp ir (merge_callee_state b0 child_out)) = SOME caller_post /\
      lookup_function nm C7.ctx_functions = SOME csf /\
      setup_callee csf args b0 = SOME child_entry /\
      (!kgss tail u.
        LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
        FOLDR (dft_exec_cons (fuel-d) C7) OK (TAKE q xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b0) /\
        (!callee argv. setup_callee callee argv
          (u with vs_gas_readings := b0.vs_gas_readings) = setup_callee callee argv b0)) /\
      (!g tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (EL q ms) g ==>
        (?extra. EL q ess = gas_events_blocks (fuel-d) C7 csf
          (child_entry with vs_gas_readings := g ++ tail) ++ extra) /\
        ((?fr. terminates (run_blocks fr C7 csf
          (child_entry with vs_gas_readings := g ++ tail))) ==>
          terminates (run_blocks (fuel-d) C7 csf
            (child_entry with vs_gas_readings := g ++ tail)) /\
          dft_res_rel (restore_result [] (run_blocks (fuel-d) C7 csf
            (child_entry with vs_gas_readings := g ++ tail)))
            (restore_result [] (IntRet ir child_out)) /\
          gas_events_blocks (fuel-d) C7 csf
            (child_entry with vs_gas_readings := g ++ tail) = EL q ess /\
          residual_result tail (IntRet ir child_out)
            (run_blocks (fuel-d) C7 csf (child_entry with vs_gas_readings := g ++ tail))) /\
        (!v. (run_blocks (fuel-d) C7 csf
              (child_entry with vs_gas_readings := g ++ tail) = OK v \/
              ?r. run_blocks (fuel-d) C7 csf
                (child_entry with vs_gas_readings := g ++ tail) = IntRet r v) ==>
          dftGasFromListTraceDefs$trace_gas
            (dftGasFromListTraceDefs$trace_blocks ((d,(EL q xs).inst_id)::p) d (fuel-d) C7 csf
              (child_entry with vs_gas_readings := g ++ tail)) = ZIP (EL q ks,g)))) ==>
  !kgss tail.
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
    let g = FLAT kgss;
        B = <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
    in
    (?extra. FLAT (TAKE k ess) =
      gas_events_block (fuel-d) C7 sf.fn_name B (be with vs_gas_readings := g ++ tail) ++ extra) /\
    (!u. FOLDR (dft_exec_cons (fuel-d) C7) OK (TAKE k xs)
        (be with vs_gas_readings := g ++ tail) = OK u ==>
      gas_events_block (fuel-d) C7 sf.fn_name B (be with vs_gas_readings := g ++ tail) =
        FLAT (TAKE k ess) /\ u.vs_gas_readings = tail /\
      dftGasFromListTraceDefs$trace_gas
        (dftGasFromListTraceDefs$trace_block p d (fuel-d) C7 sf B
          (be with vs_gas_readings := g ++ tail)) = ZIP (FLAT (TAKE k ks),g) /\
      (!tail'. FOLDR (dft_exec_cons (fuel-d) C7) OK (TAKE k xs)
          (be with vs_gas_readings := g ++ tail') = OK (u with vs_gas_readings := tail') /\
        gas_events_block (fuel-d) C7 sf.fn_name B
          (be with vs_gas_readings := g ++ tail') = FLAT (TAKE k ess)))
Proof
  map_every qx_gen_tac [`fuel`, `N`, `d`, `ms`, `xs`, `ess`, `ks`, `k`, `sf`, `p`,
    `calls`, `j`, `C8`, `root_tf`, `root_entry`, `C7`, `be`] >> strip_tac >>
  `!a. a <= k ==> !kgss tail.
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE a ms) kgss ==>
    let g = FLAT kgss;
        B = <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE a xs|>
    in
    (?extra. FLAT (TAKE a ess) =
      gas_events_block (fuel-d) C7 sf.fn_name B (be with vs_gas_readings := g ++ tail) ++ extra) /\
    (!u. FOLDR (dft_exec_cons (fuel-d) C7) OK (TAKE a xs)
        (be with vs_gas_readings := g ++ tail) = OK u ==>
      gas_events_block (fuel-d) C7 sf.fn_name B (be with vs_gas_readings := g ++ tail) =
        FLAT (TAKE a ess) /\ u.vs_gas_readings = tail /\
      dftGasFromListTraceDefs$trace_gas
        (dftGasFromListTraceDefs$trace_block p d (fuel-d) C7 sf B
          (be with vs_gas_readings := g ++ tail)) = ZIP (FLAT (TAKE a ks),g))` by
    (Induct_on `a`
     >- ((simp[] >> rpt gen_tac >>
         simp[Once gas_events_block_def, Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs),
              dftGasFromListTraceDefsTheory.trace_gas_def, get_instruction_def] >> (simp[Once gas_events_block_def, Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs), dftGasFromListTraceDefsTheory.trace_gas_def, get_instruction_def]))) >>
     suspend "observations_step") >>
  suspend "replay"
QED

Resume focus_retained_row_replay[observations_step]:
  cheat
QED

Resume focus_retained_row_replay[replay]:
  cheat
QED

Finalise focus_retained_row_replay
