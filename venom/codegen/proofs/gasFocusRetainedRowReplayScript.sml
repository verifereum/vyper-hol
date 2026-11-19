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
    !g. g = FLAT kgss ==>
    !B. B = <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|> ==>
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
  CONV_TAC (TOP_DEPTH_CONV (Unwind.UNWIND_FORALL_CONV)) >>
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
  strip_tac >> rpt gen_tac >> strip_tac >>
  `a < LENGTH ms /\ a < LENGTH xs /\ a < LENGTH ess /\ a < LENGTH ks` by decide_tac >>
  `TAKE (SUC a) ms = TAKE a ms ++ [EL a ms] /\
   TAKE (SUC a) xs = TAKE a xs ++ [EL a xs] /\
   TAKE (SUC a) ess = TAKE a ess ++ [EL a ess] /\
   TAKE (SUC a) ks = TAKE a ks ++ [EL a ks]` by
    simp[TAKE_SUC_BY_TAKE, SNOC_APPEND] >>
  `?front g. kgss = front ++ [g] /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE a ms) front /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (EL a ms) g` by
    (qpat_x_assum `LIST_REL _ (TAKE (SUC a) ms) kgss` mp_tac >>
     asm_rewrite_tac[] >> simp[LIST_REL_SPLIT1] >> metis_tac[]) >>
  gvs[] >>
  qpat_x_assum `!kgss' tail. _`
    (qspecl_then [`front`, `g ++ tail`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE a xs) /\
   ~is_terminator (EL a xs).inst_opcode /\ ~is_pseudo (EL a xs).inst_opcode` by
    (fs[EVERY_EL, LENGTH_TAKE] >> (gvs[EL_TAKE, LESS_EQ_LESS_TRANS])) >>
  `!s. FOLDR (dft_exec_cons (fuel-d) C7) OK (TAKE a xs ++ [EL a xs]) s =
    case FOLDR (dft_exec_cons (fuel-d) C7) OK (TAKE a xs) s of
      OK t => dft_exec_cons (fuel-d) C7 (EL a xs) OK t | other => other` by
    (gen_tac >> pure_rewrite_tac[FOLDR_APPEND, FOLDR] >>
     simp[Once dft_exec_prefix_continue]) >>
  qspecl_then [`TAKE a xs`, `be with vs_gas_readings := FLAT front ++ g ++ tail`,
    `be.vs_inst_idx`] mp_tac native_prefix_cut >> simp[NoAsms] >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`fuel-d`, `C7`, `sf`, `p`, `d`, `[EL a xs]`,
    `<|bb_label := be.vs_current_bb; bb_instructions := []|>`, `mk_inst 0 STOP [] []`]
    strip_assume_tac) >>
  Cases_on `FOLDR (dft_exec_cons (fuel-d) C7) OK (TAKE a xs)
    (be with vs_gas_readings := FLAT front ++ g ++ tail)`
  >- (suspend "observations_ok") >>
  gvs[] >> qexists_tac `extra ++ EL a ess` >> simp[APPEND_ASSOC]
QED

Resume focus_retained_row_replay[replay]:
  rpt gen_tac >> strip_tac >> simp[] >>
  qpat_assum `!a. a <= k ==> _` (qspec_then `k` mp_tac) >>
  simp[NoAsms] >> disch_then (qspecl_then [`kgss`, `tail`] mp_tac) >>
  simp[] >> strip_tac >>
  gen_tac >> strip_tac >>
  qpat_assum `!u. FOLDR _ _ _ _ = OK u ==> _` drule >> strip_tac >>
  gen_tac >> conj_asm1_tac
  >- ((irule focus_retained_row_tail >>
      reverse conj_tac
      >- (gvs[EVERY_MEM] >> metis_tac[]) >>
      qexistsl_tac [`sf.fn_name`, `tail`] >>
      qpat_x_assum `FLAT (TAKE k ess) = _` kall_tac >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `gas_events_block _ _ _ _ _ = _` SUBST1_TAC >>
      `MAP LENGTH ms = MAP LENGTH ess` by
        simp[MAP_EQ_EVERY2, LIST_REL_LENGTH] >>
      `MAP LENGTH (TAKE k ms) = MAP LENGTH kgss` by
        (simp[MAP_EQ_EVERY2] >>
         conj_tac >- (drule LIST_REL_LENGTH >> simp[]) >>
         irule LIST_REL_mono >> goal_assum (drule_at Any) >>
         simp[] >> metis_tac[LIST_REL_LENGTH]) >>
      gvs[LENGTH_FLAT, MAP_TAKE])) >>
  qpat_assum `!a. a <= k ==> _` (qspec_then `k` mp_tac) >>
  simp[NoAsms] >> disch_then (qspecl_then [`kgss`, `tail'`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (mp_tac o CONJUNCT2) >>
  disch_then drule >> simp[NoAsms]
QED

Resume focus_retained_row_replay[observations_ok]:
  qpat_x_assum `!u. FOLDR _ _ _ _ = OK u ==> _`
    (qspec_then `v` mp_tac) >> simp[APPEND_ASSOC] >> strip_tac >>
  qpat_x_assum `FLAT (TAKE a ess) = _` kall_tac >>
  gvs[] >>
  `gas_events_block (fuel-d) C7 sf.fn_name
    <|bb_label := be.vs_current_bb; bb_instructions :=
      REPLICATE (a + be.vs_inst_idx) (mk_inst 0 STOP [] []) ++ [EL a xs]|> v =
    gas_events_step (fuel-d) C7 sf.fn_name (EL a xs) v` by
    (once_rewrite_tac[gas_events_block_def] >>
     simp[get_instruction_def, EL_APPEND_EQN] >>
     Cases_on `step_inst (fuel-d) C7 (EL a xs) v` >>
     simp[Once gas_events_block_def, get_instruction_def]) >>
  `dftGasFromListTraceDefs$trace_gas
    (dftGasFromListTraceDefs$trace_block p d (fuel-d) C7 sf
      <|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE (a + be.vs_inst_idx) (mk_inst 0 STOP [] []) ++ [EL a xs]|> v) =
    dftGasFromListTraceDefs$visit_gas ((p,d,(EL a xs).inst_id),sf,EL a xs,v) ++
    dftGasFromListTraceDefs$trace_gas
      (dftGasFromListTraceDefs$trace_step p d (fuel-d) C7 sf (EL a xs) v)` by
    (once_rewrite_tac[cj 2 dftGasFromListTraceDefsTheory.trace_defs] >>
     simp[get_instruction_def, EL_APPEND_EQN] >>
     Cases_on `step_inst (fuel-d) C7 (EL a xs) v` >>
     simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs),
       get_instruction_def, dftGasFromListTraceDefsTheory.trace_gas_def,
       MAP_APPEND, FLAT_APPEND]) >>
  `LENGTH (FLAT (TAKE a ks)) = LENGTH (FLAT front) /\
   LENGTH (EL a ks) = LENGTH g` by
    (`MAP LENGTH ms = MAP LENGTH ks` by
       simp[MAP_EQ_EVERY2, LIST_REL_LENGTH] >>
     `MAP LENGTH (TAKE a ms) = MAP LENGTH front` by
       (simp[MAP_EQ_EVERY2] >>
        conj_tac >- (qpat_assum `LIST_REL _ (TAKE a ms) front` (mp_tac o MATCH_MP LIST_REL_LENGTH) >> simp[]) >>
        irule LIST_REL_mono >> goal_assum (drule_at Any) >>
        simp[] >> metis_tac[LIST_REL_LENGTH]) >>
     `LENGTH (EL a ms) = LENGTH (EL a ks)` by
       (gvs[LIST_REL_EL_EQN]) >>
     drule LIST_REL_LENGTH >> gvs[LENGTH_FLAT, MAP_TAKE]) >>
  `(?extra. EL a ess = gas_events_step (fuel-d) C7 sf.fn_name (EL a xs) v ++ extra) /\
   (!w. step_inst (fuel-d) C7 (EL a xs) v = OK w ==>
     gas_events_step (fuel-d) C7 sf.fn_name (EL a xs) v = EL a ess /\
     w.vs_gas_readings = tail /\
     dftGasFromListTraceDefs$visit_gas ((p,d,(EL a xs).inst_id),sf,EL a xs,v) ++
     dftGasFromListTraceDefs$trace_gas
       (dftGasFromListTraceDefs$trace_step p d (fuel-d) C7 sf (EL a xs) v) = ZIP (EL a ks,g))` by
    suspend "contribution" >>
  gvs[] >> rpt strip_tac >>
  gvs[dft_exec_cons_def, AllCaseEqs()] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  qpat_x_assum `dftGasFromListTraceDefs$visit_gas _ ++ _ = _` SUBST1_TAC >>
  irule ZIP_APPEND >> simp[]
QED

Resume focus_retained_row_replay[contribution]:
  qpat_assum `!q. q < k ==> _` (qspec_then `a` mp_tac) >>
  (impl_tac >- decide_tac) >> disch_then strip_assume_tac >>
  Cases_on `(EL a xs).inst_opcode = GAS`
  >- (gvs[] >>
      `LENGTH g = 1` by metis_tac[LIST_REL_LENGTH, LENGTH] >>
      Cases_on `g` >> gvs[] >>
      simp[gas_events_step_def, dftGasFromListTraceDefsTheory.visit_gas_def,
        dftGasFromListTraceDefsTheory.trace_step_gas,
        dftGasFromListTraceDefsTheory.trace_gas_def] >>
      rpt strip_tac >>
      qspecl_then [`fuel-d`, `C7`, `EL a xs`, `v`] mp_tac (cj 1 gasCountTheory.gas_count_suffix) >>
      simp[gasCountTheory.gas_count_suffix_def, gasCountTheory.gas_count_step_def]) >>
  Cases_on `(EL a xs).inst_opcode = INVOKE`
  >- (qpat_x_assum `!q. q < k /\ _ ==> _` (qspec_then `a` mp_tac) >>
      simp[] >> disch_then strip_assume_tac >>
      qpat_x_assum `!kgss tail u. _`
        (qspecl_then [`front`, `g ++ tail`, `v`] mp_tac) >>
      simp[] >> disch_then strip_assume_tac >>
      qpat_x_assum `!g tail. _` (qspecl_then [`g`, `tail`] mp_tac) >>
      simp[] >> disch_then strip_assume_tac >>
      simp[Once dftGasFromListTraceDefsTheory.visit_gas_def] >>
      irule focus_retained_invoke_contribution >>
      simp[] >> goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`args`, `b0`, `child_out`, `ir`] >>
      simp[] >> (gvs[])) >>
  `EL a ms = [] /\ EL a ess = [] /\ EL a ks = []` by metis_tac[] >>
  gvs[] >>
  simp[gas_events_step_def, dftGasFromListTraceDefsTheory.visit_gas_def,
    dftGasFromListTraceDefsTheory.trace_step_noninvoke,
    dftGasFromListTraceDefsTheory.trace_gas_def] >>
  rpt strip_tac >>
  qspecl_then [`fuel-d`, `C7`, `EL a xs`, `v`] mp_tac (cj 1 gasCountTheory.gas_count_suffix) >>
  simp[gasCountTheory.gas_count_suffix_def, gasCountTheory.gas_count_step_def]
QED

Finalise focus_retained_row_replay
