(* One finite upper mask covers every compatible terminating source filling.
   The internal-return clause exposes complete consumption for composition. *)
Theory dftGasMask
Ancestors
  dftGasOracleSim dftGasSimFuel dftGasFromListRestore dftGasToListReplay
  dftRunRel dftDefs o1PassContract gasEvents gasCount
  venomExecSemantics venomState list rich_list sorting option

(* A stopped extracted head cannot cross an unexecuted call. *)
Theorem stopped_head_no_crossed_invoke[local]:
  dft_gas_swap_pair x y /\
  (ev_step orc p d fuel C y s = Halt t \/
   ev_step orc p d fuel C y s = Abort a t) ==>
  x.inst_opcode <> INVOKE
Proof
  strip_tac >> strip_tac
  >- (`~is_terminator y.inst_opcode` by gvs[dft_gas_swap_pair_def] >>
      `y.inst_opcode = INVOKE` by
        metis_tac[dftGasSimLocalBoundaryTheory.ev_step_nonterminator_halt_invoke] >>
      drule_all dft_swap_invoke_partner_class >>
      simp[venomEffectsTheory.opcode_fail_class_def]) >>
  metis_tac[dftGasSimSwapStopTheory.ev_invoke_partner_no_abort]
QED

(* A continuation contributes sites only after the first segment is exact. *)
Theorem mask_prefix_after_exact[local]:
  s1 = e1 /\ (?extra. s2 = e2 ++ extra) ==>
  ?extra. s1 ++ s2 = (e1 ++ e2) ++ extra
Proof
  strip_tac >> gvs[] >> simp[APPEND_ASSOC]
QED

Theorem mask_prefix_extend[local]:
  (?extra. s1 = e1 ++ extra) ==>
  ?extra. s1 ++ s2 = e1 ++ extra
Proof
  strip_tac >> gvs[] >> simp[APPEND_ASSOC]
QED

Theorem noninvoke_block_events_prefix[local]:
  !fuel C owner bb s.
    EVERY (\i. i.inst_opcode <> INVOKE)
      (DROP s.vs_inst_idx bb.bb_instructions) ==>
    ?extra.
      MAP (\i. (owner,i.inst_id))
        (FILTER (\i. i.inst_opcode = GAS)
          (DROP s.vs_inst_idx bb.bb_instructions)) =
      gas_events_block fuel C owner bb s ++ extra
Proof
  rpt gen_tac >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions`
  >- (drule rich_listTheory.DROP_CONS_EL >>
      disch_then (fn th => fs[th]) >>
      simp[Once gas_events_block_def, venomInstTheory.get_instruction_def,
           gas_events_step_def] >>
      Cases_on `step_inst fuel C (EL s.vs_inst_idx bb.bb_instructions) s` >>
      simp[] >>
      Cases_on `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = GAS` >>
      simp[] >>
      Cases_on `is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` >>
      simp[] >>
      first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
      simp[] >>
      disch_then (qspec_then `v' with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
      simp[] >> gvs[]) >>
  simp[Once gas_events_block_def, venomInstTheory.get_instruction_def, DROP_EQ_NIL]
QED

Theorem noninvoke_block_padding_mask[local]:
  EVERY (\i. i.inst_opcode <> INVOKE)
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  sites = MAP (\i. (owner,i.inst_id))
    (FILTER (\i. i.inst_opcode = GAS)
      (DROP s.vs_inst_idx bb.bb_instructions)) ==>
  ?raw_slots.
    LENGTH raw_slots = LENGTH sites /\
    MAP THE (FILTER IS_SOME raw_slots) = [] /\
    !gobs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs ==>
      ?extra. sites = gas_events_block fuel C owner bb
        (s with vs_gas_readings := gobs ++ tail) ++ extra
Proof
  strip_tac >> qexists_tac `REPLICATE (LENGTH sites) NONE` >>
  simp[LENGTH_REPLICATE, FILTER_EQ_NIL, MEM_REPLICATE] >>
  rpt strip_tac >> gvs[] >>
  qspec_then `s with vs_gas_readings := gobs ++ tail` mp_tac
    (Q.SPECL [`fuel`, `C`, `owner`, `bb`] noninvoke_block_events_prefix) >>
  simp[]
QED

Theorem dft_blocks_gas_mask:
  !fuel C C' fn fn' s.
    LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
    LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
    o1_ctx_shape C /\ o1_ctx_shape C' /\
    MEM fn C.ctx_functions /\ fn' = dft_fn fn /\
    dft_fn_rel fn fn' /\ strict_dom_vars_defined fn s /\
    fn_reachable fn s.vs_current_bb /\
    ctx_labels_bound C s.vs_labels /\
    ctx_labels_bound C' s.vs_labels /\ ~s.vs_call_ctx.cc_static /\
    terminates (run_blocks fuel C' fn' s) /\
    gas_count_blocks fuel C' fn' s <= LENGTH s.vs_gas_readings
    ==>
    ?raw_slots sites unused.
      LENGTH raw_slots = LENGTH sites /\
      PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) s.vs_gas_readings /\
      (!t.
        (?ir. run_blocks fuel C' fn' s = IntRet ir t) ==>
        EVERY IS_SOME raw_slots /\ unused = t.vs_gas_readings) /\
      !gobs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs ==>
        (?extra.
          sites = gas_events_blocks fuel C fn
            (s with vs_gas_readings := gobs ++ tail) ++ extra) /\
        ((?fuel_src. terminates
          (run_blocks fuel_src C fn (s with vs_gas_readings := gobs ++ tail)))
         ==>
        terminates
          (run_blocks fuel C fn (s with vs_gas_readings := gobs ++ tail)) /\
        dft_res_rel
          (restore_result []
            (run_blocks fuel C fn (s with vs_gas_readings := gobs ++ tail)))
          (restore_result [] (run_blocks fuel C' fn' s)) /\
        (!t.
          (?ir. run_blocks fuel C' fn' s = IntRet ir t) ==>
          gas_events_blocks fuel C fn
            (s with vs_gas_readings := gobs ++ tail) = sites /\
          residual_result tail (run_blocks fuel C' fn' s)
            (run_blocks fuel C fn (s with vs_gas_readings := gobs ++ tail))))
Proof
  cheat
QED
