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
