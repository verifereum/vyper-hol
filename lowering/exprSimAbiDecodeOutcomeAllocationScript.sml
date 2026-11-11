Theory exprSimAbiDecodeOutcomeAllocation
Ancestors
  exprSimAbiDecodeSetupObserve exprSimAbiGasBridge abiEncoderObserver
  abiBuiltinDecodeSetup fragExec venomExecSemantics venomState words

(* The decoder outcome supplies a backwards continuation at its end cursor.
   Observing that continuation with STOP makes the setup allocation theorem
   applicable to this very endpoint, rather than to a replacement witness. *)
Theorem abi_decode_outcome_allocation:
  lower_abi_decode data info mn mx outsz start = (result,final) /\
  fn_has_code start final fn /\ frag_gas_free start final /\
  s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\ ~s.vs_halted /\
  t.vs_current_bb = final.cs_current_bb /\
  t.vs_inst_idx = LENGTH final.cs_current_insts /\
  (!fuel r. run_from fuel ctx (frag_observer start final fn id) t = r /\
      (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx (frag_observer start final fn id) s = r) /\
  ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site start mn mx) = NONE /\
      d = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas (abi_builtin_decode_output_site start mn mx) = SOME(d,outsz)) /\
  outsz < dimword (:256) ==>
  eval_operand result t = SOME (n2w d) /\
  FLOOKUP t.vs_allocas (abi_builtin_decode_output_site start mn mx) = SOME(d,outsz)
Proof
  strip_tac >>
  `run_from 0 ctx (frag_observer start final fn id) t = Halt (stop_view t)` by
    (irule run_from_stop_view >>
     simp[frag_observer_cut_lookup, frag_observer_cut_instruction] >>
     qexists_tac `id` >> simp[]) >>
  `?fuel. run_from fuel ctx (frag_observer start final fn id) s = Halt (stop_view t)` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  irule abi_decode_lower_observer_output >> simp[] >>
  goal_assum (drule_at (Pat `lower_abi_decode _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`ctx`, `fn`, `fuel`, `id`, `s`] >>
  simp[frag_observer_cut_def]
QED
