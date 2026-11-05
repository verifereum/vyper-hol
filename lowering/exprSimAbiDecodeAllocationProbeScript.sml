(* Checked observation used to recover allocation provenance from execution.
   This does not assert that the decoder effect creates an allocation. *)
Theory exprSimAbiDecodeAllocationProbe
Ancestors
  exprSimAbiGasBridge abiDecoderSiteEffect abiEncoderObserver venomExecSemantics venomState

Theorem abi_decode_observer_success_run:
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!fuel r. run_from fuel ctx (frag_observer sa sb fn id) t = r /\
       (!e. r <> Error e) ==>
       ?fuel'. run_from fuel' ctx (frag_observer sa sb fn id) s = r) ==>
  ?fuel. run_from fuel ctx (frag_observer sa sb fn id) s =
           Halt (stop_view t)
Proof
  strip_tac >>
  `run_from 0 ctx (frag_observer sa sb fn id) t = Halt (stop_view t)` by
    (irule run_from_stop_view >>
     qexistsl [`<|bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>`,
       `id`] >>
     simp[frag_observer_cut_lookup, frag_observer_cut_instruction]) >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem abi_decode_stop_view_allocas:
  FLOOKUP (stop_view t).vs_allocas site = FLOOKUP t.vs_allocas site
Proof
  simp[stop_view_def, halt_state_def]
QED
