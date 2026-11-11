(* Full frozen-premise certificate; no use of the admitted block theorem. *)
Theory internalReturnCopyFwdHaltCounterexample
Ancestors
  internalReturnCopyFwdHaltStatic internalReturnCopyFwdHaltPointer
  internalReturnCopyFwdHaltBoundary internalReturnCopyFwdHaltObservable
  internalReturnCopyFwdHaltProbe internalReturnCopyFwdSim reachableFnSim
  ptrDiscipline passSimulationDefs finite_map words

Theorem ircf_halt_counterexample_premises:
  let D = <|d_stor := (\a st. {}); d_trans := (\a st. {});
            d_imm := (\im. {}); d_ret := (\r. {})|>;
      C = ircf_halt_probe_ctx;
      s = ircf_halt_probe_state q (0w:word8);
      t = ircf_halt_probe_state q (1w:word8);
      fn = ircf_halt_probe_fn in
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  EVERY ircf_no_dst_write_alias C.ctx_functions /\
  ptr_discipline 0 C s /\ s.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\ taint_within D C s /\ dead_wf D /\
  fn_sim_below D s C (ircf_transform_ctx fn_meta rma C)
    (ircf_R D fn_meta rma C) (ircf_R_ret D fn_meta rma C) (SUC 0) /\
  MEM fn C.ctx_functions /\
  lookup_function fn.fn_name (ircf_transform_ctx fn_meta rma C).ctx_functions =
    SOME fn /\
  ircf_R D fn_meta rma C [] [] FEMPTY entry_taint fn s t /\
  block_reach s C [] [] FEMPTY entry_taint fn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME ircf_halt_probe_bb /\
  terminates (run_block 0 C ircf_halt_probe_bb s)
Proof
  simp[ircf_halt_static_shape, ircf_halt_static_ssa,
       ircf_halt_static_noalias, ircf_halt_pointer_discipline,
       ircf_halt_boundary_lookup, ircf_halt_static_no_dalloca,
       ircf_halt_probe_taint_within, ircf_halt_static_dead_wf,
       ircf_halt_probe_fuel_zero, ircf_halt_boundary_transform,
       ircf_halt_boundary_relation, ircf_halt_boundary_reach,
       ircf_halt_observable_terminates]
QED

Theorem ircf_halt_counterexample_conclusion:
  let D = <|d_stor := (\a st. {}); d_trans := (\a st. {});
            d_imm := (\im. {}); d_ret := (\r. {})|>;
      C = ircf_halt_probe_ctx;
      s = ircf_halt_probe_state q (0w:word8);
      t = ircf_halt_probe_state q (1w:word8);
      fn = ircf_halt_probe_fn in
  ~(?m bb'.
    lookup_block t.vs_current_bb fn.fn_blocks = SOME bb' /\
    block_step_rel D s C (ircf_R D fn_meta rma C)
      (ircf_R_ret D fn_meta rma C) [] [] fn
      (run_block 0 C ircf_halt_probe_bb s)
      (run_block m (ircf_transform_ctx fn_meta rma C) bb' t))
Proof
  simp[ircf_halt_boundary_transform, ircf_halt_boundary_lookup] >>
  rpt strip_tac >>
  strip_assume_tac (Q.INST [`k` |-> `0`, `s` |-> `q`,
    `b` |-> `0w:word8`] ircf_halt_probe_run) >>
  strip_assume_tac (Q.INST [`k` |-> `m`, `s` |-> `q`,
    `b` |-> `1w:word8`] ircf_halt_probe_run) >>
  mp_tac (Q.INST [`q` |-> `q`] ircf_halt_observable_mismatch) >>
  gvs[block_step_rel_def, fn_run_rel_def] >> metis_tac[]
QED

Theorem ircf_block_sim_false:
  ~(!D lo vs C fn_meta rma k stk PG G tn fn fn' s t bb.
    o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
    EVERY ircf_no_dst_write_alias C.ctx_functions /\
    ptr_discipline lo C vs /\ vs.vs_allocas = FEMPTY /\
    ~ctx_has_dalloca C /\ taint_within D C vs /\ dead_wf D /\
    fn_sim_below D vs C (ircf_transform_ctx fn_meta rma C)
      (ircf_R D fn_meta rma C) (ircf_R_ret D fn_meta rma C) (SUC k) /\
    MEM fn C.ctx_functions /\
    lookup_function fn.fn_name (ircf_transform_ctx fn_meta rma C).ctx_functions =
      SOME fn' /\
    ircf_R D fn_meta rma C stk PG G tn fn s t /\
    block_reach vs C stk PG G tn fn s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    terminates (run_block k C bb s) ==>
    ?m bb'.
      lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
      block_step_rel D vs C (ircf_R D fn_meta rma C)
        (ircf_R_ret D fn_meta rma C) stk PG fn
        (run_block k C bb s)
        (run_block m (ircf_transform_ctx fn_meta rma C) bb' t))
Proof
  strip_tac >>
  mp_tac ircf_halt_counterexample_premises >>
  mp_tac ircf_halt_counterexample_conclusion >>
  pure_rewrite_tac [LET_THM] >> BETA_TAC >> metis_tac[]
QED

(* Kernel tag audit: importing Sim's definitions must not import its admission
   into any counterexample certificate. DISK_THM is the loader's safe tag. *)
val _ = List.app (fn th =>
  case Tag.dest_tag (Thm.tag th) of
    ([], []) => ()
  | (["DISK_THM"], []) => ()
  | (os, axs) => raise Fail ("Halt counterexample tags: oracles=" ^
      String.concatWith "," os ^ "; axioms=" ^ String.concatWith "," axs))
  [ircf_halt_counterexample_premises, ircf_halt_counterexample_conclusion,
   ircf_block_sim_false];
