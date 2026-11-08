(*
 * Context simulation from block-level simulations on reachable frames
 *
 * A pass that is only correct on states the source program actually
 * reaches under the pointer discipline (its frames are frame_reachable,
 * so access_ok and allocas_from hold there) proves one block at a time:
 * from block-boundary states s (source) and t (target) related by R, with
 * s reachable, one block of the source and of the target end in results
 * related by R at the next boundary, by R_ret on internal return, or by
 * dead_result_rel on halt and abort.  Inside the block it may run callees
 * through fn_sim_below, the same simulation for smaller fuel.
 * reachable_fn_sim_ctx_sim turns that into ctx_sim.
 *
 * TOP-LEVEL:
 *   block_reach              — a block-boundary state the source reaches
 *   one_block                — one run_blocks iteration: PHIs, then the block
 *   fn_sim_below             — function-level simulation below a fuel bound
 *   reachable_fn_sim_ctx_sim — block obligation ==> ctx_sim
 *)

Theory reachableFnSim
Ancestors
  ptrDiscipline ptrSafeRun o1PassContract passSimulationDefs
  contextCodegenRel venomExecSemantics venomState

(* A block-boundary state of fn (before its PHIs) whose first active
   instruction the source reaches from vs. *)
Definition block_reach_def:
  block_reach vs C fn s <=>
    ?stk PG G tn s1 inst.
      enters_block fn s s1 /\ active_inst fn inst s1 /\
      frame_reachable vs C stk PG G tn fn inst s1
End

(* One iteration of run_blocks: the block's PHIs, then the block itself. *)
Definition one_block_def:
  one_block fuel ctx fn s =
    case lookup_block s.vs_current_bb fn.fn_blocks of
      NONE => Error "block not found"
    | SOME bb =>
        case eval_phis s bb.bb_instructions of
          Error e => Error e
        | OK s_phi =>
            exec_block fuel ctx bb
              (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
End

(* Related results of a whole function run. *)
Definition fn_run_rel_def:
  fn_run_rel D R_ret fn r r' <=>
    case (r, r') of
      (Halt s, Halt s') => dead_result_rel D r r'
    | (Abort a s, Abort a' s') => dead_result_rel D r r'
    | (IntRet v s, IntRet v' s') => v' = v /\ R_ret fn s s'
    | _ => F
End

(* Related results of one block: a non-halted OK continues under R. *)
Definition block_step_rel_def:
  block_step_rel D R R_ret fn r r' <=>
    case (r, r') of
      (OK s, OK s') =>
        (s'.vs_halted <=> s.vs_halted) /\
        (if s.vs_halted then dead_result_rel D (Halt s) (Halt s')
         else R fn s s')
    | _ => fn_run_rel D R_ret fn r r'
End

(* Every function of C simulates its namesake in C' from R-related,
   reachable block-boundary states, for every fuel below n. *)
Definition fn_sim_below_def:
  fn_sim_below D vs C C' R R_ret n <=>
    !k fn fn' s t.
      k < n /\
      MEM fn C.ctx_functions /\
      lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
      R fn s t /\ block_reach vs C fn s /\
      terminates (run_blocks k C fn s) ==>
      ?m. fn_run_rel D R_ret fn (run_blocks k C fn s) (run_blocks m C' fn' t)
End

(* Why it holds: strong induction on n for fn_sim_below n.  run_blocks
   (SUC j) C fn s is one_block j C fn s followed by Halt (halted OK),
   run_blocks j C fn s' (OK) or the propagated result; target fuels
   compose by venomExecPropsTheory.fuel_mono.  The root reduces run_context
   to run_blocks from the entry state, where frame_reachable's entry rule
   gives block_reach; o1_ctx_shape rules out IntRet/OK at the root
   (venomRetPropsTheory.run_context_not_int_ret, run_context_not_ok).
   The missing piece is carrying frame_reachable along a source run
   (across INVOKE via the call and ret rules), which nothing in the repo
   proves yet; wf_function's distinct labels make active_inst pick the
   block exec_block runs.  Pass proofs discharging the block obligation
   need that same walk to reach their INVOKE sites, so it should be an
   exported theorem. *)
Theorem reachable_fn_sim_ctx_sim:
  !D vs C C' R R_ret.
    o1_ctx_shape C /\
    C'.ctx_entry = C.ctx_entry /\
    (!fn. MEM fn C.ctx_functions ==>
          ?fn'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
                fn_entry_label fn' = fn_entry_label fn) /\
    (!name fn lbl.
       C.ctx_entry = SOME name /\
       lookup_function name C.ctx_functions = SOME fn /\
       fn_entry_label fn = SOME lbl ==>
       R fn (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                        vs_inst_idx := 0 |>)
            (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                        vs_inst_idx := 0 |>)) /\
    (!k fn fn' s t.
       fn_sim_below D vs C C' R R_ret (SUC k) /\
       MEM fn C.ctx_functions /\
       lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
       R fn s t /\ block_reach vs C fn s /\
       terminates (one_block k C fn s) ==>
       ?m. block_step_rel D R R_ret fn (one_block k C fn s)
                                       (one_block m C' fn' t)) ==>
    ctx_sim D C C' vs vs
Proof
  cheat
QED
