(*
 * Lifting per-function pass facts to the O1 stage contract.
 *
 * A pass that keeps the calling convention (it changes no INVOKE target,
 * argument value or return value, and leaves every state field but the
 * frame's variables and control position alone) is proved one function
 * at a time, in an arbitrary context.  This theory turns such facts into
 * the stage part of the pass contract (o1PassContract) between two stage
 * contexts C and C' related function by function:
 *
 *   - fn_bisim fn fn': terminating runs of fn and fn' from a frame entry
 *     state correspond, in both directions, in any context.  Runs are
 *     compared by frame_result_rel: equal return values and equal states
 *     outside the frame's variables and control position.  Every function
 *     pair related by fn_bisim gives ctx_bisim C C' (an induction on
 *     fuel through INVOKE), and that gives ctx_sim (ctx_bisim_ctx_sim).
 *
 *   - frame_sim C C' fn fn': every state a frame of fn' reaches in C'
 *     corresponds to one a frame of fn reaches in C from the same entry
 *     state, with the same alloca frame and the same memory ranges, or
 *     none (an inserted instruction that touches no memory).  Every
 *     function pair related by frame_sim transports the shared memory
 *     invariant for any memory fact closed under that correspondence
 *     (frame_sim_mem_inv), which every phase fact is (mem_corr_closed_*).
 *)
Theory o1PassLift
Ancestors
  o1PassContract unitMemInv contextRawReachable contextCodegenRel
  unitTransformDefs passSimulationDefs stateEquiv stateFrame
  venomExecSemantics venomInst venomMemDefs venomState list finite_map

(* ===== Run correspondence ===== *)

(* The state a frame of fn starts in: the context entry (run_context) and a
   callee (setup_callee) both start this way. *)
Definition fn_entry_state_def:
  fn_entry_state fn s <=>
    s.vs_vars = FEMPTY /\ s.vs_inst_idx = 0 /\ s.vs_prev_bb = NONE /\
    ~s.vs_halted /\ fn_entry_label fn = SOME s.vs_current_bb
End

(* Terminal results of a frame that its caller can't tell apart. *)
Definition frame_result_rel_def:
  frame_result_rel r r' <=>
    case (r, r') of
      (IntRet v s, IntRet v' s') =>
        v' = v /\ execution_frame s' = execution_frame s
    | (Halt s, Halt s') => execution_frame s' = execution_frame s
    | (Abort a s, Abort a' s') =>
        a' = a /\ execution_frame s' = execution_frame s
    | _ => F
End

(* One step's results: a continuing step reaches the same state. *)
Definition step_result_rel_def:
  step_result_rel r r' <=>
    case (r, r') of
      (OK s, OK s') => s' = s
    | _ => frame_result_rel r r'
End

(* fn and its transform fn' have corresponding terminating runs from every
   frame entry state, in any context. *)
Definition fn_bisim_def:
  fn_bisim fn fn' <=>
    fn'.fn_name = fn.fn_name /\ fn_entry_label fn' = fn_entry_label fn /\
    !ctx s. fn_entry_state fn s ==>
      (!fuel. terminates (run_blocks fuel ctx fn s) ==>
         ?fuel'. frame_result_rel (run_blocks fuel ctx fn s)
                                  (run_blocks fuel' ctx fn' s)) /\
      (!fuel'. terminates (run_blocks fuel' ctx fn' s) ==>
         ?fuel. frame_result_rel (run_blocks fuel ctx fn s)
                                 (run_blocks fuel' ctx fn' s))
End

(* The same, between the functions of two contexts, each run in its own
   context. *)
Definition ctx_bisim_def:
  ctx_bisim C C' <=>
    ctx_fn_names C' = ctx_fn_names C /\
    !name fn s.
      lookup_function name C.ctx_functions = SOME fn /\
      fn_entry_state fn s ==>
      ?fn'. lookup_function name C'.ctx_functions = SOME fn' /\
            fn_entry_label fn' = fn_entry_label fn /\
            (!fuel. terminates (run_blocks fuel C fn s) ==>
               ?fuel'. frame_result_rel (run_blocks fuel C fn s)
                                        (run_blocks fuel' C' fn' s)) /\
            (!fuel'. terminates (run_blocks fuel' C' fn' s) ==>
               ?fuel. frame_result_rel (run_blocks fuel C fn s)
                                       (run_blocks fuel' C' fn' s))
End

Theorem fn_bisim_ctx_bisim:
  LIST_REL fn_bisim C.ctx_functions C'.ctx_functions ==> ctx_bisim C C'
Proof
  cheat
QED

(* One instruction, run in the two contexts. *)
Theorem ctx_bisim_step_inst:
  ctx_bisim C C' ==>
  (!fuel inst s.
     terminates (step_inst fuel C inst s) ==>
     ?fuel'. step_result_rel (step_inst fuel C inst s)
                             (step_inst fuel' C' inst s)) /\
  (!fuel' inst s.
     terminates (step_inst fuel' C' inst s) ==>
     ?fuel. step_result_rel (step_inst fuel C inst s)
                            (step_inst fuel' C' inst s))
Proof
  cheat
QED

(* The entry function has no RET, so the context run never returns. *)
Theorem ctx_bisim_ctx_sim:
  ctx_bisim C C' /\ C'.ctx_entry = C.ctx_entry /\
  EVERY (\fn. C.ctx_entry = SOME fn.fn_name ==> entry_fn_no_ret fn)
        C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted ==>
  ctx_sim C C' vs vs
Proof
  cheat
QED

(* ===== Reachable-state correspondence ===== *)

(* The states a frame of fn reaches from its entry state s0 without
   leaving the frame: raw_reachable's entry, next and block rules. *)
Inductive frame_reach:
[~start:]
  (!ctx fn s0 inst s1.
     enters_block fn s0 s1 /\ active_inst fn inst s1 ==>
     frame_reach ctx fn s0 inst s1)
[~next:]
  (!ctx fn s0 inst inst' s s' fuel.
     frame_reach ctx fn s0 inst s /\
     ~is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
     active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
     frame_reach ctx fn s0 inst' (s' with vs_inst_idx := SUC s.vs_inst_idx))
[~block:]
  (!ctx fn s0 inst inst' s s' s1 fuel.
     frame_reach ctx fn s0 inst s /\
     is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
     ~s'.vs_halted /\ enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
     frame_reach ctx fn s0 inst' s1)
End

(* What the memory facts see of a state: the alloca frame, the initial
   free-memory pointer and the instruction's memory ranges.  An inserted
   instruction that touches no memory corresponds to any instruction. *)
Definition mem_corr_def:
  mem_corr inst s inst' s' <=>
    s'.vs_alloca_next = s.vs_alloca_next /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_initial_fmp = s.vs_initial_fmp /\
    (inst_mem_ranges inst' s' = [] \/
     inst_mem_ranges inst' s' = inst_mem_ranges inst s)
End

(* An INVOKE corresponds to an INVOKE of the same callee with the same
   argument values from a state that differs only in the frame, so both
   callee frames start in the same state. *)
Definition call_corr_def:
  call_corr inst s inst' s' <=>
    (inst'.inst_opcode = INVOKE ==>
       inst.inst_opcode = INVOKE /\
       execution_frame s' = execution_frame s /\
       ?nm ops ops'. decode_invoke inst = SOME (nm,ops) /\
                     decode_invoke inst' = SOME (nm,ops') /\
                     eval_operands ops' s' = eval_operands ops s)
End

(* Every state a frame of fn' reaches in C' corresponds to one a frame of
   fn reaches in C from the same entry state. *)
Definition frame_sim_def:
  frame_sim C C' fn fn' <=>
    !s0 inst' s'.
      fn_entry_state fn s0 /\ frame_reach C' fn' s0 inst' s' ==>
      ?inst s. frame_reach C fn s0 inst s /\
               mem_corr inst s inst' s' /\ call_corr inst s inst' s'
End

(* A memory fact that sees a state only through mem_corr. *)
Definition mem_corr_closed_def:
  mem_corr_closed M <=>
    !ctx fn inst s ctx' fn' inst' s'.
      M ctx fn inst s /\ mem_corr inst s inst' s' ==> M ctx' fn' inst' s'
End

Theorem frame_sim_mem_inv:
  LIST_REL (\fn fn'. fn'.fn_name = fn.fn_name /\
                     fn_entry_label fn' = fn_entry_label fn /\
                     frame_sim C C' fn fn')
           C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  mem_corr_closed M /\ mem_inv M C vs ==>
  mem_inv M C' vs
Proof
  cheat
QED

Theorem mem_corr_closed_site_mem_ok:
  mem_corr_closed site_mem_ok
Proof
  cheat
QED

Theorem mem_corr_closed_static_mem_ok:
  mem_corr_closed (static_mem_ok eom)
Proof
  cheat
QED

Theorem mem_corr_closed_lowered_mem_fact:
  mem_corr_closed (lowered_mem_fact eom)
Proof
  cheat
QED
