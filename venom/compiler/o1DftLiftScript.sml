(*
 * DFT's reachable states, for the O1 stage contract's memory facts.
 *
 * Every state a frame of a DFT schedule reaches corresponds, in the sense
 * of o1PassLift's frame_sim, to one the original frame reaches from the
 * same entry state.  frame_sim_mem_inv then carries any memory fact closed
 * under that correspondence from C to C'.
 *)
Theory o1DftLift
Ancestors
  dftRunRel dftScheduleOrder o1PassLift unitShapeDefs venomExecSemantics venomWf
  venomInst venomState list

(* Why it holds (unchecked notes): take the same instruction in C.
   - Memory ranges depend only on operand values, which the schedule
     computes before the instruction, as C does.  An instruction with
     memory ranges conflicts with RETURNDATACOPY and INVOKE, and nothing
     moves above a root (ASSERT, ASSERT_UNREACHABLE), so whenever the frame
     of fn' reaches a memory instruction, C reaches it too.
   - An instruction that runs early in C' cannot error where C would have
     stopped before it: fallible instructions keep their order, a label it
     reads as a value is bound (ctx_labels_bound, the frame starts with
     labels L and nothing writes them), and fn_shape_ok excludes CREATE and
     CREATE2, whose Venom step errors on a nested context.
   - An instruction with no memory ranges corresponds to any state C
     reaches; vs_alloca_next, vs_allocas and vs_initial_fmp don't change
     without ALLOCA.
   - INVOKE: what may have run in another order before it has no effects,
     so the non-frame state is the same; INVOKEs keep their order with
     the other fallible instructions.  A callee run of C' that returns
     gives the same return in C with the same fuel: by dft_run_blocks_rel,
     a run of C that errors, aborts or halts has no returning
     counterpart. *)
Theorem dft_frame_sim:
  !C C' L.
    LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
    EVERY fn_shape_ok C.ctx_functions /\ ctx_labels_bound C L ==>
    LIST_REL (\fn fn'. fn'.fn_name = fn.fn_name /\
                       fn_entry_label fn' = fn_entry_label fn /\
                       frame_sim L C C' fn fn')
             C.ctx_functions C'.ctx_functions
Proof
  cheat
QED
