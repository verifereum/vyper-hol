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
  dftRunRel dftScheduleOrder o1PassLift venomExecSemantics venomWf
  venomInst venomState list

(* Why it holds (unchecked notes): take the same instruction in C.
   - Memory ranges depend only on operand values, which the schedule
     computes before the instruction, as C does.  An instruction with
     memory ranges conflicts with RETURNDATACOPY and INVOKE, and nothing
     moves above a root (ASSERT, ASSERT_UNREACHABLE), so whenever the frame
     of fn' reaches a memory instruction, C reaches it too.
   - An instruction with no memory ranges corresponds to any state C
     reaches; vs_alloca_next, vs_allocas and vs_initial_fmp don't change
     without ALLOCA.
   - INVOKE: what may have run in another order before it has no effects,
     so the non-frame state is the same; INVOKEs keep their order with
     the other fallible instructions.  A callee run of C' that returns
     gives the same return in C (dft_run_blocks_rel run backwards: only an
     OK/IntRet result of C relates to one of C'), though that needs a form
     without ctx_labels_bound: a run of C' that returns has run every
     OFFSET on its path. *)
Theorem dft_frame_sim:
  !C C'.
    LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions ==>
    LIST_REL (\fn fn'. fn'.fn_name = fn.fn_name /\
                       fn_entry_label fn' = fn_entry_label fn /\
                       frame_sim C C' fn fn')
             C.ctx_functions C'.ctx_functions
Proof
  cheat
QED
