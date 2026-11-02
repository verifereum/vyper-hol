(*
 * ConcretizeMemLoc's stage contract: the semantic half of its O1 pass
 * contract, between consecutive stage contexts C (every function before
 * the pass) and C' (every function after it, each computed on a unit whose
 * callees are in their final form, o1_walk_view).
 *
 * TOP-LEVEL:
 *   concretize_stage_sim         - every terminating run of C is matched
 *   concretize_stage_static_mem  - C' accesses memory below the layout end
 *)

Theory concretizeStageSim
Ancestors
  o1PassContract ptrDiscipline unitMemInv concretizeMemLocDefs
  venomPassDispatcher

(* Why it holds (intuition, not a prescribed proof).

   The pass rewrites `p = ALLOCA sz` to `p = ASSIGN pos`, where pos comes
   from a static layout of the whole call tree: callee allocations are
   imported from the callees' fn_mems_used, and allocations whose
   memory-liveness sets (liveat ∩ used, from the base-pointer and
   MemLiveness analyses) don't intersect may share space.  INVOKE counts
   the callee's fn_mems_used and the base allocations of its operands as
   live at the call.

   Relate a source state (with the frame_reachable ghosts stk/PG/G/W) to a
   target state at the same function, block and index:
   - a variable with provenance G v = site of ALLOCA a in its frame's
     function f differs by the relocation (static pos of a in f) - base;
     every other variable is equal (ptr_use_ok + affine_pointer_ops keep
     arithmetic on pointers affine, so the offset is preserved mod 2^256);
   - for every site live (per the analysis) in some frame of the stack,
     the bytes of it in W agree at the relocated address;
   - every other field is equal, except vs_memory, vs_allocas and
     vs_alloca_next (the target has no ALLOCA, so its frames' vs_allocas
     stay empty).
   access_ok makes every access stay inside its operand's site and read
   only bytes in W; MemLiveness soundness keeps a live site's bytes from
   being clobbered through another site sharing its space.  Observable
   state (observable_equiv) holds no memory, and external-call/RETURN data
   is read inside sites from bytes in W.

   Known obligations along the way, any of which may need a separate
   lemma:
   - both analyses iterate with fuel concretize_memloc_fuel fn and return
     the last iterate when it runs out; soundness needs the fixpoint;
   - the observed callees are the C' callees taken through the later
     passes (FmpLowering, MakeSSA, SimplifyCFG, SUE, DFT, CFGNormalization);
     their fn_mems_used must be the C' one (those passes don't touch it,
     but fn_pass_step doesn't say so);
   - a callee's static accesses lie inside its fn_mems_used intervals,
     its own allocations plus its transitive imports. *)

Theorem concretize_stage_sim:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\
  mem_inv raw_mem_ok C vs /\ ptr_discipline 0 C vs /\
  dead_wf D /\ taint_within D C vs /\ EVERY ssa_form C.ctx_functions ==>
  ctx_sim_dead D C C' vs
Proof
  cheat
QED

Theorem concretize_stage_ptr:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\
  mem_inv raw_mem_ok C vs /\ ptr_discipline 0 C vs /\
  dead_wf D /\ taint_within D C vs /\ EVERY ssa_form C.ctx_functions /\
  ctx_eom_bounded eom C C' ==>
  ptr_discipline eom C' vs /\ taint_within D C' vs
Proof
  cheat
QED

Theorem concretize_stage_static_mem:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\
  mem_inv raw_mem_ok C vs /\ ptr_discipline 0 C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_eom_bounded eom C C' ==>
  mem_inv (static_mem_ok eom) C' vs
Proof
  cheat
QED
