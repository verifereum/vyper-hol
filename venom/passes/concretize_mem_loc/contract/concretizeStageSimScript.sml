(*
 * ConcretizeMemLoc's stage contract, the semantic half: every
 * terminating run of C (every function before the pass) is matched by
 * C' (every function after it, each computed on a unit whose callees are
 * in their final form, o1_walk_view), up to the dead bytes D.
 *
 * TOP-LEVEL:
 *   concretize_stage_sim
 *)
Theory concretizeStageSim
Ancestors
  o1PassContract ptrDiscipline unitMemInv concretizeMemLocDefs
  venomPassDispatcher cfgWf

(* Why it holds (intuition, not a prescribed proof).

   The pass rewrites `p = ALLOCA sz` to `p = ASSIGN pos`, where pos comes
   from a static layout of the whole call tree: callee allocations are
   imported from the callees' fn_mems_used, and allocations whose
   memory-liveness sets (liveat ∩ used, from the base-pointer and
   MemLiveness analyses) don't intersect may share space.  INVOKE counts
   the callee's fn_mems_used and the base allocations of its operands as
   live at the call.

   Relate a source state (with the frame_reachable ghosts) to a target
   state at the same function, block and index: a variable whose
   provenance is the site of ALLOCA a differs by the relocation (static
   position of a minus its runtime base), every other variable is equal;
   for every site live in some frame of the stack, its bytes agree at the
   relocated address; every other field is equal except vs_memory,
   vs_allocas and vs_alloca_next.  access_ok keeps every access inside
   its operand's site, reading only written bytes; MemLiveness soundness
   keeps a live site's bytes from being clobbered through a site sharing
   its space.  Observable state holds no memory, and external-call and
   RETURN data is read inside sites; unwritten bytes are tainted, and
   taint_within D C vs places them in D. *)
Theorem concretize_stage_sim:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  dead_wf D /\ taint_within D C vs /\ EVERY ssa_form C.ctx_functions /\
  ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions ==>
  ctx_sim D C C' vs vs
Proof
  cheat
QED
