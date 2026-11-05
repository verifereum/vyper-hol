(*
 * MakeSSA's first O1 run keeps the source rows of o1_inv besides the
 * memory, pointer and taint ones: no layout end, no DALLOCA, no FMP
 * convention or operation, the DLOAD offset bound and the alloca headroom
 * LowerDload needs, and the callee-first order.  The pass changes no
 * opcode of an existing instruction but PHIs it cleans up, adds only
 * PHIs and ASSIGNs, and renames variables, so a renamed DLOAD offset
 * holds the original's value.
 *)
Theory o1ContractMakeSsaSrc
Ancestors
  o1PassContract ptrDiscipline unitMemInv lowerDloadDefs venomPassSchedule
  list

Theorem make_ssa_stage_src_rows:
  !rpolicy D view C C' vs names.
    ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ EVERY make_ssa_input_ok C.ctx_functions /\
    callee_first names C.ctx_functions ==>
    EVERY (\fn. fn.fn_eom = NONE) C'.ctx_functions /\ ~ctx_has_dalloca C' /\
    fmp_free_ctx C' /\ mem_inv dload_offset_ok C' vs /\
    mem_inv dload_headroom_ok C' vs /\ callee_first names C'.ctx_functions
Proof
  cheat
QED
