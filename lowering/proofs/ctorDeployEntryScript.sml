(* The creation frame's entry Venom state: with the root frame's outputTo
 * shadowed as Memory, it satisfies codegen_correct's initial_ctx_rel, and it
 * is an O1 run state (as entry_venom_state_initial_ctx_rel and
 * generated_entry_code_layout_shape for calls).
 * TOP-LEVEL: deploy_entry_state_ok (a piece of e2e_deploy_correctness; admitted until proved).
 *)
Theory ctorDeployEntry
Ancestors
  ctorDeployDefs deployFrameReplay codegenCorrectness o1PassContract

Theorem deploy_entry_state_ok:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    unit_shape_ok dout.po_unit /\
    deploy_state_rel tops deploy_bc am tx es /\
    LENGTH (FST (HD es.contexts)).msgParams.code <= 24576
    ==>
    initial_ctx_rel cplan prog dout.po_unit.cu_context
      (entry_venom_state prog cplan es) (shadow_root es) /\
    o1_run_state_ok (entry_venom_state prog cplan es)
Proof
  cheat
QED
