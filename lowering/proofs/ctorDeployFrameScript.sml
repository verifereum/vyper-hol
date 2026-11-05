(* Creation-frame boundary: a run of the root-shadowed frame related to the
 * deployment unit's result gives the real creation frame's result
 * (shadow_root_run_halt/_exception and deploy_frame_complete).
 * TOP-LEVEL: deploy_venom_frame (a piece of e2e_deploy_correctness; admitted until proved).
 *)
Theory ctorDeployFrame
Ancestors
  ctorDeployDefs deployFrameReplay codegenCorrectness e2eDeployFrame

Theorem deploy_venom_frame:
  !tops runtime_bc deploy_bc am tx es src res.
    deploy_state_rel tops deploy_bc am tx es /\
    runtime_bc <> [] /\ ~(?t. runtime_bc = 0xEFw :: t) /\
    deploy_venom_result_rel tops runtime_bc tx src res /\
    (?r g. run_call (shadow_root es) = SOME (r, g) /\
           (frame_resource_starved (shadow_root es) r g \/
            venom_frame_rel (shadow_root es) r g res))
    ==>
    ?r es'. run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       deploy_result_rel tops runtime_bc tx es r es' src)
Proof
  cheat
QED
