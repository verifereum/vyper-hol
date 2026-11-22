(* Recover the units and pipeline outputs used by the linked compiler. *)
Theory linkedCompilePhases
Ancestors
  compileUnit compileVyper

Theorem compile_vyper_with_mods_success_phases:
  compile_vyper_with_mods pipeline finalizer policy mods exps =
    SOME (deploy_bc,runtime_bc) ==>
  ?rpolicy runtime_unit runtime_out deploy_unit deploy_out.
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit_mods mods exps rpolicy = SOME runtime_unit /\
    pipeline rpolicy runtime_unit = SOME runtime_out /\
    runtime_out.po_final_assembly = rpolicy.rpol_final_assembly /\
    finalize_codegen finalizer rpolicy runtime_out.po_unit = SOME runtime_bc /\
    lower_vyper_deploy_unit_mods mods exps rpolicy runtime_bc = SOME deploy_unit /\
    pipeline rpolicy deploy_unit = SOME deploy_out /\
    deploy_out.po_final_assembly = rpolicy.rpol_final_assembly /\
    finalize_codegen finalizer rpolicy deploy_out.po_unit = SOME deploy_bc
Proof
  simp[compile_vyper_with_mods_def, checked_unit_pipeline_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  goal_assum $ drule_at Any
QED
