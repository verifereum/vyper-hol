(* Applicability boundary of the internal-frame staging interface. *)
Theory bodyIntCallStageApplicability
Ancestors
  bodyIntCallJointContract bodySim compileEnv

Theorem intcall_staging_requires_internal_return_pc:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s ==>
  ce.ce_return_pc = SOME (PtrVar fp.jc_rpc 0)
Proof
  rw[intcall_frame_ok_def, intcall_expr_res_def, same_frame_def] >>
  gvs[compile_env_component_equality]
QED
