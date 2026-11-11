(* Module and return metadata agree across a callee's root boundary. *)
Theory bodyIntCallPackageExitFields
Ancestors
  bodyIntCallMetadata bodyIntCallJointContract bodySim

Theorem intcall_root_caller_exit_fields:
  intcall_frame_ok fp /\ fp.jc_tops = tops /\ fp.jc_ret_ty = ret /\
  body_inv tops ctx cenv cx /\
  body_inv tops ctx fp.jc_root_ce fp.jc_cx /\
  fp.jc_cx = (cx with stk updated_by CONS owner) /\
  cenv_module_pins tops cenv /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (nret,rbs,pvs) ==>
  fp.jc_root_ce.ce_module_vars = cenv.ce_module_vars /\
  fp.jc_root_ce.ce_module = cenv.ce_module /\
  fp.jc_root_ce.ce_is_ctor = cenv.ce_is_ctor /\
  fp.jc_root_ce.ce_returns_count = nret
Proof
  strip_tac >> drule_all body_internal_decl_return_count >> strip_tac >>
  fs[intcall_frame_ok_def, cenv_module_pins_def, body_inv_def]
QED
