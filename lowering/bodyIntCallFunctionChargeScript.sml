(* Charge of an actual internal-function compilation, including constructors. *)
Theory bodyIntCallFunctionCharge
Ancestors
  bodyIntCallPackageResource intCallCallee externalEntryShape compileEnv
  moduleLowering emitHelper context list rich_list finite_map words

Theorem internal_param_capture_projection:
  !ps idx sa caps next sb.
  compile_internal_param_decls ps idx sa = ((caps,next),sb) ==>
  MAP (\c. (FST c,FST (SND c))) caps = ps
Proof
  rpt gen_tac >> strip_tac >>
  drule intCallCalleeTheory.compile_internal_param_decls_shape >> strip_tac >>
  irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
  first_x_assum (drule_then SUBST1_TAC) >> simp[]
QED

Theorem internal_entry_prefix_layout:
  !ce ps hr sa cep caps rpc sb.
  compile_internal_entry_prefix ce ps hr sa = ((cep,caps,rpc),sb) ==>
  cep.ce_vars = ce.ce_vars /\ MAP (\c. (FST c,FST (SND c))) caps = ps
Proof
  rpt gen_tac >>
  simp[compile_internal_entry_prefix_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule internal_param_capture_projection >> simp[]
QED
