Theory readonlyInvokeCopyFwdExecutionCallAnnotations
Ancestors
  lowerDloadOracleCallAssembly readonlyInvokeCopyFwdStepsExternalOracle
  o1LowerDloadOccurrence ptrDiscipline venomInst venomState
  finite_map list pred_set words arithmetic

Theorem ricf_execution_call_annotations:
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] /\
  3 < LENGTH inst.inst_operands /\ inst.inst_outputs = [out] /\
  source_memory_write_ranges inst s = [(w2n (ro:256 word),w2n (rs:256 word))] /\
  r.vs_allocas = s.vs_allocas /\ r.vs_fmp = s.vs_fmp /\
  rq.cr_static = (inst.inst_opcode = STATICCALL \/ s.vs_call_ctx.cc_static) /\
  (inst.inst_opcode = DELEGATECALL ==> tn.t_stor = {} /\ tn.t_trans = {}) ==>
  step_prov PG G inst (update_var out w r) = set_prov G [out] NONE /\
  step_taint inst s (update_var out w r) tn =
    (ricf_call_taint tn rq s r (w2n ro) (w2n rs)
      with t_var := set_var_taint tn.t_var [out] {}) /\
  occurrence_sites_step a B inst (update_var out w r) = B
Proof
  strip_tac >>
  `{w2n ro+j | j < LENGTH (TAKE (w2n rs) r.vs_returndata)} =
   {i | w2n ro <= i /\ i < w2n ro + LENGTH (TAKE (w2n rs) r.vs_returndata)}` by
    (simp[EXTENSION] >> gen_tac >> eq_tac >> strip_tac
     >- (gvs[] >> decide_tac) >> qexists_tac `x-w2n ro` >> decide_tac) >>
  `inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL \/
   inst.inst_opcode = DELEGATECALL` by fs[MEM] >>
  mp_tac (Q.INST [`ss` |-> `update_var out w r`,
    `rz` |-> `rs:256 word`] ld_oracle_call_taint) >>
  (impl_tac >- gvs[update_var_def]) >>
  strip_tac >>
  gvs[MEM, step_prov_def, out_prov_def, occurrence_sites_step_def,
    ricf_call_taint_def, adopt_reset_def, update_var_def, taint_component_equality]
QED
