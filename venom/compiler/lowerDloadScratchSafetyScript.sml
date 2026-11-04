(* Scratch-site execution, including reuse on loop iterations. *)
Theory lowerDloadScratchSafety
Ancestors
  lowerDloadSafetyKernel venomExecSemantics venomState finite_map words

Theorem lower_dload_scratch_alloca:
  inst.inst_outputs = [a] /\
  s.vs_alloca_next < dimword(:256) /\
  (FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
    s.vs_alloca_next + 32 < dimword(:256)) /\
  (!b n. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) ==>
    n = 32 /\ b + 32 <= s.vs_alloca_next) ==>
  ?t c. exec_alloca inst s (32w:bytes32) = OK t /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (c,32) /\
    FLOOKUP t.vs_vars a = SOME (n2w c) /\
    c + 32 <= t.vs_alloca_next /\
    t.vs_alloca_next < dimword(:256) /\
    t.vs_memory = s.vs_memory /\
    (!v. v <> a ==> FLOOKUP t.vs_vars v = FLOOKUP s.vs_vars v)
Proof
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- gvs[exec_alloca_def, update_var_def, FLOOKUP_UPDATE, dimword_def] >>
  PairCases_on `x` >>
  fs[] >>
  simp[exec_alloca_def] >>
  qexists_tac `x0` >>
  simp[update_var_def, FLOOKUP_UPDATE]
QED
