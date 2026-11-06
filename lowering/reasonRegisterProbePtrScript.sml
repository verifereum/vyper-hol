(* Interface probes: compiler-name freshness is not register absence.
   ALLOCA installs output ghost facts without requiring the old register empty. *)
Theory reasonRegisterProbePtr
Ancestors allocationPtr reasonBufferPtr compileEnv ptrDiscipline venomState
  venomExecSemantics venomInst finite_map

Theorem reason_register_absence_probe[local]:
  ~fresh_vars_wrt cc
    (update_var (STRING #"%" (toString cc.cs_next_var)) w s)
Proof
  simp[fresh_vars_wrt_def, update_var_def, FDOM_FUPDATE] >>
  qexists_tac `cc.cs_next_var` >> simp[]
QED

Theorem reason_alloca_output_ghost_probe[local]:
  FLOOKUP s.vs_allocas id = NONE /\ n < dimword (:256) /\
  lookup_var out s = SOME old /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t ==>
  op_prov (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) t)
    (Var out) = SOME (s.vs_alloca_next,n) /\
  op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn)
    (Var out) = {}
Proof
  strip_tac >> drule_all fresh_alloca_ghost >> strip_tac >>
  simp[op_prov_def, op_taint_def, FLOOKUP_UPDATE]
QED
