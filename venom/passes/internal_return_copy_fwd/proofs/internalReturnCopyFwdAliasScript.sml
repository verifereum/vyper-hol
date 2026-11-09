(* Allocation identity for available ircf aliases. *)
Theory internalReturnCopyFwdAlias
Ancestors
  internalReturnCopyFwdPlan ptrDiscipline venomWfProps venomInst list finite_map words
  venomExecSemantics venomState o1LowerDloadPairedAllocation

Definition ircf_alias_value_def:
  ircf_alias_value fn s G v <=>
    !ai root sz. MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
      ai.inst_outputs = [root] /\ ai.inst_operands = [Lit sz] /\
      ircf_alias fn root v ==>
      ?w. lookup_var v s = SOME w /\ lookup_var root s = SOME w /\
        FLOOKUP s.vs_allocas ai.inst_id = SOME (w2n w,w2n sz) /\
        FLOOKUP G v = SOME (w2n w,w2n sz)
End

Definition ircf_size_coherent_def:
  ircf_size_coherent fn s <=>
    !ai root sz b z. MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
      ai.inst_outputs = [root] /\ ai.inst_operands = [Lit sz] /\
      FLOOKUP s.vs_allocas ai.inst_id = SOME (b,z) ==> z = w2n sz
End

Theorem ircf_size_coherent_empty:
  s.vs_allocas = FEMPTY ==> ircf_size_coherent fn s
Proof
  simp[ircf_size_coherent_def]
QED

Theorem ircf_alias_output_inv:
  ssa_form fn /\ MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
  ai.inst_outputs = [root] /\ ai.inst_operands = [Lit sz] /\
  MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs /\
  ircf_alias fn root v ==>
  inst = ai \/
  ?u. inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [v] /\
      MEM (Var u) inst.inst_operands /\ ircf_alias fn root u
Proof
  strip_tac >>
  qpat_x_assum `ircf_alias _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [ircf_alias_cases])
  >- (disj1_tac >> irule ssa_outputs_same_inst >>
      gvs[fn_insts_def] >> metis_tac[MEM]) >>
  `inst = inst'` by
    (irule ssa_outputs_same_inst >> gvs[fn_insts_def] >> metis_tac[MEM]) >>
  gvs[] >> metis_tac[]
QED

(* The natural-number site base need not be a representable word. *)
Theorem ircf_alloca_wrap_probe:
  inst.inst_outputs = [root] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  s.vs_alloca_next = dimword (:256) ==>
  ?t. exec_alloca inst s (1w:bytes32) = OK t /\
      lookup_var root t = SOME 0w /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (dimword (:256),1) /\
      ~(?w:bytes32. FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,1))
Proof
  strip_tac >>
  simp[exec_alloca_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  gen_tac >> qspec_then `w:bytes32` mp_tac w2n_lt >> decide_tac
QED

(* Sites use natural bases; variables contain their word representations. *)
Definition ircf_alias_site_value_def:
  ircf_alias_site_value fn s G v <=>
    !ai root sz. MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
      ai.inst_outputs = [root] /\ ai.inst_operands = [Lit sz] /\
      ircf_alias fn root v ==>
      ?b. lookup_var v s = SOME (n2w b) /\
        lookup_var root s = SOME (n2w b) /\
        FLOOKUP s.vs_allocas ai.inst_id = SOME (b,w2n sz) /\
        FLOOKUP G v = SOME (b,w2n sz)
End

Theorem ircf_alias_site_alloca:
  ssa_form fn /\ ircf_size_coherent fn s /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [out] /\ inst.inst_operands = [Lit amount] /\
  exec_alloca inst s amount = OK t ==>
  ircf_alias_site_value fn t (step_prov PG G inst t) out
Proof
  strip_tac >> simp[ircf_alias_site_value_def] >> rpt strip_tac >>
  `root = out` by
    (irule ircf_alloca_alias_root >>
     metis_tac[ircf_alloca_of_def]) >>
  `ai = inst` by
    (irule ssa_outputs_same_inst >> gvs[fn_insts_def] >> metis_tac[MEM]) >>
  gvs[] >> rename1 `MEM inst (fn_insts fn)` >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  simp[exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (simp[update_var_def] >> strip_tac >> gvs[] >>
      simp[lookup_var_def, step_prov_def, set_prov_def,
           out_prov_def, FLOOKUP_UPDATE]) >>
  PairCases_on `x` >>
  `x1 = w2n amount` by metis_tac[ircf_size_coherent_def] >>
  simp[update_var_def] >> strip_tac >> gvs[] >>
  simp[lookup_var_def, step_prov_def,
       set_prov_def, out_prov_def, FLOOKUP_UPDATE]
QED
