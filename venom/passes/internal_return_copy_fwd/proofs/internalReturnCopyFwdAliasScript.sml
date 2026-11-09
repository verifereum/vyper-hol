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
