Theory concretizePtrDallocaRuntimeSteps
Ancestors
  concretizePtrDallocaAffine concretizePtrObservationInterface
  concretizePtrDallocaBoundaryProbes concretizePtrBPReverse
  concretizePtrDallocaGhostInterface o1FrameLockstep
  ptrDiscipline venomState venomInst finite_map pred_set list

(* Only demanded arithmetic operands need scalar agreement.  In particular,
   this does not assert equality of all syntactically nonpointer variables. *)
Theorem ptr_dalloca_runtime_affine_values:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  inst.inst_operands = [a;b] /\ FDOM G SUBSET fn_pv P fn /\
  ptr_dalloca_ghost_vars G tn.t_var s Gt tnt.t_var t /\
  ptr_ledger_erases dyn births TG G /\
  ptr_mixed_vars births positions TG tn f g s t /\
  s.vs_labels = t.vs_labels /\
  (!op. MEM op [a;b] ==> ptr_nonopaque_operand f op /\ op_taint tn op = {}) /\
  out_prov PGt Gt inst t = SOME site ==>
  !op. MEM op [a;b] ==> eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `~(?v w. a = Var v /\ b = Var w /\
           v IN fn_pv P fn /\ w IN fn_pv P fn)` by
    metis_tac[ptr_reverse_affine] >>
  `!op. MEM op [a;b] /\ op_prov G op = NONE ==>
        eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule ptr_mixed_scalar_eval >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  gvs[out_prov_def, ptr_dalloca_ghost_vars_def] >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[first_prov_def, op_prov_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[eval_operand_def] >>
  fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[eval_operand_def]
QED
