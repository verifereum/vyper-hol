(* ALLOCA resource packaging valid also when an allocation site is reused. *)
Theory storageNormalizationAllocPtr
Ancestors
  allocationPtr bodyPtrDefs loweringPosts venomInst venomExecSemantics
  ptrSafeRun ptrDiscipline finite_map words

Theorem alloca_step_buffer_resources:
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword(:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
  ?b. FLOOKUP s1.vs_allocas id = SOME (b,n) /\
    b+n < dimword(:256) /\ eval_operand (Var out) s1 = SOME (n2w b) /\
    ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) out s1 n /\
    (!p sz. p <> out /\ ptr_covers G tn p s sz ==>
      ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
        (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) p s1 sz)
Proof
  strip_tac >> drule_all alloca_step_site >> strip_tac >>
  qexists_tac `b` >> simp[] >> conj_tac
  >- (irule alloca_step_ptr_covers >> metis_tac[]) >>
  rpt strip_tac >> irule alloca_step_old_ptr_covers >> metis_tac[]
QED
