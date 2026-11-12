Theory bodyPtrIfExpAllocationSite
Ancestors allocationPtr ptrDiscipline venomInst

(* Exact extent is inherited from the framed site theorem, including reuse. *)
Theorem ifexp_alloca_step_exact_provenance:
  !ctx func ce cx es s id n out u PG G.
    stmt_state_rel ctx func ce cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
    ?b. FLOOKUP u.vs_allocas id = SOME (b,n) /\
        b + n < dimword (:256) /\
        eval_operand (Var out) u = SOME (n2w b) /\
        op_prov (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
          (Var out) = SOME (b,n)
Proof
  rpt strip_tac >> drule_all alloca_step_site >> strip_tac >>
  qexists `b` >>
  simp[op_prov_def, step_prov_def, out_prov_def, set_prov_def,
       mk_inst_def, finite_mapTheory.FLOOKUP_UPDATE]
QED
