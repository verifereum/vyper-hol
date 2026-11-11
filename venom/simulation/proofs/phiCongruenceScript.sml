(* Parallel PHI evaluation: observations use the original input states. *)
Theory phiCongruence
Ancestors
  venomExecSemantics venomState venomInst list

Theorem eval_phis_rel:
  !insts s t s1 R.
  (!s t x v. R s t ==> R (update_var x v s) (update_var x v t)) /\
  R s t /\
  (!inst. MEM inst insts /\ inst.inst_opcode = PHI ==>
     eval_one_phi s inst = eval_one_phi t inst) /\
  eval_phis s insts = OK s1 ==>
  ?t1. eval_phis t insts = OK t1 /\ R s1 t1
Proof
  Induct >> rpt gen_tac >- (simp[eval_phis_def] >> metis_tac[]) >>
  strip_tac >> Cases_on `h.inst_opcode = PHI`
  >- (fs[eval_phis_def] >>
      Cases_on `eval_one_phi s h` >> gvs[] >>
      PairCases_on `x` >>
      `eval_one_phi t h = SOME (x0,x1)` by metis_tac[MEM] >>
      Cases_on `eval_phis s insts` >> gvs[] >>
      last_x_assum (qspecl_then [`s`,`t`,`v`,`R`] mp_tac) >>
      impl_tac
      >- (simp[] >> metis_tac[]) >>
      strip_tac >> simp[] >> metis_tac[]) >>
  gvs[eval_phis_def] >> metis_tac[]
QED
