(* A piece of deploy_ctor_entry_reaches_body (ctorDeployLoweringEntry).
   ADMITTED, and open: the entry state's free memory pointer comes from the
   context plan of the optimised unit (cplan), while the constructor runs
   the unoptimised unit (dunit); nothing yet relates the plan's initial
   free memory pointer to dunit's static allocations.  How to close this
   (for the runtime entry too) is still being decided; the statement may
   gain premises then. *)
Theory ctorDeployLoweringEntryFmp
Ancestors
  ctorDeployLoweringDefs exprLoweringProps

Theorem deploy_ctor_entry_fmp_room:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final
   func s.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    s.vs_fmp = n2w cplan.cp_initial_fmp /\
    alloca_room dunit.cu_context func s ==>
    fmp_room dunit.cu_context func s
Proof
  cheat
QED
