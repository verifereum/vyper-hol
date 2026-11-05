(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   ADMITTED until proved. *)
Theory ctorDeployLoweringCode
Ancestors
  ctorDeployLoweringDefs

(* With a constructor, the deploy unit is compile_generate_deploy's, laid
   out as deploy_ctor_code names it. *)
Theorem deploy_ctor_code_exists:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx
   exts ints fb cf.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    classify_functions tops = (exts, ints, fb, SOME cf) ==>
    ?body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func.
      deploy_ctor_code tops rpolicy runtime_bc dunit
        (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func)
Proof
  cheat
QED
