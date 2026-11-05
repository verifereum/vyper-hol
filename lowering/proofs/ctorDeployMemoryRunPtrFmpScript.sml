(* The deployment unit has no DALLOCA (its raw unit passes
 * o1_source_unit_ok), so fmp_room, which only constrains the free memory
 * pointer when a DALLOCA is reachable, holds at every state of its
 * __deploy function.
 *)
Theory ctorDeployMemoryRunPtrFmp
Ancestors
  exprLoweringProps ptrDiscipline o1PipelineCorrect ctorDeployShape
  ctorDeployLoweringDefs

Theorem no_dalloca_fmp_room:
  !ctx func ss.
    ~ctx_has_dalloca ctx /\ MEM func ctx.ctx_functions ==>
    fmp_room ctx func ss
Proof
  rw[fmp_room_def] >>
  fs[ctx_has_dalloca_def, listTheory.EXISTS_MEM] >>
  metis_tac[]
QED

Theorem deploy_ctor_fmp_room:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final
   func ss.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) ==>
    fmp_room dunit.cu_context func ss
Proof
  rpt strip_tac >> irule no_dalloca_fmp_room >>
  reverse conj_tac >- fs[deploy_ctor_code_def] >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  simp[o1_source_unit_ok_no_dalloca]
QED
