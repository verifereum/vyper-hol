Theory bodyPtrPopCompilerBoundary
Ancestors
  bodyPtrPopBoundaryContract bodyPtrPopGuardedWindow compileEnv list

(* Open blocks require a residual check because more instructions may be
   appended; finalized blocks only require complete-window exclusion. *)
Definition pop_comp_boundary_def:
  pop_comp_boundary s <=>
    pop_boundary_clean s.cs_current_insts /\
    EVERY (\bb. ~occurs5 pop_guarded5 bb.bb_instructions) s.cs_blocks
End

Theorem pop_comp_boundary_new_block:
  pop_comp_boundary sa /\ new_block label sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[new_block_def] >> rpt strip_tac >> gvs[] >>
  gvs[pop_comp_boundary_def, pop_boundary_clean_windows]
QED

Theorem pop_comp_boundary_return:
  pop_comp_boundary sa /\ comp_return x sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[comp_return_def] >> rpt strip_tac >> gvs[]
QED

Theorem pop_comp_boundary_bind:
  (!s x t. pop_comp_boundary s /\ f s = (x,t) ==> pop_comp_boundary t) /\
  (!x s y t. pop_comp_boundary s /\ k x s = (y,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\ comp_bind f k sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[comp_bind_def] >> pairarg_tac >> rpt strip_tac >> gvs[] >>
  `pop_comp_boundary cs'` by
    (qpat_x_assum `!s x t. _ /\ f s = _ ==> _` irule >>
     goal_assum drule >> simp[]) >>
  qpat_x_assum `!x s y t. _ /\ k x s = _ ==> _` irule >>
  qexistsl_tac [`cs'`,`a`,`r`] >> simp[]
QED
