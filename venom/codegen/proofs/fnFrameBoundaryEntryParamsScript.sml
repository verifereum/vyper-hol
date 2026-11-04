Theory fnFrameBoundaryEntryParams
Ancestors
  frameRel frameViewFacts stackPlanGen stackPlanTypes stackModel
  callLayoutDefs venomExecSemantics venomState list rich_list

(* Installing the symbolic parameter names emits no code. *)
Theorem parameter_stack_fold:
  !insts ps.
    FOLDL (\s inst. s with ps_stack :=
      stack_push (Var (HD inst.inst_outputs)) s.ps_stack) ps insts =
    ps with ps_stack := ps.ps_stack ++
      MAP (\inst. Var (HD inst.inst_outputs)) insts
Proof
  Induct >> simp[stack_push_def, SNOC_APPEND] >>
  rpt gen_tac >> rewrite_tac[GSYM APPEND_ASSOC, APPEND]
QED
