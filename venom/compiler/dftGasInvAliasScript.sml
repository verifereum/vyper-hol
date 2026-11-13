Theory dftGasInvAlias
Ancestors
  contextCodegenRelProps contextCodegenRel

Theorem same_after_assigns_older_tail:
  !xs ys a b. same_after_assigns xs a b ==>
    same_after_assigns (xs ++ ys) a b
Proof
  Induct_on `xs`
  >- simp[same_after_assigns_def] >>
  rpt gen_tac >> Cases_on `a = b` >- simp[] >>
  simp[same_after_assigns_def] >>
  Cases_on `step_back_assign h a` >>
  Cases_on `step_back_assign h b` >>
  simp[]
QED
