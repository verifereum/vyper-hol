(* Code containment along a finite chain of compiler-state extensions. *)
Theory compilerChainCode
Ancestors fragExec compileEnv list

Theorem compiler_chain_extends:
  !ss sa. EVERY (\(a,b). cs_extends a b) (ZIP (FRONT (sa::ss),ss)) ==>
    cs_extends sa (LAST (sa::ss))
Proof
  Induct >> simp[cs_extends_refl] >> rpt strip_tac >>
  irule cs_extends_trans >> goal_assum (drule_at Any) >>
  first_x_assum irule >> simp[]
QED

Theorem compiler_chain_has_code:
  !ss sa func.
    EVERY (\(a,b). cs_extends a b) (ZIP (FRONT (sa::ss),ss)) /\
    fn_has_code sa (LAST (sa::ss)) func ==>
    EVERY (\(a,b). fn_has_code a b func) (ZIP (FRONT (sa::ss),ss))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `cs_extends h (LAST (h::ss))` by
    (irule compiler_chain_extends >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >> simp[] >>
  first_x_assum irule >> simp[]
QED
