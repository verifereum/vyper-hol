Theory vyperStringScopeTest
Ancestors
  vyperState finite_map

(* A new inner binding shadows an outer binding; another name does not. *)
Theorem string_scope_shadow_and_fallthrough:
  lookup_scopes "x"
    [FEMPTY |+ ("x", inner); FEMPTY |+ ("x", outer)] = SOME inner /\
  lookup_scopes "x"
    [FEMPTY |+ ("y", other); FEMPTY |+ ("x", inner)] = SOME inner
Proof
  simp[lookup_scopes_def, FLOOKUP_UPDATE]
QED
