Theory bodyInvIntCallPinsProps
Ancestors
  bodySim

Theorem intcall_args_body_inv_pins:
  body_inv tops ctx cenv cx ==> cenv_module_pins tops cenv
Proof
  simp[bodySimTheory.body_inv_split_def]
QED
