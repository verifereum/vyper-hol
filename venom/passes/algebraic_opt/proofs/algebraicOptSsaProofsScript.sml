Theory algebraicOptSsaProofs
Ancestors
  algebraicOptDefs venomWf venomFnScheduleRunner

Theorem ao_preserves_ssa_form_proof:
  !sup fn fn' sup'.
    ssa_form fn /\
    ir_supply_covers_fn sup fn /\
    ao_transform_function_supply sup fn = (fn', sup') ==>
    ssa_form fn'
Proof
  cheat
QED
