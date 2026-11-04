Theory algebraicOptWfProofs
Ancestors
  algebraicOptDefs venomWf venomFnScheduleRunner unitShapeDefs

Theorem ao_preserves_wf_function_proof:
  !sup fn fn' sup'.
    wf_function fn /\
    fn_inst_wf fn /\
    EVERY label_positions_ok (fn_insts fn) /\
    ir_supply_inst_ok sup /\
    ir_supply_covers_fn sup fn /\
    ao_transform_function_supply sup fn = (fn', sup') ==>
    wf_function fn'
Proof
  cheat
QED
