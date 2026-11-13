(* Projection-only computation stages for the actual runtime function. *)
Theory bodyPtrBopInCodeInventory
Ancestors bodyPtrBopInUnit bodyPtrBopInUnitBody bodyPtrBopInUnitPackaging
  moduleLowering emitHelper venomWf ptrDiscipline list

Theorem equality_dispatch_id_inventory:
  MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
    (equality_dispatch_state sel).cs_blocks =
    [[8]; [4; 5; 6; 7]; [0; 1; 2; 3]]
Proof
  EVAL_TAC
QED

Theorem equality_bodies_id_inventory:
  MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
    (equality_bodies_state sel).cs_blocks =
    [[9]; [8]; [4; 5; 6; 7]; [0; 1; 2; 3]]
Proof
  EVAL_TAC
QED

Theorem equality_runtime_id_inventory:
  MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
    (equality_runtime_function sel).fn_blocks =
    [[0;1;2;3]; [4;5;6;7]; [8]; [9];
     [10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26]; [27]]
Proof
  EVAL_TAC
QED

Theorem equality_runtime_ids_distinct:
  fn_inst_ids_distinct (equality_runtime_function sel)
Proof
  rewrite_tac[fn_inst_ids_distinct_def, equality_runtime_id_inventory] >>
  EVAL_TAC
QED

Theorem equality_runtime_no_dalloca:
  ~ctx_has_dalloca (equality_runtime_context sel)
Proof
  EVAL_TAC >> simp[venomInstTheory.fn_insts_blocks_def]
QED
