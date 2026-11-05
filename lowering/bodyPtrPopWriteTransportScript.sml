Theory bodyPtrPopWriteTransport
Ancestors
  bodyPtrPopRegionInvariant ptrDiscipline venomInst venomState words pred_set

(* Operational clients must discharge both retained-byte preservation and
   replacement-byte safety. No compatibility of typed writes is asserted. *)
Theorem pop_region_taint_store_transport:
  pop_region_taint_ok st bs tv X /\
  (!k b. (k,b) IN X /\ k <> key /\ bs <= w2n k /\
         w2n k < bs + type_slot_size tv /\ b < 32 /\
         dead_bytes st bs tv (w2n k) b ==>
         dead_bytes st' bs tv (w2n k) b) /\
  (!b. b IN M /\ bs <= w2n key /\
       w2n key < bs + type_slot_size tv /\ b < 32 ==>
       dead_bytes st' bs tv (w2n key) b) ==>
  pop_region_taint_ok st' bs tv (key_update X key M)
Proof
  rewrite_tac[pop_region_taint_key_update] >>
  simp[pop_region_taint_ok_def] >> metis_tac[]
QED

Theorem pop_region_taint_sstore_transport:
  inst.inst_opcode = SSTORE /\ inst.inst_operands = [a;v] /\
  eval_operand a s = SOME key /\
  pop_region_taint_ok st bs tv tn.t_stor /\
  (!k b. (k,b) IN tn.t_stor /\ k <> key /\ bs <= w2n k /\
         w2n k < bs + type_slot_size tv /\ b < 32 /\
         dead_bytes st bs tv (w2n k) b ==>
         dead_bytes st' bs tv (w2n k) b) /\
  (!b. b IN op_taint tn v /\ bs <= w2n key /\
       w2n key < bs + type_slot_size tv /\ b < 32 ==>
       dead_bytes st' bs tv (w2n key) b) ==>
  pop_region_taint_ok st' bs tv (step_taint inst s s' tn).t_stor
Proof
  strip_tac >> simp[step_taint_def, adopt_reset_def, store_taint_def] >>
  irule pop_region_taint_store_transport >> simp[] >> qexists_tac `st` >> simp[]
QED

Theorem pop_region_taint_tstore_transport:
  inst.inst_opcode = TSTORE /\ inst.inst_operands = [a;v] /\
  eval_operand a s = SOME key /\
  pop_region_taint_ok st bs tv tn.t_trans /\
  (!k b. (k,b) IN tn.t_trans /\ k <> key /\ bs <= w2n k /\
         w2n k < bs + type_slot_size tv /\ b < 32 /\
         dead_bytes st bs tv (w2n k) b ==>
         dead_bytes st' bs tv (w2n k) b) /\
  (!b. b IN op_taint tn v /\ bs <= w2n key /\
       w2n key < bs + type_slot_size tv /\ b < 32 ==>
       dead_bytes st' bs tv (w2n key) b) ==>
  pop_region_taint_ok st' bs tv (step_taint inst s s' tn).t_trans
Proof
  strip_tac >> simp[step_taint_def, adopt_reset_def, store_taint_def] >>
  irule pop_region_taint_store_transport >> simp[] >> qexists_tac `st` >> simp[]
QED
