Theory bodyPtrPopWriteCompatibility
Ancestors
  bodyPtrDefs ptrDiscipline venomInst venomState pred_set words

val _ = Parse.hide "base";

(* Separate retained and replacement taint: neither clause asserts that
   an arbitrary typed write actually preserves a captured region. *)
Theorem pop_key_update_dead_iff:
  (!k b. (k,b) IN key_update X key M /\
         base <= w2n k /\ w2n k < base + type_slot_size tv ==>
         dead_bytes st' base tv (w2n k) b) <=>
  (!k b. (k,b) IN X /\ k <> key /\
         base <= w2n k /\ w2n k < base + type_slot_size tv ==>
         dead_bytes st' base tv (w2n k) b) /\
  (!b. b IN M /\ base <= w2n key /\
       w2n key < base + type_slot_size tv ==>
       dead_bytes st' base tv (w2n key) b)
Proof
  simp[key_update_def] >> metis_tac[]
QED

Theorem pop_sstore_dead:
  inst.inst_opcode = SSTORE /\ inst.inst_operands = [a;v] /\
  eval_operand a s = SOME key /\
  (!k b. (k,b) IN tn.t_stor /\ k <> key /\
         base <= w2n k /\ w2n k < base + type_slot_size tv ==>
         dead_bytes st' base tv (w2n k) b) /\
  (!b. b IN op_taint tn v /\ base <= w2n key /\
       w2n key < base + type_slot_size tv ==>
       dead_bytes st' base tv (w2n key) b) ==>
  !k b. (k,b) IN (step_taint inst s s' tn).t_stor /\
        base <= w2n k /\ w2n k < base + type_slot_size tv ==>
        dead_bytes st' base tv (w2n k) b
Proof
  strip_tac >>
  simp[step_taint_def, adopt_reset_def, store_taint_def] >>
  simp[pop_key_update_dead_iff]
QED
