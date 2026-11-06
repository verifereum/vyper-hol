Theory bodyPtrPopScalarStore
Ancestors
  bodyPtrPopRegionStore bodyPtrPopRegionInvariant compileEnv ptrDiscipline vyperStorage words pred_set
  vfmState venomState venomInst

val _ = Parse.hide "base";

(* No element dead bytes means the dynamic array's observer depends only
   on its header. One-slot full-word scalars are the intended consumers,
   but type_slot_size tv = 1 is unnecessary, so the interface also covers
   static multi-slot elements without dead bytes. The key may be anywhere
   in the payload: only aliasing the header is forbidden. *)
Theorem pop_scalar_array_dead_header:
  (!st0 bs0 j b. ~dead_bytes st0 bs0 tv j b) /\
  lookup_storage (n2w bs) st' = lookup_storage (n2w bs) st ==>
  (dead_bytes st' bs (ArrayTV tv (Dynamic n)) j b <=>
   dead_bytes st bs (ArrayTV tv (Dynamic n)) j b)
Proof
  strip_tac >> simp[Once dead_bytes_def] >>
  simp[Once dead_bytes_def]
QED

Theorem pop_scalar_array_clean_store:
  (!st0 bs0 j b. ~dead_bytes st0 bs0 tv j b) /\
  key <> (n2w bs : bytes32) /\
  pop_region_taint_ok st bs (ArrayTV tv (Dynamic n)) X ==>
  pop_region_taint_ok (update_storage key value st) bs
    (ArrayTV tv (Dynamic n)) (key_update X key {})
Proof
  strip_tac >>
  `lookup_storage (n2w bs) (update_storage key value st) =
     lookup_storage (n2w bs) st` by
    simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM] >>
  drule_all pop_scalar_array_dead_header >> strip_tac >>
  gvs[pop_region_taint_ok_def, key_update_def] >> metis_tac[]
QED

Theorem pop_scalar_array_sstore_cut:
  inst.inst_opcode = SSTORE /\ inst.inst_operands = [addr;v] /\
  eval_operand addr s = SOME key /\ op_taint tn v = {} /\
  st' = update_storage key value st /\
  (!st0 bs0 j b. ~dead_bytes st0 bs0 tv j b) /\
  key <> (n2w bs : bytes32) /\
  pop_region_taint_ok st bs (ArrayTV tv (Dynamic n)) tn.t_stor ==>
  pop_region_taint_ok st' bs (ArrayTV tv (Dynamic n))
    (step_taint inst s s' tn).t_stor
Proof
  strip_tac >>
  simp[step_taint_def, adopt_reset_def, store_taint_def] >>
  irule pop_scalar_array_clean_store >> simp[]
QED

Theorem pop_scalar_array_tstore_cut:
  inst.inst_opcode = TSTORE /\ inst.inst_operands = [addr;v] /\
  eval_operand addr s = SOME key /\ op_taint tn v = {} /\
  st' = update_storage key value st /\
  (!st0 bs0 j b. ~dead_bytes st0 bs0 tv j b) /\
  key <> (n2w bs : bytes32) /\
  pop_region_taint_ok st bs (ArrayTV tv (Dynamic n)) tn.t_trans ==>
  pop_region_taint_ok st' bs (ArrayTV tv (Dynamic n))
    (step_taint inst s s' tn).t_trans
Proof
  strip_tac >>
  simp[step_taint_def, adopt_reset_def, store_taint_def] >>
  irule pop_scalar_array_clean_store >> simp[]
QED
