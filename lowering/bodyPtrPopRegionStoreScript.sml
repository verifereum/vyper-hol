Theory bodyPtrPopRegionStore
Ancestors
  bodyPtrPopRegionInvariant ptrDiscipline vyperStorage words pred_set vfmState venomState

Theorem pop_region_taint_clean_store:
  bs + type_slot_size tv <= dimword (:256) /\
  (w2n key < bs \/ bs + type_slot_size tv <= w2n key) /\
  pop_region_taint_ok st bs tv X ==>
  pop_region_taint_ok (update_storage key value st) bs tv
    (key_update X key {})
Proof
  strip_tac >> (irule pop_region_taint_frame >> qexistsl [`X`,`st`] >>
  simp[key_update_def, SUBSET_DEF] >>
  conj_tac
  >- (rpt strip_tac >>
      `i < dimword (:256) /\ i <> w2n key` by decide_tac >>
      `(n2w i:bytes32) <> key` by
        (strip_tac >>
         `w2n (n2w i:bytes32) = w2n key` by simp[] >>
         gvs[w2n_n2w]) >>
      simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]) >>
  rpt strip_tac >> gvs[])
QED

(* These are step_taint specializations with explicit backend-update cuts;
   they do not assume a store is successful merely from its opcode. *)
Theorem pop_region_taint_sstore_cut:
  inst.inst_opcode = SSTORE /\ inst.inst_operands = [addr;v] /\
  eval_operand addr s = SOME key /\ op_taint tn v = {} /\
  st' = update_storage key value st /\
  bs + type_slot_size tv <= dimword (:256) /\
  (w2n key < bs \/ bs + type_slot_size tv <= w2n key) /\
  pop_region_taint_ok st bs tv tn.t_stor ==>
  pop_region_taint_ok st' bs tv (step_taint inst s s' tn).t_stor
Proof
  strip_tac >>
  simp[step_taint_def, adopt_reset_def, store_taint_def] >>
  irule pop_region_taint_clean_store >> simp[]
QED

Theorem pop_region_taint_tstore_cut:
  inst.inst_opcode = TSTORE /\ inst.inst_operands = [addr;v] /\
  eval_operand addr s = SOME key /\ op_taint tn v = {} /\
  st' = update_storage key value st /\
  bs + type_slot_size tv <= dimword (:256) /\
  (w2n key < bs \/ bs + type_slot_size tv <= w2n key) /\
  pop_region_taint_ok st bs tv tn.t_trans ==>
  pop_region_taint_ok st' bs tv (step_taint inst s s' tn).t_trans
Proof
  strip_tac >>
  simp[step_taint_def, adopt_reset_def, store_taint_def] >>
  irule pop_region_taint_clean_store >> simp[]
QED
