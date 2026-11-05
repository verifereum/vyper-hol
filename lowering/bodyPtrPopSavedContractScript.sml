Theory bodyPtrPopSavedContract
Ancestors
  bodyPtrPopRegionInvariant bodyPtrDefs compileEnv words pred_set
  ptrDiscipline vyperValue vfmState

(* Endpoint projection only, NOT a Pop counterexample.  The dynamic parent
   is empty at return.  Its dead payload may gain taint without ghost_kept
   noticing: that predicate constrains variables and memory, not storage.
   Omitted here: source evaluation, vv_post/expr_post, gas_outcome_ptr,
   body_inv/expr_body_pre, and an actual declared_storage_region witness.
   Thus the parent dead-byte set is not asserted to equal storage_dead cx.
   Operand freshness and its ghost equality remain in ghost_kept unchanged.
   The entry child bound holds for empty storage taint, while at return it
   does not.  No raw-agreement implication is tested in this theory. *)
Theorem pop_saved_endpoint_projection_obstruction:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  tn0.t_stor = {} ==>
  ghost_kept cenv es sa G0 tn0 s0 G
    (tn with t_stor := {(1w,0)}) /\
  pop_region_taint_ok st 1 (BaseTV (UintT 256)) tn0.t_stor /\
  {(1w:bytes32,0:num)} SUBSET
    {(k,b) | dead_bytes (update_storage 0w 0w st) 0
      (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (w2n k) b} /\
  ~pop_region_taint_ok (update_storage 0w 0w st) 1
    (BaseTV (UintT 256)) {(1w,0)}
Proof
  simp[ghost_kept_def, op_taint_def, pop_region_taint_ok_def,
       SUBSET_DEF, dead_bytes_def, type_slot_size_def,
       lookup_storage_def, update_storage_def,
       dimword_def, SF wordsLib.SIZES_ss] >>
  strip_tac >> conj_tac >> first_assum ACCEPT_TAC
QED
