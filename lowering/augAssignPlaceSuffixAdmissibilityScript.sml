(* Pointwise RHS success suffices for the gas-insensitive memory suffix. *)
Theory augAssignPlaceSuffixAdmissibility
Ancestors
  stmtSimAugAssignPlaceMemory gasContext vyperState

Theorem aug_place_memory_pointwise_tail:
  gas_admissible
    (bind a (\rhs. bind (lift_sum (bv rhs))
      (write_place cx (MemoryPlace id path)))) A st /\
  a (st with gas_obs := gs) = (INL rhs,ee) ==>
  gas_admissible
    (bind (lift_sum (bv rhs)) (write_place cx (MemoryPlace id path))) A ee
Proof
  strip_tac >>
  Cases_on `bind (lift_sum (bv rhs)) (write_place cx (MemoryPlace id path)) ee` >>
  rename1 `_ = (res,ff)` >>
  `A res` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def] >>
     disch_then (qspec_then `gs` mp_tac) >>
     simp[bind_def] >> gvs[bind_def]) >>
  drule aug_place_pure_suffix_gas_obs >>
  simp[gas_admissible_def] >> metis_tac[]
QED
