Theory lowerDloadControlPosition
Ancestors
  o1ContractLowerDload list rich_list

(* Position inversion is lower_dload_insts_supply_position in the ancestor.
   Retain its offset witness rather than duplicating that theorem. *)
Theorem lower_dload_insts_supply_segment_index:
  lower_dload_insts_supply a pre = (p,a1) /\
  lower_dload_inst_supply a1 i = (c,a2) /\
  lower_dload_insts_supply a2 post = (tail,b) /\
  lower_dload_insts_supply a ins = (outs,b) /\
  ins = pre ++ i::post /\ k < LENGTH c ==>
  EL (LENGTH p + k) outs = EL k c /\
  EL (LENGTH pre) ins = i
Proof
  strip_tac >>
  drule_all lower_dload_insts_supply_segment_reconstruct >>
  strip_tac >> gvs[] >>
  simp[EL_APPEND1, EL_APPEND2]
QED
