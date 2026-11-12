(*
 * Supply growth for transforms that take ids and names from an ir_supply,
 * and how a block list's names relate to its flattened instructions.
 *)

Theory irSupplyFreshProps
Ancestors
  venomFnScheduleRunner irSupply venomInst list

Theorem ir_supply_extends_refl:
  ir_supply_extends s s
Proof
  simp[ir_supply_extends_def, list_subset_def, EVERY_MEM]
QED

Theorem ir_supply_extends_trans:
  ir_supply_extends s1 s2 /\ ir_supply_extends s2 s3 ==> ir_supply_extends s1 s3
Proof
  simp[ir_supply_extends_def, list_subset_def, EVERY_MEM]
QED

Theorem fresh_inst_id_ir_supply_extends:
  fresh_inst_id s = (id,s') ==> ir_supply_extends s s'
Proof
  rw[fresh_inst_id_def] >>
  simp[ir_supply_extends_def, list_subset_def, EVERY_MEM]
QED

Theorem fresh_ir_var_ir_supply_extends:
  fresh_ir_var s = (v,s') ==> ir_supply_extends s s'
Proof
  strip_tac >> drule fresh_ir_var_contract >>
  simp[ir_supply_extends_def, list_subset_def, EVERY_MEM]
QED

(* ===== Names a function's instructions use ===== *)

Theorem blocks_ir_vars_flat:
  !bbs. FLAT (MAP block_ir_vars bbs) =
        FLAT (MAP inst_ir_vars (fn_insts_blocks bbs))
Proof
  Induct >> simp[fn_insts_blocks_def, block_ir_vars_def]
QED

Theorem blocks_ir_labels_mem:
  !bbs l. MEM l (FLAT (MAP block_ir_labels bbs)) <=>
          MEM l (MAP (\bb. bb.bb_label) bbs) \/
          MEM l (FLAT (MAP inst_ir_labels (fn_insts_blocks bbs)))
Proof
  Induct >> simp[fn_insts_blocks_def, block_ir_labels_def] >>
  rpt gen_tac >> eq_tac >> rw[] >> simp[]
QED
