(*
 * Freshness bookkeeping for transforms that take ids and names from an
 * ir_supply: what was taken is outside the old supply and recorded in the
 * new one, and the supply only grows.
 *)

Theory irSupplyFreshProps
Ancestors
  venomFnScheduleRunner irSupply venomInst list

(* Going from supply list u to u', the list xs became xs': every new
   member was outside u and is recorded in u', and distinctness of xs
   (when xs is covered by u) carries over to xs'. *)
Definition ir_fresh_ext_def:
  ir_fresh_ext (u:'a list) u' xs xs' <=>
    (!v. MEM v u ==> MEM v u') /\
    (!v. MEM v xs' ==> MEM v xs \/ (~MEM v u /\ MEM v u')) /\
    (ALL_DISTINCT xs /\ (!v. MEM v xs ==> MEM v u) ==> ALL_DISTINCT xs')
End

Theorem ir_fresh_ext_refl:
  ir_fresh_ext u u xs xs
Proof
  simp[ir_fresh_ext_def]
QED

Theorem ir_fresh_ext_append:
  ir_fresh_ext u u1 xs1 ys1 /\ ir_fresh_ext u1 u2 xs2 ys2 ==>
  ir_fresh_ext u u2 (xs1 ++ xs2) (ys1 ++ ys2)
Proof
  rewrite_tac[ir_fresh_ext_def, ALL_DISTINCT_APPEND, MEM_APPEND] >>
  strip_tac >> rpt conj_tac
  >- metis_tac[]
  >- metis_tac[]
  >> strip_tac >>
  `ALL_DISTINCT ys1` by metis_tac[] >>
  `ALL_DISTINCT ys2` by metis_tac[] >>
  simp[] >> metis_tac[]
QED

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

Theorem fn_insts_blocks_outputs_ir_vars:
  !bbs v. MEM v (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))) ==>
          MEM v (FLAT (MAP block_ir_vars bbs))
Proof
  Induct >> simp[fn_insts_blocks_def, MAP_APPEND, FLAT_APPEND] >>
  rw[] >> gvs[block_ir_vars_def, inst_ir_vars_def, MEM_FLAT, MEM_MAP] >>
  metis_tac[MEM_APPEND]
QED

Theorem fn_insts_blocks_inst_ids:
  !bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
        FLAT (MAP block_ir_inst_ids bbs)
Proof
  Induct >> simp[fn_insts_blocks_def, block_ir_inst_ids_def]
QED

Theorem blocks_inst_ids_flat:
  !bbs. FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs) =
        FLAT (MAP block_ir_inst_ids bbs)
Proof
  Induct >> simp[block_ir_inst_ids_def]
QED

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
