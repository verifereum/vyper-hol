(*
 * Instruction-ID uniqueness lemmas for Venom functions.
 *
 * Shared across Venom passes and analyses that map an instruction ID
 * back to its unique record in fn_insts under fn_inst_ids_distinct.
 *)

Theory venomInstIdsProps
Ancestors
  venomWf venomInst list

Theorem fn_insts_blocks_map_id:
  !bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
        FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

Theorem fn_inst_ids_distinct_all_distinct:
  !fn. fn_inst_ids_distinct fn ==>
       ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))
Proof
  rw[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_map_id]
QED

Theorem fn_inst_ids_distinct_inj:
  !fn x y. fn_inst_ids_distinct fn /\ MEM x (fn_insts fn) /\
           MEM y (fn_insts fn) /\ x.inst_id = y.inst_id ==> x = y
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    metis_tac[fn_inst_ids_distinct_all_distinct] >>
  gvs[MEM_EL] >>
  `EL n (MAP (\i. i.inst_id) (fn_insts fn)) =
   EL n' (MAP (\i. i.inst_id) (fn_insts fn))` by gvs[EL_MAP] >>
  `n = n'` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >> gvs[]
QED
