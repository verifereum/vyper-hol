Theory makeSsaCurrentOccurrence
Ancestors
  venomWf venomInst list

Theorem current_filter_single[local]:
  !xs x y. LENGTH (FILTER P xs) <= 1 /\ MEM x xs /\ MEM y xs /\
    P x /\ P y ==> x = y
Proof
  rpt strip_tac >>
  `MEM x (FILTER P xs) /\ MEM y (FILTER P xs)` by simp[MEM_FILTER] >>
  Cases_on `FILTER P xs` >> gvs[] >>
  Cases_on `t` >> gvs[]
QED

Theorem current_single_def_block[local]:
  !bbs a b i j.
    LENGTH (FILTER (\i. MEM v i.inst_outputs)
      (FLAT (MAP (\bb. bb.bb_instructions) bbs))) <= 1 /\
    MEM a bbs /\ MEM b bbs /\ MEM i a.bb_instructions /\
    MEM j b.bb_instructions /\ MEM v i.inst_outputs /\
    MEM v j.inst_outputs ==> a = b
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[FILTER_APPEND_DISTRIB] >> rpt strip_tac >> gvs[]
  >- (`MEM i (FILTER (\i. MEM v i.inst_outputs) a.bb_instructions)` by simp[MEM_FILTER] >>
      `MEM j (FILTER (\i. MEM v i.inst_outputs)
        (FLAT (MAP (\bb. bb.bb_instructions) bbs)))` by
        (simp[MEM_FILTER, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
      Cases_on `FILTER (\i. MEM v i.inst_outputs) a.bb_instructions` >>
      Cases_on `FILTER (\i. MEM v i.inst_outputs)
        (FLAT (MAP (\bb. bb.bb_instructions) bbs))` >> gvs[])
  >- (`MEM j (FILTER (\i. MEM v i.inst_outputs) b.bb_instructions)` by simp[MEM_FILTER] >>
      `MEM i (FILTER (\i. MEM v i.inst_outputs)
        (FLAT (MAP (\bb. bb.bb_instructions) bbs)))` by
        (simp[MEM_FILTER, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
      Cases_on `FILTER (\i. MEM v i.inst_outputs) b.bb_instructions` >>
      Cases_on `FILTER (\i. MEM v i.inst_outputs)
        (FLAT (MAP (\bb. bb.bb_instructions) bbs))` >> gvs[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem current_insts_flat[local]:
  !bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

Theorem current_single_def_occurrence:
  LENGTH (FILTER (\i. MEM v i.inst_outputs) (fn_insts fn)) <= 1 /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  MEM i a.bb_instructions /\ MEM j b.bb_instructions /\
  MEM v i.inst_outputs /\ MEM v j.inst_outputs ==> a = b /\ i = j
Proof
  simp[fn_insts_def, current_insts_flat] >> rpt strip_tac
  >- (irule current_single_def_block >> metis_tac[]) >>
  irule current_filter_single >>
  qexists_tac `\i. MEM v i.inst_outputs` >>
  qexists_tac `FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks)` >>
  simp[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED
