(* Static capacity for scratch allocation sites, independent of runtime support. *)
Theory lowerDloadPtrBudget
Ancestors
  lowerDloadDefs irSupply venomInst unitShapeDefs list rich_list pred_set

Theorem dload_inst_scratch_count[local]:
  lower_dload_inst_supply q i = (xs,q') /\ i.inst_id IN A ==>
  LENGTH (FILTER (\j. j.inst_opcode = ALLOCA /\ j.inst_id NOTIN A) xs) <=
  (if i.inst_opcode = DLOAD then 1 else 0)
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >> simp[] >>
      rw[] ) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >> simp[]) >>
  simp[lower_dload_inst_supply_def] >> rpt strip_tac >> gvs[]
QED

Theorem dload_insts_scratch_count[local]:
  !is q xs q'.
  lower_dload_insts_supply q is = (xs,q') /\
  (!i. MEM i is ==> i.inst_id IN A) ==>
  LENGTH (FILTER (\j. j.inst_opcode = ALLOCA /\ j.inst_id NOTIN A) xs) <=
  LENGTH (FILTER (\i. i.inst_opcode = DLOAD) is)
Proof
  Induct >> simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >> simp[AllCaseEqs()] >> strip_tac >>
  `h.inst_id IN A` by metis_tac[] >>
  drule_all dload_inst_scratch_count >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  gvs[FILTER_APPEND] >> Cases_on `h.inst_opcode = DLOAD` >>
  gvs[] >> decide_tac
QED

Theorem dload_blocks_scratch_count[local]:
  !bbs q cs q'.
  lower_dload_blocks_supply q bbs = (cs,q') /\
  (!i. MEM i (fn_insts_blocks bbs) ==> i.inst_id IN A) ==>
  LENGTH (FILTER (\j. j.inst_opcode = ALLOCA /\ j.inst_id NOTIN A)
    (fn_insts_blocks cs)) <=
  LENGTH (FILTER (\i. i.inst_opcode = DLOAD)
    (fn_insts_blocks bbs))
Proof
  Induct >> simp[lower_dload_blocks_supply_def, fn_insts_blocks_def] >>
  rpt gen_tac >> simp[lower_dload_block_supply_def, AllCaseEqs()] >>
  strip_tac >>
  `!i. MEM i h.bb_instructions ==> i.inst_id IN A` by metis_tac[MEM_APPEND] >>
  drule_all dload_insts_scratch_count >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  gvs[fn_insts_blocks_def, FILTER_APPEND] >> decide_tac
QED

Theorem dload_function_scratch_count:
  lower_dload_function_supply q fn = (gn,q') /\
  (!i. MEM i (fn_insts fn) ==> i.inst_id IN A) ==>
  LENGTH (FILTER (\i. i.inst_opcode = ALLOCA /\ i.inst_id NOTIN A) (fn_insts gn)) <=
  LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts fn))
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs(), fn_insts_def] >>
  rpt strip_tac >> gvs[] >> drule_all dload_blocks_scratch_count >> simp[]
QED

Theorem dload_function_scratch_budget:
  !q fn gn q' A scratch.
  lower_dload_function_supply q fn = (gn,q') /\
  (!i. MEM i (fn_insts fn) ==> i.inst_id IN A) /\
  scratch SUBSET set (MAP (\i. i.inst_id)
    (FILTER (\i. i.inst_opcode = ALLOCA /\ i.inst_id NOTIN A) (fn_insts gn))) ==>
  FINITE scratch /\ CARD scratch <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts fn))
Proof
  rpt gen_tac >> strip_tac >> drule_all dload_function_scratch_count >> strip_tac >>
  qmatch_asmsub_abbrev_tac `scratch SUBSET set ids` >>
  `FINITE scratch` by metis_tac[SUBSET_FINITE, FINITE_LIST_TO_SET] >>
  `CARD scratch <= CARD (set ids)` by (irule CARD_SUBSET >> simp[]) >>
  `CARD (set ids) <= LENGTH ids` by simp[CARD_LIST_TO_SET] >>
  gvs[Abbr `ids`] >> decide_tac
QED
