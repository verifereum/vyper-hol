Theory lowerDloadScratchBudget
Ancestors
  lowerDloadAllocation lowerDloadControlPosition lowerDloadDefs irSupply
  lowerDloadStackBound
  venomInst contextCodegenRel list rich_list pred_set

Theorem ld_inst_scratch_cap_bound[local]:
  !a i outs b cap. lower_dload_inst_supply a i = (outs,b) /\
  (i.inst_opcode = ALLOCA ==> i.inst_id IN cap) ==>
  CARD (set (MAP (\j. j.inst_id)
    (FILTER (\j. j.inst_opcode = ALLOCA) outs)) DIFF cap) <=
  if i.inst_opcode = DLOAD then 1 else 0
Proof
  simp[lower_dload_inst_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  simp[DIFF_INSERT, CARD_INSERT, FINITE_DIFF] >>
  rw[]
QED

Theorem ld_cap_union_bound[local]:
  !X Y cap m n.
    FINITE X /\ FINITE Y /\ CARD (X DIFF cap) <= m /\ CARD (Y DIFF cap) <= n ==>
    CARD ((X UNION Y) DIFF cap) <= m+n
Proof
  rpt strip_tac >>
  `(X UNION Y) DIFF cap = (X DIFF cap) UNION (Y DIFF cap)` by SET_TAC[] >>
  `CARD ((X UNION Y) DIFF cap) <= CARD (X DIFF cap) + CARD (Y DIFF cap)` by
    metis_tac[CARD_UNION_LE, FINITE_DIFF] >> decide_tac
QED

Theorem ld_insts_scratch_cap_bound:
  !ins a outs b cap.
    lower_dload_insts_supply a ins = (outs,b) /\
    set (MAP (\i. i.inst_id) (FILTER (\i. i.inst_opcode = ALLOCA) ins)) SUBSET cap ==>
    CARD (set (MAP (\i. i.inst_id) (FILTER (\i. i.inst_opcode = ALLOCA) outs)) DIFF cap) <=
    LENGTH (FILTER (\i. i.inst_opcode = DLOAD) ins)
Proof
  Induct >- simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >>
  Cases_on `lower_dload_inst_supply a h` >>
  Cases_on `lower_dload_insts_supply r ins` >>
  simp[lower_dload_insts_supply_def] >> strip_tac >> gvs[] >>
  `set (MAP (\i. i.inst_id) (FILTER (\i. i.inst_opcode = ALLOCA) ins)) SUBSET cap /\
   (h.inst_opcode = ALLOCA ==> h.inst_id IN cap)` by
    (Cases_on `h.inst_opcode = ALLOCA` >> gvs[]) >>
  first_x_assum drule_all >> strip_tac >>
  drule_all ld_inst_scratch_cap_bound >> strip_tac >>
  simp[FILTER_APPEND, MAP_APPEND, LIST_TO_SET_APPEND, UNION_DIFF] >>
  qmatch_goalsub_abbrev_tac `CARD ((X UNION Y) DIFF cap)` >>
  `CARD ((X UNION Y) DIFF cap) <=
    (if h.inst_opcode = DLOAD then 1 else 0) +
    LENGTH (FILTER (\i. i.inst_opcode = DLOAD) ins)` by
    (irule ld_cap_union_bound >> simp[Abbr `X`, Abbr `Y`]) >>
  Cases_on `h.inst_opcode = DLOAD` >> gvs[]
QED

Theorem ld_blocks_scratch_cap_bound[local]:
  !bs a bs' b cap.
    lower_dload_blocks_supply a bs = (bs',b) /\
    set (MAP (\i. i.inst_id) (FILTER (\i. i.inst_opcode = ALLOCA)
      (fn_insts_blocks bs))) SUBSET cap ==>
    CARD (set (MAP (\i. i.inst_id) (FILTER (\i. i.inst_opcode = ALLOCA)
      (fn_insts_blocks bs'))) DIFF cap) <=
    LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts_blocks bs))
Proof
  Induct >- simp[lower_dload_blocks_supply_def, fn_insts_blocks_def] >>
  rpt gen_tac >>
  Cases_on `lower_dload_block_supply a h` >>
  Cases_on `lower_dload_blocks_supply r bs` >>
  simp[lower_dload_blocks_supply_def, fn_insts_blocks_def, FILTER_APPEND, MAP_APPEND, LIST_TO_SET_APPEND,
       UNION_SUBSET] >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  `lower_dload_insts_supply a h.bb_instructions = (q.bb_instructions,r)` by
    gvs[lower_dload_block_supply_def, AllCaseEqs()] >>
  drule_all ld_insts_scratch_cap_bound >> strip_tac >>
  simp[fn_insts_blocks_def, FILTER_APPEND, MAP_APPEND, LIST_TO_SET_APPEND] >>
  pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  match_mp_tac ld_cap_union_bound >> simp[]
QED

Theorem ld_function_scratch_cap_bound:
  lower_dload_function_supply a fn = (fn',b) ==>
  let cap = set (MAP (\i. i.inst_id) (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts fn'))) DIFF
            set (MAP (\i. i.inst_id) (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts fn))) in
  FINITE cap /\ CARD cap <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts fn))
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs(), Excl "CARD_DIFF"] >>
  strip_tac >> gvs[Excl "CARD_DIFF"] >>
  simp[fn_insts_def, fn_insts_blocks_def, Excl "CARD_DIFF"] >>
  irule ld_blocks_scratch_cap_bound >> metis_tac[SUBSET_REFL]
QED

Theorem ld_active_scratch_cap_member:
  active_inst fn' i t /\ i.inst_opcode = ALLOCA /\
  ~MEM i.inst_id (MAP (\j. j.inst_id) (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts fn))) ==>
  i.inst_id IN
    (set (MAP (\j. j.inst_id) (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts fn'))) DIFF
     set (MAP (\j. j.inst_id) (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts fn))))
Proof
  simp[active_inst_def, fn_insts_def, MEM_MAP, MEM_FILTER, MEM_FLAT] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[EL_MEM, o1PassContractTheory.fn_insts_blocks_MEM]
QED

Theorem ld_aligned_card_sum_bound:
  !w xs ys. LIST_REL (\A g. FINITE A /\ CARD A <= w g) xs ys ==>
    SUM (MAP CARD xs) <= SUM (MAP w ys)
Proof
  gen_tac >> Induct >> Cases_on `ys` >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> decide_tac
QED

Theorem ld_stack_scratch_budget:
  callee_first names C.ctx_functions /\ ld_stack_origin vs C stk fn s0 /\
  LIST_REL (\A g. FINITE A /\
    CARD A <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g)))
    sets (fn :: MAP (\f. f.cf_fn) stk) ==>
  SUM (MAP CARD sets) <= ctx_dload_count C
Proof
  strip_tac >>
  drule (BETA_RULE (Q.ISPEC `\g. LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g))`
    ld_aligned_card_sum_bound)) >> strip_tac >>
  drule_all ld_stack_dload_count_bound >> decide_tac
QED
