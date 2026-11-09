Theory lowerDloadConfiguredCaps
Ancestors
  lowerDloadConfiguredSelection lowerDloadSupplySegment o1ContractLowerDload
  lowerDloadDefs venomInst o1PassContract list pred_set

Theorem lower_dload_inst_supply_alloca_cap[local]:
  lower_dload_inst_supply a i = (code,b) ==>
  CARD (set (MAP (\j. j.inst_id)
    (FILTER (\j. j.inst_opcode = ALLOCA) code)) DIFF {i.inst_id}) <=
  if i.inst_opcode = DLOAD then 1 else 0
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >> simp[CARD_DIFF]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[]) >>
  simp[lower_dload_inst_supply_def] >> strip_tac >> gvs[] >>
  Cases_on `i.inst_opcode = ALLOCA` >> simp[]
QED

Theorem lower_dload_configured_cap_finite:
  lower_dload_function_supply a f = (g,b) ==>
  FINITE (set (MAP (\i. i.inst_id)
    (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts g))) DIFF
    set (MAP (\i. i.inst_id) (fn_insts f)))
Proof
  simp[]
QED

Theorem cap_union_diff_bound[local]:
  !X Y s t. FINITE X /\ FINITE Y ==>
  CARD ((X UNION Y) DIFF (s UNION t)) <=
    CARD (X DIFF s) + CARD (Y DIFF t)
Proof
  rpt gen_tac >> strip_tac >>
  `((X UNION Y) DIFF (s UNION t)) SUBSET
    ((X DIFF s) UNION (Y DIFF t))` by SET_TAC[] >>
  `CARD ((X UNION Y) DIFF (s UNION t)) <=
    CARD ((X DIFF s) UNION (Y DIFF t))` by
    (irule CARD_SUBSET >> simp[]) >>
  `CARD ((X DIFF s) UNION (Y DIFF t)) <=
    CARD (X DIFF s) + CARD (Y DIFF t)` by
    (irule CARD_UNION_LE >> simp[]) >> decide_tac
QED

Theorem lower_dload_insts_supply_cap_bound[local]:
  !ins a outs b. lower_dload_insts_supply a ins = (outs,b) ==>
  CARD (set (MAP (\j. j.inst_id)
    (FILTER (\j. j.inst_opcode = ALLOCA) outs)) DIFF
    set (MAP (\j. j.inst_id) ins)) <=
  LENGTH (FILTER (\j. j.inst_opcode = DLOAD) ins)
Proof
  Induct >- simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >>
  Cases_on `lower_dload_inst_supply a h` >>
  Cases_on `lower_dload_insts_supply r ins` >>
  simp[lower_dload_insts_supply_def, Excl "CARD_DIFF"] >> strip_tac >>
  gvs[Excl "CARD_DIFF"] >>
  first_x_assum drule >> strip_tac >>
  drule lower_dload_inst_supply_alloca_cap >> strip_tac >>
  `{h.inst_id} UNION set (MAP (\j. j.inst_id) ins) =
    h.inst_id INSERT set (MAP (\j. j.inst_id) ins)` by SET_TAC[] >>
  qspecl_then [`set (MAP (\j. j.inst_id) (FILTER (\j. j.inst_opcode = ALLOCA) q))`,
               `set (MAP (\j. j.inst_id) (FILTER (\j. j.inst_opcode = ALLOCA) q'))`,
               `{h.inst_id}`, `set (MAP (\j. j.inst_id) ins)`]
    mp_tac cap_union_diff_bound >>
  simp[Excl "CARD_DIFF", FILTER_APPEND_DISTRIB, MAP_APPEND] >>
  Cases_on `h.inst_opcode = DLOAD` >> gvs[Excl "CARD_DIFF"] >> decide_tac
QED

Theorem lower_dload_blocks_supply_cap_bound[local]:
  !bs a gs b. lower_dload_blocks_supply a bs = (gs,b) ==>
  CARD (set (MAP (\j. j.inst_id)
    (FILTER (\j. j.inst_opcode = ALLOCA)
      (fn_insts_blocks gs))) DIFF
    set (MAP (\j. j.inst_id) (fn_insts_blocks bs))) <=
  LENGTH (FILTER (\j. j.inst_opcode = DLOAD)
    (fn_insts_blocks bs))
Proof
  Induct >- simp[lower_dload_blocks_supply_def, fn_insts_blocks_def] >>
  rpt gen_tac >> Cases_on `lower_dload_block_supply a h` >>
  Cases_on `lower_dload_blocks_supply r bs` >>
  simp[lower_dload_blocks_supply_def, Excl "CARD_DIFF"] >> strip_tac >>
  gvs[Excl "CARD_DIFF"] >> first_x_assum drule >> strip_tac >>
  `lower_dload_insts_supply a h.bb_instructions = (q.bb_instructions,r)` by
    gvs[lower_dload_block_supply_def, AllCaseEqs()] >>
  drule lower_dload_insts_supply_cap_bound >> strip_tac >>
  qspecl_then [`set (MAP (\j. j.inst_id)
                  (FILTER (\j. j.inst_opcode = ALLOCA) q.bb_instructions))`,
               `set (MAP (\j. j.inst_id)
                  (FILTER (\j. j.inst_opcode = ALLOCA)
                    (fn_insts_blocks q')))`,
               `set (MAP (\j. j.inst_id) h.bb_instructions)`,
               `set (MAP (\j. j.inst_id) (fn_insts_blocks bs))`]
    mp_tac cap_union_diff_bound >>
  simp[Excl "CARD_DIFF", fn_insts_blocks_def, FILTER_APPEND_DISTRIB, MAP_APPEND] >> decide_tac
QED

Theorem lower_dload_configured_cap_bound:
  lower_dload_function_supply a f = (g,b) ==>
  CARD (set (MAP (\i. i.inst_id)
    (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts g))) DIFF
    set (MAP (\i. i.inst_id) (fn_insts f))) <=
  LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts f))
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule lower_dload_blocks_supply_cap_bound >> simp[fn_insts_def]
QED

Theorem lower_dload_inst_supply_new_alloca[local]:
  lower_dload_inst_supply a i = (code,b) /\ MEM j code /\
  j.inst_opcode = ALLOCA /\ j.inst_id <> i.inst_id ==>
  i.inst_opcode = DLOAD /\
  (?op out. i.inst_operands = [op] /\ i.inst_outputs = [out]) /\
  code <> [] /\ (HD code).inst_opcode = ALLOCA /\ j = HD code
Proof
  strip_tac >> Cases_on `i.inst_opcode = DLOAD`
  >- gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
  gvs[lower_dload_inst_supply_def]
QED

Theorem lower_dload_insts_supply_new_alloca[local]:
  lower_dload_insts_supply a ins = (outs,b) /\
  MEM j outs /\ j.inst_opcode = ALLOCA /\
  ~MEM j.inst_id (MAP (\i. i.inst_id) ins) ==>
  ?pre i post p code tail a1 a2.
    ins = pre ++ i::post /\
    lower_dload_insts_supply a pre = (p,a1) /\
    lower_dload_inst_supply a1 i = (code,a2) /\
    lower_dload_insts_supply a2 post = (tail,b) /\
    i.inst_opcode = DLOAD /\
    (?op out. i.inst_operands = [op] /\ i.inst_outputs = [out]) /\
    code <> [] /\ (HD code).inst_opcode = ALLOCA /\ j = HD code
Proof
  strip_tac >>
  `?k. k < LENGTH outs /\ j = EL k outs` by metis_tac[MEM_EL] >>
  drule_all lower_dload_insts_supply_position >> strip_tac >>
  `MEM i ins` by simp[] >>
  `j.inst_id <> i.inst_id` by (gvs[MEM_MAP] >> metis_tac[]) >>
  `MEM j code` by metis_tac[MEM_EL] >>
  drule_all lower_dload_inst_supply_new_alloca >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem lower_dload_blocks_supply_member_prefix[local]:
  !bs a gs b j.
  lower_dload_blocks_supply a bs = (gs,b) /\
  MEM j (fn_insts_blocks gs) ==>
  ?pre bb post gp gb gt a0 a3.
    bs = pre ++ bb::post /\ gs = gp ++ gb::gt /\
    lower_dload_blocks_supply a pre = (gp,a0) /\
    lower_dload_block_supply a0 bb = (gb,a3) /\
    lower_dload_blocks_supply a3 post = (gt,b) /\
    MEM j gb.bb_instructions
Proof
  Induct >- simp[lower_dload_blocks_supply_def, fn_insts_blocks_def] >>
  rpt gen_tac >> Cases_on `lower_dload_block_supply a h` >>
  Cases_on `lower_dload_blocks_supply r bs` >>
  simp[lower_dload_blocks_supply_def, fn_insts_blocks_def] >> strip_tac >>
  gvs[fn_insts_blocks_def]
  >- (qexistsl_tac [`[]`, `h`, `bs`, `[]`, `q`, `q'`, `a`, `r`] >>
      simp[lower_dload_blocks_supply_def]) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`h::pre`, `bb`, `post`, `q::gp`, `gb`, `gt`, `a0`, `a3`] >>
  simp[lower_dload_blocks_supply_def]
QED

Theorem lower_dload_configured_cap_origin:
  lower_dload_function_supply a f = (g,b) /\
  q IN (set (MAP (\i. i.inst_id)
    (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts g))) DIFF
    set (MAP (\i. i.inst_id) (fn_insts f))) ==>
  ?bpre bb bpost qpre gb qpost a0 a3 pre i post p code tail a1 a2.
    f.fn_blocks = bpre ++ bb::bpost /\
    lower_dload_blocks_supply a bpre = (qpre,a0) /\
    lower_dload_block_supply a0 bb = (gb,a3) /\
    lower_dload_blocks_supply a3 bpost = (qpost,b) /\
    g.fn_blocks = qpre ++ gb::qpost /\
    bb.bb_instructions = pre ++ i::post /\
    lower_dload_insts_supply a0 pre = (p,a1) /\
    lower_dload_inst_supply a1 i = (code,a2) /\
    lower_dload_insts_supply a2 post = (tail,a3) /\
    i.inst_opcode = DLOAD /\
    (?op out. i.inst_operands = [op] /\ i.inst_outputs = [out]) /\
    code <> [] /\ (HD code).inst_opcode = ALLOCA /\ q = (HD code).inst_id
Proof
  simp[IN_DIFF, MEM_MAP, MEM_FILTER] >> strip_tac >>
  qpat_x_assum `lower_dload_function_supply a f = _` mp_tac >>
  simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `MEM j (fn_insts _)` >>
  `MEM j (fn_insts_blocks bbs)` by gvs[fn_insts_def] >>
  drule_all lower_dload_blocks_supply_member_prefix >> strip_tac >>
  `~MEM j.inst_id (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (gvs[fn_insts_def, fn_insts_blocks_def, MEM_MAP] >>
     metis_tac[fn_insts_blocks_MEM, MEM_APPEND, MEM]) >>
  `lower_dload_insts_supply a0 bb.bb_instructions = (gb.bb_instructions,a3)` by
    gvs[lower_dload_block_supply_def, AllCaseEqs()] >>
  drule_all lower_dload_insts_supply_new_alloca >> strip_tac >>
  qexistsl_tac [`pre`, `bb`, `post`, `gp`, `gb`, `gt`, `a0`, `a3`,
                `pre'`, `i`, `post'`, `p`, `code`, `tail`, `a1`, `a2`] >>
  simp[] >> metis_tac[]
QED
