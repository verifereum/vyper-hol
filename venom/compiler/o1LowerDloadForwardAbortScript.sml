(* Supply alignment of finite unchanged suffix segments. *)
Theory o1LowerDloadForwardAbort
Ancestors
  o1LowerDloadJointAssign o1LowerDloadAvailableSuffix o1ContractLowerDload
  lowerDloadDefs contextCodegenRel venomExecSemantics venomExecProps
  o1LowerDloadJointRelation venomInst list

Theorem ld_supply_insts_unchanged_segment:
  !segment u.
  EVERY (\i. ~MEM i.inst_opcode [DLOAD; DLOADBYTES]) segment ==>
  lower_dload_insts_supply u segment = (segment,u)
Proof
  Induct >> simp[lower_dload_insts_supply_def] >> rpt strip_tac >>
  `lower_dload_inst_supply u h = ([h],u)` by
    (irule lower_dload_inst_supply_special >> simp[]) >> simp[]
QED

Theorem ld_supply_insts_segment:
  ins = prefix ++ segment ++ tail /\
  EVERY (\i. ~MEM i.inst_opcode [DLOAD; DLOADBYTES]) segment /\
  lower_dload_insts_supply u prefix = (expanded,v) /\
  lower_dload_insts_supply u ins = (outs,w) ==>
  ?tail'. outs = expanded ++ segment ++ tail'
Proof
  strip_tac >> drule ld_supply_insts_unchanged_segment >>
  disch_then (qspec_then `v` assume_tac) >>
  Cases_on `lower_dload_insts_supply v tail` >>
  `lower_dload_insts_supply v (segment ++ tail) = (segment ++ q,r)` by
    (irule ld_supply_insts_append >> metis_tac[]) >>
  `lower_dload_insts_supply u (prefix ++ (segment ++ tail)) =
     (expanded ++ (segment ++ q),r)` by
    (irule ld_supply_insts_append >> metis_tac[]) >>
  gvs[APPEND_ASSOC]
QED

Theorem ld_supply_segment_fetch:
  ins = prefix ++ segment ++ tail /\
  EVERY (\i. ~MEM i.inst_opcode [DLOAD; DLOADBYTES]) segment /\
  lower_dload_insts_supply u prefix = (expanded,v) /\
  lower_dload_insts_supply u ins = (outs,w) /\
  bb.bb_instructions = ins /\ bb'.bb_instructions = outs /\
  k < LENGTH segment ==>
  get_instruction bb (LENGTH prefix + k) =
  get_instruction bb' (LENGTH expanded + k)
Proof
  strip_tac >> drule_all ld_supply_insts_segment >> strip_tac >>
  gvs[get_instruction_def, LENGTH_APPEND, EL_APPEND_EQN]
QED

Theorem ld_supply_interval_fetch:
  lower_dload_insts_supply u bb.bb_instructions = (outs,w) /\
  lower_dload_insts_supply u (TAKE p bb.bb_instructions) = (expanded,v) /\
  bb'.bb_instructions = outs /\ p + n <= LENGTH bb.bb_instructions /\
  (!k inst. k < n /\ get_instruction bb (p+k) = SOME inst ==>
      ~MEM inst.inst_opcode [DLOAD; DLOADBYTES]) ==>
  !k. k < n ==> get_instruction bb (p+k) =
               get_instruction bb' (LENGTH expanded+k)
Proof
  strip_tac >>
  qabbrev_tac `segment = TAKE n (DROP p bb.bb_instructions)` >>
  `bb.bb_instructions = TAKE p bb.bb_instructions ++ segment ++
                         DROP n (DROP p bb.bb_instructions)` by
    (simp[Abbr `segment`] >> metis_tac[TAKE_DROP, APPEND_ASSOC]) >>
  `LENGTH segment = n` by simp[Abbr `segment`, LENGTH_TAKE, LENGTH_DROP] >>
  `EVERY (\i. ~MEM i.inst_opcode [DLOAD; DLOADBYTES]) segment` by
    (rewrite_tac[EVERY_MEM] >> qx_gen_tac `i` >> disch_tac >>
     qpat_x_assum `MEM i segment` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
     `n' < n` by gvs[] >>
     gvs[Abbr `segment`, EL_TAKE, EL_DROP] >>
     qpat_x_assum `!k inst. _` (qspec_then `n'` mp_tac) >>
     simp[get_instruction_def]) >>
  rpt strip_tac >>
  `LENGTH (TAKE p bb.bb_instructions) = p` by simp[LENGTH_TAKE] >>
  drule ld_supply_segment_fetch >> simp[] >> metis_tac[]
QED

Theorem ld_forward_interval_unchanged:
  revert_forward_pair bb p j ==>
  SUC j <= LENGTH bb.bb_instructions /\
  (!k inst. k < SUC j - p /\ get_instruction bb (p+k) = SOME inst ==>
      ~MEM inst.inst_opcode [DLOAD; DLOADBYTES])
Proof
  simp[revert_forward_pair_def] >> strip_tac >>
  conj_tac
  >- gvs[get_instruction_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `k = 0` >- gvs[] >>
  Cases_on `p+k = j` >- gvs[] >>
  `p < p+k /\ p+k < j` by decide_tac >>
  `inst.inst_opcode = ASSIGN` by
    metis_tac[arithmeticTheory.ADD_COMM] >> simp[]
QED

Theorem ld_joint_control_forward_fetch:
  ld_joint_control u fn fn' s t /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  revert_forward_pair bb s.vs_inst_idx j ==>
  ?bb'. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    !k. k <= j - s.vs_inst_idx ==>
      get_instruction bb (s.vs_inst_idx+k) =
      get_instruction bb' (t.vs_inst_idx+k)
Proof
  pure_rewrite_tac[ld_joint_control_def] >> strip_tac >>
  rename1 `lower_dload_block_supply u1 b = (b',u2)` >>
  `MEM b fn.fn_blocks` by (simp[MEM_EL] >> metis_tac[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME b` by
    (irule MEM_lookup_block >> simp[]) >>
  `bb = b` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `bb = b` SUBST_ALL_TAC >>
  `MEM b' fn'.fn_blocks` by (simp[MEM_EL] >> metis_tac[]) >>
  `lookup_block t.vs_current_bb fn'.fn_blocks = SOME b'` by
    (irule MEM_lookup_block >> simp[] >>
     qpat_assum `lower_dload_block_supply _ _ = _` mp_tac >>
     simp[NoAsms, lower_dload_block_supply_def, AllCaseEqs()] >>
     strip_tac >>
     qpat_x_assum `_ with bb_instructions := _ = _` (SUBST1_TAC o SYM) >>
     simp[]) >>
  qexists_tac `b'` >> simp[] >>
  qpat_x_assum `lower_dload_block_supply _ _ = _` mp_tac >>
  simp[lower_dload_block_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule ld_forward_interval_unchanged >> strip_tac >>
  drule ld_supply_interval_fetch >>
  disch_then (qspecl_then [`u3`, `s.vs_inst_idx`, `SUC j - s.vs_inst_idx`]
    mp_tac) >>
  `s.vs_inst_idx < j` by metis_tac[revert_forward_pair_def] >>
  `s.vs_inst_idx + (SUC j - s.vs_inst_idx) <=
    LENGTH (EL k fn.fn_blocks).bb_instructions` by decide_tac >>
  `!r. r <= j - s.vs_inst_idx ==> r < SUC j - s.vs_inst_idx` by decide_tac >>
  `(EL k fn'.fn_blocks).bb_instructions = insts` by
    (qpat_assum `_ with bb_instructions := _ = _` (SUBST1_TAC o SYM) >>
     simp[NoAsms]) >>
  disch_then (qspecl_then [`expanded`, `EL k fn'.fn_blocks`] mp_tac) >>
  fs[arithmeticTheory.ADD_COMM] >> metis_tac[]
QED
