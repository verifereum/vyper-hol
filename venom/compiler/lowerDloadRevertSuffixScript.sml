Theory lowerDloadRevertSuffix
Ancestors
  o1ContractLowerDload lowerDloadSupplySegment lowerDloadDefs stepWriteFootprintForward ptrDiscipline
  venomExecSemantics venomInst venomState contextCodegenRel arithmetic list rich_list

(* One-step observation boundary, independent of operand definedness. *)
Theorem ld_revert_suffix_step:
  (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = REVERT) ==>
  step_inst fuel ctx inst s <> Halt t /\
  step_inst fuel ctx inst s <> IntRet vals t /\
  (step_inst fuel ctx inst s = OK t ==>
    inst.inst_opcode = ASSIGN /\ t.vs_requests = s.vs_requests /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx)
Proof
  strip_tac >> simp[step_inst_non_invoke] >>
  pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  simp[AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def, revert_state_def]
QED

Theorem ld_revert_suffix_next:
  k <= j /\ s.vs_inst_idx = k /\
  get_instruction bb k = SOME inst /\
  (!q i. k <= q /\ q < j /\ get_instruction bb q = SOME i ==>
    i.inst_opcode = ASSIGN) /\
  (?i. get_instruction bb j = SOME i /\ i.inst_opcode = REVERT) /\
  step_inst fuel ctx inst s = OK t ==>
  k < j /\ (next_inst t).vs_inst_idx = SUC k /\
  (next_inst t).vs_requests = s.vs_requests /\
  (next_inst t).vs_current_bb = s.vs_current_bb /\
  (!q i. (next_inst t).vs_inst_idx <= q /\ q < j /\
    get_instruction bb q = SOME i ==> i.inst_opcode = ASSIGN)
Proof
  strip_tac >>
  `inst.inst_opcode = ASSIGN \/ inst.inst_opcode = REVERT` by
    (Cases_on `k = j` >> gvs[] >> metis_tac[LESS_OR_EQ]) >>
  `inst.inst_opcode = ASSIGN /\ t.vs_requests = s.vs_requests /\
   t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[ld_revert_suffix_step] >>
  `k <> j` by (strip_tac >> gvs[]) >>
  `k < j` by decide_tac >>
  gvs[next_inst_def] >> rpt strip_tac >>
  first_x_assum irule >> qexists_tac `q` >> simp[] >> decide_tac
QED

Theorem ld_lower_unchanged_insts:
  !ins q. EVERY (\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES) ins ==>
  lower_dload_insts_supply q ins = (ins,q)
Proof
  Induct >> simp[lower_dload_insts_supply_def] >>
  rpt strip_tac >> simp[lower_dload_inst_supply_def]
QED

(* An actual supply-threaded expansion, not a hypothetical target suffix. *)
Theorem ld_lower_revert_segment:
  EVERY (\i. i.inst_opcode = ASSIGN) mid /\
  copy.inst_opcode = RETURNDATACOPY /\ rev.inst_opcode = REVERT /\
  lower_dload_insts_supply q pre = (before,qi) /\
  lower_dload_insts_supply qi post = (after,qe) ==>
  lower_dload_insts_supply q (pre ++ copy::(mid ++ rev::post)) =
    (before ++ copy::(mid ++ rev::after),qe)
Proof
  strip_tac >>
  `lower_dload_insts_supply qi (copy::(mid ++ [rev])) =
    (copy::(mid ++ [rev]),qi)` by
    (irule ld_lower_unchanged_insts >> gvs[EVERY_MEM] >> metis_tac[]) >>
  `lower_dload_insts_supply qi ((copy::(mid ++ [rev])) ++ post) =
    ((copy::(mid ++ [rev])) ++ after,qe)` by
    (irule lower_dload_insts_supply_append_forward >>
     qexists_tac `qi` >> simp[]) >>
  `lower_dload_insts_supply q (pre ++ ((copy::(mid ++ [rev])) ++ post)) =
    (before ++ ((copy::(mid ++ [rev])) ++ after),qe)` by
    (irule lower_dload_insts_supply_append_forward >>
     qexists_tac `qi` >> simp[]) >>
  qpat_x_assum `lower_dload_insts_supply q (pre ++ _) = _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem ld_revert_segment_interval:
  bb.bb_instructions = before ++ mid ++ rev::after /\
  EVERY (\i. i.inst_opcode = ASSIGN) mid /\ rev.inst_opcode = REVERT ==>
  get_instruction bb (LENGTH before + LENGTH mid) = SOME rev /\
  (!k i. LENGTH before <= k /\ k < LENGTH before + LENGTH mid /\
    get_instruction bb k = SOME i ==> i.inst_opcode = ASSIGN)
Proof
  simp[get_instruction_def] >> strip_tac >> conj_tac
  >- simp[EL_APPEND_EQN] >>
  rpt strip_tac >> gvs[EL_APPEND_EQN, EVERY_EL] >>
  first_x_assum irule >> qexists_tac `k - LENGTH before` >> simp[]
QED

Theorem ld_revert_pair_suffix_opcode:
  revert_forward_pair bb i j /\ i < k /\ k <= j /\
  get_instruction bb k = SOME inst ==>
  inst.inst_opcode = ASSIGN \/ inst.inst_opcode = REVERT
Proof
  simp[revert_forward_pair_def] >> rpt strip_tac >>
  Cases_on `k = j` >> gvs[] >> metis_tac[LESS_OR_EQ]
QED

Theorem ld_revert_pair_suffix_step:
  revert_forward_pair bb i j /\ i < s.vs_inst_idx /\ s.vs_inst_idx <= j /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  step_inst fuel ctx inst s <> Halt t /\
  step_inst fuel ctx inst s <> IntRet vals t /\
  (step_inst fuel ctx inst s = OK t ==>
    i < (next_inst t).vs_inst_idx /\ (next_inst t).vs_inst_idx <= j /\
    (next_inst t).vs_requests = s.vs_requests /\
    (next_inst t).vs_current_bb = s.vs_current_bb)
Proof
  strip_tac >>
  `inst.inst_opcode = ASSIGN \/ inst.inst_opcode = REVERT` by
    (irule ld_revert_pair_suffix_opcode >> metis_tac[]) >>
  `step_inst fuel ctx inst s <> Halt t /\
   step_inst fuel ctx inst s <> IntRet vals t` by
    metis_tac[ld_revert_suffix_step] >> simp[] >> strip_tac >>
  `inst.inst_opcode = ASSIGN /\ t.vs_requests = s.vs_requests /\
   t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[ld_revert_suffix_step] >>
  `s.vs_inst_idx <> j` by (strip_tac >> gvs[revert_forward_pair_def]) >>
  simp[next_inst_def] >> decide_tac
QED

Theorem ld_revert_pair_segment:
  revert_forward_pair bb i j ==>
  ?pre copy mid rev post.
    bb.bb_instructions = pre ++ copy::(mid ++ rev::post) /\
    LENGTH pre = i /\ LENGTH mid = j-i-1 /\
    copy.inst_opcode = RETURNDATACOPY /\ rev.inst_opcode = REVERT /\
    EVERY (\a. a.inst_opcode = ASSIGN) mid
Proof
  simp[revert_forward_pair_def, get_instruction_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `j < LENGTH ins` >>
  qexistsl_tac [`TAKE i ins`, `EL i ins`,
    `TAKE (j-i-1) (DROP (i+1) ins)`, `EL j ins`, `DROP (j+1) ins`] >>
  `i < LENGTH ins` by decide_tac >>
  `j-i-1 < LENGTH (DROP (i+1) ins)` by simp[] >>
  `j-i-1 + (i+1) = j` by decide_tac >>
  `SUC (j-i-1) + (i+1) = j+1` by decide_tac >>
  conj_tac
  >- (qspec_then `j-i-1` (qspec_then `DROP (i+1) ins` mp_tac) TAKE_DROP_SUC >>
      simp[EL_DROP, DROP_DROP] >> strip_tac >>
      qspec_then `i` (qspec_then `ins` mp_tac) TAKE_DROP_SUC >>
      simp[ADD1] >> gvs[Abbr `ins`] >> metis_tac[APPEND_ASSOC]) >>
  simp[EVERY_EL, EL_TAKE, EL_DROP] >> rpt strip_tac >>
  first_x_assum irule >> qexists_tac `n + (i+1)` >>
  gvs[Abbr `ins`] >> simp[] >> decide_tac
QED

Theorem ld_lower_revert_pair_suffix:
  revert_forward_pair bb i j /\
  lower_dload_insts_supply q bb.bb_instructions = (xs,qe) ==>
  ?before copy mid rev after qi.
    lower_dload_insts_supply q (TAKE i bb.bb_instructions) = (before,qi) /\
    xs = before ++ copy::(mid ++ rev::after) /\
    copy.inst_opcode = RETURNDATACOPY /\ rev.inst_opcode = REVERT /\
    LENGTH mid = j-i-1 /\ EVERY (\a. a.inst_opcode = ASSIGN) mid
Proof
  strip_tac >> drule ld_revert_pair_segment >> strip_tac >>
  Cases_on `lower_dload_insts_supply q pre` >>
  rename1 `lower_dload_insts_supply q pre = (before,qi)` >>
  Cases_on `lower_dload_insts_supply qi post` >>
  rename1 `lower_dload_insts_supply qi post = (after,qf)` >>
  drule_all ld_lower_revert_segment >> strip_tac >>
  gvs[] >> qexistsl_tac [`before`, `copy`, `mid`, `rev`, `after`, `qi`] >>
  `!a b:num. a - (a + b) = 0` by decide_tac >>
  simp[TAKE_APPEND, GSYM ADD_ASSOC]
QED

Theorem ld_revert_pair_suffix_enter:
  revert_forward_pair bb s.vs_inst_idx j /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst s = OK t ==>
  s.vs_inst_idx < (next_inst t).vs_inst_idx /\
  (next_inst t).vs_inst_idx <= j /\
  (next_inst t).vs_requests = s.vs_requests /\
  (next_inst t).vs_current_bb = s.vs_current_bb
Proof
  strip_tac >>
  `inst.inst_opcode = RETURNDATACOPY /\ s.vs_inst_idx < j` by
    gvs[revert_forward_pair_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[next_inst_def, write_memory_with_expansion_def] >> decide_tac
QED

(* The entire forwarding segment is literally unchanged at block entry. *)
Theorem ld_lower_revert_pair_zero:
  revert_forward_pair src 0 j /\
  lower_dload_block_supply q src = (dst,qe) ==>
  revert_forward_pair dst 0 j
Proof
  strip_tac >> drule ld_revert_pair_segment >> strip_tac >>
  `pre = []` by gvs[] >> gvs[] >>
  Cases_on `lower_dload_insts_supply q post` >>
  rename1 `lower_dload_insts_supply q post = (after,qf)` >>
  `lower_dload_insts_supply q (copy::(mid ++ rev::post)) =
     (copy::(mid ++ rev::after),qf)` by
    (irule (SRULE [cj 1 lower_dload_insts_supply_def]
       (Q.INST [`pre` |-> `[]`, `before` |-> `[]`]
          (SPEC_ALL ld_lower_revert_segment))) >> simp[]) >>
  `dst.bb_instructions = copy::(mid ++ rev::after)` by
    (qpat_x_assum `src.bb_instructions = _`
       (assume_tac o PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
     gvs[lower_dload_block_supply_def]) >>
  `0 < j` by metis_tac[revert_forward_pair_def] >>
  `j = SUC (LENGTH mid)` by decide_tac >>
  qpat_x_assum `LENGTH mid = _` kall_tac >>
  qpat_x_assum `j = _` SUBST_ALL_TAC >>
  qpat_x_assum `revert_forward_pair src 0 _` mp_tac >>
  qpat_x_assum `src.bb_instructions = _`
    (assume_tac o PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  simp[revert_forward_pair_def, get_instruction_def, EL_APPEND_EQN,
       TAKE_APPEND, TAKE_LENGTH_TOO_LONG, EL_CONS]
QED
