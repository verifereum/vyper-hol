Theory lowerDloadRevertSuffix
Ancestors
  o1ContractLowerDload lowerDloadSupplySegment lowerDloadDefs irSupply stepWriteFootprintForward ptrDiscipline
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

Theorem ld_revert_pair_interval_step:
  revert_forward_pair bb copypos endpos /\
  copypos <= t.vs_inst_idx /\ t.vs_inst_idx <= endpos /\
  get_instruction bb t.vs_inst_idx = SOME j ==>
  step_inst fuel CT j t <> Halt th /\
  step_inst fuel CT j t <> IntRet ret th /\
  j.inst_opcode <> INVOKE /\
  (step_inst fuel CT j t = OK z ==>
    ~is_terminator j.inst_opcode /\ z.vs_requests = t.vs_requests /\
    (next_inst z).vs_current_bb = t.vs_current_bb /\
    copypos < (next_inst z).vs_inst_idx /\
    (next_inst z).vs_inst_idx <= endpos)
Proof
  strip_tac >> Cases_on `copypos = t.vs_inst_idx`
  >- (`j.inst_opcode = RETURNDATACOPY` by gvs[revert_forward_pair_def] >>
      simp[step_inst_non_invoke] >>
      pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
      simp[AllCaseEqs(), is_terminator_def] >> rpt strip_tac >>
      gvs[] >>
      `t.vs_inst_idx < endpos` by fs[revert_forward_pair_def] >>
      simp[next_inst_def, write_memory_with_expansion_def] >> decide_tac) >>
  `copypos < t.vs_inst_idx` by decide_tac >>
  `j.inst_opcode = ASSIGN \/ j.inst_opcode = REVERT` by
    (irule ld_revert_pair_suffix_opcode >> metis_tac[]) >>
  drule_all ld_revert_pair_suffix_step >> strip_tac >>
  simp[] >> strip_tac >>
  `j.inst_opcode = ASSIGN` by metis_tac[ld_revert_suffix_step] >>
  fs[is_terminator_def, next_inst_def] >> metis_tac[]
QED

(* Only variable reservation is needed here; instruction-id wellformedness
   is independent of assignment agreement. *)
Theorem ld_inst_supply_used_vars_mono:
  lower_dload_inst_supply a i = (out,b) ==>
  !v. MEM v a.irs_used_vars ==> MEM v b.irs_used_vars
Proof
  simp[lower_dload_inst_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac fresh_ir_var_contract >>
  gvs[fresh_inst_id_def] >> metis_tac[]
QED

Theorem ld_insts_supply_used_vars_mono:
  !ins a out b. lower_dload_insts_supply a ins = (out,b) ==>
  !v. MEM v a.irs_used_vars ==> MEM v b.irs_used_vars
Proof
  Induct >- simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >>
  Cases_on `lower_dload_inst_supply a h` >>
  Cases_on `lower_dload_insts_supply r ins` >>
  simp[lower_dload_insts_supply_def] >> strip_tac >> gvs[] >>
  metis_tac[ld_inst_supply_used_vars_mono]
QED

Theorem ld_same_after_assigns_refl:
  !ins x. same_after_assigns ins x x
Proof
  Cases >> simp[same_after_assigns_def]
QED

Theorem ld_step_back_assign_support:
  EVERY (\v. MEM v used) (inst_ir_vars i) /\
  EVERY (\v. MEM v used) (venomInst$operand_vars [x]) /\
  step_back_assign i x = SOME y ==>
  EVERY (\v. MEM v used) (venomInst$operand_vars [y])
Proof
  Cases_on `x` >>
  simp[step_back_assign_def, venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def, dfgDefsTheory.operand_var_def, dfgDefsTheory.operand_vars_def,
       inst_ir_vars_def, inst_uses_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `i.inst_operands` >>
  gvs[venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def,
      dfgDefsTheory.operand_vars_def, dfgDefsTheory.operand_var_def]
QED

Theorem ld_reserved_not_fresh[local]:
  ~MEM f used ==> !v. MEM v used ==> v <> f
Proof
  metis_tac[]
QED

Theorem ld_inst_supply_assign_continuation:
  lower_dload_inst_supply a i = (out,b) /\
  EVERY (\v. MEM v a.irs_used_vars) (venomInst$operand_vars [x;y]) /\
  step_back_assign i x = SOME x' /\
  step_back_assign i y = SOME y' /\
  same_after_assigns pre x' y' ==>
  same_after_assigns (REVERSE out ++ pre) x y
Proof
  Cases_on `x = y` >- simp[ld_same_after_assigns_refl] >>
  simp[lower_dload_inst_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac (cj 1 fresh_ir_var_contract) >>
  imp_res_tac (cj 2 fresh_ir_var_contract) >>
  gvs[fresh_inst_id_def] >>
  simp[same_after_assigns_def] >>
  Cases_on `x` >> Cases_on `y` >>
  gvs[step_back_assign_def, venomInstTheory.operand_vars_def,
      venomInstTheory.operand_var_def, same_after_assigns_def] >>
  imp_res_tac ld_reserved_not_fresh >> simp[]
QED

Theorem ld_insts_supply_same_after_assigns:
  !ins a out b x y.
  EVERY (\v. MEM v a.irs_used_vars) (FLAT (MAP inst_ir_vars ins)) /\
  EVERY (\v. MEM v a.irs_used_vars) (venomInst$operand_vars [x;y]) /\
  lower_dload_insts_supply a ins = (out,b) /\
  same_after_assigns (REVERSE ins) x y ==>
  same_after_assigns (REVERSE out) x y
Proof
  Induct using SNOC_INDUCT
  >- simp[lower_dload_insts_supply_def, same_after_assigns_def] >>
  rpt gen_tac >> rename1 `SNOC i ins` >>
  rename1 `same_after_assigns (REVERSE out) x y` >>
  Cases_on `x = y`
  >- simp[ld_same_after_assigns_refl] >>
  simp[SNOC_APPEND, MAP_APPEND, FLAT_APPEND, REVERSE_APPEND,
       same_after_assigns_def] >>
  strip_tac >>
  gvs[AllCaseEqs()] >>
  Cases_on `lower_dload_insts_supply a ins` >>
  rename1 `lower_dload_insts_supply a ins = (before,qi)` >>
  Cases_on `lower_dload_inst_supply qi i` >>
  rename1 `lower_dload_inst_supply qi i = (code,qn)` >>
  `lower_dload_insts_supply a (ins ++ [i]) = (before ++ code,qn)` by
    (irule lower_dload_insts_supply_append_forward >>
     qexists_tac `qi` >> simp[lower_dload_insts_supply_def]) >>
  gvs[] >>
  Cases_on `step_back_assign i x` >> gvs[] >>
  Cases_on `step_back_assign i y` >> gvs[] >>
  rename1 `step_back_assign i x = SOME xx` >>
  rename1 `step_back_assign i y = SOME yy` >>
  `EVERY (\v. MEM v a.irs_used_vars) (venomInst$operand_vars [x]) /\
   EVERY (\v. MEM v a.irs_used_vars) (venomInst$operand_vars [y])` by
    (Cases_on `x` >> Cases_on `y` >>
     gvs[venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def]) >>
  `EVERY (\v. MEM v a.irs_used_vars) (venomInst$operand_vars [xx]) /\
   EVERY (\v. MEM v a.irs_used_vars) (venomInst$operand_vars [yy])` by
    metis_tac[ld_step_back_assign_support] >>
  `EVERY (\v. MEM v a.irs_used_vars) (venomInst$operand_vars [xx;yy])` by
    (Cases_on `xx` >> Cases_on `yy` >>
     gvs[venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def]) >>
  `same_after_assigns (REVERSE before) xx yy` by
    (first_x_assum irule >> metis_tac[]) >>
  `EVERY (\v. MEM v qi.irs_used_vars) (venomInst$operand_vars [x;y])` by
    (qpat_assum `lower_dload_insts_supply a ins = _`
       (mp_tac o MATCH_MP ld_insts_supply_used_vars_mono) >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  simp[REVERSE_APPEND] >>
  irule ld_inst_supply_assign_continuation >> metis_tac[]
QED

Theorem ld_resolve_block_assigns_support:
  !ins op used.
  EVERY (\v. MEM v used) (FLAT (MAP inst_ir_vars ins)) /\
  EVERY (\v. MEM v used) (venomInst$operand_vars [op]) ==>
  EVERY (\v. MEM v used)
    (venomInst$operand_vars [resolve_block_assigns ins op])
Proof
  Induct >- simp[resolve_block_assigns_def] >>
  rpt gen_tac >> Cases_on `op` >>
  simp[resolve_block_assigns_def] >>
  rpt strip_tac >>
  Cases_on `MEM s h.inst_outputs`
  >- (simp[] >> IF_CASES_TAC
      >- (gvs[] >>
          first_x_assum (qspecl_then [`HD h.inst_operands`, `used`] mp_tac) >>
          disch_then irule >> simp[] >>
          Cases_on `h.inst_operands` >>
          gvs[inst_ir_vars_def, inst_uses_def,
              venomInstTheory.operand_vars_def, dfgDefsTheory.operand_vars_def]) >>
      simp[]) >>
  simp[] >> first_x_assum (qspecl_then [`Var s`, `used`] mp_tac) >>
  disch_then irule >> simp[]
QED


Theorem ld_revert_segment_middle[local]:
  bb.bb_instructions = pre ++ copy::(mid ++ rev::post) ==>
  ((!k inst. LENGTH pre < k /\ k < LENGTH pre + SUC (LENGTH mid) /\
      get_instruction bb k = SOME inst ==> inst.inst_opcode = ASSIGN) <=>
   EVERY (\i. i.inst_opcode = ASSIGN) mid)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >> simp[EVERY_EL] >> rpt strip_tac >>
      first_x_assum irule >>
      qexists_tac `LENGTH pre + SUC n` >>
      simp[get_instruction_def, EL_APPEND_EQN, EL_CONS] ) >>
  simp[EVERY_EL] >> rpt strip_tac >>
  `?n. k = LENGTH pre + SUC n /\ n < LENGTH mid` by
    (qexists_tac `k - SUC (LENGTH pre)` >> decide_tac) >>
  gvs[get_instruction_def, EL_APPEND_EQN, EL_CONS]
QED

Theorem ld_revert_pair_segment_iff:
  bb.bb_instructions = pre ++ [copy] ++ mid ++ [rev] ++ post ==>
  (revert_forward_pair bb (LENGTH pre) (LENGTH pre + SUC (LENGTH mid)) <=>
   EVERY (\i. i.inst_opcode = ASSIGN) mid /\
   ?p src rds p' rds'.
    copy.inst_opcode = RETURNDATACOPY /\ copy.inst_operands = [p;src;rds] /\
    rev.inst_opcode = REVERT /\ rev.inst_operands = [p';rds'] /\
    same_after_assigns (REVERSE pre) src (Lit 0w) /\
    same_after_assigns (REVERSE pre) p (resolve_block_assigns (REVERSE mid) p') /\
    same_after_assigns (REVERSE pre) rds (resolve_block_assigns (REVERSE mid) rds'))
Proof
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> strip_tac >>
  `TAKE (LENGTH pre) bb.bb_instructions = pre` by simp[TAKE_APPEND] >>
  `DROP (SUC (LENGTH pre)) bb.bb_instructions = mid ++ rev::post` by
    simp[GSYM ADD1, DROP_APPEND] >>
  `LENGTH pre + SUC (LENGTH mid) - SUC (LENGTH pre) = LENGTH mid` by decide_tac >>
  `TAKE (LENGTH mid) (mid ++ rev::post) = mid` by simp[TAKE_APPEND] >>
  `get_instruction bb (LENGTH pre) = SOME copy` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `get_instruction bb (LENGTH pre + SUC (LENGTH mid)) = SOME rev` by
    simp[get_instruction_def, EL_APPEND_EQN, EL_CONS] >>
  drule ld_revert_segment_middle >> strip_tac >>
  pure_rewrite_tac[revert_forward_pair_def] >> asm_rewrite_tac[] >> simp[]
QED

Theorem ld_lower_revert_pair_supported:
  revert_forward_pair bb i j /\
  EVERY (\v. MEM v q.irs_used_vars)
    (FLAT (MAP inst_ir_vars bb.bb_instructions)) /\
  lower_dload_block_supply q bb = (dst,qe) ==>
  ?before qi.
    lower_dload_insts_supply q (TAKE i bb.bb_instructions) = (before,qi) /\
    revert_forward_pair dst (LENGTH before) (LENGTH before + (j-i))
Proof
  strip_tac >> drule ld_revert_pair_segment >> strip_tac >>
  `i < j` by metis_tac[revert_forward_pair_def] >>
  `j-i = SUC (LENGTH mid)` by decide_tac >>
  `bb.bb_instructions = pre ++ [copy] ++ mid ++ [rev] ++ post` by
    (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     qpat_assum `bb.bb_instructions = _` ACCEPT_TAC) >>
  drule ld_revert_pair_segment_iff >>
  `j = LENGTH pre + SUC (LENGTH mid)` by decide_tac >>
  qpat_x_assum `LENGTH mid = _` kall_tac >>
  qpat_x_assum `LENGTH pre = i` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `j = _` SUBST_ALL_TAC >>
  asm_rewrite_tac[] >> strip_tac >>
  Cases_on `lower_dload_insts_supply q pre` >>
  rename1 `lower_dload_insts_supply q pre = (before,qi)` >>
  Cases_on `lower_dload_insts_supply qi post` >>
  rename1 `lower_dload_insts_supply qi post = (after,qf)` >>
  drule_all ld_lower_revert_segment >> strip_tac >>
  `dst.bb_instructions = before ++ [copy] ++ mid ++ [rev] ++ after` by
    (qpat_x_assum `lower_dload_block_supply _ _ = _` mp_tac >>
     pure_rewrite_tac[lower_dload_block_supply_def] >>
     qpat_assum `bb.bb_instructions = pre ++ copy::_` SUBST1_TAC >>
     asm_rewrite_tac[] >> strip_tac >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> gvs[]) >>
  qexistsl_tac [`before`, `qi`] >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[TAKE_APPEND]) >>
  qpat_x_assum `EVERY _ (FLAT (MAP inst_ir_vars bb.bb_instructions))` mp_tac >>
  qpat_assum `bb.bb_instructions = pre ++ copy::_` (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[MAP_APPEND, MAP, FLAT_APPEND, FLAT, EVERY_APPEND, EVERY_DEF] >>
  strip_tac >>
  qpat_x_assum `bb.bb_instructions = _` kall_tac >>
  qpat_x_assum `bb.bb_instructions = _` kall_tac >>
  drule ld_revert_pair_segment_iff >>
  disch_then (fn th => rewrite_tac[th]) >>
  `EVERY (\v. MEM v q.irs_used_vars) (venomInst$operand_vars [p]) /\
   EVERY (\v. MEM v q.irs_used_vars) (venomInst$operand_vars [src]) /\
   EVERY (\v. MEM v q.irs_used_vars) (venomInst$operand_vars [rds]) /\
   EVERY (\v. MEM v q.irs_used_vars) (venomInst$operand_vars [p']) /\
   EVERY (\v. MEM v q.irs_used_vars) (venomInst$operand_vars [rds'])` by
    (fs[inst_ir_vars_def, inst_uses_def] >>
     Cases_on `p` >> Cases_on `src` >> Cases_on `rds` >>
     Cases_on `p'` >> Cases_on `rds'` >>
     gvs[venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def]) >>
  `EVERY (\v. MEM v q.irs_used_vars)
      (venomInst$operand_vars [resolve_block_assigns (REVERSE mid) p']) /\
   EVERY (\v. MEM v q.irs_used_vars)
      (venomInst$operand_vars [resolve_block_assigns (REVERSE mid) rds'])` by
    (conj_tac >> irule ld_resolve_block_assigns_support >>
     fs[EVERY_MEM, MEM_FLAT, MEM_MAP] >> metis_tac[MEM_REVERSE]) >>
  simp[] >> rpt conj_tac >> irule ld_insts_supply_same_after_assigns >>
  qexistsl_tac [`q`, `qi`, `pre`] >>
  simp[] >>
  `!x y. venomInst$operand_vars [x;y] =
      venomInst$operand_vars [x] ++ venomInst$operand_vars [y]` by
    (rpt gen_tac >> Cases_on `x` >>
     simp[venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def]) >>
  asm_rewrite_tac[] >>
  simp[venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def]
QED

Theorem ld_revert_endpoint_prefix_length[local]:
  revert_forward_pair bb i j /\
  lower_dload_insts_supply q (TAKE i bb.bb_instructions) = (before,qi) /\
  lower_dload_insts_supply q (TAKE j bb.bb_instructions) = (p,qj) ==>
  LENGTH p = LENGTH before + (j-i)
Proof
  strip_tac >> drule ld_revert_pair_segment >> strip_tac >>
  `i < j` by metis_tac[revert_forward_pair_def] >>
  `j = LENGTH pre + SUC (LENGTH mid)` by decide_tac >>
  qpat_x_assum `LENGTH mid = _` kall_tac >>
  qpat_x_assum `LENGTH pre = i` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `j = _` SUBST_ALL_TAC >>
  `TAKE (LENGTH pre) bb.bb_instructions = pre` by simp[TAKE_APPEND] >>
  `TAKE (LENGTH pre + SUC (LENGTH mid)) bb.bb_instructions = pre ++ copy::mid` by
    simp[TAKE_APPEND] >>
  qpat_x_assum `lower_dload_insts_supply q (TAKE _ _) = (before,qi)` mp_tac >>
  qpat_assum `TAKE (LENGTH pre) _ = _` (fn th => pure_rewrite_tac[th]) >>
  strip_tac >>
  `lower_dload_insts_supply qi (copy::mid) = (copy::mid,qi)` by
    (irule ld_lower_unchanged_insts >> fs[EVERY_MEM] >> metis_tac[]) >>
  `lower_dload_insts_supply q (pre ++ copy::mid) = (before ++ copy::mid,qi)` by
    (irule lower_dload_insts_supply_append_forward >> qexists_tac `qi` >> simp[]) >>
  qpat_x_assum `lower_dload_insts_supply q (TAKE _ _) = (p,qj)` mp_tac >>
  qpat_assum `TAKE (LENGTH pre + _) _ = _` (fn th => pure_rewrite_tac[th]) >>
  asm_rewrite_tac[] >> strip_tac >> gvs[]
QED

Theorem ld_configured_revert_interval_entry:
  in_revert_forward fn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  EVERY (\v. MEM v q.irs_used_vars)
    (FLAT (MAP inst_ir_vars bb.bb_instructions)) /\
  lower_dload_block_supply q bb = (gb,qe) /\
  lower_dload_insts_supply q (TAKE s.vs_inst_idx bb.bb_instructions) = (p,qi) /\
  lookup_block t.vs_current_bb gn.fn_blocks = SOME gb /\
  t.vs_inst_idx = LENGTH p /\
  get_instruction gb t.vs_inst_idx = SOME j ==>
  ?copypos endpos.
    lookup_block t.vs_current_bb gn.fn_blocks = SOME gb /\
    revert_forward_pair gb copypos endpos /\
    copypos <= t.vs_inst_idx /\ t.vs_inst_idx <= endpos /\
    get_instruction gb t.vs_inst_idx = SOME j
Proof
  simp[in_revert_forward_def, revert_forward_at_def] >>
  strip_tac >> gvs[]
  >- (drule_all ld_lower_revert_pair_supported >> strip_tac >>
      gvs[] >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all ld_lower_revert_pair_supported >> strip_tac >>
  drule_all ld_revert_endpoint_prefix_length >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem ld_blocks_supply_used_vars_mono:
  !bbs a out b. lower_dload_blocks_supply a bbs = (out,b) ==>
  !v. MEM v a.irs_used_vars ==> MEM v b.irs_used_vars
Proof
  Induct >- simp[lower_dload_blocks_supply_def] >>
  rpt gen_tac >>
  Cases_on `lower_dload_insts_supply a h.bb_instructions` >>
  Cases_on `lower_dload_blocks_supply r bbs` >>
  simp[lower_dload_blocks_supply_def, lower_dload_block_supply_def] >>
  strip_tac >> gvs[] >> metis_tac[ld_insts_supply_used_vars_mono]
QED
