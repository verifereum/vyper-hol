Theory acMergeCursorProofs
Ancestors
  acMergeCursorDefs acSupplyProofs acChainProofs assertCombinerDefs
  irSupplyFreshProps irSupply venomFnScheduleRunner list rich_list alist pred_set arithmetic

(* Prefix reachability records the actual supply, not arbitrary historical
   association-list values. *)
Theorem ac_merge_prefix_bounds:
  !xs cs su0 n mp su.
    ac_merge_prefix_reachable xs cs su0 n mp su ==>
    n <= LENGTH xs /\ ir_supply_extends su0 su
Proof
  ho_match_mp_tac ac_merge_prefix_reachable_ind >>
  simp[ir_supply_extends_refl] >> rpt gen_tac >> strip_tac >>
  drule ac_merge_inst_fresh >> strip_tac >>
  metis_tac[ir_supply_extends_trans]
QED

Theorem ac_merge_prefix_completion:
  !xs cs su0 n mp su.
    ac_merge_prefix_reachable xs cs su0 n mp su ==>
    SND (ac_merge_insts cs [] su0 xs) =
    SND (ac_merge_insts cs mp su (DROP n xs))
Proof
  ho_match_mp_tac ac_merge_prefix_reachable_ind >> rpt strip_tac
  >- simp[] >>
  `DROP n xs = EL n xs :: DROP (SUC n) xs` by
    simp[DROP_CONS_EL] >>
  gvs[Once ac_merge_insts_def] >>
  Cases_on `ac_merge_insts cs mp' su' (DROP (SUC n) xs)` >> gvs[]
QED

Theorem ac_merge_prefix_remaining_supply:
  ac_merge_prefix_reachable xs cs su0 n mp su ==>
  ir_supply_extends su (SND (ac_merge_insts cs [] su0 xs))
Proof
  strip_tac >> drule ac_merge_prefix_completion >> strip_tac >>
  Cases_on `ac_merge_insts cs mp su (DROP n xs)` >> gvs[] >>
  drule ac_merge_insts_fresh >> simp[]
QED

Theorem ac_merge_static_initial:
  ir_supply_extends (SND (ac_merge_insts cs [] su0 xs)) su_end ==>
  ac_merge_static xs cs su0 su_end 0 [] su0
Proof
  strip_tac >> simp[ac_merge_static_def, ac_merge_prefix_zero] >>
  irule ir_supply_extends_trans >>
  qexists `SND (ac_merge_insts cs [] su0 xs)` >> simp[] >>
  irule ac_merge_prefix_remaining_supply >>
  qexistsl [`[]`,`0`] >> simp[ac_merge_prefix_zero]
QED

Theorem ac_merge_static_step:
  ir_supply_extends (SND (ac_merge_insts cs [] su0 xs)) su_end /\
  ac_merge_static xs cs su0 su_end n mp su /\ n < LENGTH xs /\
  ac_merge_inst cs mp su (EL n xs) = (mp',out,su') ==>
  ac_merge_static xs cs su0 su_end (SUC n) mp' su' /\
  ir_supply_extends su su'
Proof
  rpt strip_tac
  >- (simp[ac_merge_static_def] >>
      `ac_merge_prefix_reachable xs cs su0 (SUC n) mp' su'` by
        (irule ac_merge_prefix_step >> fs[ac_merge_static_def] >> metis_tac[]) >>
      simp[] >> irule ir_supply_extends_trans >>
      qexists `SND (ac_merge_insts cs [] su0 xs)` >> simp[] >>
      irule ac_merge_prefix_remaining_supply >> metis_tac[]) >>
  drule ac_merge_inst_fresh >> simp[]
QED

Theorem ac_merge_inst_accumulator_step:
  ac_merge_inst cs mp su inst = (mp',out,su') ==>
  mp' = mp \/ (?p. mp' = (inst.inst_id,p)::mp)
Proof
  simp[ac_merge_inst_def] >>
  Cases_on `FIND (\mc. mc.mc_second_id = inst.inst_id) cs` >> simp[]
  >- (strip_tac >> gvs[AllCaseEqs()]) >>
  rename1 `FIND _ _ = SOME mc` >>
  `mc.mc_second_id = inst.inst_id` by (imp_res_tac FIND_P >> fs[]) >>
  Cases_on `ALOOKUP mp mc.mc_first_id` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem ac_merge_prefix_keys:
  !xs cs su0 n mp su.
    ac_merge_prefix_reachable xs cs su0 n mp su ==>
    !k p. MEM (k,p) mp ==> ?a. a < n /\ a < LENGTH xs /\
      (EL a xs).inst_id = k
Proof
  ho_match_mp_tac ac_merge_prefix_reachable_ind >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule ac_merge_inst_accumulator_step >> strip_tac >> gvs[] >>
  rpt gen_tac >> strip_tac
  >- (first_x_assum drule >> strip_tac >> qexists `a` >> simp[]) >>
  gvs[] >- (qexists `n` >> simp[]) >>
  first_x_assum drule >> strip_tac >> qexists `a` >> simp[]
QED

Theorem ac_merge_prefix_unprocessed:
  ac_merge_prefix_reachable xs cs su0 n mp su /\
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
  n <= b /\ b < LENGTH xs ==>
  ALOOKUP mp (EL b xs).inst_id = NONE
Proof
  rpt strip_tac >>
  Cases_on `ALOOKUP mp (EL b xs).inst_id` >> simp[] >>
  drule ALOOKUP_MEM >> strip_tac >>
  drule_all ac_merge_prefix_keys >> strip_tac >>
  `a = b` by
    (qpat_x_assum `ALL_DISTINCT _`
       (mp_tac o REWRITE_RULE [EL_ALL_DISTINCT_EL_EQ]) >>
     disch_then (qspecl_then [`a`,`b`] mp_tac) >> simp[EL_MAP]) >>
  decide_tac
QED

Theorem ac_merge_static_used_vars:
  ac_merge_static xs cs su0 su_end n mp su /\
  (set su_end.irs_used_vars DIFF set su0.irs_used_vars) SUBSET X ==>
  !v. MEM v su.irs_used_vars ==> MEM v su0.irs_used_vars \/ v IN X
Proof
  simp[ac_merge_static_def, ir_supply_extends_def,
       list_subset_def, EVERY_MEM, SUBSET_DEF] >> metis_tac[]
QED

Theorem ac_merge_inst_accumulator_origin:
  ac_merge_inst cs mp su inst = (mp',out,su') ==>
  !k p. MEM (k,p) mp' ==>
    MEM (k,p) mp \/
    (?mc. MEM mc cs /\ mc.mc_second_id = inst.inst_id /\
          p = ac_merge_resolve mp mc) \/
    (?v. p = Var v /\ MEM v su'.irs_used_vars /\ ~MEM v su.irs_used_vars)
Proof
  simp[ac_merge_inst_def] >>
  Cases_on `FIND (\mc. mc.mc_second_id = inst.inst_id) cs` >> simp[]
  >- (rpt strip_tac >> gvs[AllCaseEqs()]) >>
  rename1 `FIND _ _ = SOME mc` >>
  `MEM mc cs /\ mc.mc_second_id = inst.inst_id` by
    (imp_res_tac FIND_P >> imp_res_tac FIND_MEM >> fs[]) >>
  Cases_on `ALOOKUP mp mc.mc_first_id` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[AllCaseEqs(), ac_merge_resolve_def] >>
  imp_res_tac fresh_ir_var_contract >>
  gvs[fresh_inst_id_def] >> metis_tac[]
QED

Theorem ac_merge_operand_origin_mono:
  ac_merge_operand_origin xs dfg X n p /\ n <= m ==>
  ac_merge_operand_origin xs dfg X m p
Proof
  simp[ac_merge_operand_origin_def] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem ac_merge_prefix_operand_origin:
  !xs cs su0 n mp su.
    ac_merge_prefix_reachable xs cs su0 n mp su ==>
    !dfg X su_end.
    ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
    (!mc. MEM mc cs ==> ?i j c.
      i < j /\ j < LENGTH xs /\
      (EL i xs).inst_id = mc.mc_first_id /\
      (EL j xs).inst_id = mc.mc_second_id /\
      (EL i xs).inst_opcode = ASSERT /\
      (EL i xs).inst_operands = [c] /\
      ac_get_iszero_operand dfg {} c = SOME mc.mc_first_pred) /\
    ir_supply_extends su su_end /\
    (set su_end.irs_used_vars DIFF set su0.irs_used_vars) SUBSET X ==>
    !k p. MEM (k,p) mp ==> ac_merge_operand_origin xs dfg X n p
Proof
  ho_match_mp_tac ac_merge_prefix_reachable_strongind >> simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `ir_supply_extends su su'` by metis_tac[ac_merge_inst_fresh] >>
  `ir_supply_extends su su_end` by metis_tac[ir_supply_extends_trans] >>
  `!k p. MEM (k,p) mp ==> ac_merge_operand_origin xs dfg X n p` by
    metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  drule ac_merge_inst_accumulator_origin >>
  disch_then (qspecl_then [`k`,`p`] mp_tac) >> simp[] >> strip_tac
  >- metis_tac[ac_merge_operand_origin_mono, LESS_EQ_SUC_REFL]
  >- (rename1 `MEM mc cs` >>
      first_x_assum drule >> strip_tac >>
      `j = n` by
        (qpat_x_assum `ALL_DISTINCT _`
           (mp_tac o REWRITE_RULE [EL_ALL_DISTINCT_EL_EQ]) >>
         disch_then (qspecl_then [`j`,`n`] mp_tac) >> simp[EL_MAP]) >>
      gvs[ac_merge_resolve_def, AllCaseEqs()]
      >- (simp[ac_merge_operand_origin_def] >> disj2_tac >>
          qexistsl [`i`,`c`] >> simp[]) >>
      drule ALOOKUP_MEM >> strip_tac >>
      metis_tac[ac_merge_operand_origin_mono, LESS_EQ_SUC_REFL]) >>
  `ir_supply_extends su0 su` by metis_tac[ac_merge_prefix_bounds] >>
  fs[ir_supply_extends_def, list_subset_def, EVERY_MEM, SUBSET_DEF] >>
  simp[ac_merge_operand_origin_def] >> metis_tac[]
QED

Theorem ac_merge_pending_operand_origin:
  ac_merge_static xs cs su0 su_end n mp su /\
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
  (!mc. MEM mc cs ==> ?i j c.
    i < j /\ j < LENGTH xs /\
    (EL i xs).inst_id = mc.mc_first_id /\
    (EL j xs).inst_id = mc.mc_second_id /\
    (EL i xs).inst_opcode = ASSERT /\
    (EL i xs).inst_operands = [c] /\
    ac_get_iszero_operand dfg {} c = SOME mc.mc_first_pred) /\
  (set su_end.irs_used_vars DIFF set su0.irs_used_vars) SUBSET X /\
  ac_merge_pending xs cs n mp su = SOME (k,p) ==>
  ac_merge_operand_origin xs dfg X n p
Proof
  simp[ac_merge_static_def, ac_merge_pending_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> rename1 `FIND _ cs = SOME mc` >>
  `MEM mc cs /\ ac_merge_crossing xs n mc` by
    (imp_res_tac FIND_P >> imp_res_tac FIND_MEM >> fs[]) >>
  Cases_on `ALOOKUP mp mc.mc_first_id`
  >- (gvs[ac_merge_resolve_def] >>
      qpat_x_assum `!mc. MEM mc cs ==> _` drule >> strip_tac >>
      fs[ac_merge_crossing_def] >>
      rename1 `a < n` >>
      `i < LENGTH xs /\ a < LENGTH xs` by decide_tac >>
      `i = a` by
        (qpat_x_assum `ALL_DISTINCT _`
           (mp_tac o REWRITE_RULE [EL_ALL_DISTINCT_EL_EQ]) >>
         disch_then (qspecl_then [`i`,`a`] mp_tac) >> simp[EL_MAP]) >>
      simp[ac_merge_operand_origin_def] >> disj2_tac >>
      qexistsl [`i`,`c`] >> simp[] >> decide_tac) >>
  gvs[ac_merge_resolve_def] >>
  drule ALOOKUP_MEM >> strip_tac >>
  drule ac_merge_prefix_operand_origin >>
  disch_then (qspecl_then [`dfg`,`X`,`su_end`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem ac_merge_safe_gap_crossing_indices:
  i < n /\ n <= j /\ i' < n /\ n <= j' /\
  (EL i xs).inst_opcode = ASSERT /\ (EL j xs).inst_opcode = ASSERT /\
  (EL i' xs).inst_opcode = ASSERT /\ (EL j' xs).inst_opcode = ASSERT /\
  (!k. i < k /\ k < j ==> ac_is_safe_between (EL k xs)) /\
  (!k. i' < k /\ k < j' ==> ac_is_safe_between (EL k xs)) ==>
  i = i' /\ j = j'
Proof
  strip_tac >>
  `!k. ac_is_safe_between (EL k xs) ==> (EL k xs).inst_opcode <> ASSERT` by
    simp[ac_is_safe_between_def, ac_is_volatile_def] >>
  `i = i'` by
    (Cases_on `i < i'`
     >- (`i' < j` by decide_tac >> metis_tac[]) >>
     Cases_on `i' < i`
     >- (`i < j'` by decide_tac >> metis_tac[]) >> decide_tac) >>
  gvs[] >> Cases_on `j < j'`
  >- (`i < j` by decide_tac >> metis_tac[]) >>
  Cases_on `j' < j`
  >- (`i < j'` by decide_tac >> metis_tac[]) >> simp[]
QED

Theorem ac_merge_crossing_unique_conditional:
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
  (!mc. MEM mc cs ==> ?i j c d.
    i < j /\ j < LENGTH xs /\
    (EL i xs).inst_id = mc.mc_first_id /\
    (EL j xs).inst_id = mc.mc_second_id /\
    (EL i xs).inst_opcode = ASSERT /\ (EL i xs).inst_operands = [c] /\
    ac_get_iszero_operand dfg {} c = SOME mc.mc_first_pred /\
    (EL j xs).inst_opcode = ASSERT /\ (EL j xs).inst_operands = [d] /\
    ac_get_iszero_operand dfg {} d = SOME mc.mc_second_pred /\
    (!k. i < k /\ k < j ==> ac_is_safe_between (EL k xs))) ==>
  !n mc mc'. MEM mc cs /\ MEM mc' cs /\
    ac_merge_crossing xs n mc /\ ac_merge_crossing xs n mc' ==> mc = mc'
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `!a b. a < LENGTH xs /\ b < LENGTH xs /\
          (EL a xs).inst_id = (EL b xs).inst_id ==> a = b` by
    metis_tac[LENGTH_MAP, EL_MAP, ALL_DISTINCT_EL_IMP] >>
  qpat_assum `!mc. MEM mc cs ==> _` (qspec_then `mc` mp_tac) >>
  qpat_x_assum `!mc. MEM mc cs ==> _` (qspec_then `mc'` mp_tac) >>
  simp[] >> rpt strip_tac >>
  `?a b. a < n /\ n <= b /\ b < LENGTH xs /\
     (EL a xs).inst_id = mc.mc_first_id /\
     (EL b xs).inst_id = mc.mc_second_id` by metis_tac[ac_merge_crossing_def] >>
  `?a' b'. a' < n /\ n <= b' /\ b' < LENGTH xs /\
     (EL a' xs).inst_id = mc'.mc_first_id /\
     (EL b' xs).inst_id = mc'.mc_second_id` by metis_tac[ac_merge_crossing_def] >>
  `a = i' /\ b = j' /\ a' = i /\ b' = j` by
    (rpt conj_tac >> first_x_assum irule >> simp[] >> decide_tac) >>
  qpat_x_assum `!a b. _ ==> a = b` kall_tac >>
  gvs[] >>
  `a = a' /\ b = b'` by
    metis_tac[ac_merge_safe_gap_crossing_indices] >>
  gvs[] >> Cases_on `mc` >> Cases_on `mc'` >> gvs[]
QED

Theorem ac_merge_endpoint_crossing:
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
  i < j /\ j < LENGTH xs /\ n < LENGTH xs /\
  (EL i xs).inst_id = mc.mc_first_id /\
  (EL j xs).inst_id = mc.mc_second_id ==>
  (((EL n xs).inst_id = mc.mc_second_id ==> ac_merge_crossing xs n mc) /\
   ((EL n xs).inst_id = mc.mc_first_id ==> ac_merge_crossing xs (SUC n) mc))
Proof
  strip_tac >>
  `!a b. a < LENGTH xs /\ b < LENGTH xs /\
          (EL a xs).inst_id = (EL b xs).inst_id ==> a = b` by
    metis_tac[LENGTH_MAP, EL_MAP, ALL_DISTINCT_EL_IMP] >>
  conj_tac >> strip_tac
  >- (`n = j` by (first_x_assum irule >> simp[]) >>
      simp[ac_merge_crossing_def] >> qexistsl [`i`,`j`] >> simp[]) >>
  `n = i` by (first_x_assum irule >> simp[] >> decide_tac) >>
  simp[ac_merge_crossing_def] >> qexistsl [`i`,`j`] >> simp[]
QED

Theorem ac_merge_endpoint_find_conditional:
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
  (!mc. MEM mc cs ==> ?i j c d.
    i < j /\ j < LENGTH xs /\
    (EL i xs).inst_id = mc.mc_first_id /\
    (EL j xs).inst_id = mc.mc_second_id /\
    (EL i xs).inst_opcode = ASSERT /\ (EL i xs).inst_operands = [c] /\
    ac_get_iszero_operand dfg {} c = SOME mc.mc_first_pred /\
    (EL j xs).inst_opcode = ASSERT /\ (EL j xs).inst_operands = [d] /\
    ac_get_iszero_operand dfg {} d = SOME mc.mc_second_pred /\
    (!k. i < k /\ k < j ==> ac_is_safe_between (EL k xs))) ==>
  !n mc. n < LENGTH xs /\ MEM mc cs ==>
    (((EL n xs).inst_id = mc.mc_second_id ==>
       FIND (ac_merge_crossing xs n) cs = SOME mc /\
       FIND (\c. c.mc_second_id = (EL n xs).inst_id) cs = SOME mc) /\
     ((EL n xs).inst_id = mc.mc_first_id ==>
       FIND (ac_merge_crossing xs (SUC n)) cs = SOME mc))
Proof
  strip_tac >>
  `!n mc mc'. MEM mc cs /\ MEM mc' cs /\
     ac_merge_crossing xs n mc /\ ac_merge_crossing xs n mc' ==> mc = mc'` by
    (rpt strip_tac >> irule ac_merge_crossing_unique_conditional >>
     simp[] >> metis_tac[]) >>
  `!n mc. n < LENGTH xs /\ MEM mc cs ==>
    (((EL n xs).inst_id = mc.mc_second_id ==> ac_merge_crossing xs n mc) /\
     ((EL n xs).inst_id = mc.mc_first_id ==> ac_merge_crossing xs (SUC n) mc))` by
    (rpt strip_tac >>
     qpat_x_assum `!mc. MEM mc cs ==> _` drule >> strip_tac >>
     metis_tac[ac_merge_endpoint_crossing]) >>
  qpat_x_assum `!mc. MEM mc cs ==> _` kall_tac >>
  rpt gen_tac >> strip_tac >> conj_tac >> strip_tac
  >- (`ac_merge_crossing xs n mc` by metis_tac[] >>
      `!c. MEM c cs /\ c.mc_second_id = (EL n xs).inst_id ==> c = mc` by
        metis_tac[] >>
      qpat_x_assum `!n mc. _` kall_tac >>
      `!c. MEM c cs /\ ac_merge_crossing xs n c ==> c = mc` by metis_tac[] >>
      qpat_x_assum `!n mc mc'. _` kall_tac >>
      Induct_on `cs` >> simp[FIND_thm] >> rpt strip_tac >> metis_tac[]) >>
  `ac_merge_crossing xs (SUC n) mc` by metis_tac[] >>
  qpat_x_assum `!n mc. _` kall_tac >>
  Induct_on `cs` >> simp[FIND_thm] >> rpt strip_tac >> metis_tac[]
QED

Theorem ac_merge_crossing_interval:
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\ i < j /\ j < LENGTH xs /\
  (EL i xs).inst_id = mc.mc_first_id /\
  (EL j xs).inst_id = mc.mc_second_id ==>
  !n. ac_merge_crossing xs n mc <=> i < n /\ n <= j
Proof
  strip_tac >> gen_tac >> eq_tac
  >- (simp[ac_merge_crossing_def] >> rpt strip_tac >>
      `i < LENGTH xs /\ i' < LENGTH xs` by decide_tac >>
      `i = i' /\ j = j'` by
        (qpat_x_assum `ALL_DISTINCT _`
           (mp_tac o REWRITE_RULE [EL_ALL_DISTINCT_EL_EQ]) >>
         simp[EL_MAP] >> metis_tac[]) >> simp[]) >>
  strip_tac >> simp[ac_merge_crossing_def] >>
  qexistsl [`i`,`j`] >> simp[]
QED

Theorem ac_merge_crossing_carry:
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\ i < j /\ j < LENGTH xs /\
  (EL i xs).inst_id = mc.mc_first_id /\
  (EL j xs).inst_id = mc.mc_second_id /\
  (!k. i < k /\ k < j ==> ac_is_safe_between (EL k xs)) /\
  (EL n xs).inst_id <> mc.mc_first_id /\
  (EL n xs).inst_id <> mc.mc_second_id ==>
  (ac_merge_crossing xs n mc <=> ac_merge_crossing xs (SUC n) mc) /\
  (ac_merge_crossing xs n mc ==> ac_is_safe_between (EL n xs))
Proof
  strip_tac >>
  `!m. ac_merge_crossing xs m mc <=> i < m /\ m <= j` by
    (gen_tac >> irule ac_merge_crossing_interval >> simp[] >> metis_tac[]) >>
  `n <> i /\ n <> j` by metis_tac[] >>
  simp[]
QED
