(* Configured instruction-list slices and expansion control. *)
Theory o1LowerDloadSuppliedSegmentControl
Ancestors
  o1LowerDloadJointAssign o1LowerDloadJointRelation o1ContractLowerDload
  lowerDloadDefs irSupply contextCodegenRel venomExecProps venomInst venomState list

Theorem ld_supply_insts_slice:
  !u outs w j pre v inst es v'.
    lower_dload_insts_supply u ins = (outs,w) /\ j < LENGTH ins /\
    lower_dload_insts_supply u (TAKE j ins) = (pre,v) /\
    EL j ins = inst /\ lower_dload_inst_supply v inst = (es,v') ==>
    TAKE (LENGTH es) (DROP (LENGTH pre) outs) = es /\
    LENGTH pre + LENGTH es <= LENGTH outs /\
    lower_dload_insts_supply u (TAKE (SUC j) ins) = (pre ++ es,v')
Proof
  Induct_on `ins`
  >- simp[] >>
  rpt gen_tac >> Cases_on `j`
  >- (simp[lower_dload_insts_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[TAKE_APPEND1]) >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  strip_tac >>
  qpat_x_assum `lower_dload_insts_supply u (_::TAKE _ _) = _`
    (mp_tac o REWRITE_RULE [Once lower_dload_insts_supply_def]) >>
  simp[NoAsms, AllCaseEqs()] >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  simp[Once lower_dload_insts_supply_def, DROP_APPEND, DROP_LENGTH_TOO_LONG,
       APPEND_ASSOC]
QED


Theorem ld_supply_dload_shape:
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [ptr] /\
  inst.inst_outputs = [out] /\ lower_dload_inst_supply v inst = (es,v') ==>
  LENGTH es = 4 /\ (HD es).inst_id = v.irs_next_inst /\
  (HD es).inst_opcode = ALLOCA /\ (HD es).inst_operands = [Lit 32w]
Proof
  simp[lower_dload_inst_supply_def, fresh_inst_id_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac fresh_ir_var_contract >> gvs[]
QED

Theorem ld_supply_dloadbytes_length:
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;src;sz] /\
  lower_dload_inst_supply v inst = (es,v') ==> LENGTH es = 2
Proof
  simp[lower_dload_inst_supply_def, fresh_inst_id_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

(* Reservation monotonicity needs no global well-formedness of reserved IDs. *)
Theorem ld_supply_inst_reservations:
  lower_dload_inst_supply u inst = (es,v) ==>
  u.irs_next_inst <= v.irs_next_inst /\
  (!x. MEM x u.irs_used_vars ==> MEM x v.irs_used_vars)
Proof
  Cases_on `inst.inst_opcode = DLOAD`
  >- (simp[lower_dload_inst_supply_def, fresh_inst_id_def, AllCaseEqs()] >>
      rpt strip_tac >> imp_res_tac fresh_ir_var_contract >> gvs[] >>
      metis_tac[]) >>
  Cases_on `inst.inst_opcode = DLOADBYTES`
  >- (simp[lower_dload_inst_supply_def, fresh_inst_id_def, AllCaseEqs()] >>
      rpt strip_tac >> imp_res_tac fresh_ir_var_contract >> gvs[] >>
      metis_tac[]) >>
  simp[lower_dload_inst_supply_def]
QED

Theorem ld_supply_insts_reservations:
  !u es v. lower_dload_insts_supply u ins = (es,v) ==>
  u.irs_next_inst <= v.irs_next_inst /\
  (!x. MEM x u.irs_used_vars ==> MEM x v.irs_used_vars)
Proof
  Induct_on `ins`
  >- simp[lower_dload_insts_supply_def] >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> drule ld_supply_inst_reservations >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem ld_supply_blocks_reservations:
  !u es v. lower_dload_blocks_supply u bs = (es,v) ==>
  u.irs_next_inst <= v.irs_next_inst /\
  (!x. MEM x u.irs_used_vars ==> MEM x v.irs_used_vars)
Proof
  Induct_on `bs`
  >- simp[lower_dload_blocks_supply_def] >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs()] >>
  rpt strip_tac >> drule ld_supply_insts_reservations >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem ld_joint_control_segment:
  ld_joint_control u fn fn' s t /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  active_inst fn inst s ==>
  ?v es v' bb'. lower_dload_inst_supply v inst = (es,v') /\
    EVERY (\id. id < v.irs_next_inst) (fn_ir_inst_ids fn) /\
    (!x. MEM x (fn_ir_vars fn) ==> MEM x v.irs_used_vars) /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    TAKE (LENGTH es) (DROP t.vs_inst_idx bb'.bb_instructions) = es /\
    t.vs_inst_idx + LENGTH es <= LENGTH bb'.bb_instructions /\
    (!ptr out. inst.inst_opcode = DLOAD /\ inst.inst_operands = [ptr] /\
      inst.inst_outputs = [out] ==>
      ld_joint_scratch u fn inst.inst_id (HD es).inst_id) /\
    (!next. active_inst fn next (s with vs_inst_idx := SUC s.vs_inst_idx) ==>
      ld_joint_control u fn fn'
        (s with vs_inst_idx := SUC s.vs_inst_idx)
        (t with vs_inst_idx := t.vs_inst_idx + LENGTH es))
Proof
  simp[ld_joint_control_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lower_dload_block_supply u1 bb` >>
  `MEM bb fn.fn_blocks` by
    (simp[MEM_EL] >> qexists_tac `k` >> simp[Abbr `bb`]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> simp[]) >>
  `EL s.vs_inst_idx bb.bb_instructions = inst` by
    (gvs[active_inst_def] >>
     `lookup_block t.vs_current_bb fn.fn_blocks = SOME bb'` by
       (irule MEM_lookup_block >> simp[]) >> gvs[]) >>
  qpat_assum `lower_dload_block_supply _ _ = _`
    (mp_tac o REWRITE_RULE [lower_dload_block_supply_def]) >>
  simp[NoAsms, AllCaseEqs()] >> strip_tac >>
  Cases_on `lower_dload_inst_supply u3 inst` >>
  rename1 `lower_dload_inst_supply u3 inst = (es,v')` >>
  drule_all ld_supply_insts_slice >> strip_tac >>
  `u.irs_next_inst <= u3.irs_next_inst /\
   (!x. MEM x u.irs_used_vars ==> MEM x u3.irs_used_vars)` by
    (drule ld_supply_blocks_reservations >> strip_tac >>
     qpat_assum `lower_dload_insts_supply _ (TAKE s.vs_inst_idx _) = _`
       (mp_tac o MATCH_MP ld_supply_insts_reservations) >> strip_tac >>
     conj_tac >- decide_tac >> metis_tac[]) >>
  qexistsl_tac [`u3`,`es`,`v'`,`EL k fn'.fn_blocks`] >> simp[] >>
  conj_tac
  >- (gvs[venomFnScheduleRunnerTheory.ir_supply_covers_fn_def, EVERY_MEM] >>
      rpt strip_tac >> res_tac >> decide_tac) >>
  conj_tac
  >- (gvs[venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
          venomFnScheduleRunnerTheory.list_subset_def, EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (irule MEM_lookup_block >> conj_tac
      >- (drule lower_dload_function_supply_labels >> simp[fn_labels_def]) >>
      conj_tac
      >- (qpat_assum `_ with bb_instructions := _ = _` (SUBST1_TAC o SYM) >>
          simp[]) >>
      simp[MEM_EL] >> qexists_tac `k` >> simp[]) >>
  qpat_assum `_ with bb_instructions := _ = _`
    (fn th => once_rewrite_tac[GSYM th]) >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `es <> [] /\ (HD es).inst_opcode = ALLOCA /\
       (HD es).inst_operands = [Lit 32w]` by
        (gvs[lower_dload_inst_supply_def, fresh_inst_id_def, AllCaseEqs()]) >>
      simp[ld_joint_scratch_def] >> qexists_tac `k` >>
      qunabbrev_tac `bb` >> simp[] >>
      qexistsl_tac [`s.vs_inst_idx`,`expanded`,`u3`,`es`,`v'`] >>
      simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `SUC s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `active_inst fn next _` mp_tac >>
     simp[active_inst_def] >> strip_tac >>
     qmatch_asmsub_rename_tac `SUC s.vs_inst_idx < LENGTH dest.bb_instructions` >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME dest` by
       (irule MEM_lookup_block >> simp[]) >> gvs[]) >>
  qexistsl_tac [`k`,`pre`,`u1`,`u2`,`expanded ++ es`,`v'`] >>
  gvs[Abbr `bb`]
QED

Theorem ld_supply_expansion_fresh:
  lower_dload_inst_supply v inst = (es,v') /\
  ((inst.inst_opcode = DLOAD /\ inst.inst_operands = [ptr] /\
      inst.inst_outputs = [out]) \/
   (inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;ptr;sz])) ==>
  EVERY (\x. ~MEM x v.irs_used_vars)
    (FLAT (MAP (\i. i.inst_outputs)
      (TAKE (if inst.inst_opcode = DLOAD then 2 else 1) es))) /\
  (HD es).inst_id = v.irs_next_inst /\
  v.irs_next_inst < v'.irs_next_inst
Proof
  strip_tac >>
  gvs[lower_dload_inst_supply_def, fresh_inst_id_def, AllCaseEqs()] >>
  imp_res_tac fresh_ir_var_contract >> gvs[] >> metis_tac[]
QED

Theorem ld_supply_expansion_source_fresh:
  EVERY (\id. id < v.irs_next_inst) (fn_ir_inst_ids fn) /\
  (!x. MEM x (fn_ir_vars fn) ==> MEM x v.irs_used_vars) /\
  lower_dload_inst_supply v inst = (es,v') /\
  ((inst.inst_opcode = DLOAD /\ inst.inst_operands = [ptr] /\
      inst.inst_outputs = [out]) \/
   (inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;ptr;sz])) ==>
  ~MEM (HD es).inst_id (fn_ir_inst_ids fn) /\
  EVERY (\x. ~MEM x (fn_ir_vars fn))
    (FLAT (MAP (\i. i.inst_outputs)
      (TAKE (if inst.inst_opcode = DLOAD then 2 else 1) es)))
Proof
  strip_tac >> drule ld_supply_expansion_fresh >> simp[] >> strip_tac >>
  gvs[EVERY_MEM] >> metis_tac[prim_recTheory.LESS_REFL]
QED

Theorem ld_supply_blocks_flat:
  !u out v. lower_dload_blocks_supply u bs = (out,v) ==>
  lower_dload_insts_supply u (fn_insts_blocks bs) = (fn_insts_blocks out,v)
Proof
  Induct_on `bs`
  >- simp[lower_dload_blocks_supply_def, fn_insts_blocks_def,
          lower_dload_insts_supply_def] >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs()] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[fn_insts_blocks_def] >>
  Cases_on `lower_dload_insts_supply u (h.bb_instructions ++ fn_insts_blocks bs)` >>
  drule lower_dload_insts_supply_append >> strip_tac >> gvs[]
QED

Theorem ld_supply_prefix_counter_order:
  !u i j pre v later w es v'.
  i < j /\ j <= LENGTH ins /\
  lower_dload_insts_supply u (TAKE i ins) = (pre,v) /\
  lower_dload_insts_supply u (TAKE j ins) = (later,w) /\
  lower_dload_inst_supply v (EL i ins) = (es,v') /\
  v.irs_next_inst < v'.irs_next_inst ==>
  v.irs_next_inst < w.irs_next_inst
Proof
  Induct_on `ins`
  >- simp[] >> rpt gen_tac >> Cases_on `i` >> Cases_on `j` >>
  simp[lower_dload_insts_supply_def, AllCaseEqs()] >> rpt strip_tac
  >- (gvs[] >> drule ld_supply_insts_reservations >> strip_tac >> decide_tac) >>
  gvs[] >> first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

Theorem ld_blocks_flat_prefix:
  !k j. k < LENGTH bs /\ j < LENGTH (EL k bs).bb_instructions ==>
  let n = LENGTH (fn_insts_blocks (TAKE k bs)) + j in
    n < LENGTH (fn_insts_blocks bs) /\
    EL n (fn_insts_blocks bs) = EL j (EL k bs).bb_instructions /\
    TAKE n (fn_insts_blocks bs) =
      fn_insts_blocks (TAKE k bs) ++ TAKE j (EL k bs).bb_instructions
Proof
  Induct_on `bs`
  >- simp[] >> rpt gen_tac >> Cases_on `k` >>
  simp[fn_insts_blocks_def, LET_THM] >> strip_tac
  >- simp[EL_APPEND_EQN, TAKE_APPEND1] >>
  first_x_assum drule_all >> strip_tac >>
  gvs[LET_THM] >>
  simp[EL_APPEND_EQN, APPEND_ASSOC] >>
  Cases_on `j + LENGTH (fn_insts_blocks (TAKE n bs)) = 0`
  >- gvs[TAKE_APPEND1] >>
  simp[TAKE_APPEND2, APPEND_ASSOC]
QED

Theorem ld_scratch_flat_prefix:
  ld_joint_scratch u fn did aid ==>
  ?n before v es v'.
    n < LENGTH (fn_insts fn) /\
    (EL n (fn_insts fn)).inst_id = did /\
    lower_dload_insts_supply u (TAKE n (fn_insts fn)) = (before,v) /\
    lower_dload_inst_supply v (EL n (fn_insts fn)) = (es,v') /\
    aid = v.irs_next_inst /\ v.irs_next_inst < v'.irs_next_inst
Proof
  simp[ld_joint_scratch_def] >> rpt strip_tac >>
  drule ld_supply_blocks_flat >> strip_tac >>
  drule_all ld_blocks_flat_prefix >> simp[LET_THM] >> strip_tac >>
  `?prefix. lower_dload_insts_supply u
    (fn_insts_blocks (TAKE k fn.fn_blocks) ++
     TAKE j (EL k fn.fn_blocks).bb_instructions) = (prefix,u2)` by
    (Cases_on `lower_dload_insts_supply u
       (fn_insts_blocks (TAKE k fn.fn_blocks) ++
        TAKE j (EL k fn.fn_blocks).bb_instructions)` >>
     drule lower_dload_insts_supply_append >> strip_tac >> gvs[] >>
     metis_tac[]) >>
  `u2.irs_next_inst = aid /\ u2.irs_next_inst < u3.irs_next_inst` by
    (drule ld_supply_expansion_fresh >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`LENGTH (fn_insts_blocks (TAKE k fn.fn_blocks)) + j`,
               `prefix`,`u2`,`expansion`,`u3`] >>
  simp[fn_insts_def]
QED

Theorem ld_supply_prefix_counter_injective:
  i < LENGTH ins /\ j < LENGTH ins /\
  lower_dload_insts_supply u (TAKE i ins) = (pre,v) /\
  lower_dload_insts_supply u (TAKE j ins) = (later,w) /\
  lower_dload_inst_supply v (EL i ins) = (es,v') /\
  lower_dload_inst_supply w (EL j ins) = (fs,w') /\
  v.irs_next_inst < v'.irs_next_inst /\
  w.irs_next_inst < w'.irs_next_inst /\
  v.irs_next_inst = w.irs_next_inst ==> i = j
Proof
  strip_tac >>
  `i <= LENGTH ins /\ j <= LENGTH ins` by decide_tac >>
  Cases_on `i < j`
  >- (drule_all ld_supply_prefix_counter_order >> simp[]) >>
  Cases_on `j < i`
  >- (drule_all ld_supply_prefix_counter_order >> simp[]) >>
  decide_tac
QED

Theorem ld_joint_scratch_injective:
  ld_joint_scratch u fn did aid /\ ld_joint_scratch u fn did' aid ==>
  did = did'
Proof
  strip_tac >> imp_res_tac ld_scratch_flat_prefix >> gvs[] >>
  qpat_x_assum `ld_joint_scratch _ _ _ _` kall_tac >>
  qpat_x_assum `ld_joint_scratch _ _ _ _` kall_tac >>
  metis_tac[ld_supply_prefix_counter_injective]
QED

Theorem ld_joint_scratch_functional:
  ALL_DISTINCT (fn_ir_inst_ids fn) /\
  ld_joint_scratch u fn did aid /\ ld_joint_scratch u fn did aid' ==>
  aid = aid'
Proof
  strip_tac >> imp_res_tac ld_scratch_flat_prefix >>
  `fn_ir_inst_ids fn = MAP (\i. i.inst_id) (fn_insts fn)` by
    (qsuff_tac `!bs. FLAT (MAP block_ir_inst_ids bs) =
       MAP (\i. i.inst_id) (fn_insts_blocks bs)`
     >- simp[fn_ir_inst_ids_def, fn_insts_def] >>
     Induct >> simp[fn_insts_blocks_def, block_ir_inst_ids_def]) >>
  `n = n'` by
    (`ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by metis_tac[] >>
     `n < LENGTH (MAP (\i. i.inst_id) (fn_insts fn)) /\
      n' < LENGTH (MAP (\i. i.inst_id) (fn_insts fn))` by simp[] >>
     `EL n (MAP (\i. i.inst_id) (fn_insts fn)) =
      EL n' (MAP (\i. i.inst_id) (fn_insts fn))` by simp[EL_MAP] >>
     metis_tac[ALL_DISTINCT_EL_IMP]) >>
  gvs[]
QED
