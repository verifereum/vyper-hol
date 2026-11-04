(* Supply alignment of finite unchanged suffix segments. *)
Theory o1LowerDloadForwardAbort
Ancestors
  o1LowerDloadJointAssign o1LowerDloadAvailableSuffix o1ContractLowerDload
  lowerDloadDefs contextCodegenRel venomExecSemantics venomExecProps
  o1LowerDloadJointRelation o1LowerDloadExceptional o1LowerDloadJointScalar
  o1LowerDloadJointRangeCopy o1PassContract unitShapeDefs venomWf
  o1LowerDloadOccurrence o1LowerDloadEnvironment venomInst list

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

(* The COPY discards the memory relation; only the finite suffix is aligned. *)
Theorem ld_available_forward_abort:
  s.vs_labels = t.vs_labels /\
  (!v. v IN V ==> (IS_SOME (FLOOKUP s.vs_vars v) <=>
                   IS_SOME (FLOOKUP t.vs_vars v))) /\
  revert_forward_pair bb s.vs_inst_idx j /\
  (!k. k <= j - s.vs_inst_idx ==>
    get_instruction bb (s.vs_inst_idx+k) =
    get_instruction bb' (t.vs_inst_idx+k)) /\
  (!k ii v. k <= j - s.vs_inst_idx /\
    get_instruction bb (s.vs_inst_idx+k) = SOME ii /\
    MEM (Var v) ii.inst_operands ==> v IN V) /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dst;src;sz] /\
  eval_operand src s = eval_operand src t /\
  eval_operand sz s = eval_operand sz t /\
  s.vs_returndata = t.vs_returndata /\
  exec_block fuel C bb s = Abort reason s1 ==>
  ?t1. exec_block fuel C' bb' t = Abort reason t1
Proof
  strip_tac >>
  `get_instruction bb' t.vs_inst_idx = SOME inst` by
    (qpat_x_assum `!k. k <= _ ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  `IS_SOME (eval_operand dst s) <=> IS_SOME (eval_operand dst t)` by
    (irule ld_available_operand >> simp[] >> qexists_tac `V` >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `!k ii v. _` (qspec_then `0` mp_tac) >>
     simp[] >> metis_tac[MEM]) >>
  qpat_x_assum `exec_block fuel C bb s = _` mp_tac >>
  simp[Once exec_block_def, step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs(), is_terminator_def] >> strip_tac >>
  (Cases_on `eval_operand dst t` >- gvs[] >>
   rename1 `eval_operand dst t = SOME target_dest` >>
   pure_once_rewrite_tac[exec_block_def] >> pure_asm_rewrite_tac[] >>
   simp[step_inst_non_invoke] >>
   asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
   simp[is_terminator_def] >>
   qpat_x_assum `write_memory_with_expansion _ _ s = s''` (SUBST_ALL_TAC o SYM) >>
   drule_at (Pat `exec_block _ _ _ _ = _`) ld_available_suffix_abort >>
   disch_then irule >>
   simp[venomStateTheory.write_memory_with_expansion_def,
        venomStateTheory.write_memory_def] >>
   qpat_x_assum `revert_forward_pair _ _ _`
     (strip_assume_tac o REWRITE_RULE [revert_forward_pair_def]) >>
   qexistsl_tac [`V`, `j - SUC s.vs_inst_idx`, `inst2`] >>
   simp[] >>
   (conj_tac
    >- (rpt strip_tac >>
        `SUC k <= j - s.vs_inst_idx` by decide_tac >>
        qpat_x_assum `!k ii v. _` (qspec_then `SUC k` mp_tac) >>
        simp[NoAsms, arithmeticTheory.ADD_CLAUSES] >>
        fs[arithmeticTheory.ADD_CLAUSES] >> metis_tac[]) >>
    conj_tac
    >- (rpt strip_tac >>
        `s.vs_inst_idx < k + SUC s.vs_inst_idx /\
         k + SUC s.vs_inst_idx < j` by decide_tac >> metis_tac[]) >>
    rpt strip_tac >>
    `SUC k <= j - s.vs_inst_idx` by decide_tac >>
    qpat_x_assum `!k. k <= _ ==> _` (qspec_then `SUC k` mp_tac) >>
    simp[arithmeticTheory.ADD_CLAUSES]))
QED

Theorem ld_joint_forward_abort:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = RETURNDATACOPY /\ in_revert_forward fn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block fuel C bb s = Abort reason s1 ==>
  ?fn' bb' t1. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    exec_block fuel C' bb' t = Abort reason t1
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by
    (drule ld_joint_source >> strip_tac >>
     drule occ_frame_reachable_annotation >> simp[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (gvs[o1_ctx_shape_def, EVERY_MEM] >>
     first_x_assum drule >> simp[o1_fn_shape_def, wf_function_def, fn_labels_def]) >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (qpat_assum `active_inst _ _ _` mp_tac >>
     simp[NoAsms, active_inst_def] >> strip_tac >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb'` by
       (irule MEM_lookup_block >> simp[]) >>
     gvs[get_instruction_def]) >>
  `?j. revert_forward_pair bb s.vs_inst_idx j` by
    (qpat_x_assum `in_revert_forward _ _`
       (strip_assume_tac o REWRITE_RULE [in_revert_forward_def, revert_forward_at_def]) >>
     gvs[] >- metis_tac[] >>
     qpat_x_assum `revert_forward_pair _ _ _`
       (strip_assume_tac o REWRITE_RULE [revert_forward_pair_def]) >> gvs[]) >>
  `?dst src sz. inst.inst_operands = [dst;src;sz]` by
    metis_tac[revert_forward_pair_def, optionTheory.SOME_11] >>
  `eval_operand src s = eval_operand src t` by
    (drule ld_joint_copy_scalar_operand >> disch_then irule >> simp[]) >>
  `eval_operand sz s = eval_operand sz t` by
    (drule ld_joint_copy_scalar_operand >> disch_then irule >> simp[]) >>
  qhdtm_assum `ld_joint_boundary`
    (strip_assume_tac o REWRITE_RULE [ld_joint_boundary_def]) >>
  qhdtm_assum `ld_joint_frame`
    (strip_assume_tac o REWRITE_RULE [ld_joint_frame_def]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks)` by
    (qhdtm_assum `ld_joint_control`
       (strip_assume_tac o REWRITE_RULE [ld_joint_control_def]) >>
     drule lower_dload_function_supply_labels >> simp[fn_labels_def]) >>
  drule_all ld_joint_control_forward_fetch >> strip_tac >>
  qexistsl_tac [`fn'`,`bb'`] >> simp[] >>
  irule ld_available_forward_abort >>
  qexistsl_tac [`C`, `{v | MEM v (fn_ir_vars fn)}`, `bb`, `dst`, `inst`,
                 `j`, `s`, `s1`, `src`, `sz`] >>
  simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule ld_env_lookup_defined >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule ld_active_operand_ir_var >>
      qexistsl_tac [`ii`, `s with vs_inst_idx := s.vs_inst_idx + k`] >>
      simp[] >> simp[active_inst_def] >>
      `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
        metis_tac[lookup_block_MEM, lookup_block_label] >>
      qexists_tac `bb` >> gvs[get_instruction_def, AllCaseEqs()]) >>
  fs[ld_joint_local_fields_def]
QED
