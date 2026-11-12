(* A forwarding copy and its revert are simulated together: the copy
   overwrites every byte subsequently read by the revert. *)
Theory mem2varRevertForward
Ancestors
  mem2varInvariant mem2varDefs ptrDiscipline unitTransformDefs
  contextCodegenRel codegenRel venomWf venomExecSemantics venomState
  passSimulationDefs finite_map list words venomExecProofs mem2varFrame
  frameViewMemory regularCallEmitSim venomMemProps simplifyCfgFrameRf

Theorem m2v_step_back_assign_eval:
  step_inst fuel ctx inst s = OK t /\
  ~is_terminator inst.inst_opcode /\
  step_back_assign inst op = SOME op' ==>
  eval_operand op t = eval_operand op' s
Proof
  rpt strip_tac >> Cases_on `op` >>
  gvs[step_back_assign_def, eval_operand_def]
  >- (Cases_on `MEM s' inst.inst_outputs` >>
      gvs[AllCaseEqs()]
      >- (Cases_on `inst.inst_operands` >> gvs[] >>
          gvs[step_inst_non_invoke, step_inst_base_def,
              AllCaseEqs(), lookup_var_def, update_var_def, FLOOKUP_UPDATE])
      >> simp[eval_operand_def] >>
      metis_tac[venomInstProofsTheory.step_preserves_non_output_vars])
  >> metis_tac[step_inst_preserves_labels_always]
QED

Theorem m2v_public_eval_operand:
  m2v_public_rel fn s t /\ m2v_fresh_names_disjoint fn /\
  MEM inst (fn_insts fn) /\ MEM op inst.inst_operands ==>
  eval_operand op s = eval_operand op t
Proof
  rpt strip_tac >> Cases_on `op` >> simp[eval_operand_def]
  >- (gvs[m2v_public_rel_def, m2v_equiv_def,
          m2v_fresh_names_disjoint_def] >> metis_tac[])
  >> gvs[m2v_public_rel_def, m2v_equiv_def,
         m2v_frame_def, venom_state_component_equality]
QED

Theorem m2v_public_next:
  m2v_public_rel fn s t ==>
  m2v_public_rel fn (s with vs_inst_idx := i) (t with vs_inst_idx := j)
Proof
  simp[m2v_public_rel_def, m2v_equiv_def, lookup_var_def,
       in_promoted_region_def, mem_byte_def]
QED

Theorem m2v_public_update_var:
  m2v_public_rel fn s t ==>
  m2v_public_rel fn (update_var out value s) (update_var out value t)
Proof
  simp[m2v_public_rel_def, m2v_equiv_def, lookup_var_def,
       in_promoted_region_def, mem_byte_def, update_var_def,
       FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem m2v_mem_byte_read_byte:
  mem_byte i s = read_byte i s.vs_memory
Proof
  simp[mem_byte_def, codegenRelTheory.read_byte_def]
QED

Theorem m2v_public_common_write:
  m2v_public_rel fn s t ==>
  m2v_public_rel fn (write_memory_with_expansion off bytes s)
                   (write_memory_with_expansion off bytes t)
Proof
  strip_tac >> fs[m2v_public_rel_def, m2v_equiv_def] >>
  conj_tac
  >- simp[write_memory_with_expansion_def, lookup_var_def]
  >> simp[in_promoted_region_def, write_memory_with_expansion_vs_allocas,
          m2v_mem_byte_read_byte] >> rpt strip_tac >>
  irule write_memory_byte_agreement >>
  fs[in_promoted_region_def, m2v_mem_byte_read_byte]
QED

Theorem m2v_common_write_range:
  off <= i /\ i < off + LENGTH bytes ==>
  mem_byte i (write_memory_with_expansion off bytes s) =
  mem_byte i (write_memory_with_expansion off bytes t)
Proof
  simp[m2v_mem_byte_read_byte, read_byte_write_memory_with_expansion]
QED

Theorem m2v_padded_read_cong:
  (!i. off <= i /\ i < off + n ==> mem_byte i s = mem_byte i t) ==>
  read_memory off n s = read_memory off n t
Proof
  simp[m2v_mem_byte_read_byte, read_memory_def] >>
  simp[padded_memory_read_cong]
QED

Theorem m2v_public_finish:
  m2v_public_rel fn s t ==>
  m2v_public_rel fn (halt_state (set_returndata rd s))
                   (halt_state (set_returndata rd t))
Proof
  simp[m2v_public_rel_def, m2v_equiv_def, halt_state_def,
       set_returndata_def, lookup_var_def, in_promoted_region_def,
       mem_byte_def, m2v_frame_def, venom_state_component_equality] >>
  metis_tac[]
QED

Theorem m2v_reachable_prefix:
  !vs ctx stk PG G tn f inst s.
    frame_reachable vs ctx stk PG G tn f inst s ==>
    !name root.
      ctx.ctx_entry = SOME name /\
      lookup_function name ctx.ctx_functions = SOME root /\
      wf_function root /\
      EVERY (\ins. ins.inst_opcode <> INVOKE) (fn_insts root) ==>
      stk = [] /\ f = root /\
      (!bb p q. MEM bb root.fn_blocks /\
        bb.bb_label = s.vs_current_bb /\
        same_after_assigns
          (REVERSE (TAKE s.vs_inst_idx bb.bb_instructions)) p q ==>
        eval_operand p s = eval_operand q s)
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[enters_block_def] >>
      drule eval_phis_preserves_current_bb >> strip_tac >>
      `lookup_block lbl f.fn_blocks = SOME bb` by
        (irule venomExecProofsTheory.MEM_lookup_block >>
         gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
      gvs[] >>
      `!xs. EVERY (\ins. ins.inst_opcode <> ASSIGN)
         (TAKE (phi_prefix_length xs) xs)` by
        (gen_tac >> mp_tac (Q.SPEC `xs` analysisSimProofsBaseTheory.phi_prefix_all_phi) >>
         simp[EVERY_MEM] >> strip_tac >> rpt strip_tac >>
         first_x_assum drule >> simp[]) >>
      `p = q` by
        (gvs[scfg_same_after_nonassigns]) >> simp[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      first_x_assum (drule_then strip_assume_tac) >> gvs[] >>
      rpt strip_tac >>
      drule_all venomInstProofsTheory.step_preserves_control_flow >>
      strip_tac >> gvs[active_inst_def] >>
      rename1 `MEM oldbb f.fn_blocks` >>
      `lookup_block oldbb.bb_label f.fn_blocks = SOME oldbb` by
        (irule venomExecProofsTheory.MEM_lookup_block >>
         gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
      rename1 `step_inst fuel ctx (EL s.vs_inst_idx src.bb_instructions) s = OK s'` >>
      `src = oldbb` by
        (fs[wf_function_def, venomInstTheory.fn_labels_def] >>
         metis_tac[venomExecProofsTheory.MEM_lookup_block, optionTheory.SOME_11]) >>
      gvs[rich_listTheory.TAKE_SUC_BY_TAKE, REVERSE_SNOC,
          same_after_assigns_def, AllCaseEqs()] >>
      Cases_on `step_back_assign (EL s.vs_inst_idx oldbb.bb_instructions) p` >>
      gvs[] >>
      Cases_on `step_back_assign (EL s.vs_inst_idx oldbb.bb_instructions) q` >>
      gvs[] >>
      `eval_operand p s' = eval_operand q s'` by
        metis_tac[m2v_step_back_assign_eval] >>
      Cases_on `p` >> Cases_on `q` >>
      gvs[eval_operand_def, lookup_var_def])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      first_x_assum (drule_then strip_assume_tac) >> gvs[] >>
      rpt strip_tac >> gvs[enters_block_def] >>
      drule eval_phis_preserves_current_bb >> strip_tac >>
      rename1 `lookup_block s'.vs_current_bb f.fn_blocks = SOME entered` >>
      `lookup_block bb.bb_label f.fn_blocks = SOME bb` by
        (irule venomExecProofsTheory.MEM_lookup_block >>
         gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
      gvs[] >>
      `!xs. EVERY (\ins. ins.inst_opcode <> ASSIGN)
         (TAKE (phi_prefix_length xs) xs)` by
        (gen_tac >> mp_tac (Q.SPEC `xs` analysisSimProofsBaseTheory.phi_prefix_all_phi) >>
         simp[EVERY_MEM] >> strip_tac >> rpt strip_tac >>
         first_x_assum drule >> simp[]) >>
      `p = q` by gvs[scfg_same_after_nonassigns] >> simp[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      first_x_assum (drule_then strip_assume_tac) >> gvs[] >>
      drule_all ctxLookupAgreeHelpersTheory.EVERY_active_inst >> simp[])
  >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  gvs[EVERY_MEM, EXISTS_MEM]
QED

Theorem m2v_reachable_same_after_assigns:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  wf_function fn /\
  EVERY (\ins. ins.inst_opcode <> INVOKE) (fn_insts fn) /\
  frame_reachable vs ctx [] [] G tn fn inst s /\
  MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  same_after_assigns (REVERSE (TAKE s.vs_inst_idx bb.bb_instructions)) p q ==>
  eval_operand p s = eval_operand q s
Proof
  rpt strip_tac >> drule_all m2v_reachable_prefix >>
  strip_tac >> first_x_assum irule >> qexists_tac `bb` >> simp[]
QED

Theorem m2v_assign_resolve_eval:
  inst_wf inst /\ inst.inst_opcode = ASSIGN /\
  step_inst fuel ctx inst s = OK t /\
  (!op. eval_operand op s = eval_operand (resolve_block_assigns xs op) u) ==>
  eval_operand op t = eval_operand (resolve_block_assigns (inst::xs) op) u
Proof
  rpt strip_tac >>
  `LENGTH inst.inst_outputs = 1 /\ LENGTH inst.inst_operands = 1` by
    gvs[inst_wf_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  `!op. eval_operand op t =
     eval_operand (if op = Var h then HD inst.inst_operands else op) s` by
    (gen_tac >> irule m2v_step_back_assign_eval >>
     qexistsl_tac [`ctx`, `fuel`, `inst`] >>
     Cases_on `op` >> simp[step_back_assign_def, venomInstTheory.is_terminator_def] >>
     rpt strip_tac >> gvs[] >> IF_CASES_TAC >> simp[]) >>
  first_x_assum (qspec_then `op` mp_tac) >>
  Cases_on `op` >>
  simp[resolve_block_assigns_def] >>
  Cases_on `s' = h` >> simp[]
QED



Theorem m2v_forward_src_zero:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn /\ wf_function fn /\
  EVERY (\ins. ins.inst_opcode <> INVOKE) (fn_insts fn) /\
  frame_reachable vs ctx [] [] G tn fn copy s /\
  MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  s.vs_inst_idx = i /\ revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ copy.inst_operands = [p; src; rds] ==>
  eval_operand src s = SOME 0w
Proof
  rpt strip_tac >> gvs[revert_forward_pair_def] >>
  `eval_operand src s = eval_operand (Lit 0w) s` by
    (irule m2v_reachable_same_after_assigns >> metis_tac[]) >>
  gvs[eval_operand_def]
QED



Theorem m2v_assign_exec_interval:
  !fn fuel ctx bb n a s t.
    a + n <= LENGTH bb.bb_instructions /\
    s.vs_inst_idx = a /\ t.vs_inst_idx = a /\
    m2v_public_rel fn s t /\ m2v_fresh_names_disjoint fn /\
    (!k. a <= k /\ k < a + n ==>
      inst_wf (EL k bb.bb_instructions) /\
      (EL k bb.bb_instructions).inst_opcode = ASSIGN /\
      MEM (EL k bb.bb_instructions) (fn_insts fn)) ==>
    (?e. exec_block fuel ctx bb s = Error e) \/
    (?s' t'. s'.vs_inst_idx = a + n /\ t'.vs_inst_idx = a + n /\
      exec_block fuel ctx bb s = exec_block fuel ctx bb s' /\
      exec_block fuel ctx bb t = exec_block fuel ctx bb t' /\
      m2v_public_rel fn s' t' /\
      s'.vs_memory = s.vs_memory /\ t'.vs_memory = t.vs_memory /\
      (!op. eval_operand op s' = eval_operand
        (resolve_block_assigns (REVERSE (TAKE n (DROP a bb.bb_instructions))) op) s))
Proof
  rpt gen_tac >> map_every qid_spec_tac [`t`, `s`, `a`, `n`] >>
  Induct >- (rpt strip_tac >> disj2_tac >> qexistsl_tac [`s`, `t`] >>
             simp[resolve_block_assigns_def]) >>
  rpt gen_tac >> strip_tac >>
  `a + n < LENGTH bb.bb_instructions` by decide_tac >>
  `!k. a <= k /\ k < a + n ==>
      inst_wf (EL k bb.bb_instructions) /\
      (EL k bb.bb_instructions).inst_opcode = ASSIGN /\
      MEM (EL k bb.bb_instructions) (fn_insts fn)` by
    (rpt strip_tac >> simp[]) >>
  first_x_assum (qspecl_then [`a`, `s`, `t`] mp_tac) >>
  simp[] >> strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  rename1 `m2v_public_rel fn s' t'` >>
  `inst_wf (EL (a + n) bb.bb_instructions) /\
   (EL (a + n) bb.bb_instructions).inst_opcode = ASSIGN /\
   MEM (EL (a + n) bb.bb_instructions) (fn_insts fn)` by
    (first_x_assum (qspec_then `a + n` mp_tac) >> simp[]) >>
  qabbrev_tac `inst = EL (a + n) bb.bb_instructions` >>
  `get_instruction bb (a + n) = SOME inst` by
    simp[venomInstTheory.get_instruction_def, Abbr `inst`] >>
  `?src out. inst.inst_operands = [src] /\ inst.inst_outputs = [out]` by
    (gvs[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  `eval_operand src s' = eval_operand src t'` by
    (irule m2v_public_eval_operand >> metis_tac[MEM]) >>
  Cases_on `eval_operand src s'`
  >- (disj1_tac >>
      `exec_block fuel ctx bb s' = Error "undefined operand"` by
        (once_rewrite_tac[exec_block_def] >>
         qpat_x_assum `!op. eval_operand op s' = _` kall_tac >>
         qpat_x_assum `NONE = eval_operand src t'` kall_tac >>
         simp[step_inst_non_invoke, step_inst_base_def,
              venomInstTheory.is_terminator_def]) >>
      metis_tac[]) >>
  rename1 `eval_operand src s' = SOME value` >>
  `eval_operand src t' = SOME value` by metis_tac[] >>
  qabbrev_tac `ss = update_var out value s'` >>
  qabbrev_tac `tt = update_var out value t'` >>
  `step_inst fuel ctx inst s' = OK ss /\
   step_inst fuel ctx inst t' = OK tt` by
    (qpat_x_assum `!op. eval_operand op s' = _` kall_tac >>
     qpat_x_assum `SOME value = eval_operand src t'` kall_tac >>
     simp[step_inst_non_invoke, step_inst_base_def, Abbr `ss`, Abbr `tt`]) >>
  `exec_block fuel ctx bb s' =
     exec_block fuel ctx bb (ss with vs_inst_idx := a + SUC n) /\
   exec_block fuel ctx bb t' =
     exec_block fuel ctx bb (tt with vs_inst_idx := a + SUC n)` by
    (conj_tac >> CONV_TAC (LHS_CONV (REWR_CONV exec_block_def)) >>
     simp[venomInstTheory.is_terminator_def, arithmeticTheory.ADD_CLAUSES]) >>
  disj2_tac >>
  qexistsl_tac [`ss with vs_inst_idx := a + SUC n`,
                `tt with vs_inst_idx := a + SUC n`] >>
  simp[] >>
  conj_tac
  >- (irule m2v_public_next >>
      simp[Abbr `ss`, Abbr `tt`, m2v_public_update_var]) >>
  simp[Abbr `ss`, Abbr `tt`, update_var_def] >>
  `TAKE (SUC n) (DROP a bb.bb_instructions) =
    SNOC inst (TAKE n (DROP a bb.bb_instructions))` by
    simp[rich_listTheory.TAKE_SUC_BY_TAKE, EL_DROP, Abbr `inst`] >>
  simp[REVERSE_SNOC] >> gen_tac >>
  `eval_operand op (update_var out value s') = eval_operand
     (resolve_block_assigns (inst :: REVERSE (TAKE n (DROP a bb.bb_instructions))) op) s` by
    (irule m2v_assign_resolve_eval >> simp[] >>
     qexistsl_tac [`ctx`, `fuel`, `s'`] >> simp[]) >>
  Cases_on `op` >> gvs[eval_operand_def, lookup_var_def, update_var_def]
QED

Theorem m2v_revert_forward_sim:
  !ctx name fn vs G tn copy s1 s2 bb i j fuel.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
    o1_initial_state_ok vs /\ m2v_fresh_names_disjoint fn /\
    EVERY (\inst. inst.inst_opcode <> INVOKE) (fn_insts fn) /\
    frame_reachable vs ctx [] [] G tn fn copy s1 /\
    MEM bb fn.fn_blocks /\ bb.bb_label = s1.vs_current_bb /\
    revert_forward_pair bb i j /\ get_instruction bb i = SOME copy /\
    s1.vs_inst_idx = i /\ s2.vs_inst_idx = i /\
    m2v_public_rel fn s1 s2 ==>
    (?e. exec_block fuel ctx bb s1 = Error e) \/
    lift_result (m2v_public_rel fn) (m2v_public_rel fn)
      (m2v_public_rel fn)
      (exec_block fuel ctx bb s1) (exec_block fuel ctx bb s2)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `revert_forward_pair bb i j` mp_tac >>
  pure_rewrite_tac[revert_forward_pair_def] >> strip_tac >> gvs[] >>
  `!k inst. get_instruction bb k = SOME inst ==>
     MEM inst bb.bb_instructions /\ MEM inst (fn_insts fn) /\ inst_wf inst` by
    (rpt gen_tac >> strip_tac >>
     `MEM inst bb.bb_instructions` by
       (gvs[venomInstTheory.get_instruction_def, AllCaseEqs()] >>
        metis_tac[MEM_EL]) >>
     simp[] >> conj_tac
     >- (simp[venomInstTheory.fn_insts_def] >>
         metis_tac[venomInstTheory.fmp_fn_insts_blocks_intro]) >>
     metis_tac[fn_inst_wf_def]) >>
  `eval_operand src s1 = SOME 0w` by
    (irule m2v_forward_src_zero >> metis_tac[]) >>
  `!op. MEM op copy.inst_operands ==>
    eval_operand op s1 = eval_operand op s2` by
    (rpt strip_tac >> irule m2v_public_eval_operand >> metis_tac[]) >>
  `eval_operand p s1 = eval_operand p s2 /\
   eval_operand src s2 = SOME 0w /\
   eval_operand rds s1 = eval_operand rds s2` by
    metis_tac[MEM] >>
  qpat_x_assum `!op. MEM op copy.inst_operands ==> _` kall_tac >>
  Cases_on `eval_operand p s1`
  >- (disj1_tac >> qexists_tac `"undefined operand"` >>
      once_rewrite_tac[exec_block_def] >>
      gvs[step_inst_non_invoke, step_inst_base_def]) >>
  Cases_on `eval_operand rds s1`
  >- (disj1_tac >> qexists_tac `"undefined operand"` >>
      qpat_x_assum `SOME _ = eval_operand p s2` kall_tac >>
      once_rewrite_tac[exec_block_def] >>
      gvs[step_inst_non_invoke, step_inst_base_def]) >>
  rename1 `eval_operand p s1 = SOME dest` >>
  rename1 `eval_operand rds s1 = SOME sz` >>
  qpat_x_assum `SOME dest = eval_operand p s2` (assume_tac o SYM) >>
  qpat_x_assum `SOME sz = eval_operand rds s2` (assume_tac o SYM) >>
  `s1.vs_returndata = s2.vs_returndata` by
    gvs[m2v_public_rel_def, m2v_equiv_def, m2v_frame_def, venom_state_component_equality] >>
  Cases_on `LENGTH s1.vs_returndata < w2n sz`
  >- (disj2_tac >> once_rewrite_tac[exec_block_def] >>
      gvs[step_inst_non_invoke, step_inst_base_def, stateEquivTheory.lift_result_def,
           m2v_public_finish]) >>
  qabbrev_tac `bytes = TAKE (w2n sz) s1.vs_returndata` >>
  qabbrev_tac `ss = write_memory_with_expansion (w2n dest) bytes s1` >>
  qabbrev_tac `tt = write_memory_with_expansion (w2n dest) bytes s2` >>
  `step_inst fuel ctx copy s1 = OK ss /\ step_inst fuel ctx copy s2 = OK tt` by
    (gvs[step_inst_non_invoke, step_inst_base_def, Abbr `ss`, Abbr `tt`, Abbr `bytes`]) >>
  `exec_block fuel ctx bb s1 = exec_block fuel ctx bb (ss with vs_inst_idx := SUC s1.vs_inst_idx) /\
   exec_block fuel ctx bb s2 = exec_block fuel ctx bb (tt with vs_inst_idx := SUC s1.vs_inst_idx)` by
    (conj_tac >> CONV_TAC (LHS_CONV (REWR_CONV exec_block_def)) >>
     simp[venomInstTheory.is_terminator_def]) >>
  `m2v_public_rel fn ss tt` by
    simp[Abbr `ss`, Abbr `tt`, m2v_public_common_write] >>
  `j < LENGTH bb.bb_instructions` by
    gvs[venomInstTheory.get_instruction_def, AllCaseEqs()] >>
  `!k. SUC s1.vs_inst_idx <= k /\ k < j ==>
      inst_wf (EL k bb.bb_instructions) /\
      (EL k bb.bb_instructions).inst_opcode = ASSIGN /\
      MEM (EL k bb.bb_instructions) (fn_insts fn)` by
    (rpt gen_tac >> strip_tac >>
     `get_instruction bb k = SOME (EL k bb.bb_instructions)` by
       simp[venomInstTheory.get_instruction_def] >> metis_tac[arithmeticTheory.LESS_EQ]) >>
  mp_tac (Q.SPECL [`fn`, `fuel`, `ctx`, `bb`, `j - SUC s1.vs_inst_idx`,
    `SUC s1.vs_inst_idx`, `ss with vs_inst_idx := SUC s1.vs_inst_idx`,
    `tt with vs_inst_idx := SUC s1.vs_inst_idx`] m2v_assign_exec_interval) >>
  simp[m2v_public_next] >> strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  `!op. eval_operand op (ss with vs_inst_idx := SUC s1.vs_inst_idx) = eval_operand op s1` by
    (gen_tac >> `eval_operand op ss = eval_operand op s1` by
      (irule m2v_step_back_assign_eval >>
       qexistsl_tac [`ctx`, `fuel`, `copy`] >>
       `copy.inst_outputs = []` by
         (`inst_wf copy` by metis_tac[] >> gvs[inst_wf_def]) >>
       Cases_on `op` >> simp[step_back_assign_def, venomInstTheory.is_terminator_def]) >>
     Cases_on `op` >> gvs[eval_operand_def, lookup_var_def]) >>
  `eval_operand p' s' = SOME dest /\ eval_operand rds' s' = SOME sz` by
    (conj_tac >>
     `!q r. same_after_assigns (REVERSE (TAKE s1.vs_inst_idx bb.bb_instructions)) q r ==>
        eval_operand q s1 = eval_operand r s1` by
       (rpt strip_tac >> irule m2v_reachable_same_after_assigns >> metis_tac[]) >>
     metis_tac[]) >>
  `eval_operand p' t' = SOME dest /\ eval_operand rds' t' = SOME sz` by
    (conj_tac >> metis_tac[m2v_public_eval_operand, MEM]) >>
  `LENGTH bytes = w2n sz` by gvs[Abbr `bytes`, LENGTH_TAKE] >>
  `read_memory (w2n dest) (w2n sz) s' = read_memory (w2n dest) (w2n sz) t'` by
    (irule m2v_padded_read_cong >> rpt strip_tac >>
     `mem_byte i s' = mem_byte i ss /\ mem_byte i t' = mem_byte i tt` by
       simp[mem_byte_def] >>
     simp[] >> simp[Abbr `ss`, Abbr `tt`] >>
     irule m2v_common_write_range >> simp[]) >>
  qpat_x_assum `!op. eval_operand op s' = _` kall_tac >>
  qpat_x_assum `!op. eval_operand op (ss with vs_inst_idx := _) = _` kall_tac >>
  disj2_tac >> asm_rewrite_tac[] >>
  once_rewrite_tac[exec_block_def] >>
  simp[step_inst_non_invoke, step_inst_base_def,
       GSYM read_memory_def, stateEquivTheory.lift_result_def,
       revert_state_def, GSYM halt_state_def, m2v_public_finish]
QED
