Theory mem2varBlockSim
Ancestors
  venomFnInstsProofs mem2varBlockSimHelpers
  mem2varInvariant mem2varReach mem2varRevertForward
  ptrDiscipline unitTransformDefs contextCodegenRel
  fnBlockStepHelpers stepWriteFootprintForward
  mem2varDefs mem2varProofs mem2varFrame
  passSharedTransfer passSharedField
  venomExecSemantics venomState venomWf
  venomInst venomInstProofs venomExecProofs
  stateEquiv
  passSimulationDefs passSimulationProps
  instIdxIndep analysisSimDefs
  dfgDefs dfgCorrectnessProof
  basePtrDefs basePtrProofs
  pointerConfinedDefs memLocDefs
  venomEffects venomMemDefs venomMemProps venomMemProofs
  finite_map list rich_list pred_set pair
  opcodeClass
Libs
  HolKernel boolLib bossLib BasicProvers dep_rewrite markerLib mem2varFrameLib

val _ = augment_srw_ss [mem2varFrameLib.frame_ss];

Theorem m2v_unchanged_read_disjoint[local]:
  m2v_access_safe fn inst s /\
  ~(?ao pvar. FIND (\(ao,pvar,sz). MEM (Var ao) inst.inst_operands)
      (m2v_promo_list fn) = SOME (ao,pvar,32)) /\
  MEM (off,len) (source_memory_read_ranges inst s) ==>
  !addr. off <= addr /\ addr < off + len ==>
    ~in_promoted_region fn s addr
Proof
  rw[m2v_access_safe_def, MEM_APPEND] >> metis_tac[]
QED

Theorem m2v_step_unchanged_return[local]:
  !fn inst s1 s2 fuel ctx.
    (inst.inst_opcode = RETURN \/ inst.inst_opcode = REVERT) /\
    ~(?ao pvar. FIND (\(ao,pvar,sz). MEM (Var ao) inst.inst_operands)
      (m2v_promo_list fn) = SOME (ao,pvar,32)) /\
    m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
    m2v_ao_undef_sync fn s1 s2 /\ m2v_fresh_names_disjoint fn /\
    m2v_access_safe fn inst s1 /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
    s1.vs_alloca_next = s2.vs_alloca_next ==>
    (?e. step_inst fuel ctx inst s1 = Error e) \/
    lift_result
      (\s t. m2v_inv_noix fn s t /\ m2v_non32_ok fn s t /\
        m2v_ao_undef_sync fn s t /\ s.vs_alloca_next = t.vs_alloca_next)
      (\s t. m2v_inv_noix fn s t /\ m2v_non32_ok fn s t /\
        m2v_ao_undef_sync fn s t /\ s.vs_alloca_next = t.vs_alloca_next)
      (\s t. m2v_inv_noix fn s t /\ m2v_non32_ok fn s t /\
        m2v_ao_undef_sync fn s t /\ s.vs_alloca_next = t.vs_alloca_next)
      (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)
Proof
  rpt gen_tac >> strip_tac >>
  `?off_op sz_op. inst.inst_operands = [off_op; sz_op]` by
    (qpat_x_assum `inst_wf _` mp_tac >> simp[Once inst_wf_def] >>
     Cases_on `inst.inst_operands` >> simp[] >>
     Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >> metis_tac[]) >>
  `eval_operand off_op s1 = eval_operand off_op s2` by
    (irule m2v_inv_noix_eval_agrees >> metis_tac[MEM]) >>
  `eval_operand sz_op s1 = eval_operand sz_op s2` by
    (irule m2v_inv_noix_eval_agrees >> metis_tac[MEM]) >>
  Cases_on `inst.inst_opcode = RETURN` >> gvs[] >>
  simp[step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >> simp[] >>
  Cases_on `eval_operand off_op s2` >> gvs[] >>
  Cases_on `eval_operand sz_op s2` >> gvs[] >>
  rename1 `eval_operand off_op s2 = SOME off_val` >>
  rename1 `eval_operand sz_op s2 = SOME sz_val` >>
  `!addr. w2n off_val <= addr /\ addr < w2n off_val + w2n sz_val ==>
      ~in_promoted_region fn s1 addr` by
    (ho_match_mp_tac m2v_unchanged_read_disjoint >>
     simp[source_memory_read_ranges_def, memory_range_of_operands_def]) >>
  `TAKE (w2n sz_val) (DROP (w2n off_val) s1.vs_memory ++ REPLICATE (w2n sz_val) 0w) =
   TAKE (w2n sz_val) (DROP (w2n off_val) s2.vs_memory ++ REPLICATE (w2n sz_val) 0w)` by
    (irule mem_byte_agrees_take_drop >> rpt strip_tac >>
     fs[m2v_inv_noix_def] >> metis_tac[]) >>
  simp[lift_result_def] >> metis_tac[m2v_terminal_inv_preserved]
QED

Theorem m2v_forward_phi_entry[local]:
  !bb i j. revert_forward_pair bb i j ==>
    ~(i < phi_prefix_length bb.bb_instructions /\
      phi_prefix_length bb.bb_instructions <= j)
Proof
  rpt strip_tac >>
  drule revert_forward_pair_past_phis >> decide_tac
QED

Theorem m2v_forward_exclusion_next[local]:
  !bb k.
    (!i j. revert_forward_pair bb i j ==> ~(i < k /\ k <= j)) /\
    (!j. ~revert_forward_pair bb k j) ==>
    !i j. revert_forward_pair bb i j ==> ~(i < SUC k /\ SUC k <= j)
Proof
  rpt strip_tac >>
  `i <= k /\ k < j` by decide_tac >>
  Cases_on `i = k` >> metis_tac[arithmeticTheory.LESS_OR_EQ,
                                arithmeticTheory.LESS_IMP_LESS_OR_EQ]
QED

Theorem m2v_rewrite_other[local]:
  !fn inst. inst.inst_opcode <> MSTORE /\ inst.inst_opcode <> MLOAD /\
    inst.inst_opcode <> RETURN ==> m2v_rewrite_inst fn inst = [inst]
Proof
  rpt strip_tac >> simp[m2v_rewrite_inst_def] >>
  Cases_on `FIND (\(ao,_,_). MEM (Var ao) inst.inst_operands)
    (m2v_promo_list fn)` >> simp[] >>
  PairCases_on `x` >> simp[m2v_promote_inst_def]
QED

Theorem m2v_bt_unchanged_suffix[local]:
  !fn bb s fuel ctx.
    bb_well_formed bb /\ s.vs_inst_idx < LENGTH bb.bb_instructions /\
    (!k. s.vs_inst_idx <= k /\ k < LENGTH bb.bb_instructions ==>
      (EL k bb.bb_instructions).inst_opcode <> MSTORE /\
      (EL k bb.bb_instructions).inst_opcode <> MLOAD /\
      (EL k bb.bb_instructions).inst_opcode <> RETURN) ==>
    exec_block fuel ctx bb s = exec_block fuel ctx (m2v_bt fn bb) s
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `m2v_rewrite_inst fn (LAST bb.bb_instructions) = [LAST bb.bb_instructions]` by
    (irule m2v_rewrite_other >>
     first_x_assum (qspec_then `LENGTH bb.bb_instructions - 1` mp_tac) >>
     simp[LAST_EL, arithmeticTheory.PRE_SUB1] >> metis_tac[]) >>
  `EVERY (\x. LENGTH (m2v_rewrite_inst fn x) = 1) bb.bb_instructions` by
    (drule m2v_rewrite_front_sing >>
     disch_then (qspec_then `fn` assume_tac) >>
     drule APPEND_FRONT_LAST >>
     disch_then (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  irule exec_block_same_insts >>
  simp[m2v_bt_instructions, FLAT_MAP_SING_LENGTH] >>
  rpt strip_tac >> simp[FLAT_MAP_SING_EL] >>
  `m2v_rewrite_inst fn (EL i bb.bb_instructions) = [EL i bb.bb_instructions]` by
    (irule m2v_rewrite_other >> metis_tac[]) >> simp[]
QED

Theorem m2v_bt_forward_suffix[local]:
  !fn bb s j fuel ctx.
    bb_well_formed bb /\ revert_forward_pair bb s.vs_inst_idx j ==>
    exec_block fuel ctx bb s = exec_block fuel ctx (m2v_bt fn bb) s
Proof
  rpt gen_tac >> strip_tac >>
  fs[revert_forward_pair_def, get_instruction_def, AllCaseEqs()] >>
  `j = PRE (LENGTH bb.bb_instructions)` by
    (fs[bb_well_formed_def] >>
     first_x_assum irule >> simp[is_terminator_def]) >>
  irule m2v_bt_unchanged_suffix >> simp[] >>
  qx_gen_tac `k` >> strip_tac >>
  Cases_on `k = s.vs_inst_idx` >- gvs[] >>
  Cases_on `k = j` >- gvs[] >>
  `s.vs_inst_idx < k /\ k < j` by decide_tac >>
  `((EL k bb.bb_instructions).inst_opcode = ASSIGN)` by
    (first_x_assum irule >> simp[]) >> simp[]
QED

Theorem m2v_forward_block_sim[local]:
  !ctx name fn vs G tn copy s1 s2 bb j fuel.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
    o1_initial_state_ok vs /\ m2v_fresh_names_disjoint fn /\
    EVERY (\inst. inst.inst_opcode <> INVOKE) (fn_insts fn) /\
    frame_reachable vs ctx [] [] G tn fn copy s1 /\
    MEM bb fn.fn_blocks /\ bb.bb_label = s1.vs_current_bb /\
    bb_well_formed bb /\ revert_forward_pair bb s1.vs_inst_idx j /\
    get_instruction bb s1.vs_inst_idx = SOME copy /\
    s2.vs_inst_idx = s1.vs_inst_idx /\ m2v_inv_noix fn s1 s2 ==>
    (?e. exec_block fuel ctx bb s1 = Error e) \/
    lift_result
      (\s t. m2v_inv_noix fn s t /\ m2v_non32_ok fn s t /\
             m2v_ao_undef_sync fn s t)
      (m2v_public_rel fn) (m2v_public_rel fn)
      (exec_block fuel ctx bb s1)
      (exec_block fuel ctx (m2v_bt fn bb) s2)
Proof
  rpt gen_tac >> strip_tac >>
  `m2v_public_rel fn s1 s2` by
    fs[m2v_public_rel_def, m2v_inv_noix_def, m2v_equiv_def] >>
  `(?e. exec_block fuel ctx bb s1 = Error e) \/
   lift_result (m2v_public_rel fn) (m2v_public_rel fn) (m2v_public_rel fn)
     (exec_block fuel ctx bb s1) (exec_block fuel ctx bb s2)` by
    (irule m2v_revert_forward_sim >> metis_tac[]) >>
  pop_assum strip_assume_tac >- simp[] >>
  `exec_block fuel ctx (m2v_bt fn bb) s2 = exec_block fuel ctx bb s2` by
    (sym_tac >> irule m2v_bt_forward_suffix >> metis_tac[]) >>
  simp[] >>
  drule revert_forward_pair_no_normal >>
  disch_tac >>
  Cases_on `exec_block fuel ctx bb s1` >>
  Cases_on `exec_block fuel ctx bb s2` >>
  gvs[lift_result_def]
QED

Theorem m2v_reachable_suffix_sim[local]:
  !n ctx name fn vs G tn inst bb fuel s1 s2.
    n = LENGTH bb.bb_instructions - s1.vs_inst_idx /\
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
    o1_initial_state_ok vs /\
    ptr_discipline vs.vs_alloca_next ctx vs /\
    raw_unit_memory_ok ctx vs /\
    m2v_promotable_wf fn /\ m2v_fresh_names_disjoint fn /\
    m2v_promo_sizes_bounded fn /\ m2v_return_size_bounded fn /\
    EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts fn) /\
    frame_reachable vs ctx [] [] G tn fn inst s1 /\
    MEM bb fn.fn_blocks /\ bb.bb_label = s1.vs_current_bb /\
    s1.vs_inst_idx <= LENGTH bb.bb_instructions /\
    (!i j. revert_forward_pair bb i j ==>
      ~(i < s1.vs_inst_idx /\ s1.vs_inst_idx <= j)) /\
    s2.vs_inst_idx = s1.vs_inst_idx /\
    m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
    m2v_ao_undef_sync fn s1 s2 /\
    m2v_pvars_set fn bb s1.vs_inst_idx s2 ==>
    (?e. exec_block fuel ctx bb s1 = Error e) \/
    lift_result
      (\s t. m2v_inv_noix fn s t /\ m2v_non32_ok fn s t /\
             m2v_ao_undef_sync fn s t)
      (m2v_public_rel fn) (m2v_public_rel fn)
      (exec_block fuel ctx bb s1)
      (exec_block fuel ctx (m2v_bt fn bb) s2)
Proof
  Induct_on `n` >> rpt gen_tac >> strip_tac
  >- (disj1_tac >> once_rewrite_tac[exec_block_def] >>
      simp[get_instruction_def]) >>
  `s1.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `active_inst fn inst s1` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     once_rewrite_tac[frame_reachable_cases] >> metis_tac[]) >>
  `get_instruction bb s1.vs_inst_idx = SOME inst` by
    (fs[active_inst_def] >>
     `ALL_DISTINCT (fn_labels fn)` by fs[wf_function_def] >>
     `bb = bb'` by metis_tac[fn_labels_def, mem2varProofsTheory.ALL_DISTINCT_MAP_IMP] >>
     gvs[get_instruction_def]) >>
  Cases_on `?j. revert_forward_pair bb s1.vs_inst_idx j`
  >- suspend "forward" >>
  suspend "ordinary"
QED
Resume m2v_reachable_suffix_sim[forward]:
  irule m2v_forward_block_sim >> metis_tac[]
QED
Resume m2v_reachable_suffix_sim[ordinary]:
  `~in_revert_forward fn s1` by
    (fs[in_revert_forward_def] >>
     rpt strip_tac >>
     `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb` by
       (irule venomExecProofsTheory.MEM_lookup_block >>
        simp[] >> fs[wf_function_def, fn_labels_def]) >>
     gvs[revert_forward_at_def] >>
     `j < s1.vs_inst_idx` by
       (qpat_x_assum `revert_forward_pair bb j _` mp_tac >>
        simp[Once revert_forward_pair_def] >> strip_tac) >>
     metis_tac[arithmeticTheory.LESS_OR_EQ]) >>
  drule_all m2v_reachable_memory_safety >> strip_tac >>
  `MEM inst bb.bb_instructions` by
    (fs[get_instruction_def, AllCaseEqs()] >> metis_tac[EL_MEM]) >>
  `MEM inst (fn_insts fn)` by metis_tac[MEM_fn_insts] >>
  `inst_wf inst` by
    (drule_all fn_inst_wf_every_bb >> simp[EVERY_MEM] >>
     disch_then drule >> simp[]) >>
  `inst.inst_opcode <> INVOKE` by gvs[EVERY_MEM] >>
  `!x. MEM x (fn_insts fn) ==>
       x.inst_opcode <> MEMTOP /\ x.inst_opcode <> DRET /\
       x.inst_opcode <> RETFMP` by
    (qpat_x_assum `ptr_discipline _ _ _` mp_tac >>
     simp[ptr_discipline_def] >> strip_tac >>
     `MEM fn ctx.ctx_functions` by
       (fs[lookup_function_def] >> metis_tac[FIND_MEM]) >>
     fs[EVERY_MEM] >>
     qpat_x_assum `!f. MEM f ctx.ctx_functions ==> _`
       (qspec_then `fn` mp_tac) >>
     simp[fn_ptr_ok_def] >> metis_tac[]) >>
  `ssa_form fn` by fs[wf_ssa_def] >>
  `s1.vs_alloca_next = s2.vs_alloca_next` by fs[m2v_inv_noix_def] >>
  `EL s1.vs_inst_idx bb.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  `EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `MEM i (fn_insts fn)` by (irule MEM_fn_insts >> metis_tac[]) >>
     gvs[EVERY_MEM]) >>
  `EVERY (\i. i.inst_opcode <> MEMTOP) bb.bb_instructions` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `MEM i (fn_insts fn)` by (irule MEM_fn_insts >> metis_tac[]) >>
     first_x_assum drule >> simp[]) >>
  Cases_on `is_terminator inst.inst_opcode`
  >- suspend "terminal" >>
  suspend "nonterminal"
QED
Resume m2v_reachable_suffix_sim[nonterminal]:
  `s1.vs_inst_idx < LENGTH bb.bb_instructions - 1` by
    (irule nonterm_not_last >> simp[]) >>
  irule m2v_exec_block_step_chain >> simp[] >>
  qexists `HD (m2v_rewrite_inst fn inst)` >> simp[] >>
  conj_tac >- suspend "continuation" >>
  conj_tac >- (irule m2v_rewrite_nonterm >> simp[]) >>
  conj_tac >- simp[m2v_bt_get_inst_nonterm] >>
  suspend "step_sim"
QED
Resume m2v_reachable_suffix_sim[step_sim]:
  Cases_on `step_inst fuel ctx inst s1`
  >- suspend "step_ok"
  >- (gvs[step_inst_non_invoke] >>
      metis_tac[step_inst_base_no_halt])
  >- suspend "step_abort"
  >- (gvs[step_inst_non_invoke] >>
      metis_tac[step_inst_base_no_intret]) >>
  simp[]
QED
Resume m2v_reachable_suffix_sim[step_ok]:
  `?v2. step_inst fuel ctx (HD (m2v_rewrite_inst fn inst)) s2 = OK v2 /\
        m2v_inv_noix fn v v2` by
    (qsuff_tac `?v2. step_inst fuel ctx
       (HD (m2v_rewrite_inst fn (EL s1.vs_inst_idx bb.bb_instructions))) s2 = OK v2 /\
       m2v_inv_noix fn v v2` >- simp[] >>
     irule m2v_nonterminal_step_dispatch >> simp[] >> metis_tac[]) >>
  `m2v_non32_ok fn v v2` by
    (fs[m2v_non32_ok_def] >>
     metis_tac[m2v_non32_ok_preserved_step]) >>
  `m2v_ao_undef_sync fn v v2` by
    (irule m2v_ao_undef_sync_preserved_step >>
     metis_tac[]) >>
  simp[lift_result_def]
QED
Resume m2v_reachable_suffix_sim[step_abort]:
  drule_all m2v_nonterminal_abort_sim >> strip_tac >>
  simp[lift_result_def] >>
  qpat_x_assum `m2v_inv_noix fn v s2'` mp_tac >>
  simp[m2v_inv_noix_def, m2v_public_rel_def, m2v_equiv_def]
QED
Resume m2v_reachable_suffix_sim[continuation]:
  rpt gen_tac >> strip_tac >>
  `s1'.vs_current_bb = s1.vs_current_bb` by
    (`step_inst_base inst s1 = OK s1'` by metis_tac[step_inst_non_invoke] >>
     drule_all venomInstProofs1Theory.step_inst_base_preserves_all >> simp[]) >>
  `active_inst fn (EL (SUC s1.vs_inst_idx) bb.bb_instructions)
     (s1' with vs_inst_idx := SUC s1.vs_inst_idx)` by
    (simp[active_inst_def] >> qexists `bb` >> simp[]) >>
  `frame_reachable vs ctx [] [] (step_prov [] G inst s1')
     (step_taint inst s1 s1' tn) fn
     (EL (SUC s1.vs_inst_idx) bb.bb_instructions)
     (s1' with vs_inst_idx := SUC s1.vs_inst_idx)` by
    (irule (cj 2 frame_reachable_rules) >> metis_tac[]) >>
  `m2v_pvars_set fn bb (SUC s1.vs_inst_idx) s2'` by
    (irule m2v_pvars_set_after_dispatch >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!ctx name fn vs G tn inst bb fuel s1 s2. _` irule >>
  simp[] >>
  conj_tac >- (mp_tac (Q.SPECL [`bb`, `s1.vs_inst_idx`]
                         m2v_forward_exclusion_next) >> gvs[]) >>
  rpt conj_tac
  >- metis_tac[m2v_ao_undef_sync_update_idx]
  >- (qpat_x_assum `m2v_inv_noix fn s1' s2'` mp_tac >>
      simp[m2v_inv_noix_def, m2v_equiv_def, lookup_var_def,
           allocas_non_overlapping_def, in_promoted_region_def,
           mem_byte_def, mload_def] >> strip_tac >> gvs[] >> metis_tac[])
  >- metis_tac[m2v_non32_ok_update_idx]
  >- metis_tac[m2v_pvars_set_update_idx] >>
  metis_tac[]
QED
Resume m2v_reachable_suffix_sim[terminal]:
  `s1.vs_inst_idx = LENGTH bb.bb_instructions - 1` by
    (fs[bb_well_formed_def] >> metis_tac[arithmeticTheory.PRE_SUB1]) >>
  `inst = LAST bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[LAST_EL, arithmeticTheory.PRE_SUB1]) >>
  Cases_on `?ao pvar. FIND (\(ao,pvar,sz). MEM (Var ao) inst.inst_operands)
      (m2v_promo_list fn) = SOME (ao,pvar,32)`
  >- suspend "terminal32" >>
  `m2v_rewrite_inst fn inst = [inst]` by
    (Cases_on `FIND (\(ao,pvar,sz). MEM (Var ao) inst.inst_operands) (m2v_promo_list fn)` >>
     gvs[m2v_rewrite_inst_def] >> PairCases_on `x` >>
     `x2 <> 32` by metis_tac[] >>
     `MEM (x0,x1,x2) (m2v_promo_list fn)` by metis_tac[FIND_MEM] >>
     `32 <= x2` by (fs[m2v_promo_sizes_bounded_def, EVERY_MEM] >>
       qpat_x_assum `!e. MEM e (m2v_promo_list fn) ==> _`
         (qspec_then `(x0,x1,x2)` mp_tac) >> simp[]) >>
     simp[m2v_promote_inst_def]) >>
  suspend "terminal_unchanged"
QED
Resume m2v_reachable_suffix_sim[terminal_unchanged]:
  `get_instruction (m2v_bt fn bb) s2.vs_inst_idx = SOME inst` by
    (mp_tac (Q.SPECL [`fn`,`bb`,`0`] m2v_bt_get_inst_term) >> gvs[]) >>
  `(?e. exec_block fuel ctx bb s1 = Error e) \/
   lift_result
     (\s t. m2v_inv_noix fn s t /\ m2v_non32_ok fn s t /\
       m2v_ao_undef_sync fn s t /\ s.vs_alloca_next = t.vs_alloca_next)
     (\s t. m2v_inv_noix fn s t /\ m2v_non32_ok fn s t /\
       m2v_ao_undef_sync fn s t /\ s.vs_alloca_next = t.vs_alloca_next)
     (\s t. m2v_inv_noix fn s t /\ m2v_non32_ok fn s t /\
       m2v_ao_undef_sync fn s t /\ s.vs_alloca_next = t.vs_alloca_next)
     (exec_block fuel ctx bb s1) (exec_block fuel ctx (m2v_bt fn bb) s2)` by
    (qpat_x_assum `inst = LAST _` kall_tac >>
     irule exec_block_terminal_lift >> simp[] >>
     conj_tac >- (rpt strip_tac >> fs[m2v_inv_noix_def]) >>
     Cases_on `inst.inst_opcode = RETURN \/ inst.inst_opcode = REVERT`
     >- (irule m2v_step_unchanged_return >> metis_tac[]) >>
     disj2_tac >> irule m2v_step_easy_terminator_full >> metis_tac[]) >>
  pop_assum strip_assume_tac >- simp[] >>
  Cases_on `exec_block fuel ctx bb s1` >>
  Cases_on `exec_block fuel ctx (m2v_bt fn bb) s2` >>
  gvs[lift_result_def] >>
  qpat_x_assum `m2v_inv_noix fn v v'` mp_tac >>
  simp[m2v_public_rel_def, m2v_inv_noix_def, m2v_equiv_def]
QED
Resume m2v_reachable_suffix_sim[terminal32]:
  pop_assum strip_assume_tac >>
  `inst.inst_opcode = RETURN` by
    (drule_all promo_find_inst_opcode >> strip_tac >> gvs[is_terminator_def]) >>
  qpat_x_assum `inst = LAST _` kall_tac >>
  `MEM (ao,pvar,32) (m2v_promo_list fn)` by metis_tac[FIND_MEM] >>
  `?sz. inst.inst_operands = [Var ao; Lit sz] /\ w2n sz <= 32` by
    (`MEM (Var ao) inst.inst_operands` by
       (drule FIND_P >> simp[]) >>
     fs[m2v_return_size_bounded_def] >>
     first_x_assum (qspecl_then [`bb`,`inst`,`ao`,`pvar`] mp_tac) >> simp[]) >>
  `m2v_rewrite_inst fn inst =
    [<|inst_id := inst.inst_id; inst_opcode := MSTORE;
       inst_operands := [Var ao; Var pvar]; inst_outputs := []|>; inst]` by
    simp[m2v_rewrite_inst_def, m2v_promote_inst_def] >>
  `IS_SOME (lookup_var pvar s2)` by
    (irule m2v_pvars_set_use_is_some >>
     qexistsl [`ao`,`bb`,`fn`,`s1.vs_inst_idx`] >> simp[]) >>
  `ao NOTIN m2v_fresh_vars fn` by metis_tac[m2v_promo_list_ao_not_fresh] >>
  `lookup_var ao s2 = lookup_var ao s1` by fs[m2v_inv_noix_def] >>
  Cases_on `lookup_var ao s1`
  >- (disj1_tac >> once_rewrite_tac[exec_block_def] >> simp[] >>
      simp[step_inst_non_invoke] >> pure_once_rewrite_tac[step_inst_base_def] >>
      asm_rewrite_tac[] >> simp[eval_operand_def]) >>
  rename1 `lookup_var ao s1 = SOME addr` >>
  `lookup_var pvar s2 = SOME (mload (w2n addr) s1)` by
    (qpat_x_assum `m2v_inv_noix _ _ _` mp_tac >>
     simp[m2v_inv_noix_def] >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  `LAST bb.bb_instructions = inst` by
    (Cases_on `bb.bb_instructions` >> gvs[LAST_EL, arithmeticTheory.PRE_SUB1]) >>
  `get_instruction (m2v_bt fn bb) s2.vs_inst_idx =
    SOME <|inst_id := inst.inst_id; inst_opcode := MSTORE;
      inst_operands := [Var ao; Var pvar]; inst_outputs := []|>` by
    (mp_tac (Q.SPECL [`fn`,`bb`,`0`] m2v_bt_get_inst_term) >> simp[]) >>
  `get_instruction (m2v_bt fn bb) (SUC s2.vs_inst_idx) = SOME inst` by
    (mp_tac (Q.SPECL [`fn`,`bb`,`1`] m2v_bt_get_inst_term) >>
     simp[arithmeticTheory.ADD1]) >>
  `get_instruction (m2v_bt fn bb) (SUC (LENGTH bb.bb_instructions - 1)) = SOME inst` by
    metis_tac[] >>
  qpat_x_assum `LAST _ = inst` kall_tac >>
  disj2_tac >> once_rewrite_tac[exec_block_def] >> simp[] >>
  simp[step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  simp[eval_operand_def] >>
  simp[exec_write2_def, eval_operand_def, is_terminator_def] >>
  once_rewrite_tac[exec_block_def] >>
  simp[mstore_preserves, lookup_var_mstore_idx] >>
  simp[step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  simp[eval_operand_def, lookup_var_mstore_idx, mstore_preserves] >>
  DEP_ONCE_REWRITE_TAC [return_data_mstore_roundtrip] >> simp[lift_result_def] >>
  `m2v_inv_noix fn s1 (mstore (w2n addr) (mload (w2n addr) s1) s2)` by
    (irule m2v_inv_noix_mstore_s2_only >> metis_tac[]) >>
  `m2v_inv_noix fn s1
    (mstore (w2n addr) (mload (w2n addr) s1) s2 with
       vs_inst_idx := SUC (LENGTH bb.bb_instructions - 1))` by
    (irule m2v_inv_noix_update_idx_s2 >> simp[]) >>
  `m2v_inv_noix fn
    (halt_state (set_returndata (TAKE (w2n sz)
       (DROP (w2n addr) s1.vs_memory ++ REPLICATE (w2n sz) 0w)) s1))
    (halt_state (set_returndata (TAKE (w2n sz)
       (DROP (w2n addr) s1.vs_memory ++ REPLICATE (w2n sz) 0w))
       (mstore (w2n addr) (mload (w2n addr) s1) s2 with
          vs_inst_idx := SUC (LENGTH bb.bb_instructions - 1))))` by
    (irule m2v_inv_noix_halt_state >> irule m2v_inv_noix_set_returndata >> simp[]) >>
  pop_assum mp_tac >> simp[m2v_public_rel_def, m2v_inv_noix_def, m2v_equiv_def]
QED
Finalise m2v_reachable_suffix_sim

(* Actual block entry is after parallel PHI evaluation. A forwarding copy
   and its final REVERT must be consumed together before synchronization
   of promoted variables can be discarded. *)
Theorem m2v_per_block_sim:
  !ctx name fn vs G tn inst bb fuel s1 s2.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
    o1_initial_state_ok vs /\
    ptr_discipline vs.vs_alloca_next ctx vs /\
    raw_unit_memory_ok ctx vs /\
    m2v_promotable_wf fn /\ m2v_fresh_names_disjoint fn /\
    m2v_promo_sizes_bounded fn /\ m2v_return_size_bounded fn /\
    EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts fn) /\
    frame_reachable vs ctx [] [] G tn fn inst s1 /\
    MEM bb fn.fn_blocks /\ bb.bb_label = s1.vs_current_bb /\
    s1.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
    s2.vs_inst_idx = s1.vs_inst_idx /\
    m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
    m2v_ao_undef_sync fn s1 s2 /\
    m2v_pvars_set fn bb s1.vs_inst_idx s2 ==>
    (?e. exec_block fuel ctx bb s1 = Error e) \/
    lift_result
      (\s t. m2v_inv_noix fn s t /\ m2v_non32_ok fn s t /\
             m2v_ao_undef_sync fn s t)
      (m2v_public_rel fn) (m2v_public_rel fn)
      (exec_block fuel ctx bb s1)
      (exec_block fuel ctx (m2v_bt fn bb) s2)
Proof
  rpt strip_tac >>
  irule m2v_reachable_suffix_sim >>
  simp[phi_prefix_length_le] >>
  conj_tac >- metis_tac[m2v_forward_phi_entry] >>
  qexistsl [`G`,`inst`,`tn`,`vs`] >> simp[]
QED
