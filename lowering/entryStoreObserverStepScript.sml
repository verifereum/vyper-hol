(* Transport exactly the observer's successful memory-copy edge. *)
Theory entryStoreObserverStep
Ancestors
  exprSimAbiGasBridge fragGasOriginPtr fragGasOrigin fragGasPathPtr
  createSizePrefixReplay
  abiEncoderProps contextCodegenRel memSafeRun ptrSafeRun ptrDiscipline
  venomInst venomInstProps venomExecSemantics venomState gasCount gasEvents
  list pair abiEncoderObserver venomMemProps taintAgree createSizeCutCode venomExecProofs

Theorem store_observer_not_forward[local]:
  lookup_block u.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME i /\
  i.inst_opcode <> REVERT /\ i.inst_opcode <> RETURNDATACOPY ==>
  ~revert_forward_at bb u.vs_inst_idx /\ ~in_revert_forward f u
Proof
  rw[in_revert_forward_def] >> metis_tac[revert_forward_at_opcode, optionTheory.SOME_11]
QED

Theorem store_observer_ptr_fetch[local]:
  lookup_block u.vs_current_bb f.fn_blocks = SOME bb /\
  lookup_block u.vs_current_bb obs.fn_blocks = SOME ob /\
  get_instruction bb u.vs_inst_idx = SOME i /\
  get_instruction ob u.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> REVERT /\
  i.inst_opcode <> RETURNDATACOPY /\
  (ctx_has_dalloca ctx /\ ~ctx_has_dalloca oc ==> allocas_below_fmp u) /\
  ptr_safe_step D lo fuel oc obs PG G tn i u ==>
  ptr_safe_step D lo fuel ctx f PG G tn i u
Proof
  strip_tac >>
  `~in_revert_forward f u /\ ~in_revert_forward obs u` by
    metis_tac[store_observer_not_forward] >>
  `access_ok lo G f i u <=> access_ok lo G obs i u` by simp[access_ok_def] >>
  `taint_ok f tn i u <=> taint_ok obs tn i u` by simp[taint_ok_def, about_to_revert_def] >>
  fs[ptr_safe_step_def, ptr_inst_ok_def, step_inst_non_invoke] >>
  metis_tac[]
QED

Theorem observer_mem_safe_transfer[local]:
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> DALLOCA /\
  (ctx_has_dalloca oc ==> ctx_has_dalloca ctx) /\
  mem_safe_step fuel oc i u ==> mem_safe_step fuel ctx i u
Proof
  strip_tac >>
  qpat_x_assum `mem_safe_step fuel oc i u` mp_tac >>
  asm_simp_tac bool_ss [mem_safe_step_non_invoke, dalloca_no_wrap_non_dalloca] >>
  metis_tac[]
QED

Theorem store_observer_jump[local]:
  MEM i.inst_opcode [JMP; JNZ] /\ step_inst fuel ctx i u = OK t ==>
  t = jump_to t.vs_current_bb u /\ MEM (Label t.vs_current_bb) i.inst_operands
Proof
  simp[] >> strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs(), jump_to_def]
QED

Theorem store_observer_jump_state[local]:
  MEM i.inst_opcode [JMP; JNZ] /\ step_inst fuel ctx i u = OK t /\
  ~u.vs_halted ==>
  t.vs_inst_idx = 0 /\ ~t.vs_halted /\ MEM (Label t.vs_current_bb) i.inst_operands
Proof
  strip_tac >> drule_all store_observer_jump >> strip_tac >>
  qpat_x_assum `t = jump_to _ _` (fn th => once_rewrite_tac[th]) >>
  simp[jump_to_def] >> fs[jump_to_def]
QED

Theorem store_observer_phi_zero[local]:
  lookup_block t.vs_current_bb f.fn_blocks = SOME bb /\
  phi_prefix_length bb.bb_instructions = 0 ==>
  eval_phis t bb.bb_instructions = OK t /\ entry_prov f t G = G /\
  entry_taint_vars f t tn = tn
Proof
  strip_tac >> simp[entry_prov_def, entry_taint_vars_def, fragExecTheory.eval_phis_no_phi] >>
  Cases_on `bb.bb_instructions` >>
  gvs[phi_prefix_length_def, phis_prov_def, phis_taint_def, AllCaseEqs()]
QED

Theorem store_observer_install[local]:
  ~u.vs_halted /\ lookup_block u.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME i /\ i.inst_opcode <> GAS /\
  i.inst_opcode <> INVOKE /\ mem_safe_step fuel ctx i u /\
  ptr_safe_step D lo fuel ctx f PG G tn i u /\
  ((?t. step_inst fuel ctx i u = OK t /\ ~is_terminator i.inst_opcode /\
        ~t.vs_halted /\ v = t with vs_inst_idx := SUC u.vs_inst_idx /\
        (G1,tn1) = ghost_step fuel ctx PG G tn i u) \/
   (?t bb'. step_inst fuel ctx i u = OK t /\ is_terminator i.inst_opcode /\
        ~t.vs_halted /\ v = t /\ t.vs_inst_idx = 0 /\ G1 = G /\ tn1 = tn /\
        lookup_block t.vs_current_bb f.fn_blocks = SOME bb' /\
        phi_prefix_length bb'.bb_instructions = 0)) ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,f,PG) (u,G,tn) [] (OK v,G1,tn1)
Proof
  strip_tac
  >- (simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
      conj_tac >> qexists_tac `fuel` >> simp[gas_events_step_def, gas_count_step_def]) >>
  `eval_phis t bb'.bb_instructions = OK t /\ entry_prov f t G = G /\
   entry_taint_vars f t tn = tn` by metis_tac[store_observer_phi_zero] >>
  `t with vs_inst_idx := 0 = t` by simp[] >>
  simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
  conj_tac >> qexists_tac `fuel` >> simp[gas_events_step_def, gas_count_step_def] >>
  metis_tac[]
QED

Theorem store_observer_prefix[local]:
  (u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut b /\
  lookup_block u.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME i /\ i.inst_id IN frag_ids a b /\
  gas_origin_ptr_edge (D,lo,explicit,ctx,f,PG) (u,G,tn) [] (OK v,G1,tn1) ==>
  create_prefix_step a b explicit ctx f u [] v
Proof
  strip_tac >> fs[create_prefix_step_def, frag_observer_cut_def, gas_origin_ptr_edge_def] >>
  qpat_x_assum `gas_origin_edge T _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[gas_origin_edge_def] >> simp[] >> metis_tac[]
QED

(* The geometry is shared by stopped store and encoder observers. *)
Theorem create_observer_joint_step_transfer:
  (u.vs_current_bb,u.vs_inst_idx) IN frag_observer_region a b /\
  (u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut b /\
  (!ob i. lookup_block u.vs_current_bb obs.fn_blocks = SOME ob /\
    get_instruction ob u.vs_inst_idx = SOME i ==>
    MEM i (frag_code a b) /\ i.inst_id IN frag_ids a b /\
    i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> REVERT /\ i.inst_opcode <> RETURNDATACOPY /\
    i.inst_opcode <> DALLOCA /\ i.inst_opcode <> SETFMP /\
    i.inst_opcode <> DRET /\ i.inst_opcode <> DJMP /\
    ?bb. lookup_block u.vs_current_bb f.fn_blocks = SOME bb /\
         get_instruction bb u.vs_inst_idx = SOME i) /\
  (!i lbl. MEM i (frag_code a b) /\
    MEM lbl (create_cut_targets i.inst_opcode i.inst_operands) ==>
    (lbl,0) IN frag_observer_region a b /\
    ?ob bb. lookup_block lbl obs.fn_blocks = SOME ob /\
            lookup_block lbl f.fn_blocks = SOME bb /\
            phi_prefix_length ob.bb_instructions = 0 /\
            phi_prefix_length bb.bb_instructions = 0) /\
  (ctx_has_dalloca oc ==> ctx_has_dalloca ctx) /\
  (ctx_has_dalloca ctx /\ ~ctx_has_dalloca oc ==> allocas_below_fmp u) /\
  gas_origin_ptr_edge (D,lo,explicit,oc,obs,PG) (u,G,tn) [] (OK v,G1,tn1) ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,f,PG) (u,G,tn) [] (OK v,G1,tn1) /\
  create_prefix_step a b explicit ctx f u [] v /\
  abi_observer_step ctx f (frag_observer_cut b) u v /\
  (v.vs_current_bb,v.vs_inst_idx) IN frag_observer_region a b /\
  ~v.vs_halted /\ v.vs_fmp = u.vs_fmp /\ (alloca_inv u ==> alloca_inv v)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule gas_origin_ptr_edge_common_fuel >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `fuel` (qx_choose_then `ob` (qx_choose_then `inst`
      (qx_choose_then `middle` (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))) >>
  qpat_assum `!ob i. _` (drule_all_then strip_assume_tac) >>
  `mem_safe_step fuel oc inst u` by metis_tac[revert_forward_at_opcode] >>
  `mem_safe_step fuel ctx inst u` by metis_tac[observer_mem_safe_transfer] >>
  `ptr_safe_step D lo fuel ctx f PG G tn inst u` by
    (irule store_observer_ptr_fetch >> metis_tac[]) >>
  `step_inst fuel ctx inst u = middle` by fs[step_inst_non_invoke] >>
  `step_inst 0 ctx inst u = middle` by fs[step_inst_non_invoke] >>
  `!w. middle = OK w ==> w.vs_fmp = u.vs_fmp /\ (alloca_inv u ==> alloca_inv w)` by
    (rpt strip_tac >> metis_tac[step_inst_non_invoke, step_inst_base_OK_fmp_frame,
       alloca_inv_step_inst]) >>
  qpat_x_assum `[] = MAP _ _` kall_tac >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,f,PG) (u,G,tn) [] (OK v,G1,tn1) /\
   abi_observer_step ctx f (frag_observer_cut b) u v /\
   (v.vs_current_bb,v.vs_inst_idx) IN frag_observer_region a b /\
   ~v.vs_halted /\ v.vs_fmp = u.vs_fmp /\ (alloca_inv u ==> alloca_inv v)` suffices_by
    (strip_tac >> asm_rewrite_tac[] >> irule store_observer_prefix >> metis_tac[]) >>
  qpat_x_assum `(?t. middle = OK t /\ ~is_terminator _ /\ _) \/ _` mp_tac >>
  simp[fragExecTheory.exit_result_def] >> strip_tac
  >- (conj_tac
      >- (irule store_observer_install >>
          `ghost_step fuel oc PG G tn inst u = ghost_step fuel ctx PG G tn inst u` by
            metis_tac[ghost_step_non_invoke] >> metis_tac[]) >>
      conj_tac
      >- (simp[abi_observer_step_def] >> metis_tac[]) >>
      `t.vs_current_bb = u.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
      simp[venomMemProofsTheory.alloca_inv_set_inst_idx] >>
      qpat_x_assum `(u.vs_current_bb,u.vs_inst_idx) IN _` mp_tac >>
      simp[frag_observer_region_def] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_SUC_REFL]) >>
  TRY (qpat_x_assum `exit_result middle` mp_tac >>
       qpat_assum `OK v = middle` (fn th => pure_once_rewrite_tac[GSYM th]) >>
       simp[fragExecTheory.exit_result_def] >> NO_TAC) >>
  `?t. middle = OK t /\ is_terminator inst.inst_opcode /\
       ((?target entered. lookup_block t.vs_current_bb obs.fn_blocks = SOME target /\
           eval_phis t target.bb_instructions = OK entered /\
           v = entered with vs_inst_idx := phi_prefix_length target.bb_instructions /\
           G1 = entry_prov obs t G /\ tn1 = entry_taint_vars obs t tn) \/
        (v = t /\ G1 = G /\ tn1 = tn))` suffices_by
  (disch_then (qx_choose_then `land` (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `step_inst_base inst u = OK land` by fs[step_inst_non_invoke] >>
  `MEM inst.inst_opcode [JMP; JNZ]` by
    (simp[] >> metis_tac[step_inst_base_ok_terminator_jump]) >>
  `land.vs_inst_idx = 0 /\ ~land.vs_halted` by metis_tac[store_observer_jump_state] >>
  `MEM land.vs_current_bb (create_cut_targets inst.inst_opcode inst.inst_operands)` by
    metis_tac[create_cut_targets_sound] >>
  qpat_assum `!i lbl. _` (drule_all_then strip_assume_tac) >>
  `v = land /\ G1 = G /\ tn1 = tn` by
    (qpat_x_assum `(?target entered. lookup_block _ _ = SOME target /\ _) \/ _`
       strip_assume_tac
     >- (rename1 `eval_phis land landed_block.bb_instructions = OK entered_state` >>
         `phi_prefix_length landed_block.bb_instructions = 0` by metis_tac[optionTheory.SOME_11] >>
         `eval_phis land landed_block.bb_instructions = OK land /\
          entry_prov obs land G = G /\ entry_taint_vars obs land tn = tn` by
           (irule store_observer_phi_zero >> metis_tac[]) >> fs[]) >>
     simp[]) >>
  simp[] >> conj_tac >- (irule store_observer_install >> metis_tac[]) >>
  rename1 `lookup_block land.vs_current_bb f.fn_blocks = SOME target'` >>
  `eval_phis land target'.bb_instructions = OK land` by
    metis_tac[store_observer_phi_zero] >>
  simp[abi_observer_step_def] >> metis_tac[]) >>
  metis_tac[]
QED

(* The geometric premises only concern the emitted instructions and their
   generated branch labels, not the observer's memory or pointer semantics. *)
Theorem store_observer_joint_step:
  cs_extends a b /\ fn_has_code a b f /\ frag_gas_free a b /\
  (u.vs_current_bb,u.vs_inst_idx) IN frag_observer_region a b /\
  (u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut b /\
  (!i. MEM i (frag_code a b) ==>
    i.inst_id IN frag_ids a b /\
    MEM i.inst_opcode [ADD; MLOAD; AND; MCOPY; NOT; MSTORE; INVALID; ASSIGN;
                       JMP; LT; ISZERO; JNZ; MUL; GT; ASSERT]) /\
  (!i lbl. MEM i (frag_code a b) /\ MEM i.inst_opcode [JMP; JNZ] /\
    MEM (Label lbl) i.inst_operands ==>
    (lbl,0) IN frag_observer_region a b /\
    ?ob bb. lookup_block lbl (frag_observer a b f id).fn_blocks = SOME ob /\
            lookup_block lbl f.fn_blocks = SOME bb /\
            phi_prefix_length ob.bb_instructions = 0 /\
            phi_prefix_length bb.bb_instructions = 0) /\
  gas_origin_ptr_edge (D,lo,explicit,ctx,frag_observer a b f id,PG)
    (u,G,tn) [] (OK v,G1,tn1) ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,f,PG) (u,G,tn) [] (OK v,G1,tn1) /\
  create_prefix_step a b explicit ctx f u [] v /\
  (v.vs_current_bb,v.vs_inst_idx) IN frag_observer_region a b
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_assum `gas_origin_ptr_edge _ _ _ _`
    (mp_then (Pat `gas_origin_ptr_edge _ _ _ _`)
      (qspecl_then [`f`,`ctx`,`b`,`a`] mp_tac) create_observer_joint_step_transfer) >>
  impl_tac
  >- (simp[] >> conj_tac
      >- (rpt strip_tac >> drule_all frag_observer_code_provenance >> strip_tac >>
          drule_all frag_observer_instruction_agrees >> strip_tac >>
          qpat_assum `!i. MEM i (frag_code _ _) ==> _`
            (drule_then (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
          gvs[] >> metis_tac[]) >>
      rpt strip_tac >>
      `MEM i.inst_opcode [JMP; JNZ] /\ MEM (Label lbl) i.inst_operands` by
        (`i.inst_opcode <> DJMP` by
           (qpat_assum `!j. MEM j (frag_code _ _) ==> _`
              (qspec_then `i` (drule_then (mp_tac o CONJUNCT2))) >>
            simp_tac (srw_ss()) [] >> rpt strip_tac >> gvs[]) >>
         qpat_x_assum `MEM lbl (create_cut_targets _ _)` mp_tac >>
         Cases_on `i.inst_opcode = JMP` >> Cases_on `i.inst_opcode = JNZ` >>
         simp[create_cut_targets_def] >> rpt (CASE_TAC >> gvs[])) >>
      metis_tac[]) >>
  metis_tac[]
QED
