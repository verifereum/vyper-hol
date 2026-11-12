Theory lowerDloadCoverageLoad
Ancestors
  lowerDloadNormalLoad lowerDloadControlPosition lowerDloadPhaseBoundary
  lowerDloadOrdinaryNext lowerDloadSupplySegment lowerDloadDefs
  lowerDloadNormalData lowerDloadCoverageInvariant lowerDloadFrameCertificate
  lowerDloadOwnership lowerDloadAllocation o1ContractLowerDload
  lowerDloadProvenanceSupport
  venomExecSemantics venomState venomInst ptrDiscipline finite_map list words

Theorem ld_configured_load_next_backward:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn u0 s t0
    astk live keys d0 A suspended gstk f /\
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!fn. MEM fn CS.ctx_functions ==> fn_ptr_ok P fn) /\
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  ~in_revert_forward fn s /\ dload_offset_ok CS fn i s /\
  (!v. off = Var v ==> v IN U) /\
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\ b.inst_outputs = [bv] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\ c.inst_outputs = [] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  av <> bv /\ av NOTIN U /\ bv NOTIN U /\ av NOTIN V /\ bv NOTIN V /\
  out IN U /\ out IN V /\ av NOTIN FDOM BH /\ bv NOTIN FDOM BH /\
  ld_target_prefix CT [a;b;c;d] t0 u0 (SUC (SUC (SUC (SUC 0)))) t u /\
  code_layout_valid s /\
  eval_operand (Label "code_end") t0 =
    SOME (n2w (LENGTH s.vs_code - LENGTH s.vs_data_section)) /\
  a.inst_id IN keys /\ allocas_non_overlapping t0 /\ alloca_next_valid t0 /\
  t0.vs_alloca_next < dimword (:256) /\
  (a.inst_id NOTIN A ==> t0.vs_alloca_next + 32 < dimword (:256)) /\
  lower_dload_block_supply a0 bb = (gb,bend) /\
  lower_dload_insts_supply a0 pre = (p,a1) /\
  lower_dload_inst_supply a1 i = ([a;b;c;d],a2) /\
  lower_dload_inst_supply a2 j = (next,a3) /\
  lower_dload_insts_supply a3 post = (tail,bend) /\
  bb.bb_instructions = pre ++ i::j::post /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t0.vs_current_bb gn.fn_blocks = SOME gb /\
  s.vs_inst_idx = LENGTH pre /\ t0.vs_inst_idx = LENGTH p ==>
  ?z. step_inst fuelS CS i s = OK z /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_set_prov AG [out] NONE)
      (ld_set_prov (ld_set_prov BH [bv] NONE) [out] NONE)
      (step_taint i s z tn) u (z with vs_inst_idx := SUC s.vs_inst_idx) t
      astk live keys d0 (a.inst_id INSERT A) suspended gstk f /\
    ld_annotated_reachable vs0 CS astk k L AP (ld_set_prov AG [out] NONE)
      (step_taint i s z tn) fn j (z with vs_inst_idx := SUC s.vs_inst_idx) /\
    active_inst gn (HD next) t /\
    lower_dload_insts_supply a0 (pre ++ [i]) = (p ++ [a;b;c;d],a2) /\
    (z with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx = LENGTH (pre ++ [i]) /\
    t.vs_inst_idx = LENGTH (p ++ [a;b;c;d])
Proof
  strip_tac >>
  qpat_assum `ld_annotated_reachable _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any (drule_all_then mp_tac) ld_load_normal_data_backward) >>
  disch_then (qspec_then `fuelS` (qx_choose_then `z` strip_assume_tac)) >>
  `z.vs_current_bb = s.vs_current_bb /\ t.vs_current_bb = t0.vs_current_bb` by
    (qpat_assum `z with vs_vars := _ = s` (SUBST1_TAC o SYM) >>
     qpat_assum `t with <|vs_memory := _; vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = t0` (SUBST1_TAC o SYM) >> simp[]) >>
  drule ld_target_prefix_index >> strip_tac >>
  `next <> []` by metis_tac[lower_dload_inst_supply_nonempty] >>
  `lower_dload_insts_supply a1 (i::j::post) = ([a;b;c;d] ++ next ++ tail,bend)` by
    simp[lower_dload_insts_supply_def] >>
  `lower_dload_insts_supply a0 (pre ++ (i::j::post)) =
    (p ++ ([a;b;c;d] ++ next ++ tail),bend)` by
    (irule lower_dload_insts_supply_append_forward >>
     goal_assum (drule_at Any) >> simp[]) >>
  `gb.bb_instructions = p ++ [a;b;c;d] ++ next ++ tail` by
    gvs[lower_dload_block_supply_def] >>
  `lower_dload_insts_supply a0 (pre ++ [i]) = (p ++ [a;b;c;d],a2) /\
   active_inst fn j (z with vs_inst_idx := SUC (LENGTH pre)) /\
   active_inst gn (HD next) (t with vs_inst_idx := LENGTH p + LENGTH [a;b;c;d])` by
    (irule lower_dload_configured_segment_next >>
     goal_assum (drule_at Any) >> simp[]) >>
  `ld_erase L = z.vs_allocas` by
    (drule ld_normal_data_frame >>
     disch_then (mp_tac o MATCH_MP ld_frame_data_embedding) >>
     simp[ld_frame_embedding_def]) >>
  `ld_annotated_reachable vs0 CS astk k L AP (ld_set_prov AG [out] NONE)
     (step_taint i s z tn) fn j (z with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_assum `ld_step_prov AP AG L i = _` (SUBST1_TAC o SYM) >>
     irule ld_annotated_reachable_next >>
     goal_assum (drule_at Any) >>
     simp[ld_select_alloca_def, is_terminator_def] >>
     metis_tac[ld_annotated_active_inst]) >>
  `t with vs_inst_idx := LENGTH p + LENGTH [a;b;c;d] = t` by
    (`LENGTH p + LENGTH [a;b;c;d] = t.vs_inst_idx` by simp[] >>
     pop_assum SUBST1_TAC >> simp[]) >>
  qexists_tac `z` >> simp[] >> conj_tac
  >- (qpat_assum `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ u z t _ _ _ _ _ _ _ _`
        mp_tac >>
      disch_then (mp_tac o Q.SPECL [`SUC (LENGTH (pre:instruction list))`,`t.vs_inst_idx`] o
        MATCH_MP ld_normal_data_index_update) >> simp[]) >>
  qpat_x_assum `active_inst gn _ _` mp_tac >>
  qpat_assum `t with vs_inst_idx := _ = t` SUBST1_TAC >> simp[]
QED
