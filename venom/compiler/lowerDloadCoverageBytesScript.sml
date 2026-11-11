Theory lowerDloadCoverageBytes
Ancestors
  lowerDloadNormalBytes lowerDloadControlPosition lowerDloadPhaseBoundary
  lowerDloadOrdinaryNext lowerDloadSupplySegment lowerDloadDefs
  lowerDloadNormalData lowerDloadCoverageInvariant lowerDloadFrameCertificate
  lowerDloadOwnership lowerDloadAllocation o1ContractLowerDload
  lowerDloadProvenanceSupport
  venomExecSemantics venomState venomInst ptrDiscipline finite_map list words

Theorem ld_configured_bytes_next_backward:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn u0 s t0
    astk live keys d A suspended gstk f /\
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!fn. MEM fn CS.ctx_functions ==> fn_ptr_ok P fn) /\
  i.inst_opcode = DLOADBYTES /\ i.inst_operands = [dst;off;sz] /\
  i.inst_outputs = [] /\ ~in_revert_forward fn s /\
  (!v. MEM (Var v) [dst;off;sz] ==> v IN U) /\
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  c.inst_outputs = [] /\
  (!v. dst = Var v ==> v <> av) /\ (!v. sz = Var v ==> v <> av) /\
  ld_target_prefix CT [a;c] t0 u0 (SUC (SUC 0)) t u /\
  code_layout_valid s /\
  eval_operand (Label "code_end") t0 =
    SOME (n2w (LENGTH s.vs_code - LENGTH s.vs_data_section)) /\
  dload_offset_ok CS fn i s /\ av NOTIN U /\ av NOTIN V /\
  av NOTIN FDOM BH /\
  lower_dload_block_supply a0 bb = (gb,b) /\
  lower_dload_insts_supply a0 pre = (p,a1) /\
  lower_dload_inst_supply a1 i = ([a;c],a2) /\
  lower_dload_inst_supply a2 j = (next,a3) /\
  lower_dload_insts_supply a3 post = (tail,b) /\
  bb.bb_instructions = pre ++ i::j::post /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t0.vs_current_bb gn.fn_blocks = SOME gb /\
  s.vs_inst_idx = LENGTH pre /\ t0.vs_inst_idx = LENGTH p ==>
  ?z. step_inst fuelS CS i s = OK z /\
    ld_normal_data CS fn V U lo E L H AP BP AG BH
      (step_taint i s z tn) u (z with vs_inst_idx := SUC s.vs_inst_idx) t
      astk live keys d A suspended gstk f /\
    ld_annotated_reachable vs0 CS astk k L AP AG
      (step_taint i s z tn) fn j (z with vs_inst_idx := SUC s.vs_inst_idx) /\
    active_inst gn (HD next) t /\
    lower_dload_insts_supply a0 (pre ++ [i]) = (p ++ [a;c],a2) /\
    (z with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx = LENGTH (pre ++ [i]) /\
    t.vs_inst_idx = LENGTH (p ++ [a;c])
Proof
  strip_tac >>
  drule_all ld_bytes_normal_data_backward >>
  disch_then (qspec_then `fuelS` (qx_choose_then `z` strip_assume_tac)) >>
  `z.vs_current_bb = s.vs_current_bb /\ t.vs_current_bb = t0.vs_current_bb` by
    (qpat_assum `z with vs_memory := _ = s` (SUBST1_TAC o SYM) >>
     qpat_assum `t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|> = t0`
       (SUBST1_TAC o SYM) >> simp[]) >>
  drule ld_target_prefix_index >> strip_tac >>
  `next <> []` by metis_tac[lower_dload_inst_supply_nonempty] >>
  `lower_dload_insts_supply a1 (i::j::post) = ([a;c] ++ next ++ tail,b)` by
    simp[lower_dload_insts_supply_def] >>
  `lower_dload_insts_supply a0 (pre ++ (i::j::post)) =
    (p ++ ([a;c] ++ next ++ tail),b)` by
    (irule lower_dload_insts_supply_append_forward >>
     goal_assum (drule_at Any) >> simp[]) >>
  `gb.bb_instructions = p ++ [a;c] ++ next ++ tail` by
    gvs[lower_dload_block_supply_def] >>
  `lower_dload_insts_supply a0 (pre ++ [i]) = (p ++ [a;c],a2) /\
   active_inst fn j (z with vs_inst_idx := SUC (LENGTH pre)) /\
   active_inst gn (HD next) (t with vs_inst_idx := LENGTH p + LENGTH [a;c])` by
    (irule lower_dload_configured_segment_next >>
     goal_assum (drule_at Any) >> simp[]) >>
  `ld_erase L = z.vs_allocas` by
    (drule ld_normal_data_frame >>
     disch_then (mp_tac o MATCH_MP ld_frame_data_embedding) >>
     simp[ld_frame_embedding_def]) >>
  `ld_annotated_reachable vs0 CS astk k L AP AG
     (step_taint i s z tn) fn j (z with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_assum `ld_step_prov AP AG L i = AG` (SUBST1_TAC o SYM) >>
     irule ld_annotated_reachable_next >>
     goal_assum (drule_at Any) >>
     simp[ld_select_alloca_def, is_terminator_def] >>
     metis_tac[ld_annotated_active_inst]) >>
  `t with vs_inst_idx := LENGTH p + LENGTH [a;c] = t` by
    (`LENGTH p + LENGTH [a;c] = t.vs_inst_idx` by simp[] >>
     pop_assum SUBST1_TAC >> simp[]) >>
  qexists_tac `z` >> simp[] >> conj_tac
  >- (qpat_assum `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ u z t _ _ _ _ _ _ _ _`
        mp_tac >>
      disch_then (mp_tac o Q.SPECL [`SUC (LENGTH (pre:instruction list))`,`t.vs_inst_idx`] o
        MATCH_MP ld_normal_data_index_update) >> simp[]) >>
  qpat_x_assum `active_inst gn _ _` mp_tac >>
  qpat_assum `t with vs_inst_idx := _ = t` SUBST1_TAC >> simp[]
QED
