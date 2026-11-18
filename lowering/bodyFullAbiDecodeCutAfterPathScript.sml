Theory bodyFullAbiDecodeCutAfterPath
Ancestors
  bodyFullAbiDecodeCutPath exprSimAbiGasBridge fragGasPath fragExec
  abiEncoderObserver venomExecSemantics venomInst venomInstProps venomState
  relation list
Libs
  bodyFullAbiDecodeCutPathLib

(* Only the current block and index select an instruction off the relabelled
   entry. Keep layout facts separate from the selected execution. *)
val after_controls = ``\obs cut L.
  (!lbl idx bb i.
     lbl <> L /\ (lbl,idx) <> cut /\
     lookup_block lbl obs.fn_blocks = SOME bb /\ get_instruction bb idx = SOME i ==>
     i.inst_opcode <> PHI /\ i.inst_opcode <> INVOKE /\
     i.inst_opcode <> STOP /\ i.inst_opcode <> RETURN /\
     (!s t. MEM i.inst_opcode [JMP; JNZ; DJMP] /\ step_inst_base i s = OK t ==>
            t.vs_current_bb <> L)) /\
  (!lbl bb. lbl <> L /\ lookup_block lbl obs.fn_blocks = SOME bb ==>
            phi_prefix_length bb.bb_instructions = 0) /\
  (?bb id. lookup_block (FST cut) obs.fn_blocks = SOME bb /\
           get_instruction bb (SND cut) = SOME (mk_inst id STOP [] []))``;

Theorem cut_after_related[local]:
  v.vs_current_bb <> L ==>
  frag_relabel_state L entry (v with vs_prev_bb := p) v
Proof
  simp[frag_relabel_state_def] >> strip_tac >> qexists `v.vs_prev_bb` >>
  simp[venom_state_component_equality]
QED

Theorem cut_after_within[local]:
  lookup_block s.vs_current_bb obs.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  (s.vs_current_bb,s.vs_inst_idx) <> cut /\ s.vs_current_bb <> L /\
  ~s.vs_halted /\ ~t.vs_halted /\ i.inst_opcode <> PHI /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  step_inst_base i s = OK t ==>
  ?w. abi_observer_step ctx obs cut (s with vs_prev_bb := p) w /\
      w.vs_current_bb <> L /\
      frag_relabel_state L entry w (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by
    (irule (cj 1 step_preserves_control_flow) >> metis_tac[step_inst_non_invoke]) >>
  `step_inst 0 ctx i (s with vs_prev_bb := p) = OK (t with vs_prev_bb := p)` by
    (simp[step_inst_non_invoke] >>
     drule_all frag_relabel_base_nonphi >>
     disch_then (qspecl_then [`p`,`s.vs_current_bb`] mp_tac) >>
     simp[venom_state_component_equality]) >>
  qexists `(t with vs_inst_idx := SUC s.vs_inst_idx) with vs_prev_bb := p` >>
  simp[cut_after_related, abi_observer_step_def] >>
  qexists `t with vs_prev_bb := p` >> simp[venom_state_component_equality]
QED

Theorem cut_after_jump[local]:
  lookup_block s.vs_current_bb obs.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  (s.vs_current_bb,s.vs_inst_idx) <> cut /\
  ~s.vs_halted /\ ~t.vs_halted /\ i.inst_opcode <> INVOKE /\
  is_terminator i.inst_opcode /\ MEM i.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst_base i s = OK t /\ t.vs_current_bb <> L /\
  lookup_block t.vs_current_bb obs.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 ==>
  ?w. abi_observer_step ctx obs cut (s with vs_prev_bb := p) w /\
      w.vs_current_bb <> L /\
      frag_relabel_state L entry w (t with vs_inst_idx := 0)
Proof
  strip_tac >>
  `step_inst 0 ctx i (s with vs_prev_bb := p) =
     OK (t with vs_prev_bb := SOME s.vs_current_bb)` by
    (simp[step_inst_non_invoke] >> drule_all frag_relabel_jump_control >>
     disch_then (qspecl_then [`p`,`s.vs_current_bb`] mp_tac) >>
     simp[venom_state_component_equality]) >>
  qexists `(t with vs_inst_idx := 0) with vs_prev_bb := SOME s.vs_current_bb` >>
  simp[cut_after_related, abi_observer_step_def] >>
  qexists `t with vs_prev_bb := SOME s.vs_current_bb` >>
  simp[eval_phis_no_phi, venom_state_component_equality]
QED

Theorem cut_after_ok_edge[local]:
  (^after_controls) obs cut L /\ v.vs_current_bb <> L /\
  lookup_block t.vs_current_bb obs.fn_blocks <> NONE /\
  gas_path_edge ctx obs v n (OK t) ==>
  ?w. abi_observer_step ctx obs cut (v with vs_prev_bb := p) w /\
      w.vs_current_bb <> L /\ frag_relabel_state L entry w t
Proof
  simp_tac bool_ss [BETA_THM] >> simp[gas_path_edge_def] >>
  rpt strip_tac >> gvs[exit_result_def] >>
  rename1 `lookup_block v.vs_current_bb obs.fn_blocks = SOME current` >>
  `(v.vs_current_bb,v.vs_inst_idx) <> cut` by
    (strip_tac >> gvs[] >>
     fs[step_inst_non_invoke, mk_inst_def, step_inst_base_opcode_eqs]) >>
  qpat_assum `!lbl idx bb i. _` (qspecl_then
    [`v.vs_current_bb`,`v.vs_inst_idx`,`current`,`inst`] mp_tac) >>
  simp[] >> strip_tac >> gvs[step_inst_non_invoke]
  >- (irule cut_after_within >> metis_tac[])
  >- suspend "enter"
  >- suspend "jump"
  >> qpat_assum `OK t = _` (fn th => fs[GSYM th, exit_result_def])
QED

Resume cut_after_ok_edge[enter]:
  rename1 `step_inst_base inst v = OK middle` >>
  rename1 `lookup_block middle.vs_current_bb obs.fn_blocks = SOME target` >>
  `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[frag_successful_terminator_jump, step_inst_non_invoke] >>
  `middle.vs_current_bb <> L /\ phi_prefix_length target.bb_instructions = 0` by
    metis_tac[MEM] >>
  gvs[eval_phis_no_phi] >> irule cut_after_jump >> simp[]
QED

Resume cut_after_ok_edge[jump]:
  rename1 `step_inst_base inst v = OK (jump_to lbl v)` >>
  `~(jump_to lbl v).vs_halted` by simp[jump_to_def] >>
  `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[frag_successful_terminator_jump, step_inst_non_invoke] >>
  `?target. lookup_block (jump_to lbl v).vs_current_bb obs.fn_blocks = SOME target` by
    (Cases_on `lookup_block (jump_to lbl v).vs_current_bb obs.fn_blocks` >> fs[]) >>
  `(jump_to lbl v).vs_current_bb <> L /\ phi_prefix_length target.bb_instructions = 0` by
    metis_tac[MEM] >>
  `jump_to lbl v = (jump_to lbl v) with vs_inst_idx := 0` by
     simp[jump_to_def, venom_state_component_equality] >>
  pop_assum (fn th => once_rewrite_tac[th]) >> irule cut_after_jump >> metis_tac[]
QED

Finalise cut_after_ok_edge


Theorem cut_after_revert_edge[local]:
  (^after_controls) obs cut L /\ v.vs_current_bb <> L /\
  gas_path_edge ctx obs v n (Abort Revert_abort t) ==>
  ?w k. frag_relabel_state L entry w t /\
        run_from k ctx obs (v with vs_prev_bb := p) = Abort Revert_abort w
Proof
  simp_tac bool_ss [BETA_THM] >> simp[gas_path_edge_def] >>
  rpt strip_tac >> gvs[exit_result_def] >>
  rename1 `lookup_block v.vs_current_bb obs.fn_blocks = SOME current` >>
  `(v.vs_current_bb,v.vs_inst_idx) <> cut` by
    (strip_tac >> gvs[] >>
     fs[step_inst_non_invoke, mk_inst_def, step_inst_base_opcode_eqs]) >>
  qpat_assum `!lbl idx bb i. _` (qspecl_then
    [`v.vs_current_bb`,`v.vs_inst_idx`,`current`,`inst`] mp_tac) >>
  simp[] >> strip_tac >> gvs[step_inst_non_invoke] >>
  qpat_x_assum `Abort Revert_abort t = _` (assume_tac o SYM) >>
  `t.vs_current_bb = v.vs_current_bb` by
    (drule_all frag_relabel_base_abort >>
     disch_then (qspecl_then [`v.vs_prev_bb`,`v.vs_current_bb`] mp_tac) >>
     simp[venom_state_component_equality]) >>
  `step_inst 0 ctx inst (v with vs_prev_bb := p) =
     Abort Revert_abort (t with vs_prev_bb := p)` by
    (simp[step_inst_non_invoke] >> drule_all frag_relabel_base_abort >>
     disch_then (qspecl_then [`p`,`v.vs_current_bb`] mp_tac) >>
     simp[venom_state_component_equality]) >>
  qexistsl [`t with vs_prev_bb := p`,`0`] >>
  simp[cut_after_related, run_from_def] >>
  `exec_block 0 ctx current (v with vs_prev_bb := p) =
     Abort Revert_abort (t with vs_prev_bb := p)` by
    (irule exec_block_step_abort >> qexists `inst` >> simp[]) >> simp[]
QED

(* A raw jump need not provide a target lookup itself. The selected
   continuation supplies it either at its first edge or at the OK endpoint. *)
Theorem cut_after_lookup[local]:
  gas_path ctx obs v n r /\
  (!t. r = OK t ==> lookup_block t.vs_current_bb obs.fn_blocks <> NONE) ==>
  lookup_block v.vs_current_bb obs.fn_blocks <> NONE
Proof
  simp[Once gas_path_cases] >> rpt strip_tac >> gvs[] >>
  fs[gas_path_edge_def]
QED

Theorem cut_after_path_aux[local]:
  !ctx obs v n r. gas_path ctx obs v n r ==>
    !cut L entry p cursor.
      (^after_controls) obs cut L /\ v.vs_current_bb <> L /\
      (case r of
         OK t => lookup_block t.vs_current_bb obs.fn_blocks <> NONE /\
                 (t.vs_current_bb,t.vs_inst_idx) = cursor
       | Abort a t => a = Revert_abort
       | _ => F) ==>
      (^shadow_result) ctx obs cut L entry (v with vs_prev_bb := p) cursor r
Proof
  ho_match_mp_tac gas_path_strongind >> rpt conj_tac
  >- (simp_tac bool_ss [BETA_THM] >> rpt strip_tac >>
      rename1 `~v.vs_halted` >>
      disj1_tac >> qexistsl [`v`, `v with vs_prev_bb := p`] >>
      gvs[cut_after_related, RTC_REFL])
  >- suspend "cons"
  >> suspend "exit"
QED

Resume cut_after_path_aux[cons]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `gas_path ctx obs middle m r` >>
  `lookup_block middle.vs_current_bb obs.fn_blocks <> NONE` by
    (irule cut_after_lookup >> qexistsl [`ctx`,`m`,`r`] >>
     simp[] >> rpt strip_tac >> gvs[]) >>
  drule_all cut_after_ok_edge >>
  disch_then (qspecl_then [`p`,`entry`] strip_assume_tac) >>
  irule abi_decode_cut_prefix_bind >> qexists `w` >>
  conj_tac >- metis_tac[RTC_SINGLE] >>
  `w = middle with vs_prev_bb := w.vs_prev_bb` by
    (drule_all frag_relabel_state_cut >> simp[venom_state_component_equality]) >>
  pop_assum SUBST1_TAC >> qpat_assum `!cut L entry p cursor. _` irule >> simp[] >>
  metis_tac[frag_relabel_state_fields]
QED

Resume cut_after_path_aux[exit]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `r` >>
  gvs[exit_result_def] >> strip_tac >> gvs[] >>
  simp_tac bool_ss [BETA_THM] >>
  irule (BETA_RULE cut_after_revert_edge) >>
  conj_tac >- gvs[] >> simp[] >>
  conj_tac >- (qexists `cut` >> simp[] >> metis_tac[MEM]) >>
  qexists `n` >> simp[]
QED

Finalise cut_after_path_aux

(* All paths use the same observer. A successful endpoint can already be
   at the outer cut; its zero-edge observation does not execute the STOP. *)
Theorem abi_decode_cut_after_path:
  gas_path ctx obs v n r /\ (^after_controls) obs cut L /\
  u.vs_current_bb <> L /\ frag_relabel_state L entry u v /\
  (case r of
     OK t => lookup_block t.vs_current_bb obs.fn_blocks <> NONE /\
             (t.vs_current_bb,t.vs_inst_idx) = cursor
   | Abort a t => a = Revert_abort
   | _ => F) ==>
  (^shadow_result) ctx obs cut L entry u cursor r
Proof
  strip_tac >>
  `u = v with vs_prev_bb := u.vs_prev_bb /\ v.vs_current_bb <> L` by
    (drule_all frag_relabel_state_cut >> simp[venom_state_component_equality]) >>
  qpat_x_assum `u = _` SUBST1_TAC >> irule cut_after_path_aux >> metis_tac[]
QED
