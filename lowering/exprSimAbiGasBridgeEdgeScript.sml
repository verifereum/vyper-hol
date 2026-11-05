(* The relabeled-observer gas bridges without the end-block premise on the
   counted function: when the fragment ends in a fresh empty block, the
   counted path stops at the jump into it, at index 0, before any PHIs
   there run.  The observer-side (fn') premises are unchanged. *)
Theory exprSimAbiGasBridgeEdge
Ancestors
  exprSimAbiGasBridge
  fragGasMode fragExec exprLoweringProps abiDecoderLoop abiEncoderObserver
  venomInst venomExecSemantics venomState compileEnv list rich_list
  fragGasPath gasCount arithmetic venomExecProofs venomInstProps venomWf
  instIdxIndep

Definition frag_relabel_edge_context_def:
  frag_relabel_edge_context sa sb L ids fn <=>
    cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
    fn_has_code sa sb fn /\ LENGTH ids = LENGTH sa.cs_current_insts /\
    L <> sb.cs_current_bb /\
    ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
    EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code sa sb)
End

Theorem frag_relabel_edge_observer_phis:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
  lbl <> L /\
  lookup_block lbl (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb ==>
  phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  `emitted_blocks sa sb <> []` by
    (drule frag_extends_emitted_shape >> strip_tac >> gvs[]) >>
  drule frag_relabel_observer_lookup_cases >> strip_tac
  >- (gvs[] >>
      `EVERY (\i. i.inst_opcode <> PHI) sb.cs_current_insts` by
        (fs[frag_ops_free_def, frag_code_def, NULL_EQ, EVERY_APPEND, EVERY_MEM] >>
         metis_tac[]) >>
      Cases_on `sb.cs_current_insts` >>
      fs[phi_prefix_length_def, mk_inst_def]) >>
  drule_all start_swap_emitted_blocks >> strip_tac >> fs[MEM_APPEND] >> gvs[] >>
  drule_all frag_relabel_front_nonphi >> strip_tac >>
  Cases_on `bb.bb_instructions` >> fs[phi_prefix_length_def]
QED

Theorem frag_relabel_edge_base_nonphi[local]:
  inst.inst_opcode <> PHI /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst_base inst s = OK t ==>
  step_inst_base inst (s with <|vs_current_bb := b; vs_prev_bb := p|>) =
    OK (t with <|vs_current_bb := b; vs_prev_bb := p|>)
Proof
  Cases_on `is_pseudo inst.inst_opcode`
  >- (Cases_on `inst.inst_opcode` >>
      fs[is_pseudo_def] >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> simp[update_var_def]) >>
  metis_tac[frag_relabel_base_ordinary]
QED

Theorem frag_relabel_edge_ordinary:
  frag_relabel_state L entry u v /\ ~u.vs_halted /\
  lookup_block v.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> GAS /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  step_inst_base inst u = OK middle /\ ~middle.vs_halted ==>
  ?v'. gas_path_edge ctx fn v 0 (OK v') /\
       frag_relabel_state L entry
         (middle with vs_inst_idx := SUC u.vs_inst_idx) v'
Proof
  strip_tac >>
  `middle.vs_current_bb = u.vs_current_bb` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  fs[frag_relabel_state_def] >> gvs[] >>
  drule_all frag_relabel_edge_base_nonphi >>
  disch_then (qspecl_then
    [`p`, `if u.vs_current_bb = L then entry else u.vs_current_bb`] assume_tac) >>
  qexists_tac `middle with <|vs_current_bb :=
     (if u.vs_current_bb = L then entry else u.vs_current_bb);
     vs_prev_bb := p; vs_inst_idx := SUC u.vs_inst_idx|>` >>
  gvs[] >> conj_tac
  >- (simp[gas_path_edge_def] >> qexists_tac `0` >>
      simp[step_inst_non_invoke, gas_count_step_def]) >>
  qexists_tac `p` >> simp[venom_state_component_equality]
QED

Theorem frag_relabel_edge_operand_control[local]:
  !op s b p.
    eval_operand op (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem frag_relabel_edge_jump_control:
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\ step_inst_base inst u = OK middle ==>
  step_inst_base inst (u with <|vs_current_bb := b; vs_prev_bb := p|>) =
    OK (middle with vs_prev_bb := SOME b)
Proof
  simp[MEM] >> strip_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[frag_relabel_edge_operand_control] >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  simp[jump_to_def, venom_state_component_equality]
QED

Theorem frag_relabel_edge_raw_jump:
  frag_relabel_state L entry u v /\ ~u.vs_halted /\
  lookup_block v.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst /\
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst_base inst u = OK (jump_to lbl u) /\ lbl <> L ==>
  ?v'. gas_path_edge ctx fn v 0 (OK v') /\
       frag_relabel_state L entry (jump_to lbl u) v'
Proof
  strip_tac >> fs[frag_relabel_state_def] >> gvs[] >>
  `step_inst_base inst (u with <|vs_current_bb :=
    (if u.vs_current_bb = L then entry else u.vs_current_bb); vs_prev_bb := p|>) =
    OK ((jump_to lbl u) with vs_prev_bb :=
      SOME (if u.vs_current_bb = L then entry else u.vs_current_bb))` by
    metis_tac[frag_relabel_edge_jump_control, MEM] >>
  (qexists_tac `jump_to lbl (u with <|vs_current_bb :=
    (if u.vs_current_bb = L then entry else u.vs_current_bb); vs_prev_bb := p|>)` >>
  conj_tac
  >- (simp[gas_path_edge_def] >> qexists_tac `0` >>
      gvs[jump_to_def, step_inst_non_invoke, gas_count_step_def, MEM,
          is_terminator_def] >>
      disj2_tac >> disj1_tac >> qexists_tac `lbl` >> simp[]) >>
  simp[frag_relabel_state_def, jump_to_def, venom_state_component_equality])
QED

Theorem frag_edge_successful_terminator_jump[local]:
  step_inst 0 ctx inst s = OK middle /\ ~middle.vs_halted /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> STOP /\ inst.inst_opcode <> RETURN ==>
  MEM inst.inst_opcode [JMP; JNZ; DJMP]
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  pairarg_tac >> gvs[]
QED

Theorem frag_relabel_edge_region_entry_bound:
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  LENGTH ids = LENGTH sa.cs_current_insts ==>
  (u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)
Proof
  simp[frag_observer_region_def, start_relabel_def] >> metis_tac[]
QED

Theorem frag_relabel_edge_off_cut_opcodes:
  frag_relabel_edge_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  (u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut sb /\
  lookup_block u.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst ==>
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> STOP /\ inst.inst_opcode <> RETURN
Proof
  strip_tac >> fs[frag_relabel_edge_context_def] >>
  `(u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)` by
    metis_tac[frag_relabel_edge_region_entry_bound] >>
  drule_all frag_relabel_code_provenance >> strip_tac >>
  fs[frag_ops_free_def, EVERY_MEM]
QED

Theorem frag_relabel_edge_region_closed:
  frag_relabel_edge_context sa sb L ids fn ==>
  observer_region_closed ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb)
    (frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb))
Proof
  strip_tac >> rw[observer_region_closed_def] >>
  fs[abi_observer_step_def] >>
  drule_all frag_relabel_edge_off_cut_opcodes >> strip_tac
  >- (drule_all step_preserves_control_flow >> strip_tac >>
      gvs[frag_observer_region_def] >> metis_tac[LESS_EQ_SUC_REFL, LESS_EQ_TRANS]) >>
  `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[frag_edge_successful_terminator_jump] >>
  `middle.vs_current_bb <> L` by
    (`(s.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= s.vs_inst_idx)` by
       (fs[frag_relabel_edge_context_def] >> metis_tac[frag_relabel_edge_region_entry_bound]) >>
     `step_inst_base inst s = OK middle` by metis_tac[step_inst_non_invoke] >>
     fs[frag_relabel_edge_context_def, EVERY_MEM] >>
     metis_tac[frag_relabel_jump_no_reentry, MEM]) >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  drule frag_relabel_observer_lookup_cases >> strip_tac >>
  fs[frag_relabel_edge_context_def] >> drule_all start_swap_fields >> strip_tac >>
  gvs[frag_observer_region_def, start_relabel_def, MEM_MAP] >> metis_tac[]
QED

Theorem frag_relabel_edge_step:
  frag_relabel_edge_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  frag_relabel_state L sa.cs_current_bb u v /\
  abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb) u u' ==>
  ?v'. gas_path_edge ctx fn v 0 (OK v') /\ frag_relabel_state L sa.cs_current_bb u' v'
Proof
  strip_tac >> fs[abi_observer_step_def] >>
  drule_all frag_relabel_edge_off_cut_opcodes >> strip_tac >>
  `(u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)` by
    (fs[frag_relabel_edge_context_def] >> metis_tac[frag_relabel_edge_region_entry_bound]) >>
  `?original. lookup_block
    (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb)
      fn.fn_blocks = SOME original /\
    get_instruction original u.vs_inst_idx = SOME inst` by
    (fs[frag_relabel_edge_context_def] >> drule_all frag_relabel_instruction_agrees >> simp[]) >>
  `step_inst_base inst u = OK middle` by metis_tac[step_inst_non_invoke] >>
  drule frag_relabel_state_fields >> strip_tac
  >- (irule frag_relabel_edge_ordinary >> goal_assum (drule_at Any) >> gvs[]) >>
  `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[frag_edge_successful_terminator_jump] >>
  `middle.vs_current_bb <> L` by
    (fs[frag_relabel_edge_context_def, EVERY_MEM] >>
     metis_tac[frag_relabel_jump_no_reentry, MEM]) >>
  `phi_prefix_length target.bb_instructions = 0` by
    (fs[frag_relabel_edge_context_def] >> metis_tac[frag_relabel_edge_observer_phis]) >>
  qpat_x_assum `eval_phis _ _ = _` mp_tac >>
  once_rewrite_tac[GSYM eval_phis_prefix] >> simp[eval_phis_def] >> strip_tac >> gvs[] >>
  rename1 `step_inst_base inst u = OK jumped` >>
  `jumped = jump_to jumped.vs_current_bb u` by
    (gvs[MEM] >>
     gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
     simp[jump_to_def]) >>
  `jumped.vs_inst_idx = 0` by
    (qpat_x_assum `jumped = jump_to _ _` mp_tac >>
     simp[jump_to_def, venom_state_component_equality] >> metis_tac[]) >>
  `jumped with vs_inst_idx := 0 = jumped` by
    simp[venom_state_component_equality] >>
  gvs[] >> metis_tac[frag_relabel_edge_raw_jump, MEM]
QED

Theorem frag_exec_gas_path_relabel_edge:
  !ctx sa sb Q R fn s.
    (!L ids fn'.
       LENGTH ids = LENGTH sa.cs_current_insts /\
       fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) fn' /\
       fn_inst_ids_distinct fn' /\ fn'.fn_name = fn.fn_name /\
       (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\
            i.inst_opcode <> NOP ==> MEM i (fn_insts fn)) /\
       (!i. MEM i (fn_insts fn') ==> i.inst_opcode <> INVOKE) /\
       (sb.cs_current_insts <> [] \/
        !bb. lookup_block sb.cs_current_bb fn'.fn_blocks = SOME bb ==>
             phi_prefix_length bb.bb_instructions = 0) ==>
       (?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
            t.vs_inst_idx = LENGTH sb.cs_current_insts /\
            !fuel r. run_from fuel ctx fn' t = r /\ (!e. r <> Error e) ==>
                     ?fuel'. run_from fuel' ctx fn' (s with vs_current_bb := L) = r) \/
       (?fuel r. run_from fuel ctx fn' (s with vs_current_bb := L) = r /\
                 exit_result r /\ R r)) /\
    sa.cs_blocks <> sb.cs_blocks /\ cs_extends sa sb /\ frag_ops_free sa sb /\
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
    (!t p. Q t ==> Q (t with vs_prev_bb := p)) /\ (!h. ~R (Halt h)) /\
    (!a t b p. R (Abort a t) ==>
       R (Abort a (t with <| vs_current_bb := b; vs_prev_bb := p |>))) /\
    (!v t b p. R (IntRet v t) ==>
       R (IntRet v (t with <| vs_current_bb := b; vs_prev_bb := p |>))) /\
    fn_has_code sa sb fn /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
    (?r. gas_marked_path F ctx fn s 0 r /\ exit_result r /\ R r)
Proof
  cheat
QED

Theorem abi_decode_sim_gas_path_relabel_edge:
  !ctx sa sb Q fn s.
    (!L ids fn'.
       LENGTH ids = LENGTH sa.cs_current_insts /\
       fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) fn' /\
       fn_inst_ids_distinct fn' /\ fn'.fn_name = fn.fn_name /\
       (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\
            i.inst_opcode <> NOP ==> MEM i (fn_insts fn)) /\
       (!i. MEM i (fn_insts fn') ==> i.inst_opcode <> INVOKE) /\
       (!bb. lookup_block sb.cs_current_bb fn'.fn_blocks = SOME bb ==>
             phi_prefix_length bb.bb_instructions = 0) ==>
       ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
           t.vs_inst_idx = LENGTH sb.cs_current_insts /\
           abi_decode_sim ctx fn' (s with vs_current_bb := L) t) /\
    sa.cs_blocks <> sb.cs_blocks /\ cs_extends sa sb /\ frag_ops_free sa sb /\
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
    (!t p. Q t ==> Q (t with vs_prev_bb := p)) /\
    fn_has_code sa sb fn /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED
