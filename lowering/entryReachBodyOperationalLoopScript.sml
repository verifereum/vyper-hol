Theory entryReachBodyOperationalLoop
Ancestors
  entryReachBodyOperationalPath entryReachBodyExactArrayLoop entryReachBodyRegisteredChild
  abiDecoderExecution abiEncoderObserver abiEncoderRegisteredEffect
  abiEncoderPrimitiveEffect abiAllocationHistory allocaFrontierBound allocaBudgetProps
  localPtrsProps venomMemDefs venomMemProofs finite_map pred_set
  venomExecSemantics venomExecProofs venomInst venomState
  fragExec exprLoweringProps instIdxIndep words list rich_list arithmetic

Theorem loop_terminator_path[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\ is_terminator inst.inst_opcode /\
  step_inst 0 ctx inst s = OK t /\ ~s.vs_halted /\ ~t.vs_halted /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 /\ t.vs_inst_idx = 0 ==>
  entry_decode_path ctx fn s t
Proof
  strip_tac >> irule entry_decode_path_step >>
  qexists_tac `(s.vs_current_bb,SUC s.vs_inst_idx)` >>
  simp[abi_observer_step_def] >>
  qexists_tac `t` >> simp[] >>
  once_rewrite_tac[GSYM eval_phis_prefix] >> simp[eval_phis_def]
QED

Theorem loop_header_path[local]:
  abi_decode_loop_cfg fn hdr body_lbl exit id ip src CALLDATALOAD iv cv cmp done /\
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr n j s /\
  src <> Var iv /\ iv <> cv /\ n < dimword (:256) ==>
  entry_decode_path ctx fn s
    (jump_to (if j < n then body_lbl else exit)
      (abi_decode_header_state iv cv cmp done j n s))
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by
    simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
  `run_inst_seq (TAKE 4 (abi_decode_header_insts id ip src CALLDATALOAD
      iv cv cmp done body_lbl exit)) s =
    OK (abi_decode_header_state iv cv cmp done j n s)` by
    (irule abi_decode_header_prefix >> fs[abi_decode_loop_ready_def]) >>
  qmatch_goalsub_abbrev_tac `jump_to lbl h` >>
  `~h.vs_halted` by
    fs[Abbr `h`, abi_decode_header_state_def, update_var_def, abi_decode_loop_ready_def] >>
  `entry_decode_path ctx fn s (h with vs_inst_idx := 4)` by
    (drule_at (Pat `run_inst_seq _ _ = OK _`) entry_decode_sequence_path >>
     fs[abi_decode_loop_cfg_def, abi_decode_loop_ready_def, Abbr `h`,
       abi_decode_header_insts_def, mk_inst_def, is_terminator_def]) >>
  irule entry_decode_path_trans >> qexists_tac `h with vs_inst_idx := 4` >>
  simp[] >> irule loop_terminator_path >>
  simp[jump_to_def] >> conj_tac
  >- (fs[abi_decode_loop_cfg_def, Abbr `lbl`] >> Cases_on `j < n` >> metis_tac[]) >>
  qexistsl_tac [`<|bb_label := hdr; bb_instructions :=
       abi_decode_header_insts id ip src CALLDATALOAD iv cv cmp done body_lbl exit|>`,
     `mk_inst (id+4) JNZ [Var done;Label exit;Label body_lbl] []`] >>
  fs[abi_decode_loop_cfg_def, abi_decode_loop_ready_def, Abbr `h`, Abbr `lbl`,
     abi_decode_header_insts_def, get_instruction_def, mk_inst_def, is_terminator_def,
     jump_to_def, abi_decode_header_state_def, update_var_def] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def,
       eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       bool_to_word_def, jump_to_def] >>
  Cases_on `j < n` >> simp[]
QED

Theorem loop_backedge_path[local]:
  entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr n j s /\
  lookup_block hdr fn.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 /\
  ip <> Var nv /\ j < n /\ n < dimword (:256) ==>
  entry_decode_path ctx fn s
    (jump_to hdr (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)))
Proof
  strip_tac >>
  `run_inst_seq (TAKE 2 (abi_decode_backedge_insts bid iv nv ip hdr)) s =
    OK (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) s))` by
    (irule abi_decode_increment_prefix >> fs[entry_loop_child_end_def] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `jump_to hdr h` >>
  `~h.vs_halted /\ h.vs_current_bb = tail` by
    fs[Abbr `h`, mstore_def, write_memory_with_expansion_def, update_var_def,
       entry_loop_child_end_def] >>
  `entry_decode_path ctx fn s (h with vs_inst_idx := LENGTH prefix + 2)` by
    (drule_at (Pat `run_inst_seq _ _ = OK _`) entry_decode_sequence_path >>
     fs[entry_loop_child_end_def, Abbr `h`, abi_decode_backedge_insts_def,
       mk_inst_def, is_terminator_def, DROP_LENGTH_APPEND]) >>
  irule entry_decode_path_trans >>
  qexists_tac `h with vs_inst_idx := LENGTH prefix + 2` >> simp[] >>
  irule loop_terminator_path >> simp[jump_to_def] >>
  qpat_x_assum `entry_loop_child_end _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[entry_loop_child_end_def]) >>
  qexistsl_tac [`bb`, `mk_inst (bid+2) JMP [Label hdr] []`] >>
  fs[entry_loop_child_end_def, abi_decode_backedge_insts_def,
     get_instruction_def, listTheory.EL_APPEND_EQN, mk_inst_def, is_terminator_def] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def, jump_to_def]
QED

Theorem loop_header_effect[local]:
  abi_encoder_registered_effect ids outs s
    (jump_to lbl (abi_decode_header_state iv cv cmp done j n s))
Proof
  simp[abi_encoder_registered_effect_def, jump_to_def,
       abi_decode_header_state_def, update_var_def]
QED

Theorem loop_backedge_effect[local]:
  cid IN ids /\ FLOOKUP s.vs_allocas cid = SOME (p,32) ==>
  abi_encoder_registered_effect ids outs s
    (jump_to hdr (mstore p (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)))
Proof
  strip_tac >>
  `abi_encoder_registered_effect ids outs s (mstore p (n2w (SUC j)) s)` by
    (irule abi_encoder_registered_slot_store >> metis_tac[]) >>
  gvs[abi_encoder_registered_effect_def, jump_to_def, mstore_def,
      write_memory_with_expansion_def, update_var_def] >> metis_tac[]
QED

Definition entry_operational_loop_resources_def:
  entry_operational_loop_resources ctx fn site cid p oid d cap s <=>
    alloca_inv s /\ abi_alloca_history (fn_insts fn) s /\
    alloca_frontier_inv ctx fn site s /\
    FLOOKUP s.vs_allocas cid = SOME (p,32) /\
    FLOOKUP s.vs_allocas oid = SOME (d,cap)
End

Theorem loop_resources_frame[local]:
  entry_operational_loop_resources ctx fn site cid p oid d cap s /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  entry_operational_loop_resources ctx fn site cid p oid d cap t
Proof
  strip_tac >>
  `remaining_alloca_budget (fn_insts fn) t = remaining_alloca_budget (fn_insts fn) s` by
    (irule remaining_alloca_budget_domain_cong >> simp[]) >>
  fs[entry_operational_loop_resources_def, alloca_frontier_inv_def,
     abi_alloca_history_def, alloca_inv_def, allocas_non_overlapping_def,
     alloca_next_valid_def] >> metis_tac[]
QED

Theorem loop_header_resources[local]:
  entry_operational_loop_resources ctx fn site cid p oid d cap s ==>
  entry_operational_loop_resources ctx fn site cid p oid d cap
    (jump_to lbl (abi_decode_header_state iv cv cmp done j n s))
Proof
  strip_tac >> irule loop_resources_frame >> qexists_tac `s` >>
  simp[jump_to_def, abi_decode_header_state_def, update_var_def]
QED

Theorem loop_backedge_resources[local]:
  entry_operational_loop_resources ctx fn site cid p oid d cap s ==>
  entry_operational_loop_resources ctx fn site cid p oid d cap
    (jump_to hdr (mstore p (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)))
Proof
  strip_tac >> irule loop_resources_frame >> qexists_tac `s` >>
  simp[jump_to_def, mstore_def, write_memory_with_expansion_def, update_var_def]
QED

Theorem loop_child_effect_enlarge:
  abi_encoder_registered_effect child_ids
    [(d+32+j*type_memory_size tv,type_memory_size tv)] s t /\
  child_ids SUBSET ids /\ j < LENGTH xs ==>
  abi_encoder_registered_effect ids [(d,32+LENGTH xs*type_memory_size tv)] s t
Proof
  strip_tac >> irule abi_encoder_registered_effect_enlarge >>
  qexistsl_tac [`child_ids`, `[(d+32+j*type_memory_size tv,type_memory_size tv)]`] >>
  simp[] >> rpt strip_tac >>
  `SUC j * type_memory_size tv <= LENGTH xs * type_memory_size tv` by
    (irule LESS_MONO_MULT >> simp[]) >>
  qpat_x_assum `SUC j * _ <= _` mp_tac >>
  pure_rewrite_tac[MULT_CLAUSES] >> decide_tac
QED

Definition entry_operational_loop_callback_def:
  entry_operational_loop_callback ctx fn site body_lbl tail prefix bid iv nv ip hdr src
      p srcaddr tv xs d cap cid oid child_ids <=>
    !j u. j < LENGTH xs /\ ~u.vs_halted /\ u.vs_current_bb = body_lbl /\
      u.vs_inst_idx = 0 /\
      entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap u ==>
      ?t. entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr
            (LENGTH xs) j t /\
        entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap t /\
        val_in_memory tv (EL j xs) (d+32+j*type_memory_size tv) t.vs_memory /\
        entry_loop_fields u t /\ entry_decode_path ctx fn u t /\
        abi_encoder_registered_effect child_ids
          [(d+32+j*type_memory_size tv,type_memory_size tv)] u t
End

Theorem loop_callback_endpoint[local]:
  entry_operational_loop_callback ctx fn site body_lbl tail prefix bid iv nv ip hdr src
    p srcaddr tv xs d cap cid oid child_ids /\
  j < LENGTH xs /\ ~u.vs_halted /\ u.vs_current_bb = body_lbl /\ u.vs_inst_idx = 0 /\
  entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap u /\
  entry_loop_prefix tv xs d j u /\ EVERY (val_wf tv) xs /\
  32+j*type_memory_size tv <= cap /\ oid NOTIN child_ids /\ child_ids SUBSET ids ==>
  ?t. entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr
        (LENGTH xs) j t /\
    entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap t /\
    entry_loop_prefix tv xs d (SUC j) t /\ entry_loop_fields u t /\
    entry_decode_path ctx fn u t /\
    abi_encoder_registered_effect ids [(d,32+LENGTH xs*type_memory_size tv)] u t
Proof
  strip_tac >>
  `?t. entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr
      (LENGTH xs) j t /\
    entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap t /\
    val_in_memory tv (EL j xs) (d+32+j*type_memory_size tv) t.vs_memory /\
    entry_loop_fields u t /\ entry_decode_path ctx fn u t /\
    abi_encoder_registered_effect child_ids
      [(d+32+j*type_memory_size tv,type_memory_size tv)] u t` by
    (fs[entry_operational_loop_callback_def] >> metis_tac[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >> conj_tac
  >- (irule entry_registered_child_prefix_extend >>
      qpat_assum `abi_encoder_registered_effect _ _ _ _` (irule_at Any) >>
      fs[entry_operational_loop_resources_def] >> metis_tac[]) >>
  irule loop_child_effect_enlarge >> metis_tac[]
QED

Theorem loop_backedge_prefix[local]:
  entry_operational_loop_resources ctx fn site cid p oid d cap s /\
  entry_loop_prefix tv xs d j s /\ EVERY (val_wf tv) xs /\ j <= LENGTH xs /\
  32+j*type_memory_size tv <= cap /\ oid <> cid ==>
  entry_loop_prefix tv xs d j
    (jump_to hdr (mstore p (n2w (SUC i)) (update_var nv (n2w (SUC i)) s)))
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `entry_loop_prefix tv xs d j t` >>
  `entry_operational_loop_resources ctx fn site cid p oid d cap t` by
    (simp[Abbr `t`] >> irule loop_backedge_resources >> simp[]) >>
  `abi_encoder_registered_effect {cid}
    [(d+32+j*type_memory_size tv,type_memory_size tv)] s t` by
    (simp[Abbr `t`] >> irule loop_backedge_effect >>
     fs[entry_operational_loop_resources_def]) >>
  irule entry_registered_child_prefix >>
  qpat_assum `abi_encoder_registered_effect _ _ _ _` (irule_at Any) >>
  fs[entry_operational_loop_resources_def] >> metis_tac[]
QED

Definition entry_operational_loop_shell_def:
  entry_operational_loop_shell ctx fn site hdr body_lbl exit hid tail prefix bid
      ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid ids child_ids <=>
    abi_decode_loop_cfg fn hdr body_lbl exit hid ip src CALLDATALOAD iv cv cmp done /\
    src <> Var iv /\ iv <> cv /\ ip <> Var nv /\ src <> Var nv /\
    LENGTH xs < dimword (:256) /\ EVERY (val_wf tv) xs /\
    32+LENGTH xs*type_memory_size tv <= cap /\ oid <> cid /\
    cid IN ids /\ oid NOTIN child_ids /\ child_ids SUBSET ids /\
    entry_operational_loop_callback ctx fn site body_lbl tail prefix bid iv nv ip hdr src
      p srcaddr tv xs d cap cid oid child_ids
End

Theorem loop_shell_capacity[local]:
  entry_operational_loop_shell ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid ids child_ids /\
  j <= LENGTH xs ==> 32+j*type_memory_size tv <= cap
Proof
  strip_tac >>
  `j * type_memory_size tv <= LENGTH xs * type_memory_size tv` by
    (irule LESS_MONO_MULT >> simp[]) >>
  qhdtm_x_assum `entry_operational_loop_shell`
    (strip_assume_tac o REWRITE_RULE[entry_operational_loop_shell_def]) >>
  decide_tac
QED

Theorem entry_operational_loop_header_phase:
  abi_decode_loop_cfg fn hdr body_lbl exit hid ip src CALLDATALOAD iv cv cmp done /\
  src <> Var iv /\ iv <> cv /\ LENGTH xs < dimword (:256) /\
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) j s /\
  entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap s /\
  entry_loop_prefix tv xs d j s /\
  t = jump_to (if j < LENGTH xs then body_lbl else exit)
    (abi_decode_header_state iv cv cmp done j (LENGTH xs) s) ==>
  (~t.vs_halted /\ t.vs_current_bb = (if j < LENGTH xs then body_lbl else exit) /\
   t.vs_inst_idx = 0) /\
  entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap t /\
  entry_loop_prefix tv xs d j t /\ entry_loop_fields s t /\
  entry_decode_path ctx fn s t /\
  abi_encoder_registered_effect ids [(d,32+LENGTH xs*type_memory_size tv)] s t
Proof
  strip_tac >> gvs[] >> rpt conj_tac
  >- fs[abi_decode_loop_ready_def, jump_to_def, abi_decode_header_state_def, update_var_def]
  >- simp[jump_to_def]
  >- simp[jump_to_def]
  >- (irule loop_header_resources >> simp[])
  >- fs[entry_loop_prefix_def, jump_to_def, abi_decode_header_state_def, update_var_def]
  >- simp[entry_loop_fields_def, jump_to_def, abi_decode_header_state_def, update_var_def]
  >- (irule loop_header_path >> metis_tac[]) >>
  irule loop_header_effect
QED

Theorem loop_shell_header[local]:
  entry_operational_loop_shell ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid ids child_ids /\
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) j s /\
  entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap s /\
  entry_loop_prefix tv xs d j s /\
  t = jump_to (if j < LENGTH xs then body_lbl else exit)
    (abi_decode_header_state iv cv cmp done j (LENGTH xs) s) ==>
  (~t.vs_halted /\ t.vs_current_bb = (if j < LENGTH xs then body_lbl else exit) /\
   t.vs_inst_idx = 0) /\
  entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap t /\
  entry_loop_prefix tv xs d j t /\ entry_loop_fields s t /\
  entry_decode_path ctx fn s t /\
  abi_encoder_registered_effect ids [(d,32+LENGTH xs*type_memory_size tv)] s t
Proof
  strip_tac >> irule entry_operational_loop_header_phase >>
  fs[entry_operational_loop_shell_def] >> metis_tac[]
QED

Theorem entry_operational_loop_backedge_phase:
  abi_decode_loop_cfg fn hdr body_lbl exit hid ip src CALLDATALOAD iv cv cmp done /\
  ip <> Var nv /\ src <> Var nv /\ LENGTH xs < dimword (:256) /\
  EVERY (val_wf tv) xs /\ 32+LENGTH xs*type_memory_size tv <= cap /\
  oid <> cid /\ cid IN ids /\
  j < LENGTH xs /\
  entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr (LENGTH xs) j s /\
  entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap s /\
  entry_loop_prefix tv xs d (SUC j) s /\
  t = jump_to hdr (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)) ==>
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) (SUC j) t /\
  entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap t /\
  entry_loop_prefix tv xs d (SUC j) t /\ entry_loop_fields s t /\
  entry_decode_path ctx fn s t /\
  abi_encoder_registered_effect ids [(d,32+LENGTH xs*type_memory_size tv)] s t
Proof
  strip_tac >>
  `SUC j <= LENGTH xs` by decide_tac >>
  `32+SUC j*type_memory_size tv <= cap` by
    (`SUC j*type_memory_size tv <= LENGTH xs*type_memory_size tv` by
       (irule LESS_MONO_MULT >> simp[]) >> decide_tac) >>
  gvs[] >> conj_tac >- suspend "ready" >> conj_tac
  >- (irule loop_backedge_resources >> simp[]) >> conj_tac
  >- (irule loop_backedge_prefix >> fs[entry_operational_loop_shell_def] >> metis_tac[]) >>
  conj_tac
  >- simp[entry_loop_fields_def, jump_to_def, mstore_def,
          write_memory_with_expansion_def, update_var_def] >> conj_tac
  >- (irule loop_backedge_path >>
      fs[entry_operational_loop_shell_def, abi_decode_loop_cfg_def] >>
      simp[abi_decode_header_insts_def, phi_prefix_length_def, mk_inst_def] >>
      qhdtm_assum `entry_loop_child_end` (irule_at Any) >> simp[] >> decide_tac) >>
  irule loop_backedge_effect >> fs[entry_operational_loop_shell_def,
    entry_operational_loop_resources_def] >> metis_tac[]
QED

Resume entry_operational_loop_backedge_phase[ready]:
  fs[entry_operational_loop_shell_def, entry_loop_child_end_def] >>
  simp[abi_decode_loop_ready_def, abi_decode_mload_jump,
    mload_mstore_same_proof, abiDecoderContractTheory.abi_decode_load_def,
    abiDecoderContractTheory.abi_decode_source_def,
    jump_to_def, update_var_def, mstore_def, write_memory_with_expansion_def] >>
  conj_tac >- (Cases_on `ip` >> gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  Cases_on `src` >> gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
    abiDecoderContractTheory.abi_decode_load_def, abiDecoderContractTheory.abi_decode_source_def]
QED

Finalise entry_operational_loop_backedge_phase

Theorem loop_shell_backedge[local]:
  entry_operational_loop_shell ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid ids child_ids /\
  j < LENGTH xs /\
  entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr (LENGTH xs) j s /\
  entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap s /\
  entry_loop_prefix tv xs d (SUC j) s /\
  t = jump_to hdr (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)) ==>
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) (SUC j) t /\
  entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap t /\
  entry_loop_prefix tv xs d (SUC j) t /\ entry_loop_fields s t /\
  entry_decode_path ctx fn s t /\
  abi_encoder_registered_effect ids [(d,32+LENGTH xs*type_memory_size tv)] s t
Proof
  strip_tac >> irule entry_operational_loop_backedge_phase >>
  fs[entry_operational_loop_shell_def] >> metis_tac[]
QED

Definition entry_loop_trace_def:
  entry_loop_trace ctx fn ids outs s t <=>
    entry_loop_fields s t /\ entry_decode_path ctx fn s t /\
    abi_encoder_registered_effect ids outs s t
End

Theorem loop_trace_refl:
  entry_loop_trace ctx fn ids outs s s
Proof
  simp[entry_loop_trace_def, entry_loop_fields_def,
       entry_decode_path_refl, abi_encoder_registered_effect_refl]
QED

Theorem loop_trace_trans:
  entry_loop_trace ctx fn ids outs s t /\ entry_loop_trace ctx fn ids outs t u ==>
  entry_loop_trace ctx fn ids outs s u
Proof
  simp_tac bool_ss [entry_loop_trace_def] >> strip_tac >>
  metis_tac[entry_registered_fields_trans, entry_decode_path_trans,
            abi_encoder_registered_effect_trans]
QED

Definition entry_operational_loop_inv_def:
  entry_operational_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid j s <=>
    abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) j s /\
    entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap s /\
    entry_loop_prefix tv xs d j s
End

Theorem loop_shell_round[local]:
  entry_operational_loop_shell ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid ids child_ids /\
  entry_operational_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid j s /\
  j < LENGTH xs ==>
  ?v. entry_operational_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid (SUC j) v /\
    entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s v
Proof
  strip_tac >>
  fs[entry_operational_loop_inv_def] >>
  qabbrev_tac `h = jump_to (if j < LENGTH xs then body_lbl else exit)
    (abi_decode_header_state iv cv cmp done j (LENGTH xs) s)` >>
  `(~h.vs_halted /\ h.vs_current_bb = (if j < LENGTH xs then body_lbl else exit) /\ h.vs_inst_idx = 0) /\
   entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap h /\
   entry_loop_prefix tv xs d j h /\
   entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s h` by
    (simp_tac bool_ss [entry_loop_trace_def] >>
     irule loop_shell_header >> simp[Abbr `h`] >> metis_tac[]) >>
  `j <= LENGTH xs` by decide_tac >>
  `32+j*type_memory_size tv <= cap` by (irule loop_shell_capacity >> metis_tac[]) >>
  `?t. entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr (LENGTH xs) j t /\
    entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap t /\
    entry_loop_prefix tv xs d (SUC j) t /\
    entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] h t` by
    (simp_tac bool_ss [entry_loop_trace_def] >> irule loop_callback_endpoint >>
     fs[entry_operational_loop_shell_def] >> metis_tac[]) >>
  qabbrev_tac `v = jump_to hdr
    (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) t))` >>
  `entry_operational_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid (SUC j) v /\
   entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] t v` by
    (simp_tac bool_ss [entry_operational_loop_inv_def, entry_loop_trace_def,
       GSYM CONJ_ASSOC] >>
     irule loop_shell_backedge >> simp[Abbr `v`] >> metis_tac[]) >>
  qexists_tac `v` >> conj_tac >- fs[entry_operational_loop_inv_def] >>
  irule loop_trace_trans >> qexists_tac `t` >> reverse conj_tac
  >- fs[ADD_COMM] >>
  irule loop_trace_trans >> qexists_tac `h` >> fs[ADD_COMM]
QED

Theorem loop_shell_exit[local]:
  entry_operational_loop_shell ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid ids child_ids /\
  entry_operational_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid (LENGTH xs) s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
    entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap t /\
    entry_loop_prefix tv xs d (LENGTH xs) t /\
    entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s t
Proof
  strip_tac >>
  qexists_tac `jump_to exit
    (abi_decode_header_state iv cv cmp done (LENGTH xs) (LENGTH xs) s)` >>
  simp_tac bool_ss [entry_loop_trace_def] >>
  irule (SRULE [GSYM CONJ_ASSOC] (Q.INST [`j` |-> `LENGTH xs`] loop_shell_header)) >>
  fs[entry_operational_loop_inv_def] >> metis_tac[]
QED

Theorem loop_trace_sim:
  entry_loop_trace ctx fn ids outs s t ==> abi_decode_sim ctx fn s t
Proof
  simp_tac bool_ss [entry_loop_trace_def] >> strip_tac >>
  irule entry_decode_path_sim >> asm_rewrite_tac[]
QED

Theorem entry_operational_array_loop_from_index:
  entry_operational_loop_shell ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid ids child_ids /\
  entry_operational_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid j s ==>
  ?t. (~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
    entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap t /\
    entry_loop_prefix tv xs d (LENGTH xs) t /\
    entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s t) /\
    abi_decode_sim ctx fn s t
Proof
  strip_tac >>
  qabbrev_tac `loopinv = \k u.
    entry_operational_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid k u /\
    entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s u` >>
  `!k u. loopinv k u /\ k < LENGTH xs ==>
    ?v. loopinv (SUC k) v /\ abi_decode_sim ctx fn u v` by
    (simp_tac bool_ss [Abbr `loopinv`] >> rpt strip_tac >>
     drule_all loop_shell_round >> disch_then (qx_choose_then `v` strip_assume_tac) >>
     qexists_tac `v` >> asm_rewrite_tac[] >> conj_tac
     >- (irule loop_trace_trans >> qexists_tac `u` >> asm_rewrite_tac[]) >>
     irule loop_trace_sim >> goal_assum (drule_at Any)) >>
  `!u. loopinv (LENGTH xs) u ==>
    ?t. (~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
      entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap t /\
      entry_loop_prefix tv xs d (LENGTH xs) t /\
      entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s t) /\
      abi_decode_sim ctx fn u t` by
    (simp_tac bool_ss [Abbr `loopinv`] >> rpt strip_tac >>
     drule_all loop_shell_exit >> disch_then (qx_choose_then `t` strip_assume_tac) >>
     qexists_tac `t` >> asm_rewrite_tac[] >> conj_tac
     >- (irule loop_trace_trans >> qexists_tac `u` >> asm_rewrite_tac[]) >>
     irule loop_trace_sim >> goal_assum (drule_at Any)) >>
  ho_match_mp_tac abiDecoderLoopTheory.abi_decode_finite_iteration >>
  qexistsl_tac [`LENGTH xs`, `j`, `loopinv`] >>
  simp[Abbr `loopinv`, loop_trace_refl] >>
  fs[entry_operational_loop_inv_def, abi_decode_loop_ready_def]
QED

(* The allocating initializer's raw endpoint is not yet at the header.  Its
   operational certificate uses this PC-adjusted endpoint.  This handoff
   consumes exactly its allocation/history/frontier and registered-effect
   outputs, plus the pre-existing destination ownership. *)
Theorem entry_operational_loop_initializer_resources:
  abi_alloca_history (fn_insts fn) t /\ alloca_inv t /\
  alloca_frontier_inv ctx fn site t /\ FLOOKUP t.vs_allocas cid = SOME (p,32) /\
  FLOOKUP initial.vs_allocas oid = SOME (d,cap) /\
  abi_encoder_registered_effect {cid} [(d,32)] initial t /\ cid IN ids ==>
  entry_operational_loop_resources ctx fn site cid p oid d cap
    (t with vs_inst_idx := ix) /\
  entry_loop_prefix tv xs d 0 (t with vs_inst_idx := ix) /\
  abi_encoder_registered_effect ids [(d,32+LENGTH xs*type_memory_size tv)]
    initial (t with vs_inst_idx := ix)
Proof
  strip_tac >>
  `FLOOKUP t.vs_allocas oid = SOME (d,cap)` by
    (irule abi_encoder_registered_effect_allocated >> goal_assum (drule_at Any) >> simp[]) >>
  `entry_operational_loop_resources ctx fn site cid p oid d cap t` by
    simp[entry_operational_loop_resources_def] >>
  conj_tac >- (irule loop_resources_frame >> qexists_tac `t` >> simp[]) >>
  conj_tac >- simp[entry_loop_prefix_def] >>
  `abi_encoder_registered_effect ids [(d,32+LENGTH xs*type_memory_size tv)] initial t` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`{cid}`, `[(d,32)]`] >> simp[] >> rpt strip_tac >> decide_tac) >>
  irule abi_encoder_registered_effect_trans >> qexists_tac `t` >> asm_rewrite_tac[] >>
  irule abi_encoder_registered_inst_idx
QED

(* The recursive child obligation is entry_operational_loop_callback_def:
   a SINGLE endpoint with the exact kth value, unchanged observable fields,
   an actual operational path and registered effect, PLUS alloca_inv,
   instruction-justified history, frontier credit, and both persistent
   ownership entries.  Its allocation IDs may be reused by later children;
   no completed-prefix preservation is assumed in that callback. *)
