(* Indexed decoder loops with an allocation owner distinct from the
   decoded destination.  All execution witnesses remain common endpoints. *)
Theory entryReachBodyOwnedLoop
Ancestors
  entryReachBodyOwnedRegion entryReachBodyIndexedLoopInput
  entryReachBodyExactArrayLoop valueEncodingProps
  entryReachBodyOperationalLoop entryReachBodyOperationalPath
  abiAllocationHistory allocaFrontierBound allocaBudgetProps
  abiDecoderLoop abiDecoderExecution abiDecoderContract
  abiEncoderRegisteredEffect venomMemDefs venomExecSemantics venomState
  localPtrsProps finite_map words list arithmetic pred_set rich_list
  abiEncoderObserver abiEncoderPrimitiveEffect venomExecProofs venomInst
  venomMemProofs fragExec instIdxIndep exprLoweringProps

Definition entry_owned_loop_resources_def:
  entry_owned_loop_resources ctx fn site cid p oid root extent d cap s <=>
    alloca_inv s /\ abi_alloca_history (fn_insts fn) s /\
    alloca_frontier_inv ctx fn site s /\
    FLOOKUP s.vs_allocas cid = SOME (p,32) /\
    entry_owned_region oid root extent d cap s
End

Definition entry_owned_loop_inv_def:
  entry_owned_loop_inv ctx fn site hdr ip src p srcaddr tv xs
      d cap cid oid root extent j s <=>
    abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) j s /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap s /\
    entry_loop_prefix tv xs d j s
End

Theorem owned_resources_frame[local]:
  entry_owned_loop_resources ctx fn site cid p oid root extent d cap s /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  entry_owned_loop_resources ctx fn site cid p oid root extent d cap t
Proof
  strip_tac >>
  `remaining_alloca_budget (fn_insts fn) t = remaining_alloca_budget (fn_insts fn) s` by
    (irule remaining_alloca_budget_domain_cong >> simp[]) >>
  fs[entry_owned_loop_resources_def, entry_owned_region_def,
     alloca_frontier_inv_def, abi_alloca_history_def, alloca_inv_def,
     allocas_non_overlapping_def, alloca_next_valid_def] >> metis_tac[]
QED

Theorem owned_header_resources[local]:
  entry_owned_loop_resources ctx fn site cid p oid root extent d cap s ==>
  entry_owned_loop_resources ctx fn site cid p oid root extent d cap
    (jump_to lbl (abi_decode_header_state iv cv cmp done j n s))
Proof
  strip_tac >> irule owned_resources_frame >> qexists_tac `s` >>
  simp[jump_to_def, abi_decode_header_state_def, update_var_def]
QED

Theorem owned_backedge_resources[local]:
  entry_owned_loop_resources ctx fn site cid p oid root extent d cap s ==>
  entry_owned_loop_resources ctx fn site cid p oid root extent d cap
    (jump_to hdr (mstore p (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)))
Proof
  strip_tac >> irule owned_resources_frame >> qexists_tac `s` >>
  simp[jump_to_def, mstore_def, write_memory_with_expansion_def, update_var_def]
QED

Theorem owned_backedge_prefix[local]:
  entry_owned_loop_resources ctx fn site cid p oid root extent d cap s /\
  oid <> cid /\ 32+j*type_memory_size tv <= cap /\ j <= LENGTH xs /\
  EVERY (val_wf tv) xs /\ entry_loop_prefix tv xs d j s ==>
  entry_loop_prefix tv xs d j
    (jump_to hdr (mstore p w (update_var nv v s)))
Proof
  strip_tac >>
  `d+cap <= p \/ p+32 <= d` by
    (fs[entry_owned_loop_resources_def] >>
     drule entry_owned_region_counter_separation >>
     disch_then (qspecl_then [`p`,`cid`] mp_tac) >> simp[] >> metis_tac[]) >>
  simp_tac bool_ss [entry_loop_prefix_def] >> rpt strip_tac >>
  `val_wf tv (EL k xs)` by
    (fs[EVERY_EL] >> first_x_assum irule >> decide_tac) >>
  `val_in_memory tv (EL k xs) (d+32+k*type_memory_size tv) s.vs_memory` by
    fs[entry_loop_prefix_def] >>
  `SUC k*type_memory_size tv <= j*type_memory_size tv` by
    (irule LESS_MONO_MULT >> simp[]) >>
  qpat_x_assum `SUC k * _ <= _`
    (assume_tac o PURE_REWRITE_RULE [MULT_CLAUSES]) >>
  `p+32 <= d+32+k*type_memory_size tv \/
    d+32+k*type_memory_size tv+type_memory_size tv <= p` by decide_tac >>
  `val_in_memory tv (EL k xs) (d+32+k*type_memory_size tv)
    (mstore p w (s with vs_memory := s.vs_memory)).vs_memory` by
    (irule (cj 1 mstore_preserves_val_in_memory) >> simp[]) >>
  gvs[jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def]
QED

Definition entry_owned_indexed_contract_def:
  entry_owned_indexed_contract ctx fn site hdr body_lbl exit hid tail prefix bid
      ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid root extent
      ids child_ids kin B E Q <=>
    abi_decode_loop_cfg fn hdr body_lbl exit hid ip src CALLDATALOAD iv cv cmp done /\
    src <> Var iv /\ iv <> cv /\ ip <> Var nv /\ src <> Var nv /\
    LENGTH xs < dimword (:256) /\ EVERY (val_wf tv) xs /\
    32+LENGTH xs*type_memory_size tv <= cap /\ oid <> cid /\
    cid IN ids /\ oid NOTIN child_ids /\ child_ids SUBSET ids /\
    (!j s. kin j s /\
       entry_owned_loop_inv ctx fn site hdr ip src p srcaddr tv xs
         d cap cid oid root extent j s ==>
       if j < LENGTH xs then
         B j (jump_to body_lbl (abi_decode_header_state iv cv cmp done j (LENGTH xs) s))
       else Q (jump_to exit (abi_decode_header_state iv cv cmp done j (LENGTH xs) s))) /\
    (!j u. B j u /\ j < LENGTH xs /\ ~u.vs_halted /\
       u.vs_current_bb = body_lbl /\ u.vs_inst_idx = 0 /\
       entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap u ==>
       ?t. E j t /\
         entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr (LENGTH xs) j t /\
         entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap t /\
         val_in_memory tv (EL j xs) (d+32+j*type_memory_size tv) t.vs_memory /\
         entry_loop_fields u t /\ entry_decode_path ctx fn u t /\
         abi_encoder_registered_effect child_ids
           [(d+32+j*type_memory_size tv,type_memory_size tv)] u t) /\
    (!j t. E j t /\ j < LENGTH xs /\
       entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr (LENGTH xs) j t /\
       entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap t ==>
       kin (SUC j) (jump_to hdr
         (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) t))))
End

Theorem owned_child_boundary[local]:
  entry_owned_indexed_contract ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid root extent
    ids child_ids kin B E Q /\
  B j u /\ j < LENGTH xs /\ ~u.vs_halted /\ u.vs_current_bb = body_lbl /\
  u.vs_inst_idx = 0 /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap u /\
  entry_loop_prefix tv xs d j u ==>
  ?t. E j t /\
    entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr (LENGTH xs) j t /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap t /\
    entry_loop_prefix tv xs d (SUC j) t /\
    entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] u t
Proof
  strip_tac >> fs[entry_owned_indexed_contract_def] >>
  qpat_x_assum `!j u. B j u /\ _ ==> _` drule_all >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  `32+j*type_memory_size tv <= cap` by
    (`j*type_memory_size tv <= LENGTH xs*type_memory_size tv` by
       (irule LESS_MONO_MULT >> simp[]) >> decide_tac) >>
  `entry_loop_prefix tv xs d (SUC j) t` by
    (irule entry_owned_child_prefix_extend >> simp[] >>
     qpat_assum `abi_encoder_registered_effect _ _ _ _` (irule_at Any) >>
     fs[entry_owned_loop_resources_def] >> metis_tac[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  simp_tac bool_ss [entry_loop_trace_def] >> asm_rewrite_tac[] >>
  once_rewrite_tac[ADD_COMM] >> irule loop_child_effect_enlarge >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED

(* Control-flow recipes are local in OperationalLoop; ownership is irrelevant
   to these instruction-level paths. *)
Theorem owned_terminator_path[local]:
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
  simp[abi_observer_step_def] >> qexists_tac `t` >> simp[] >>
  once_rewrite_tac[GSYM eval_phis_prefix] >> simp[eval_phis_def]
QED

Theorem owned_header_path[local]:
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
  simp[] >> irule owned_terminator_path >> simp[jump_to_def] >> conj_tac
  >- (fs[abi_decode_loop_cfg_def, Abbr `lbl`] >> Cases_on `j < n` >> metis_tac[]) >>
  qexistsl_tac [`<|bb_label := hdr; bb_instructions :=
       abi_decode_header_insts id ip src CALLDATALOAD iv cv cmp done body_lbl exit|>`,
     `mk_inst (id+4) JNZ [Var done;Label exit;Label body_lbl] []`] >>
  fs[abi_decode_loop_cfg_def, abi_decode_loop_ready_def, Abbr `h`, Abbr `lbl`,
     abi_decode_header_insts_def, get_instruction_def, mk_inst_def, is_terminator_def,
     jump_to_def, abi_decode_header_state_def, update_var_def] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
       bool_to_word_def, jump_to_def] >>
  Cases_on `j < n` >> simp[]
QED

Theorem owned_backedge_path[local]:
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
  irule owned_terminator_path >> simp[jump_to_def] >>
  qpat_x_assum `entry_loop_child_end _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[entry_loop_child_end_def]) >>
  qexistsl_tac [`bb`, `mk_inst (bid+2) JMP [Label hdr] []`] >>
  fs[entry_loop_child_end_def, abi_decode_backedge_insts_def,
     get_instruction_def, EL_APPEND_EQN, mk_inst_def, is_terminator_def] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def, jump_to_def]
QED

Theorem owned_header_effect[local]:
  abi_encoder_registered_effect ids outs s
    (jump_to lbl (abi_decode_header_state iv cv cmp done j n s))
Proof
  simp[abi_encoder_registered_effect_def, jump_to_def,
       abi_decode_header_state_def, update_var_def]
QED

Theorem owned_backedge_effect[local]:
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

Theorem owned_header_phase:
  abi_decode_loop_cfg fn hdr body_lbl exit hid ip src CALLDATALOAD iv cv cmp done /\
  src <> Var iv /\ iv <> cv /\ LENGTH xs < dimword (:256) /\
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) j s /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap s /\
  entry_loop_prefix tv xs d j s /\
  t = jump_to (if j < LENGTH xs then body_lbl else exit)
    (abi_decode_header_state iv cv cmp done j (LENGTH xs) s) ==>
  (~t.vs_halted /\ t.vs_current_bb = (if j < LENGTH xs then body_lbl else exit) /\
   t.vs_inst_idx = 0) /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap t /\
  entry_loop_prefix tv xs d j t /\ entry_loop_fields s t /\
  entry_decode_path ctx fn s t /\
  abi_encoder_registered_effect ids [(d,32+LENGTH xs*type_memory_size tv)] s t
Proof
  strip_tac >> gvs[] >> rpt conj_tac
  >- fs[abi_decode_loop_ready_def, jump_to_def, abi_decode_header_state_def, update_var_def]
  >- simp[jump_to_def]
  >- simp[jump_to_def]
  >- (irule owned_header_resources >> simp[])
  >- fs[entry_loop_prefix_def, jump_to_def, abi_decode_header_state_def, update_var_def]
  >- simp[entry_loop_fields_def, jump_to_def, abi_decode_header_state_def, update_var_def]
  >- (irule owned_header_path >> metis_tac[]) >>
  irule owned_header_effect
QED

Theorem owned_backedge_phase:
  abi_decode_loop_cfg fn hdr body_lbl exit hid ip src CALLDATALOAD hiv cv cmp done /\
  ip <> Var nv /\ src <> Var nv /\ LENGTH xs < dimword (:256) /\
  EVERY (val_wf tv) xs /\ 32+LENGTH xs*type_memory_size tv <= cap /\
  oid <> cid /\ cid IN ids /\ j < LENGTH xs /\
  entry_loop_child_end fn tail prefix bid biv nv ip hdr src p srcaddr (LENGTH xs) j s /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap s /\
  entry_loop_prefix tv xs d (SUC j) s /\
  t = jump_to hdr (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)) ==>
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) (SUC j) t /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap t /\
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
  >- (irule owned_backedge_resources >> simp[]) >> conj_tac
  >- (irule owned_backedge_prefix >> simp[] >>
      qpat_assum `entry_owned_loop_resources _ _ _ _ _ _ _ _ _ _ _`
        (irule_at Any) >> simp[]) >> conj_tac
  >- simp[entry_loop_fields_def, jump_to_def, mstore_def,
          write_memory_with_expansion_def, update_var_def] >> conj_tac
  >- (irule owned_backedge_path >>
      fs[abi_decode_loop_cfg_def] >>
      simp[abi_decode_header_insts_def, phi_prefix_length_def, mk_inst_def] >>
      qhdtm_assum `entry_loop_child_end` (irule_at Any) >> simp[] >> decide_tac) >>
  irule owned_backedge_effect >> fs[entry_owned_loop_resources_def] >> metis_tac[]
QED

Resume owned_backedge_phase[ready]:
  fs[entry_loop_child_end_def] >>
  simp[abi_decode_loop_ready_def, abi_decode_mload_jump,
    mload_mstore_same_proof, abiDecoderContractTheory.abi_decode_load_def,
    abiDecoderContractTheory.abi_decode_source_def,
    jump_to_def, update_var_def, mstore_def, write_memory_with_expansion_def] >>
  conj_tac >- (Cases_on `ip` >> gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  Cases_on `src` >> gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
    abiDecoderContractTheory.abi_decode_load_def, abiDecoderContractTheory.abi_decode_source_def]
QED

Finalise owned_backedge_phase

Theorem owned_header_boundary[local]:
  entry_owned_indexed_contract ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid root extent ids child_ids kin B E Q /\
  entry_owned_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid root extent j s /\
  kin j s /\
  t = jump_to (if j < LENGTH xs then body_lbl else exit)
    (abi_decode_header_state iv cv cmp done j (LENGTH xs) s) ==>
  (~t.vs_halted /\ t.vs_current_bb = (if j < LENGTH xs then body_lbl else exit) /\
    t.vs_inst_idx = 0) /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap t /\
  entry_loop_prefix tv xs d j t /\
  entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s t /\
  (if j < LENGTH xs then B j t else Q t)
Proof
  strip_tac >>
  `if j < LENGTH xs then B j t else Q t` by
    (fs[entry_owned_indexed_contract_def] >>
     first_x_assum drule >> simp[] >> Cases_on `j < LENGTH xs` >> gvs[]) >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[entry_loop_trace_def, GSYM CONJ_ASSOC] >>
  irule (SRULE [GSYM CONJ_ASSOC] owned_header_phase) >>
  fs[entry_owned_indexed_contract_def, entry_owned_loop_inv_def] >> metis_tac[]
QED

Theorem owned_backedge_boundary[local]:
  entry_owned_indexed_contract ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid root extent ids child_ids kin B E Q /\
  E j s /\ j < LENGTH xs /\
  entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr (LENGTH xs) j s /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap s /\
  entry_loop_prefix tv xs d (SUC j) s /\
  t = jump_to hdr (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)) ==>
  entry_owned_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid root extent (SUC j) t /\
  entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s t /\ kin (SUC j) t
Proof
  strip_tac >>
  `kin (SUC j) t` by
    (fs[entry_owned_indexed_contract_def] >>
     qpat_x_assum `!j t. E j t /\ _ ==> _` drule_all >> simp[]) >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[entry_owned_loop_inv_def, entry_loop_trace_def, GSYM CONJ_ASSOC] >>
  irule (SRULE [GSYM CONJ_ASSOC] owned_backedge_phase) >>
  fs[entry_owned_indexed_contract_def] >> metis_tac[]
QED

Theorem owned_loop_round[local]:
  entry_owned_indexed_contract ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid root extent ids child_ids kin B E Q /\
  entry_owned_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid root extent j s /\
  kin j s /\ j < LENGTH xs ==>
  ?v. entry_owned_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid root extent (SUC j) v /\
    kin (SUC j) v /\ entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s v
Proof
  strip_tac >>
  qabbrev_tac `h = jump_to (if j < LENGTH xs then body_lbl else exit)
    (abi_decode_header_state iv cv cmp done j (LENGTH xs) s)` >>
  `(~h.vs_halted /\ h.vs_current_bb = body_lbl /\ h.vs_inst_idx = 0) /\
   entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap h /\
   entry_loop_prefix tv xs d j h /\
   entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s h /\ B j h` by
    (`h = jump_to (if j < LENGTH xs then body_lbl else exit)
        (abi_decode_header_state iv cv cmp done j (LENGTH xs) s)` by simp[Abbr `h`] >>
     drule_all owned_header_boundary >> simp[Abbr `h`]) >>
  drule_all owned_child_boundary >> disch_then (qx_choose_then `t` strip_assume_tac) >>
  qabbrev_tac `v = jump_to hdr
    (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) t))` >>
  `entry_owned_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid root extent (SUC j) v /\
   entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] t v /\ kin (SUC j) v` by
    (`v = jump_to hdr
        (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) t))` by simp[Abbr `v`] >>
     drule_all owned_backedge_boundary >> simp[Abbr `v`]) >>
  qexists_tac `v` >> asm_rewrite_tac[] >>
  irule loop_trace_trans >> qexists_tac `t` >> reverse conj_tac
  >- fs[ADD_COMM] >>
  irule loop_trace_trans >> qexists_tac `h` >> fs[ADD_COMM]
QED

Theorem owned_loop_exit[local]:
  entry_owned_indexed_contract ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid root extent ids child_ids kin B E Q /\
  entry_owned_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid root extent (LENGTH xs) s /\
  kin (LENGTH xs) s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap t /\
    entry_loop_prefix tv xs d (LENGTH xs) t /\
    entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s t /\ Q t
Proof
  strip_tac >>
  qabbrev_tac `t = jump_to exit
    (abi_decode_header_state iv cv cmp done (LENGTH xs) (LENGTH xs) s)` >>
  `t = jump_to (if LENGTH xs < LENGTH xs then body_lbl else exit)
    (abi_decode_header_state iv cv cmp done (LENGTH xs) (LENGTH xs) s)` by simp[Abbr `t`] >>
  drule_all owned_header_boundary >>
  simp_tac (srw_ss()) [NoAsms] >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem entry_owned_indexed_array_loop_from_index:
  entry_owned_indexed_contract ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid root extent ids child_ids kin B E Q /\
  entry_owned_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid root extent j s /\
  kin j s ==>
  ?t. (~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap t /\
    entry_loop_prefix tv xs d (LENGTH xs) t /\
    entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s t /\ Q t) /\
    abi_decode_sim ctx fn s t
Proof
  strip_tac >>
  qabbrev_tac `loopinv = \k u.
    entry_owned_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid root extent k u /\
    kin k u /\ entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s u` >>
  `!k u. loopinv k u /\ k < LENGTH xs ==>
    ?v. loopinv (SUC k) v /\ abi_decode_sim ctx fn u v` by
    (simp_tac bool_ss [Abbr `loopinv`] >> rpt strip_tac >>
     drule_all owned_loop_round >> disch_then (qx_choose_then `v` strip_assume_tac) >>
     qexists_tac `v` >> asm_rewrite_tac[] >> conj_tac
     >- (irule loop_trace_trans >> qexists_tac `u` >> asm_rewrite_tac[]) >>
     irule loop_trace_sim >> goal_assum (drule_at Any)) >>
  `!u. loopinv (LENGTH xs) u ==>
    ?t. (~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
      entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap t /\
      entry_loop_prefix tv xs d (LENGTH xs) t /\
      entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s t /\ Q t) /\
      abi_decode_sim ctx fn u t` by
    (simp_tac bool_ss [Abbr `loopinv`] >> rpt strip_tac >>
     drule_all owned_loop_exit >> disch_then (qx_choose_then `t` strip_assume_tac) >>
     qexists_tac `t` >> asm_rewrite_tac[] >> conj_tac
     >- (irule loop_trace_trans >> qexists_tac `u` >> asm_rewrite_tac[]) >>
     irule loop_trace_sim >> goal_assum (drule_at Any)) >>
  ho_match_mp_tac abi_decode_finite_iteration >>
  qexistsl_tac [`LENGTH xs`, `j`, `loopinv`] >>
  simp[Abbr `loopinv`, loop_trace_refl] >>
  fs[entry_owned_loop_inv_def, abi_decode_loop_ready_def]
QED
