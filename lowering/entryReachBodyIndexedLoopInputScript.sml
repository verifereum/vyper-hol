(* Phase-indexed semantic inputs for the operational array loop.
   kin, B, E and Q describe data at header, body, child end and exit;
   they do not assert an execution exists. *)
Theory entryReachBodyIndexedLoopInput
Ancestors
  valueEncodingDefs entryReachBodyOperationalLoop entryReachBodyOperationalHeader
  entryReachBodyRegisteredChild entryReachBodyExactArrayLoop abiDecoderLoop
  abiDecoderExecution abiDecoderContract abiEncoderRegisteredEffect
  venomExecSemantics venomState words list arithmetic pred_set

Definition entry_indexed_loop_contract_def:
  entry_indexed_loop_contract ctx fn site hdr body_lbl exit hid tail prefix bid
      ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid ids child_ids kin B E Q <=>
    abi_decode_loop_cfg fn hdr body_lbl exit hid ip src CALLDATALOAD iv cv cmp done /\
    src <> Var iv /\ iv <> cv /\ ip <> Var nv /\ src <> Var nv /\
    LENGTH xs < dimword (:256) /\ EVERY (val_wf tv) xs /\
    32+LENGTH xs*type_memory_size tv <= cap /\ oid <> cid /\
    cid IN ids /\ oid NOTIN child_ids /\ child_ids SUBSET ids /\
    (!j s. kin j s /\
       entry_operational_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid j s ==>
       if j < LENGTH xs then
         B j (jump_to body_lbl (abi_decode_header_state iv cv cmp done j (LENGTH xs) s))
       else Q (jump_to exit (abi_decode_header_state iv cv cmp done j (LENGTH xs) s))) /\
    (!j u. B j u /\ j < LENGTH xs /\ ~u.vs_halted /\
       u.vs_current_bb = body_lbl /\ u.vs_inst_idx = 0 /\
       entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap u ==>
       ?t. E j t /\
         entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr (LENGTH xs) j t /\
         entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap t /\
         val_in_memory tv (EL j xs) (d+32+j*type_memory_size tv) t.vs_memory /\
         entry_loop_fields u t /\ entry_decode_path ctx fn u t /\
         abi_encoder_registered_effect child_ids
           [(d+32+j*type_memory_size tv,type_memory_size tv)] u t) /\
    (!j t. E j t /\ j < LENGTH xs /\
       entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr (LENGTH xs) j t /\
       entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap t ==>
       kin (SUC j) (jump_to hdr
         (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) t))))
End

Theorem indexed_header_boundary[local]:
  entry_indexed_loop_contract ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid ids child_ids kin B E Q /\
  entry_operational_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid j s /\
  kin j s /\
  t = jump_to (if j < LENGTH xs then body_lbl else exit)
    (abi_decode_header_state iv cv cmp done j (LENGTH xs) s) ==>
  (~t.vs_halted /\ t.vs_current_bb = (if j < LENGTH xs then body_lbl else exit) /\
    t.vs_inst_idx = 0) /\
  entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap t /\
  entry_loop_prefix tv xs d j t /\
  entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s t /\
  (if j < LENGTH xs then B j t else Q t)
Proof
  strip_tac >>
  `if j < LENGTH xs then B j t else Q t` by
    (fs[entry_indexed_loop_contract_def] >>
     first_x_assum drule >> simp[] >> Cases_on `j < LENGTH xs` >> gvs[]) >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[entry_loop_trace_def, GSYM CONJ_ASSOC] >>
  irule (SRULE [GSYM CONJ_ASSOC] entry_operational_loop_header_phase) >>
  fs[entry_indexed_loop_contract_def, entry_operational_loop_inv_def] >> metis_tac[]
QED

Theorem indexed_child_boundary[local]:
  entry_indexed_loop_contract ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid ids child_ids kin B E Q /\
  B j u /\ j < LENGTH xs /\ ~u.vs_halted /\ u.vs_current_bb = body_lbl /\
  u.vs_inst_idx = 0 /\
  entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap u /\
  entry_loop_prefix tv xs d j u ==>
  ?t. E j t /\
    entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr (LENGTH xs) j t /\
    entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap t /\
    entry_loop_prefix tv xs d (SUC j) t /\
    entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] u t
Proof
  strip_tac >> fs[entry_indexed_loop_contract_def] >>
  qpat_x_assum `!j u. B j u /\ _ ==> _` drule_all >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  `32+j*type_memory_size tv <= cap` by
    (`j*type_memory_size tv <= LENGTH xs*type_memory_size tv` by
       (irule LESS_MONO_MULT >> simp[]) >> decide_tac) >>
  `entry_loop_prefix tv xs d (SUC j) t` by
    (irule entry_registered_child_prefix_extend >> simp[] >>
     qpat_assum `abi_encoder_registered_effect _ _ _ _` (irule_at Any) >>
     fs[entry_operational_loop_resources_def] >> metis_tac[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  simp_tac bool_ss [entry_loop_trace_def] >> asm_rewrite_tac[] >>
  once_rewrite_tac[ADD_COMM] >> irule loop_child_effect_enlarge >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem indexed_backedge_boundary[local]:
  entry_indexed_loop_contract ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid ids child_ids kin B E Q /\
  E j s /\ j < LENGTH xs /\
  entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr (LENGTH xs) j s /\
  entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap s /\
  entry_loop_prefix tv xs d (SUC j) s /\
  t = jump_to hdr (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)) ==>
  entry_operational_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid (SUC j) t /\
  entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s t /\ kin (SUC j) t
Proof
  strip_tac >>
  `kin (SUC j) t` by
    (fs[entry_indexed_loop_contract_def] >>
     qpat_x_assum `!j t. E j t /\ _ ==> _` drule_all >> simp[]) >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[entry_operational_loop_inv_def, entry_loop_trace_def, GSYM CONJ_ASSOC] >>
  irule (SRULE [GSYM CONJ_ASSOC] entry_operational_loop_backedge_phase) >>
  fs[entry_indexed_loop_contract_def] >> metis_tac[]
QED

Theorem indexed_loop_round[local]:
  entry_indexed_loop_contract ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid ids child_ids kin B E Q /\
  entry_operational_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid j s /\
  kin j s /\ j < LENGTH xs ==>
  ?v. entry_operational_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid (SUC j) v /\
    kin (SUC j) v /\ entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s v
Proof
  strip_tac >>
  qabbrev_tac `h = jump_to (if j < LENGTH xs then body_lbl else exit)
    (abi_decode_header_state iv cv cmp done j (LENGTH xs) s)` >>
  `(~h.vs_halted /\ h.vs_current_bb = body_lbl /\ h.vs_inst_idx = 0) /\
   entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap h /\
   entry_loop_prefix tv xs d j h /\
   entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s h /\ B j h` by
    (`h = jump_to (if j < LENGTH xs then body_lbl else exit)
        (abi_decode_header_state iv cv cmp done j (LENGTH xs) s)` by simp[Abbr `h`] >>
     drule_all indexed_header_boundary >> simp[Abbr `h`]) >>
  drule_all indexed_child_boundary >> disch_then (qx_choose_then `t` strip_assume_tac) >>
  qabbrev_tac `v = jump_to hdr
    (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) t))` >>
  `entry_operational_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid (SUC j) v /\
   entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] t v /\ kin (SUC j) v` by
    (`v = jump_to hdr
        (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) t))` by simp[Abbr `v`] >>
     drule_all indexed_backedge_boundary >> simp[Abbr `v`]) >>
  qexists_tac `v` >> asm_rewrite_tac[] >>
  irule loop_trace_trans >> qexists_tac `t` >> reverse conj_tac
  >- fs[ADD_COMM] >>
  irule loop_trace_trans >> qexists_tac `h` >> fs[ADD_COMM]
QED

Theorem indexed_loop_exit[local]:
  entry_indexed_loop_contract ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid ids child_ids kin B E Q /\
  entry_operational_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid (LENGTH xs) s /\
  kin (LENGTH xs) s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
    entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap t /\
    entry_loop_prefix tv xs d (LENGTH xs) t /\
    entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s t /\ Q t
Proof
  strip_tac >>
  qabbrev_tac `t = jump_to exit
    (abi_decode_header_state iv cv cmp done (LENGTH xs) (LENGTH xs) s)` >>
  `t = jump_to (if LENGTH xs < LENGTH xs then body_lbl else exit)
    (abi_decode_header_state iv cv cmp done (LENGTH xs) (LENGTH xs) s)` by simp[Abbr `t`] >>
  drule_all indexed_header_boundary >>
  simp_tac (srw_ss()) [NoAsms] >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem entry_indexed_operational_array_loop_from_index:
  entry_indexed_loop_contract ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src iv cv cmp done nv p srcaddr tv xs d cap cid oid ids child_ids kin B E Q /\
  entry_operational_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid j s /\
  kin j s ==>
  ?t. (~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
    entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap t /\
    entry_loop_prefix tv xs d (LENGTH xs) t /\
    entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s t /\ Q t) /\
    abi_decode_sim ctx fn s t
Proof
  strip_tac >>
  qabbrev_tac `loopinv = \k u.
    entry_operational_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid k u /\
    kin k u /\ entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s u` >>
  `!k u. loopinv k u /\ k < LENGTH xs ==>
    ?v. loopinv (SUC k) v /\ abi_decode_sim ctx fn u v` by
    (simp_tac bool_ss [Abbr `loopinv`] >> rpt strip_tac >>
     drule_all indexed_loop_round >> disch_then (qx_choose_then `v` strip_assume_tac) >>
     qexists_tac `v` >> asm_rewrite_tac[] >> conj_tac
     >- (irule loop_trace_trans >> qexists_tac `u` >> asm_rewrite_tac[]) >>
     irule loop_trace_sim >> goal_assum (drule_at Any)) >>
  `!u. loopinv (LENGTH xs) u ==>
    ?t. (~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
      entry_operational_loop_resources ctx fn site cid (w2n p) oid d cap t /\
      entry_loop_prefix tv xs d (LENGTH xs) t /\
      entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s t /\ Q t) /\
      abi_decode_sim ctx fn u t` by
    (simp_tac bool_ss [Abbr `loopinv`] >> rpt strip_tac >>
     drule_all indexed_loop_exit >> disch_then (qx_choose_then `t` strip_assume_tac) >>
     qexists_tac `t` >> asm_rewrite_tac[] >> conj_tac
     >- (irule loop_trace_trans >> qexists_tac `u` >> asm_rewrite_tac[]) >>
     irule loop_trace_sim >> goal_assum (drule_at Any)) >>
  ho_match_mp_tac abi_decode_finite_iteration >>
  qexistsl_tac [`LENGTH xs`, `j`, `loopinv`] >>
  simp[Abbr `loopinv`, loop_trace_refl] >>
  fs[entry_operational_loop_inv_def, abi_decode_loop_ready_def]
QED
