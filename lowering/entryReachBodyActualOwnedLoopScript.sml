(* Actual decoder loops reload the index in the body: hiv and biv need not
   name the same register. Ownership and operational endpoints are unchanged. *)
Theory entryReachBodyActualOwnedLoop
Ancestors
  valueEncodingDefs entryReachBodyOwnedLoop entryReachBodyOwnedRegion
  entryReachBodyIndexedLoopInput entryReachBodyExactArrayLoop
  entryReachBodyOperationalLoop entryReachBodyOperationalPath
  entryReachBodyCanonicalBytesArray
  abiDecoderLoop abiDecoderExecution abiDecoderContract
  abiEncoderRegisteredEffect venomMemDefs venomExecSemantics venomState
  localPtrsProps finite_map words list arithmetic pred_set rich_list
  abiEncoderObserver abiEncoderPrimitiveEffect venomExecProofs venomInst
  venomMemProofs fragExec instIdxIndep exprLoweringProps valueEncodingProps

Definition entry_actual_owned_indexed_contract_def:
  entry_actual_owned_indexed_contract ctx fn site hdr body_lbl exit hid tail prefix bid
      ip src hiv biv cv cmp done nv p srcaddr tv xs d cap cid oid root extent
      ids child_ids kin B E Q <=>
    abi_decode_loop_cfg fn hdr body_lbl exit hid ip src CALLDATALOAD hiv cv cmp done /\
    src <> Var hiv /\ hiv <> cv /\ ip <> Var nv /\ src <> Var nv /\
    LENGTH xs < dimword (:256) /\ EVERY (val_wf tv) xs /\
    32+LENGTH xs*type_memory_size tv <= cap /\ oid <> cid /\
    cid IN ids /\ oid NOTIN child_ids /\ child_ids SUBSET ids /\
    (!j s. kin j s /\
       entry_owned_loop_inv ctx fn site hdr ip src p srcaddr tv xs
         d cap cid oid root extent j s ==>
       if j < LENGTH xs then
         B j (jump_to body_lbl (abi_decode_header_state hiv cv cmp done j (LENGTH xs) s))
       else Q (jump_to exit (abi_decode_header_state hiv cv cmp done j (LENGTH xs) s))) /\
    (!j u. B j u /\ j < LENGTH xs /\ ~u.vs_halted /\
       u.vs_current_bb = body_lbl /\ u.vs_inst_idx = 0 /\
       entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap u ==>
       ?t. E j t /\
         entry_loop_child_end fn tail prefix bid biv nv ip hdr src p srcaddr (LENGTH xs) j t /\
         entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap t /\
         val_in_memory tv (EL j xs) (d+32+j*type_memory_size tv) t.vs_memory /\
         entry_loop_fields u t /\ entry_decode_path ctx fn u t /\
         abi_encoder_registered_effect child_ids
           [(d+32+j*type_memory_size tv,type_memory_size tv)] u t) /\
    (!j t. E j t /\ j < LENGTH xs /\
       entry_loop_child_end fn tail prefix bid biv nv ip hdr src p srcaddr (LENGTH xs) j t /\
       entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap t ==>
       kin (SUC j) (jump_to hdr
         (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) t))))
End

Theorem actual_owned_child_boundary[local]:
  entry_actual_owned_indexed_contract ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src hiv biv cv cmp done nv p srcaddr tv xs d cap cid oid root extent
    ids child_ids kin B E Q /\
  B j u /\ j < LENGTH xs /\ ~u.vs_halted /\ u.vs_current_bb = body_lbl /\
  u.vs_inst_idx = 0 /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap u /\
  entry_loop_prefix tv xs d j u ==>
  ?t. E j t /\
    entry_loop_child_end fn tail prefix bid biv nv ip hdr src p srcaddr (LENGTH xs) j t /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap t /\
    entry_loop_prefix tv xs d (SUC j) t /\
    entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] u t
Proof
  strip_tac >> fs[entry_actual_owned_indexed_contract_def] >>
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

Theorem actual_owned_header_boundary[local]:
  entry_actual_owned_indexed_contract ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src hiv biv cv cmp done nv p srcaddr tv xs d cap cid oid root extent ids child_ids kin B E Q /\
  entry_owned_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid root extent j s /\
  kin j s /\
  t = jump_to (if j < LENGTH xs then body_lbl else exit)
    (abi_decode_header_state hiv cv cmp done j (LENGTH xs) s) ==>
  (~t.vs_halted /\ t.vs_current_bb = (if j < LENGTH xs then body_lbl else exit) /\
    t.vs_inst_idx = 0) /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap t /\
  entry_loop_prefix tv xs d j t /\
  entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s t /\
  (if j < LENGTH xs then B j t else Q t)
Proof
  strip_tac >>
  `if j < LENGTH xs then B j t else Q t` by
    (fs[entry_actual_owned_indexed_contract_def] >>
     first_x_assum drule >> simp[] >> Cases_on `j < LENGTH xs` >> gvs[]) >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[entry_loop_trace_def, GSYM CONJ_ASSOC] >>
  irule (SRULE [GSYM CONJ_ASSOC] owned_header_phase) >>
  fs[entry_actual_owned_indexed_contract_def, entry_owned_loop_inv_def] >> metis_tac[]
QED

Theorem actual_owned_backedge_boundary[local]:
  entry_actual_owned_indexed_contract ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src hiv biv cv cmp done nv p srcaddr tv xs d cap cid oid root extent ids child_ids kin B E Q /\
  E j s /\ j < LENGTH xs /\
  entry_loop_child_end fn tail prefix bid biv nv ip hdr src p srcaddr (LENGTH xs) j s /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap s /\
  entry_loop_prefix tv xs d (SUC j) s /\
  t = jump_to hdr (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)) ==>
  entry_owned_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid root extent (SUC j) t /\
  entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s t /\ kin (SUC j) t
Proof
  strip_tac >>
  `kin (SUC j) t` by
    (fs[entry_actual_owned_indexed_contract_def] >>
     qpat_x_assum `!j t. E j t /\ _ ==> _` drule_all >> simp[]) >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[entry_owned_loop_inv_def, entry_loop_trace_def, GSYM CONJ_ASSOC] >>
  irule (SRULE [GSYM CONJ_ASSOC] owned_backedge_phase) >>
  fs[entry_actual_owned_indexed_contract_def] >> metis_tac[]
QED

Theorem actual_owned_loop_round[local]:
  entry_actual_owned_indexed_contract ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src hiv biv cv cmp done nv p srcaddr tv xs d cap cid oid root extent ids child_ids kin B E Q /\
  entry_owned_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid root extent j s /\
  kin j s /\ j < LENGTH xs ==>
  ?v. entry_owned_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid root extent (SUC j) v /\
    kin (SUC j) v /\ entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s v
Proof
  strip_tac >>
  qabbrev_tac `h = jump_to (if j < LENGTH xs then body_lbl else exit)
    (abi_decode_header_state hiv cv cmp done j (LENGTH xs) s)` >>
  `(~h.vs_halted /\ h.vs_current_bb = body_lbl /\ h.vs_inst_idx = 0) /\
   entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap h /\
   entry_loop_prefix tv xs d j h /\
   entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s h /\ B j h` by
    (`h = jump_to (if j < LENGTH xs then body_lbl else exit)
        (abi_decode_header_state hiv cv cmp done j (LENGTH xs) s)` by simp[Abbr `h`] >>
     drule_all actual_owned_header_boundary >> simp[Abbr `h`]) >>
  drule_all actual_owned_child_boundary >> disch_then (qx_choose_then `t` strip_assume_tac) >>
  qabbrev_tac `v = jump_to hdr
    (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) t))` >>
  `entry_owned_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid root extent (SUC j) v /\
   entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] t v /\ kin (SUC j) v` by
    (`v = jump_to hdr
        (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) t))` by simp[Abbr `v`] >>
     drule_all actual_owned_backedge_boundary >> simp[Abbr `v`]) >>
  qexists_tac `v` >> asm_rewrite_tac[] >>
  irule loop_trace_trans >> qexists_tac `t` >> reverse conj_tac
  >- fs[ADD_COMM] >>
  irule loop_trace_trans >> qexists_tac `h` >> fs[ADD_COMM]
QED

Theorem actual_owned_loop_exit[local]:
  entry_actual_owned_indexed_contract ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src hiv biv cv cmp done nv p srcaddr tv xs d cap cid oid root extent ids child_ids kin B E Q /\
  entry_owned_loop_inv ctx fn site hdr ip src p srcaddr tv xs d cap cid oid root extent (LENGTH xs) s /\
  kin (LENGTH xs) s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap t /\
    entry_loop_prefix tv xs d (LENGTH xs) t /\
    entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s t /\ Q t
Proof
  strip_tac >>
  qabbrev_tac `t = jump_to exit
    (abi_decode_header_state hiv cv cmp done (LENGTH xs) (LENGTH xs) s)` >>
  `t = jump_to (if LENGTH xs < LENGTH xs then body_lbl else exit)
    (abi_decode_header_state hiv cv cmp done (LENGTH xs) (LENGTH xs) s)` by simp[Abbr `t`] >>
  drule_all actual_owned_header_boundary >>
  simp_tac (srw_ss()) [NoAsms] >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem entry_actual_owned_indexed_array_loop_from_index:
  entry_actual_owned_indexed_contract ctx fn site hdr body_lbl exit hid tail prefix bid
    ip src hiv biv cv cmp done nv p srcaddr tv xs d cap cid oid root extent ids child_ids kin B E Q /\
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
     drule_all actual_owned_loop_round >> disch_then (qx_choose_then `v` strip_assume_tac) >>
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
     drule_all actual_owned_loop_exit >> disch_then (qx_choose_then `t` strip_assume_tac) >>
     qexists_tac `t` >> asm_rewrite_tac[] >> conj_tac
     >- (irule loop_trace_trans >> qexists_tac `u` >> asm_rewrite_tac[]) >>
     irule loop_trace_sim >> goal_assum (drule_at Any)) >>
  ho_match_mp_tac abi_decode_finite_iteration >>
  qexistsl_tac [`LENGTH xs`, `j`, `loopinv`] >>
  simp[Abbr `loopinv`, loop_trace_refl] >>
  fs[entry_owned_loop_inv_def, abi_decode_loop_ready_def]
QED

(* Compiler-facing validation: the CFG is obtained from the actual prefix,
   while child_end uses the body's reload register, exactly as the suffix
   does. In particular this application does not identify the two names. *)
Theorem entry_actual_owned_compiler_backedge:
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = (labels,body_st) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring n) asz msz body_st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
    (Lit 0w) (DecBytestring n) middle = ((),last) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) last =
    ((),final) /\ fn_has_code loop_st final fn /\
  (!bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  final.cs_next_var <= limit_st.cs_next_var /\
  ip <> Var (STRING #"%" (toString last.cs_next_var)) /\
  src <> Var (STRING #"%" (toString last.cs_next_var)) /\
  LENGTH xs < dimword (:256) /\ EVERY (val_wf tv) xs /\
  32+LENGTH xs*type_memory_size tv <= cap /\ oid <> cid /\ cid IN ids /\
  j < LENGTH xs /\
  entry_loop_child_end fn last.cs_current_bb last.cs_current_insts last.cs_next_id
    (STRING #"%" (toString body_st.cs_next_var))
    (STRING #"%" (toString last.cs_next_var)) ip (FST labels) src p srcaddr
    (LENGTH xs) j s /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap s /\
  entry_loop_prefix tv xs d (SUC j) s /\
  t = jump_to (FST labels) (mstore (w2n p) (n2w (SUC j))
    (update_var (STRING #"%" (toString last.cs_next_var)) (n2w (SUC j)) s)) ==>
  entry_owned_loop_inv ctx fn site (FST labels) ip src p srcaddr tv xs
    d cap cid oid root extent (SUC j) t /\
  entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] s t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all entry_bytes_array_phase_layout >> strip_tac >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[entry_owned_loop_inv_def, entry_loop_trace_def, GSYM CONJ_ASSOC] >>
  irule (SRULE [GSYM CONJ_ASSOC] owned_backedge_phase) >>
  simp[SF SFY_ss]
QED
