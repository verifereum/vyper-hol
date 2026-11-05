(* Exact-source-list array loop shell: observable fields and indexed memory. *)
Theory entryReachBodyExactArrayLoop
Ancestors
  calldataDynOwned abiDecoderExecution abiDecoderFrameCompose
  valueEncoding valueEncodingProps venomState venomExecSemantics words list
  arithmetic abiDecoderContract emitHelperProps venomMemProofs abiDecoderLoop venomInst

Definition entry_loop_fields_def:
  entry_loop_fields s t <=>
    (t.vs_accounts, t.vs_transient, t.vs_logs, t.vs_tx_ctx,
     t.vs_block_ctx, t.vs_outcomes, t.vs_requests, t.vs_pending_deletions,
     t.vs_gas_readings, t.vs_fmp, t.vs_call_ctx, t.vs_data_section) =
    (s.vs_accounts, s.vs_transient, s.vs_logs, s.vs_tx_ctx,
     s.vs_block_ctx, s.vs_outcomes, s.vs_requests, s.vs_pending_deletions,
     s.vs_gas_readings, s.vs_fmp, s.vs_call_ctx, s.vs_data_section)
End

Theorem entry_loop_fields_refl[local]:
  entry_loop_fields s s
Proof
  simp[entry_loop_fields_def]
QED

Theorem entry_loop_fields_trans[local]:
  entry_loop_fields s t /\ entry_loop_fields t u ==> entry_loop_fields s u
Proof
  simp[entry_loop_fields_def] >> metis_tac[]
QED

Theorem entry_loop_header_fields[local]:
  t = jump_to lbl (abi_decode_header_state iv cv cmp done j n s) ==>
  entry_loop_fields s t /\ t.vs_halted = s.vs_halted /\
  t.vs_current_bb = lbl /\ t.vs_inst_idx = 0
Proof
  simp[abi_decode_header_state_def, update_var_def, jump_to_def,
       entry_loop_fields_def]
QED

Theorem entry_loop_backedge_fields[local]:
  t = jump_to hdr (mstore p (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)) ==>
  entry_loop_fields s t /\ t.vs_halted = s.vs_halted /\
  t.vs_current_bb = hdr /\ t.vs_inst_idx = 0
Proof
  simp[update_var_def, jump_to_def, mstore_def,
       write_memory_with_expansion_def, entry_loop_fields_def]
QED

Definition entry_loop_prefix_def:
  entry_loop_prefix tv xs d j s <=>
    !k. k < j ==> val_in_memory tv (EL k xs)
      (d+32+k*type_memory_size tv) s.vs_memory
End

Theorem entry_loop_prefix_zero[local]:
  entry_loop_prefix tv xs d 0 s
Proof
  simp[entry_loop_prefix_def]
QED

Theorem entry_loop_prefix_extend[local]:
  entry_loop_prefix tv xs d j s /\
  val_in_memory tv (EL j xs) (d+32+j*type_memory_size tv) s.vs_memory ==>
  entry_loop_prefix tv xs d (SUC j) s
Proof
  simp[entry_loop_prefix_def] >> rpt strip_tac >>
  Cases_on `k = j` >> gvs[] >> first_x_assum irule >> decide_tac
QED

Theorem entry_loop_prefix_header[local]:
  entry_loop_prefix tv xs d j s ==>
  entry_loop_prefix tv xs d j (jump_to lbl (abi_decode_header_state iv cv cmp done i n s))
Proof
  simp[entry_loop_prefix_def, jump_to_def, abi_decode_header_state_def, update_var_def]
QED

Theorem entry_loop_prefix_backedge[local]:
  entry_loop_prefix tv xs d j s /\ j <= LENGTH xs /\ EVERY (val_wf tv) xs /\
  (!k. k < j ==> p+32 <= d+32+k*type_memory_size tv \/
     d+32+k*type_memory_size tv+type_memory_size tv <= p) ==>
  entry_loop_prefix tv xs d j
    (jump_to hdr (mstore p (n2w (SUC i)) (update_var nv (n2w (SUC i)) s)))
Proof
  simp_tac bool_ss [entry_loop_prefix_def] >> rpt strip_tac >>
  `val_wf tv (EL k xs)` by
    (gvs[EVERY_EL] >> first_x_assum irule >> decide_tac) >>
  `val_in_memory tv (EL k xs) (d+32+k*type_memory_size tv) s.vs_memory` by simp[] >>
  `p+32 <= d+32+k*type_memory_size tv \/
   d+32+k*type_memory_size tv+type_memory_size tv <= p` by simp[] >>
  `val_in_memory tv (EL k xs) (d+32+k*type_memory_size tv)
    (mstore p (n2w (SUC i)) (s with vs_memory := s.vs_memory)).vs_memory` by
    (irule (cj 1 mstore_preserves_val_in_memory) >> simp[]) >>
  gvs[update_var_def, jump_to_def, mstore_def, write_memory_with_expansion_def]
QED

(* Child execution stops BEFORE the emitted increment/store/jump. *)
Definition entry_loop_child_end_def:
  entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr n j t <=>
    (?bb. lookup_block tail fn.fn_blocks = SOME bb /\
      bb.bb_instructions = prefix ++ abi_decode_backedge_insts bid iv nv ip hdr) /\
    t.vs_current_bb = tail /\ t.vs_inst_idx = LENGTH prefix /\ ~t.vs_halted /\
    eval_operand (Var iv) t = SOME (n2w j) /\ eval_operand ip t = SOME p /\
    eval_operand src t = SOME srcaddr /\
    abi_decode_load CALLDATALOAD srcaddr t = n2w n
End

Theorem entry_loop_backedge_ready[local]:
  entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr n j t /\
  ip <> Var nv /\ src <> Var nv /\ j < n /\ n < dimword (:256) ==>
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr n (SUC j)
    (jump_to hdr (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) t)))
Proof
  simp_tac bool_ss [entry_loop_child_end_def] >> strip_tac >>
  simp[abi_decode_loop_ready_def, abi_decode_mload_jump,
    mload_mstore_same_proof, abi_decode_load_def, abi_decode_source_def,
    jump_to_def, update_var_def, mstore_def, write_memory_with_expansion_def] >>
  conj_tac >- (Cases_on `ip` >> gvs[eval_operand_def, lookup_var_def,
    finite_mapTheory.FLOOKUP_UPDATE]) >>
  Cases_on `src` >> gvs[eval_operand_def, lookup_var_def,
    finite_mapTheory.FLOOKUP_UPDATE, abi_decode_load_def, abi_decode_source_def]
QED

Definition entry_loop_callback_def:
  entry_loop_callback ctx fn body_lbl tail prefix bid iv nv ip hdr src p srcaddr
      tv xs d J <=>
    !j u. j < LENGTH xs /\ ~u.vs_halted /\ u.vs_current_bb = body_lbl /\
      u.vs_inst_idx = 0 /\ J u /\ entry_loop_prefix tv xs d j u ==>
      ?t. entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr
             (LENGTH xs) j t /\
        J t /\ entry_loop_prefix tv xs d (SUC j) t /\
        entry_loop_fields u t /\ abi_decode_sim ctx fn u t
End

Definition entry_loop_shell_def:
  entry_loop_shell ctx fn hdr body_lbl exit hid tail prefix bid ip src iv cv cmp done nv
      p srcaddr tv xs d J <=>
    abi_decode_loop_cfg fn hdr body_lbl exit hid ip src CALLDATALOAD iv cv cmp done /\
    src <> Var iv /\ iv <> cv /\ ip <> Var nv /\ src <> Var nv /\
    LENGTH xs < dimword (:256) /\ EVERY (val_wf tv) xs /\
    (!k. k < LENGTH xs ==> w2n p+32 <= d+32+k*type_memory_size tv \/
      d+32+k*type_memory_size tv+type_memory_size tv <= w2n p) /\
    (!j u. J u ==> J (jump_to (if j < LENGTH xs then body_lbl else exit)
      (abi_decode_header_state iv cv cmp done j (LENGTH xs) u))) /\
    (!j u. J u ==> J (jump_to hdr
      (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) u)))) /\
    entry_loop_callback ctx fn body_lbl tail prefix bid iv nv ip hdr src p srcaddr
      tv xs d J
End

Theorem entry_loop_shell_header_sim[local]:
  entry_loop_shell ctx fn hdr body_lbl exit hid tail prefix bid ip src iv cv cmp done nv
    p srcaddr tv xs d J /\
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) j s ==>
  abi_decode_sim ctx fn s (jump_to (if j < LENGTH xs then body_lbl else exit)
    (abi_decode_header_state iv cv cmp done j (LENGTH xs) s))
Proof
  simp_tac bool_ss [entry_loop_shell_def, abi_decode_loop_cfg_def,
    abi_decode_loop_ready_def] >> strip_tac >>
  irule abi_decode_header_sim >> simp[abi_decode_source_opcode_def] >>
  metis_tac[]
QED

Theorem entry_loop_shell_backedge_sim[local]:
  entry_loop_shell ctx fn hdr body_lbl exit hid tail prefix bid ip src iv cv cmp done nv
    p srcaddr tv xs d J /\ j < LENGTH xs /\
  entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr (LENGTH xs) j t ==>
  abi_decode_sim ctx fn t (jump_to hdr
    (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) t)))
Proof
  simp_tac bool_ss [entry_loop_shell_def, entry_loop_child_end_def,
    abi_decode_loop_cfg_def] >> strip_tac >>
  irule abi_decode_backedge_sim >>
  simp[abi_decode_header_insts_def, phi_prefix_length_def, mk_inst_def] >>
  metis_tac[]
QED

Theorem entry_loop_shell_step[local]:
  entry_loop_shell ctx fn hdr body_lbl exit hid tail prefix bid ip src iv cv cmp done nv
    p srcaddr tv xs d J /\
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) j s /\
  J s /\ entry_loop_prefix tv xs d j s /\ j < LENGTH xs ==>
  ?v. abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) (SUC j) v /\
    J v /\ entry_loop_prefix tv xs d (SUC j) v /\
    entry_loop_fields s v /\ abi_decode_sim ctx fn s v
Proof
  strip_tac >>
  drule_all entry_loop_shell_header_sim >> simp[] >> strip_tac >>
  qabbrev_tac `h = jump_to body_lbl
    (abi_decode_header_state iv cv cmp done j (LENGTH xs) s)` >>
  `entry_loop_fields s h /\ ~h.vs_halted /\ h.vs_current_bb = body_lbl /\
    h.vs_inst_idx = 0` by
    (gvs[abi_decode_loop_ready_def, Abbr `h`] >>
     simp[entry_loop_fields_def, jump_to_def, abi_decode_header_state_def, update_var_def]) >>
  `J h /\ entry_loop_prefix tv xs d j h` by
    (fs[entry_loop_shell_def, Abbr `h`] >> conj_tac
     >- (qpat_x_assum `!j u. J u ==> J (jump_to (if _ then _ else _) _)`
           (qspecl_then [`j`,`s`] mp_tac) >> simp[]) >>
     irule entry_loop_prefix_header >> simp[]) >>
  `?t. entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr
      (LENGTH xs) j t /\ J t /\ entry_loop_prefix tv xs d (SUC j) t /\
      entry_loop_fields h t /\ abi_decode_sim ctx fn h t` by
    (fs[entry_loop_shell_def, entry_loop_callback_def] >> metis_tac[]) >>
  drule_all entry_loop_shell_backedge_sim >> strip_tac >>
  qabbrev_tac `v = jump_to hdr
    (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) t))` >>
  qexists_tac `v` >> rpt conj_tac
  >- (unabbrev_all_tac >> irule entry_loop_backedge_ready >>
      fs[entry_loop_shell_def] >> metis_tac[])
  >- fs[entry_loop_shell_def, Abbr `v`]
  >- (simp[Abbr `v`] >> irule entry_loop_prefix_backedge >>
      fs[entry_loop_shell_def] >> metis_tac[LESS_EQ])
  >- (irule entry_loop_fields_trans >> qexists_tac `t` >> conj_tac
      >- metis_tac[entry_loop_fields_trans] >>
      simp[Abbr `v`, entry_loop_fields_def, jump_to_def, mstore_def,
        update_var_def, write_memory_with_expansion_def]) >>
  metis_tac[abi_decode_sim_trans]
QED

Theorem entry_loop_shell_exit[local]:
  entry_loop_shell ctx fn hdr body_lbl exit hid tail prefix bid ip src iv cv cmp done nv
    p srcaddr tv xs d J /\
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) (LENGTH xs) s /\
  J s /\ entry_loop_prefix tv xs d (LENGTH xs) s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
    J t /\ entry_loop_prefix tv xs d (LENGTH xs) t /\
    entry_loop_fields s t /\ abi_decode_sim ctx fn s t
Proof
  strip_tac >> drule_all entry_loop_shell_header_sim >> simp[] >> strip_tac >>
  qexists_tac `jump_to exit
    (abi_decode_header_state iv cv cmp done (LENGTH xs) (LENGTH xs) s)` >>
  `J (jump_to exit
    (abi_decode_header_state iv cv cmp done (LENGTH xs) (LENGTH xs) s))` by
    (fs[entry_loop_shell_def] >>
     qpat_x_assum `!j u. J u ==> J (jump_to (if _ then _ else _) _)`
       (qspecl_then [`LENGTH xs`,`s`] mp_tac) >> simp[]) >>
  simp[entry_loop_prefix_header, entry_loop_fields_def,
    abi_decode_loop_ready_def, jump_to_def, abi_decode_header_state_def,
    update_var_def] >> gvs[abi_decode_loop_ready_def]
QED

Theorem entry_exact_array_loop_from_index:
  entry_loop_shell ctx fn hdr body_lbl exit hid tail prefix bid ip src iv cv cmp done nv
    p srcaddr tv xs d J /\
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) j s /\
  J s /\ entry_loop_prefix tv xs d j s ==>
  ?t. (~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
    J t /\ entry_loop_prefix tv xs d (LENGTH xs) t /\
    entry_loop_fields s t) /\ abi_decode_sim ctx fn s t
Proof
  strip_tac >>
  qabbrev_tac `loopinv = \j u.
    abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) j u /\
    J u /\ entry_loop_prefix tv xs d j u /\ entry_loop_fields s u` >>
  `!i u. loopinv i u /\ i < LENGTH xs ==>
    ?v. loopinv (SUC i) v /\ abi_decode_sim ctx fn u v` by
    (simp_tac bool_ss [Abbr `loopinv`] >> rpt strip_tac >>
     drule_all entry_loop_shell_step >> strip_tac >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[entry_loop_fields_trans]) >>
  `!u. loopinv (LENGTH xs) u ==> ?t.
    (~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
      J t /\ entry_loop_prefix tv xs d (LENGTH xs) t /\ entry_loop_fields s t) /\
    abi_decode_sim ctx fn u t` by
    (simp_tac bool_ss [Abbr `loopinv`] >> rpt strip_tac >>
     drule_all entry_loop_shell_exit >> strip_tac >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[entry_loop_fields_trans]) >>
  ho_match_mp_tac abi_decode_finite_iteration >>
  qexistsl_tac [`LENGTH xs`,`j`,`loopinv`] >>
  simp[Abbr `loopinv`, entry_loop_fields_refl] >>
  gvs[abi_decode_loop_ready_def]
QED

Theorem entry_exact_array_loop:
  entry_loop_shell ctx fn hdr body_lbl exit hid tail prefix bid ip src iv cv cmp done nv
    p srcaddr tv xs d J /\
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) 0 s /\ J s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\ J t /\
    (!k. k < LENGTH xs ==> val_in_memory tv (EL k xs)
      (d+32+k*type_memory_size tv) t.vs_memory) /\
    entry_loop_fields s t /\ abi_decode_sim ctx fn s t
Proof
  strip_tac >>
  `entry_loop_prefix tv xs d 0 s` by simp[entry_loop_prefix_zero] >>
  drule_all entry_exact_array_loop_from_index >>
  simp[entry_loop_prefix_def] >> metis_tac[]
QED

Theorem entry_loop_backedge_header_word[local]:
  d+32 <= w2n p \/ w2n p+32 <= d ==>
  mem_word_at d
    (jump_to hdr (mstore (w2n p) w (update_var nv w s))).vs_memory =
  mem_word_at d s.vs_memory
Proof
  strip_tac >> simp_tac bool_ss [jump_to_def, venom_state_accfupds] >>
  asm_simp_tac (srw_ss()) [mstore_mem_word_at_disjoint, update_var_def]
QED

Theorem entry_loop_shell_with_header[local]:
  entry_loop_shell ctx fn hdr body_lbl exit hid tail prefix bid ip src iv cv cmp done nv
    p srcaddr tv xs d J /\
  (d+32 <= w2n p \/ w2n p+32 <= d) /\
  entry_loop_callback ctx fn body_lbl tail prefix bid iv nv ip hdr src p srcaddr
    tv xs d (\u. J u /\ mem_word_at d u.vs_memory = n2w (LENGTH xs)) ==>
  entry_loop_shell ctx fn hdr body_lbl exit hid tail prefix bid ip src iv cv cmp done nv
    p srcaddr tv xs d (\u. J u /\ mem_word_at d u.vs_memory = n2w (LENGTH xs))
Proof
  simp_tac bool_ss [entry_loop_shell_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >>
      simp[jump_to_def, abi_decode_header_state_def, update_var_def] >> metis_tac[]) >>
  rpt strip_tac >> metis_tac[entry_loop_backedge_header_word]
QED

Theorem entry_exact_dynamic_array_loop:
  entry_loop_shell ctx fn hdr body_lbl exit hid tail prefix bid ip src iv cv cmp done nv
    p srcaddr tv xs d J /\
  (d+32 <= w2n p \/ w2n p+32 <= d) /\
  entry_loop_callback ctx fn body_lbl tail prefix bid iv nv ip hdr src p srcaddr
    tv xs d (\u. J u /\ mem_word_at d u.vs_memory = n2w (LENGTH xs)) /\
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) 0 s /\
  J s /\ mem_word_at d s.vs_memory = n2w (LENGTH xs) /\ LENGTH xs <= maxn ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\ J t /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d t.vs_memory /\
    entry_loop_fields s t /\ abi_decode_sim ctx fn s t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all entry_loop_shell_with_header >> strip_tac >>
  ` (\u. J u /\ mem_word_at d u.vs_memory = n2w (LENGTH xs)) s` by simp[] >>
  drule_all entry_exact_array_loop >> simp_tac bool_ss [] >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  irule (cj 2 calldata_terminal_array_memory) >>
  fs[entry_loop_shell_def] >> goal_assum (drule_at Any) >> simp[]
QED

(* Interface checks: zero iterations have an explicit, memory-preserving
   endpoint; one iteration retains the particular supplied source value. *)
Theorem entry_exact_array_loop_empty[local]:
  entry_loop_shell ctx fn hdr body_lbl exit hid tail prefix bid ip src iv cv cmp done nv
    p srcaddr tv [] d J /\
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr 0 0 s ==>
  ?t. t = jump_to exit (abi_decode_header_state iv cv cmp done 0 0 s) /\
    ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
    t.vs_memory = s.vs_memory /\ entry_loop_fields s t /\ abi_decode_sim ctx fn s t
Proof
  strip_tac >>
  `abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH ([]:value list)) 0 s`
    by simp[] >>
  drule_all entry_loop_shell_header_sim >> simp[] >> strip_tac >>
  gvs[abi_decode_loop_ready_def, jump_to_def, abi_decode_header_state_def,
    update_var_def, entry_loop_fields_def]
QED

Theorem entry_exact_array_loop_singleton[local]:
  entry_loop_shell ctx fn hdr body_lbl exit hid tail prefix bid ip src iv cv cmp done nv
    p srcaddr tv [x] d J /\
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr 1 0 s /\ J s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\ J t /\
    val_in_memory tv x (d+32) t.vs_memory /\
    entry_loop_fields s t /\ abi_decode_sim ctx fn s t
Proof
  strip_tac >>
  `abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH [x]) 0 s` by simp[] >>
  drule_all entry_exact_array_loop >> simp[]
QED
