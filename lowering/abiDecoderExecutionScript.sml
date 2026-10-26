(* Concrete nonrecursive loop shell. Recursive children remain separate. *)
Theory abiDecoderExecution
Ancestors
  abiDecoderLoop abiDecoderFrame abiDecoderComposition abiDecoderContract
  fragExec emitHelperProps exprLoweringProps venomExecSemantics venomExecProofs
  venomState venomInst words arithmetic compileEnv emitHelper

Definition abi_decode_header_insts_def:
  abi_decode_header_insts id ip src opc iv cv cmp done body_lbl exit =
    [mk_inst id MLOAD [ip] [iv];
     mk_inst (id+1) opc [src] [cv];
     mk_inst (id+2) LT [Var iv;Var cv] [cmp];
     mk_inst (id+3) ISZERO [Var cmp] [done];
     mk_inst (id+4) JNZ [Var done;Label exit;Label body_lbl] []]
End

Definition abi_decode_header_state_def:
  abi_decode_header_state iv cv cmp done i ncount s =
    update_var done (bool_to_word (~(i < ncount)))
      (update_var cmp (bool_to_word (i < ncount))
        (update_var cv (n2w ncount) (update_var iv (n2w i) s)))
End

Theorem abi_decode_load_update:
  abi_decode_load opc p (update_var v w s) = abi_decode_load opc p s /\
  mload a (update_var v w s) = mload a s
Proof
  simp[abi_decode_load_def, abi_decode_source_def, mload_def, update_var_def]
QED

Theorem abi_decode_header_prefix:
  abi_decode_source_opcode opc /\ src <> Var iv /\ iv <> cv /\
  eval_operand ip s = SOME p /\ eval_operand src s = SOME srcaddr /\
  mload (w2n p) s = n2w i /\ abi_decode_load opc srcaddr s = n2w ncount /\
  i <= ncount /\ ncount < dimword(:256) ==>
  run_inst_seq (TAKE 4 (abi_decode_header_insts id ip src opc iv cv cmp done body_lbl exit)) s =
    OK (abi_decode_header_state iv cv cmp done i ncount s)
Proof
  strip_tac >>
  `eval_operand src (update_var iv (n2w i) s) = SOME srcaddr` by
    (Cases_on `src` >> gvs[eval_operand_def, lookup_var_update_var]) >>
  `step_inst_base (mk_inst id MLOAD [ip] [iv]) s =
     OK (update_var iv (n2w i) s)` by
    simp[Once step_inst_base_def, exec_read1_def, mk_inst_def] >>
  `step_inst_base (mk_inst (id+1) opc [src] [cv])
      (update_var iv (n2w i) s) =
     OK (update_var cv (n2w ncount) (update_var iv (n2w i) s))` by
    (drule_all abi_decode_read_step >> simp[abi_decode_load_update]) >>
  `i < dimword(:256)` by decide_tac >>
  simp[abi_decode_header_insts_def, run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_update_var, w2n_n2w] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_pure1_def,
       eval_operand_def, lookup_var_update_var, abi_decode_header_state_def] >>
  Cases_on `i < ncount` >> simp[bool_to_word_def]
QED

Theorem abi_decode_header_control:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  abi_decode_source_opcode opc /\ src <> Var iv /\ iv <> cv /\
  eval_operand ip s = SOME p /\ eval_operand src s = SOME srcaddr /\
  mload (w2n p) s = n2w i /\ abi_decode_load opc srcaddr s = n2w ncount /\
  i <= ncount /\ ncount < dimword(:256) ==>
  exec_block fuel ctx
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts id ip src opc iv cv cmp done body_lbl exit_lbl|> s =
    OK (jump_to (if i < ncount then body_lbl else exit_lbl)
      (abi_decode_header_state iv cv cmp done i ncount s))
Proof
  strip_tac >>
  `opc <> INVOKE /\ ~is_terminator opc` by
    gvs[abi_decode_source_opcode_def, is_terminator_def] >>
  drule_all abi_decode_header_prefix >> strip_tac >>
  qspecl_then [`TAKE 4 (abi_decode_header_insts id ip src opc iv cv cmp done body_lbl exit_lbl)`,
    `s`, `fuel`, `ctx`,
    `<|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts id ip src opc iv cv cmp done body_lbl exit_lbl|>`]
    mp_tac exec_block_run_inst_seq >>
  simp[abi_decode_header_insts_def, mk_inst_def, is_terminator_def,
       abi_decode_source_opcode_def] >>
  strip_tac >> simp[] >>
  simp[Once exec_block_def, get_instruction_def, abi_decode_header_insts_def] >>
  simp[step_inst_def, Once step_inst_base_def, mk_inst_def,
       abi_decode_header_state_def, eval_operand_def, lookup_var_update_var] >>
  Cases_on `i < ncount` >>
  simp[bool_to_word_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, jump_to_def, is_terminator_def]
QED

(* A control edge consumes one block of fuel, not the child's fuel. *)
Theorem abi_decode_edge_sim:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!f. exec_block f ctx bb s = OK t) /\ ~t.vs_halted /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 /\ t.vs_inst_idx = 0 ==>
  abi_decode_sim ctx fn s t
Proof
  strip_tac >> rw[abi_decode_sim_def] >> qexists_tac `SUC fuel` >>
  simp[run_from_def] >>
  drule_all run_blocks_run_from_no_phi >> simp[run_from_def]
QED

Definition abi_decode_backedge_insts_def:
  abi_decode_backedge_insts id iv nv ip hdr =
    [mk_inst id ADD [Var iv;Lit 1w] [nv];
     mk_inst (id+1) MSTORE [ip;Var nv] [];
     mk_inst (id+2) JMP [Label hdr] []]
End

Theorem abi_decode_increment_prefix:
  eval_operand (Var iv) s = SOME (n2w i) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ i < ncount /\ ncount < dimword(:256) ==>
  run_inst_seq (TAKE 2 (abi_decode_backedge_insts id iv nv ip hdr)) s =
    OK (mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) s))
Proof
  strip_tac >>
  `eval_operand ip (update_var nv (n2w (SUC i)) s) = SOME p` by
    (Cases_on `ip` >> gvs[eval_operand_def, lookup_var_update_var]) >>
  drule_all abi_decode_loop_increment_word >> strip_tac >>
  simp[abi_decode_backedge_insts_def, run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_write2_def,
       eval_operand_update_var, eval_operand_lit]
QED

Theorem abi_decode_backedge_control:
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w i) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ i < ncount /\ ncount < dimword(:256) ==>
  exec_block fuel ctx bb s =
    OK (jump_to hdr
      (mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) s)))
Proof
  strip_tac >> drule_all abi_decode_increment_prefix >> strip_tac >>
  qspecl_then [`TAKE 2 (abi_decode_backedge_insts id iv nv ip hdr)`,
    `s`, `fuel`, `ctx`, `bb`] mp_tac exec_block_run_inst_seq >>
  simp[abi_decode_backedge_insts_def, mk_inst_def, is_terminator_def,
       rich_listTheory.DROP_LENGTH_APPEND] >>
  strip_tac >> simp[] >>
  simp[Once exec_block_def, get_instruction_def, abi_decode_backedge_insts_def,
       listTheory.EL_APPEND_EQN] >>
  simp[step_inst_def, Once step_inst_base_def, mk_inst_def, is_terminator_def,
       jump_to_def, mstore_def, update_var_def]
QED

Theorem abi_decode_header_observations:
  abi_decode_footprint_frame fp s
    (abi_decode_header_state iv cv cmp done i ncount s) /\
  mload p (abi_decode_header_state iv cv cmp done i ncount s) = mload p s /\
  abi_decode_load opc srcaddr
    (abi_decode_header_state iv cv cmp done i ncount s) =
    abi_decode_load opc srcaddr s
Proof
  simp[abi_decode_header_state_def, abi_decode_footprint_frame_def,
       abi_decode_load_def, abi_decode_source_def, mload_def, update_var_def]
QED

Theorem abi_decode_header_sim:
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts id ip src opc iv cv cmp done body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  abi_decode_source_opcode opc /\ src <> Var iv /\ iv <> cv /\
  eval_operand ip s = SOME p /\ eval_operand src s = SOME srcaddr /\
  mload (w2n p) s = n2w i /\ abi_decode_load opc srcaddr s = n2w ncount /\
  i <= ncount /\ ncount < dimword(:256) ==>
  abi_decode_sim ctx fn s
    (jump_to (if i < ncount then body_lbl else exit_lbl)
      (abi_decode_header_state iv cv cmp done i ncount s))
Proof
  strip_tac >> irule abi_decode_edge_sim >>
  simp[jump_to_def, abi_decode_header_state_def, update_var_def] >>
  conj_tac
  >- (gen_tac >> drule_all abi_decode_header_control >>
      simp[jump_to_def, abi_decode_header_state_def, update_var_def]) >>
  Cases_on `i < ncount` >> simp[]
QED

Theorem abi_decode_backedge_sim:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w i) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ i < ncount /\ ncount < dimword(:256) ==>
  abi_decode_sim ctx fn s
    (jump_to hdr (mstore (w2n p) (n2w (SUC i))
      (update_var nv (n2w (SUC i)) s)))
Proof
  strip_tac >> irule abi_decode_edge_sim >>
  simp[jump_to_def, mstore_def, update_var_def] >>
  gen_tac >> drule_all abi_decode_backedge_control >>
  simp[jump_to_def, mstore_def, update_var_def]
QED

(* Loop-ready is an observation predicate, never an execution premise. *)
Definition abi_decode_loop_ready_def:
  abi_decode_loop_ready hdr ip src opc p srcaddr ncount j s <=>
    s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    eval_operand ip s = SOME p /\ eval_operand src s = SOME srcaddr /\
    mload (w2n p) s = n2w j /\ abi_decode_load opc srcaddr s = n2w ncount /\
    j <= ncount
End

Definition abi_decode_loop_cfg_def:
  abi_decode_loop_cfg fn hdr body_lbl exit_lbl id ip src opc iv cv cmp done <=>
    hdr <> body_lbl /\ hdr <> exit_lbl /\ body_lbl <> exit_lbl /\
    lookup_block hdr fn.fn_blocks = SOME
      <|bb_label := hdr; bb_instructions :=
        abi_decode_header_insts id ip src opc iv cv cmp done body_lbl exit_lbl|> /\
    (?bb. lookup_block body_lbl fn.fn_blocks = SOME bb /\
          phi_prefix_length bb.bb_instructions = 0) /\
    (?bb. lookup_block exit_lbl fn.fn_blocks = SOME bb /\
          phi_prefix_length bb.bb_instructions = 0)
End

Theorem abi_decode_ready_header_sim:
  abi_decode_loop_cfg fn hdr body_lbl exit_lbl id ip src opc iv cv cmp done /\
  abi_decode_loop_ready hdr ip src opc p srcaddr ncount j s /\
  abi_decode_source_opcode opc /\ src <> Var iv /\ iv <> cv /\
  ncount < dimword(:256) ==>
  abi_decode_sim ctx fn s
    (jump_to (if j < ncount then body_lbl else exit_lbl)
      (abi_decode_header_state iv cv cmp done j ncount s))
Proof
  strip_tac >>
  gvs[abi_decode_loop_cfg_def, abi_decode_loop_ready_def] >>
  irule abi_decode_header_sim >> simp[] >> metis_tac[]
QED

(* The child can end in a different block, and can use its own fuel. Only
   the actual ADD/MSTORE/JMP suffix is handled by this adapter. *)
Theorem abi_decode_child_backedge:
  frag_exec ctx st0 st1 B C (K F) /\ fn_has_code st0 st1 fn /\
  B s /\ ~s.vs_halted /\ s.vs_current_bb = st0.cs_current_bb /\
  s.vs_inst_idx = LENGTH st0.cs_current_insts /\
  lookup_block st1.cs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = st1.cs_current_insts ++
    abi_decode_backedge_insts id iv nv ip hdr /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  ip <> Var nv /\ j < ncount /\ ncount < dimword(:256) /\
  (!u. C u ==> ~u.vs_halted /\
    eval_operand (Var iv) u = SOME (n2w j) /\ eval_operand ip u = SOME p /\
    J (SUC j) (jump_to hdr (mstore (w2n p) (n2w (SUC j))
      (update_var nv (n2w (SUC j)) u)))) ==>
  ?t. J (SUC j) t /\ abi_decode_sim ctx fn s t
Proof
  strip_tac >> drule_all abi_decode_sim_from_fragment >> strip_tac >>
  rename1 `C u` >>
  `abi_decode_sim ctx fn u
    (jump_to hdr (mstore (w2n p) (n2w (SUC j))
      (update_var nv (n2w (SUC j)) u)))` by
    (irule abi_decode_backedge_sim >> simp[] >> metis_tac[]) >>
  metis_tac[abi_decode_sim_trans]
QED

Theorem abi_decode_shell_step:
  abi_decode_loop_cfg fn hdr body_lbl exit_lbl hid ip src opc hv cv cmp done /\
  abi_decode_loop_ready hdr ip src opc p srcaddr ncount j s /\
  abi_decode_source_opcode opc /\ src <> Var hv /\ hv <> cv /\
  ip <> Var nv /\ j < ncount /\ ncount < dimword(:256) /\
  st0.cs_current_bb = body_lbl /\ st0.cs_current_insts = [] /\
  frag_exec ctx st0 st1 B C (K F) /\ fn_has_code st0 st1 fn /\
  B (jump_to body_lbl (abi_decode_header_state hv cv cmp done j ncount s)) /\
  lookup_block st1.cs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = st1.cs_current_insts ++
    abi_decode_backedge_insts bid iv nv ip hdr /\
  (!u. C u ==> ~u.vs_halted /\
    eval_operand (Var iv) u = SOME (n2w j) /\ eval_operand ip u = SOME p /\
    J (SUC j) (jump_to hdr (mstore (w2n p) (n2w (SUC j))
      (update_var nv (n2w (SUC j)) u)))) ==>
  ?t. J (SUC j) t /\ abi_decode_sim ctx fn s t
Proof
  strip_tac >>
  `abi_decode_sim ctx fn s
    (jump_to body_lbl (abi_decode_header_state hv cv cmp done j ncount s))` by
    (drule_all abi_decode_ready_header_sim >> simp[]) >>
  `lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src opc hv cv cmp done body_lbl exit_lbl|>` by
    gvs[abi_decode_loop_cfg_def] >>
  `phi_prefix_length
    (abi_decode_header_insts hid ip src opc hv cv cmp done body_lbl exit_lbl) = 0` by
    simp[abi_decode_header_insts_def, phi_prefix_length_def, mk_inst_def] >>
  `(jump_to body_lbl (abi_decode_header_state hv cv cmp done j ncount s)).vs_current_bb =
      st0.cs_current_bb /\
    (jump_to body_lbl (abi_decode_header_state hv cv cmp done j ncount s)).vs_inst_idx =
      LENGTH st0.cs_current_insts` by simp[jump_to_def] >>
  `~(jump_to body_lbl
      (abi_decode_header_state hv cv cmp done j ncount s)).vs_halted` by
    fs[abi_decode_loop_ready_def, jump_to_def,
       abi_decode_header_state_def, update_var_def] >>
  `?t. J (SUC j) t /\ abi_decode_sim ctx fn
    (jump_to body_lbl (abi_decode_header_state hv cv cmp done j ncount s)) t` by
    (irule abi_decode_child_backedge >> simp[] >> conj_tac
     >- metis_tac[] >>
     qpat_assum `frag_exec ctx st0 st1 B C (K F)` (irule_at Any) >>
     simp[] >>
     irule_at Any EQ_REFL >> simp[] >> metis_tac[]) >>
  metis_tac[abi_decode_sim_trans]
QED

Theorem abi_decode_mload_jump:
  mload p (jump_to lbl s) = mload p s
Proof
  simp[mload_def, jump_to_def]
QED

Theorem abi_decode_backedge_observations:
  MEM (w2n p,32) fp ==>
  abi_decode_footprint_frame fp s
    (jump_to hdr (mstore (w2n p) w (update_var nv w s))) /\
  mload (w2n p) (jump_to hdr (mstore (w2n p) w (update_var nv w s))) = w
Proof
  strip_tac >> conj_tac
  >- (simp[abi_decode_footprint_frame_def, jump_to_def] >> conj_tac
      >- (rpt strip_tac >>
          irule EQ_TRANS >>
          irule_at Any valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
          simp[update_var_def] >>
          gvs[abi_footprint_disjoint_def] >> first_x_assum drule >> simp[]) >>
      simp[mstore_def, update_var_def]) >>
  simp[abi_decode_mload_jump, venomMemProofsTheory.mload_mstore_same_proof]
QED

(* Conditional finite shell: B/C are the separately proved body (address
   calculation plus recursive child) contracts. J carries the initialized
   prefix, unread source suffix and the output/scratch frame. *)
Theorem abi_decode_shell_sim:
  abi_decode_loop_cfg fn hdr body_lbl exit_lbl hid ip src opc hv cv cmp done /\
  abi_decode_source_opcode opc /\ src <> Var hv /\ hv <> cv /\ ip <> Var nv /\
  ncount < dimword(:256) /\ i <= ncount /\ J i s /\
  (!j u. J j u ==> abi_decode_loop_ready hdr ip src opc p srcaddr ncount j u) /\
  st0.cs_current_bb = body_lbl /\ st0.cs_current_insts = [] /\
  fn_has_code st0 st1 fn /\
  lookup_block st1.cs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = st1.cs_current_insts ++
    abi_decode_backedge_insts bid iv nv ip hdr /\
  (!j. j < ncount ==>
    frag_exec ctx st0 st1 (B j) (C j) (K F) /\
    (!u. J j u ==>
      B j (jump_to body_lbl (abi_decode_header_state hv cv cmp done j ncount u))) /\
    (!u. C j u ==> ~u.vs_halted /\
      eval_operand (Var iv) u = SOME (n2w j) /\ eval_operand ip u = SOME p /\
      J (SUC j) (jump_to hdr (mstore (w2n p) (n2w (SUC j))
        (update_var nv (n2w (SUC j)) u))))) ==>
  ?u. J ncount u /\ abi_decode_sim ctx fn s
    (jump_to exit_lbl (abi_decode_header_state hv cv cmp done ncount ncount u))
Proof
  strip_tac >>
  `!j u. J j u /\ j < ncount ==>
    ?v. J (SUC j) v /\ abi_decode_sim ctx fn u v` by
    (rpt strip_tac >>
     qpat_assum `!j. j < ncount ==> _` (qspec_then `j` mp_tac) >>
     (impl_tac >- decide_tac) >> strip_tac >>
     `abi_decode_loop_ready hdr ip src opc p srcaddr ncount j u` by metis_tac[] >>
     `B j (jump_to body_lbl (abi_decode_header_state hv cv cmp done j ncount u))`
       by metis_tac[] >>
     drule_all abi_decode_shell_step >> simp[]) >>
  `!u. J ncount u ==> ?v.
    (?w. J ncount w /\ v = jump_to exit_lbl
      (abi_decode_header_state hv cv cmp done ncount ncount w)) /\
    abi_decode_sim ctx fn u v` by
    (rpt strip_tac >>
     `abi_decode_loop_ready hdr ip src opc p srcaddr ncount ncount u` by metis_tac[] >>
     drule_all abi_decode_ready_header_sim >> simp[] >> strip_tac >>
     metis_tac[]) >>
  `?t. (?w. J ncount w /\ t = jump_to exit_lbl
      (abi_decode_header_state hv cv cmp done ncount ncount w)) /\
    abi_decode_sim ctx fn s t` suffices_by metis_tac[] >>
  ho_match_mp_tac abi_decode_finite_iteration >>
  qexistsl_tac [`ncount`,`i`,`J`] >> simp[]
QED

(* Packaging into the fragment interface. Code containment is purely static;
   recursive execution is demanded only for the body fragments, never for
   the whole loop. cs_extends supplies child containment in any containing fn. *)
Theorem abi_decode_shell_fragment:
  st_hdr.cs_current_bb = hdr /\ st_hdr.cs_current_insts = [] /\
  st_exit.cs_current_bb = exit_lbl /\ st_exit.cs_current_insts = [] /\
  cs_extends st_hdr st0 /\ cs_extends st0 st1 /\ cs_extends st1 st_exit /\
  st0.cs_current_bb = body_lbl /\ st0.cs_current_insts = [] /\
  (!fn. fn_has_code st_hdr st_exit fn ==>
    abi_decode_loop_cfg fn hdr body_lbl exit_lbl hid ip src opc hv cv cmp done /\
    ?bb. lookup_block st1.cs_current_bb fn.fn_blocks = SOME bb /\
      bb.bb_instructions = st1.cs_current_insts ++
        abi_decode_backedge_insts bid iv nv ip hdr) /\
  abi_decode_source_opcode opc /\ src <> Var hv /\ hv <> cv /\ ip <> Var nv /\
  ncount < dimword(:256) /\ i <= ncount /\
  (!j u. J j u ==> abi_decode_loop_ready hdr ip src opc p srcaddr ncount j u) /\
  (!j. j < ncount ==>
    frag_exec ctx st0 st1 (B j) (C j) (K F) /\
    (!u. J j u ==>
      B j (jump_to body_lbl (abi_decode_header_state hv cv cmp done j ncount u))) /\
    (!u. C j u ==> ~u.vs_halted /\
      eval_operand (Var iv) u = SOME (n2w j) /\ eval_operand ip u = SOME p /\
      J (SUC j) (jump_to hdr (mstore (w2n p) (n2w (SUC j))
        (update_var nv (n2w (SUC j)) u))))) ==>
  frag_exec ctx st_hdr st_exit (J i)
    (\t. ?u. J ncount u /\ t = jump_to exit_lbl
      (abi_decode_header_state hv cv cmp done ncount ncount u)) (K F)
Proof
  strip_tac >> simp[frag_exec_def] >> rpt strip_tac >>
  `fn_has_code st0 st1 fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `abi_decode_loop_cfg fn hdr body_lbl exit_lbl hid ip src opc hv cv cmp done /\
    ?bb. lookup_block st1.cs_current_bb fn.fn_blocks = SOME bb /\
      bb.bb_instructions = st1.cs_current_insts ++
        abi_decode_backedge_insts bid iv nv ip hdr` by metis_tac[] >>
  `?u. J ncount u /\ abi_decode_sim ctx fn s
    (jump_to exit_lbl (abi_decode_header_state hv cv cmp done ncount ncount u))` by
    (drule_all abi_decode_shell_sim >> simp[]) >>
  `~u.vs_halted` by metis_tac[abi_decode_loop_ready_def] >>
  qexists_tac `jump_to exit_lbl
    (abi_decode_header_state hv cv cmp done ncount ncount u)` >>
  simp[jump_to_def, abi_decode_header_state_def, update_var_def] >>
  qpat_x_assum `abi_decode_sim ctx fn s _` mp_tac >>
  simp[abi_decode_sim_def, jump_to_def,
       abi_decode_header_state_def, update_var_def] >> metis_tac[]
QED

(* These equations are exactly the header calls in
   compile_abi_decode_dyn_loop; output names and instruction IDs are not
   assumed. The emitted-shape lemmas pin them to the operational adapters. *)
Theorem abi_decode_emitted_header:
  emit_op MLOAD [ip] st0 = (iop,st1) /\
  emit_op opc [src] st1 = (cop,st2) /\
  emit_op LT [iop;cop] st2 = (test,st3) /\
  emit_op ISZERO [test] st3 = (done_op,st4) /\
  emit_inst JNZ [done_op;Label exit_lbl;Label body_lbl] [] st4 = ((),st5) ==>
  ?iv cv cmp done.
    iop = Var iv /\ cop = Var cv /\ test = Var cmp /\ done_op = Var done /\
    st5.cs_current_insts = st0.cs_current_insts ++
      abi_decode_header_insts st0.cs_next_id ip src opc iv cv cmp done body_lbl exit_lbl /\
    st5.cs_blocks = st0.cs_blocks /\ st5.cs_current_bb = st0.cs_current_bb
Proof
  simp[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[abi_decode_header_insts_def,
    listTheory.APPEND_ASSOC]
QED

Theorem abi_decode_emitted_backedge:
  emit_op ADD [Var iv;Lit 1w] st0 = (new_i,st1) /\
  emit_void MSTORE [ip;new_i] st1 = ((),st2) /\
  emit_inst JMP [Label hdr] [] st2 = ((),st3) ==>
  ?nv. new_i = Var nv /\ st3.cs_current_insts = st0.cs_current_insts ++
    abi_decode_backedge_insts st0.cs_next_id iv nv ip hdr /\
    st3.cs_blocks = st0.cs_blocks /\ st3.cs_current_bb = st0.cs_current_bb
Proof
  simp[emit_op_def, emit_void_def, emit_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[abi_decode_backedge_insts_def,
    listTheory.APPEND_ASSOC]
QED

(* Finished headers and child backedges remain present after later compiler
   work. This is the static containment premise used by shell_fragment. *)
Theorem abi_decode_finished_block_contained:
  new_block lbl st = (old,st1) /\ cs_extends st1 st2 /\
  fn_has_code st st2 fn ==>
  lookup_block st.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts|>
Proof
  strip_tac >>
  `cs_extends st st1` by metis_tac[cs_extends_new_block] >>
  `fn_has_code st st1 fn` by metis_tac[fn_has_code_split] >>
  gvs[new_block_def, fn_has_code_def, emitted_blocks_def]
QED

(* Outstanding recursive closure: B must be established by the emitted body
   address calculations at each index; C must supply the child's typed
   output and protect iv/ip/source operands and the index slot. J must retain
   initialized output prefix, unread memory-source suffix and a frame allowing
   allocated scratch. The index write must be disjoint from future source
   bytes/count; metadata compatibility and nonwrap/capacity obligations for
   each translated child remain required. These conditional shell results
   do not discharge any of those recursive obligations. *)

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_EXECUTION_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder execution boundary not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderExecution");
