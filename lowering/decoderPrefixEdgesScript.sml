(* Continuation-independent safety for exact decoder shell edges. *)
Theory decoderPrefixEdges
Ancestors
  calldataDynStep memSafeRun venomExecSemantics venomState
  abiDecoderExecution abiDecoderContract abiDecoderGuards

Theorem decoder_edge_all_fuel_pullback:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!f. exec_block f ctx bb s = OK t) /\
  (!f. mem_safe_block f ctx bb s) /\ ~t.vs_halted /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 /\ t.vs_inst_idx = 0 ==>
  ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s)
Proof
  strip_tac >> strip_tac >>
  `t with vs_inst_idx := 0 = t` by (Cases_on `t` >> gvs[]) >>
  `eval_phis t next_bb.bb_instructions = OK t` by
    (Cases_on `next_bb.bb_instructions` >>
     gvs[phi_prefix_length_def, eval_phis_def] >>
     Cases_on `h.inst_opcode = PHI` >> gvs[]) >>
  `!fuel. mem_safe_blocks fuel ctx fn t` by
    (Cases >- simp[Once mem_safe_blocks_def] >>
     drule_all mem_safe_blocks_run >>
     disch_then (qspecl_then [`n`, `ctx`] mp_tac) >>
     asm_rewrite_tac[]) >>
  simp[mem_safe_run_def]
QED

Theorem calldata_header_all_fuel_pullback:
  lookup_block s.vs_current_bb fn.fn_blocks =
    SOME <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts id ip src CALLDATALOAD iv cv cmp done body_lbl exit_lbl|> /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  src <> Var iv /\ iv <> cv /\
  eval_operand ip s = SOME p /\ eval_operand src s = SOME srcaddr /\
  mload (w2n p) s = n2w j /\
  abi_decode_load CALLDATALOAD srcaddr s = n2w n /\
  j <= n /\ n < dimword (:256) /\ w2n p+32 <= s.vs_alloca_next /\
  lookup_block (if j<n then body_lbl else exit_lbl) fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 /\
  t = jump_to (if j<n then body_lbl else exit_lbl)
        (abi_decode_header_state iv cv cmp done j n s) ==>
  ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s)
Proof
  strip_tac >>
  ho_match_mp_tac (GEN_ALL decoder_edge_all_fuel_pullback) >>
  goal_assum (drule_at (Pos hd)) >>
  qexists_tac `next_bb` >> conj_tac
  >- (gen_tac >> asm_rewrite_tac[] >> irule abi_decode_header_control >>
      simp[abi_decode_source_opcode_def] >> metis_tac[]) >>
  conj_tac
  >- (gen_tac >> irule calldata_header_block_safe >> metis_tac[]) >>
  gvs[jump_to_def, abi_decode_header_state_def, update_var_def]
QED

Theorem calldata_backedge_all_fuel_pullback:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ j < n /\ n < dimword (:256) /\
  w2n p+32 <= s.vs_alloca_next /\
  lookup_block hdr fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 /\
  t = jump_to hdr
        (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)) ==>
  ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s)
Proof
  strip_tac >>
  ho_match_mp_tac (GEN_ALL decoder_edge_all_fuel_pullback) >>
  goal_assum (drule_at (Pos hd)) >>
  qexists_tac `next_bb` >> conj_tac
  >- (gen_tac >> asm_rewrite_tac[] >> irule abi_decode_backedge_control >>
      metis_tac[]) >>
  conj_tac
  >- (gen_tac >> irule calldata_backedge_block_safe >> metis_tac[]) >>
  gvs[jump_to_def, mstore_def, update_var_def]
QED
