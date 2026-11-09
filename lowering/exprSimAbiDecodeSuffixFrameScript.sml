Theory exprSimAbiDecodeSuffixFrame
Ancestors
  abiEncoderObserver venomExecProofs venomInstProofs venomExecSemantics
  venomState venomInst list finite_map pred_set arithmetic

Theorem abi_decode_step_output_frame:
  step_inst 0 ctx inst s = OK t /\ ~MEM x inst.inst_outputs ==>
  FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  Cases_on `is_terminator inst.inst_opcode` >> strip_tac
  >- (drule_all step_terminator_preserves_vars >> simp[lookup_var_def]) >>
  drule_all step_preserves_non_output_vars >> simp[lookup_var_def]
QED

Theorem abi_decode_phis_prefix_frame:
  !insts s t x. eval_phis s insts = OK t /\
  (!i. MEM i (TAKE (phi_prefix_length insts) insts) ==> ~MEM x i.inst_outputs) ==>
  FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  Induct >- simp[eval_phis_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI` >>
  simp[eval_phis_def, phi_prefix_length_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule eval_phis_only_updates_vs_vars >> strip_tac >>
  `~MEM x h.inst_outputs` by metis_tac[] >>
  drule eval_one_phi_output_mem >> strip_tac >>
  `out <> x` by metis_tac[] >>
  gvs[update_var_def, FLOOKUP_UPDATE] >>
  first_x_assum irule >> metis_tac[]
QED

Definition abi_decode_region_write_safe_def:
  abi_decode_region_write_safe ctx fn cut region protected <=>
    (!s bb inst. region s /\
      (s.vs_current_bb,s.vs_inst_idx) <> cut /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst ==>
      !x. x IN protected ==> ~MEM x inst.inst_outputs) /\
    (!s bb inst middle target entered.
      region s /\ (s.vs_current_bb,s.vs_inst_idx) <> cut /\
      ~s.vs_halted /\ inst.inst_opcode <> INVOKE /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      step_inst 0 ctx inst s = OK middle /\ is_terminator inst.inst_opcode /\
      ~middle.vs_halted /\
      lookup_block middle.vs_current_bb fn.fn_blocks = SOME target /\
      eval_phis middle target.bb_instructions = OK entered /\ ~entered.vs_halted ==>
      !i x. MEM i (TAKE (phi_prefix_length target.bb_instructions) target.bb_instructions) /\
        x IN protected ==> ~MEM x i.inst_outputs) /\
    (!s t. region s /\ abi_observer_step ctx fn cut s t ==> region t)
End

Theorem abi_decode_observer_step_var_frame:
  abi_decode_region_write_safe ctx fn cut region protected /\
  region s /\ abi_observer_step ctx fn cut s t ==>
  region t /\ !x. x IN protected ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_region_write_safe _ _ _ _ _`
    (CONJUNCTS_THEN2 (mk_asm "FETCH_SAFE")
      (CONJUNCTS_THEN2 (mk_asm "PHI_SAFE") (mk_asm "REGION_CLOSED")) o
     REWRITE_RULE [abi_decode_region_write_safe_def]) >>
  conj_tac
  >- (asm "REGION_CLOSED" drule >> simp[]) >>
  asm_x "REGION_CLOSED" kall_tac >> rpt strip_tac >>
  fs[abi_observer_step_def] >> gvs[]
  >- (asm_x "PHI_SAFE" kall_tac >>
      irule abi_decode_step_output_frame >>
      asm_x "FETCH_SAFE" mp_tac >> metis_tac[]) >>
  `FLOOKUP middle.vs_vars x = FLOOKUP s.vs_vars x` by
    (asm_x "PHI_SAFE" kall_tac >>
     irule abi_decode_step_output_frame >>
      asm_x "FETCH_SAFE" mp_tac >> metis_tac[]) >>
  asm_x "FETCH_SAFE" kall_tac >>
  `FLOOKUP entered.vs_vars x = FLOOKUP middle.vs_vars x` by
    (irule abi_decode_phis_prefix_frame >>
     qexists_tac `target.bb_instructions` >> simp[] >>
     asm_x "PHI_SAFE" mp_tac >> simp[] >> metis_tac[]) >> simp[]
QED

Theorem abi_decode_local_prefix_var_frame:
  !ctx fn cut s t. local_prefix ctx fn cut s t ==>
  !region protected.
    region s /\ abi_decode_region_write_safe ctx fn cut region protected ==>
    !x. x IN protected ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  ho_match_mp_tac local_prefix_ind >> conj_tac >- simp[] >>
  rpt strip_tac >> drule_all abi_decode_observer_step_var_frame >> strip_tac >>
  metis_tac[]
QED

Theorem abi_decode_local_prefix_stop_var_frame:
  local_prefix ctx fn cut s t /\ region s /\
  abi_decode_region_write_safe ctx fn cut region protected /\
  stop_view t = h /\ x IN protected ==>
  FLOOKUP h.vs_vars x = FLOOKUP s.vs_vars x
Proof
  strip_tac >> drule_all abi_decode_local_prefix_var_frame >>
  gvs[stop_view_def, halt_state_def]
QED
