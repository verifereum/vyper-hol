(* Memory checks and real-state transport for decoder reentry. *)
Theory abiDecodeMemReentry
Ancestors
  abiDecodeMemSequenceReentry abiDecoderVarExtend abiDecoderVarSequence
  abiDecoderReentry fragGasPathMem fragGasSeqMem
  execEquivParamProps execEquivParamDefs codegenRel contextCodegenRel memSafeRun unitTransformDefs
  abiEncoderVarTransport abiEncoderExtendControl opcodeClass venomExecSemantics venomState venomInst finite_map list

Theorem abi_decode_reentry_edge_check[local]:
  abi_decoder_vars_extend extras s t /\ abi_decoder_inputs_defined inst s /\
  abi_decoder_reentry_opcode inst.inst_opcode /\
  (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step fuel ctx inst s) ==>
  (revert_forward_at bb t.vs_inst_idx \/ mem_safe_step 0 ctx inst t)
Proof
  strip_tac >> drule_all abi_encoder_vars_extend_control >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by metis_tac[abi_decoder_reentry_non_invoke] >>
  drule_all abi_decode_reentry_memory_checks >> strip_tac >>
  fs[mem_safe_step_non_invoke]
QED

Theorem abi_decode_reentry_edge_next[local]:
  abi_decoder_vars_extend extras s t /\ abi_decoder_reentry_opcode inst.inst_opcode /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step fuel ctx inst s) /\
  ~is_terminator inst.inst_opcode /\ step_inst_base inst s = OK u ==>
  ?v. gas_path_mem_edge ctx fn t 0 (OK v) /\
      abi_decoder_vars_extend extras (u with vs_inst_idx := SUC s.vs_inst_idx) v
Proof
  strip_tac >> drule abi_encoder_vars_extend_control >> strip_tac >>
  drule_all abi_decoder_step_inputs_defined >> strip_tac >>
  `revert_forward_at bb t.vs_inst_idx \/ mem_safe_step 0 ctx inst t`
    by (irule abi_decode_reentry_edge_check >> simp[] >> metis_tac[]) >>
  drule_all abi_decoder_step_vars_extend >> strip_tac >>
  rename1 `step_inst_base inst t = OK large` >>
  drule_all abi_encoder_vars_extend_control >> strip_tac >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS` by
    fs[abi_decoder_reentry_opcode_def] >>
  `~large.vs_halted` by metis_tac[venomInstProofsTheory.step_preserves_halted,
    step_inst_non_invoke] >>
  qexists_tac `large with vs_inst_idx := SUC s.vs_inst_idx` >>
  reverse conj_tac >- (metis_tac[abi_encoder_vars_extend_idx]) >>
  fs[] >> simp[gas_path_mem_edge_def, step_inst_non_invoke,
    gasCountTheory.gas_count_step_def] >>
  metis_tac[abi_encoder_vars_extend_idx]
QED

Theorem abi_decode_reentry_edge_enter[local]:
  abi_decoder_vars_extend extras s t /\ abi_decoder_reentry_opcode inst.inst_opcode /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step fuel ctx inst s) /\
  is_terminator inst.inst_opcode /\ step_inst_base inst s = OK u /\
  ~u.vs_halted /\ lookup_block u.vs_current_bb fn.fn_blocks = SOME target /\
  eval_phis u target.bb_instructions = OK entered /\ ~entered.vs_halted ==>
  ?v. gas_path_mem_edge ctx fn t 0 (OK v) /\
      abi_decoder_vars_extend extras
        (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) v
Proof
  strip_tac >> drule abi_encoder_vars_extend_control >> strip_tac >>
  drule_all abi_decoder_step_inputs_defined >> strip_tac >>
  `revert_forward_at bb t.vs_inst_idx \/ mem_safe_step 0 ctx inst t`
    by (irule abi_decode_reentry_edge_check >> simp[] >> metis_tac[]) >>
  drule_all abi_decoder_step_vars_extend >> strip_tac >>
  rename1 `step_inst_base inst t = OK large` >>
  drule_all abi_encoder_phis_extend >> strip_tac >>
  rename1 `eval_phis large target.bb_instructions = OK large_entered` >>
  `~large.vs_halted /\ large.vs_current_bb = u.vs_current_bb /\
   ~large_entered.vs_halted` by metis_tac[abi_encoder_vars_extend_control] >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS` by
    fs[abi_decoder_reentry_opcode_def] >>
  qexists_tac `large_entered with vs_inst_idx := phi_prefix_length target.bb_instructions` >>
  (reverse conj_tac >- metis_tac[abi_encoder_vars_extend_idx] >>
   fs[] >> simp[gas_path_mem_edge_def] >>
   qexists_tac `0` >>
   simp[step_inst_non_invoke, gasCountTheory.gas_count_step_def] >>
   disj1_tac >> qexists_tac `target` >> simp[])
QED

Theorem abi_decode_reentry_step_jump[local]:
  abi_decoder_vars_extend extras s t /\ abi_decoder_reentry_opcode inst.inst_opcode /\
  is_terminator inst.inst_opcode /\ step_inst_base inst s = OK (jump_to lbl s) ==>
  step_inst_base inst t = OK (jump_to lbl t)
Proof
  strip_tac >> drule_all abi_decoder_step_inputs_defined >> strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t`
    by metis_tac[abi_decode_reentry_operand_agreement] >>
  Cases_on `inst.inst_opcode` >>
  gvs[abi_decoder_reentry_opcode_def, is_terminator_def] >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  gvs[jump_to_def, venom_state_component_equality]
QED

Theorem abi_decode_reentry_edge_jump[local]:
  abi_decoder_vars_extend extras s t /\ abi_decoder_reentry_opcode inst.inst_opcode /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step fuel ctx inst s) /\
  is_terminator inst.inst_opcode /\ step_inst_base inst s = OK (jump_to lbl s) ==>
  gas_path_mem_edge ctx fn t 0 (OK (jump_to lbl t)) /\
  abi_decoder_vars_extend extras (jump_to lbl s) (jump_to lbl t)
Proof
  strip_tac >> drule abi_encoder_vars_extend_control >> strip_tac >>
  drule_all abi_decoder_step_inputs_defined >> strip_tac >>
  `revert_forward_at bb t.vs_inst_idx \/ mem_safe_step 0 ctx inst t`
    by (irule abi_decode_reentry_edge_check >> simp[] >> metis_tac[]) >>
  drule_all abi_decode_reentry_step_jump >> strip_tac >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS` by
    fs[abi_decoder_reentry_opcode_def] >>
  (reverse conj_tac >- metis_tac[abi_encoder_vars_extend_jump] >>
   fs[] >> simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
   simp[step_inst_non_invoke, gasCountTheory.gas_count_step_def] >>
   metis_tac[])
QED

Theorem abi_decode_reentry_edge_revert[local]:
  abi_decoder_vars_extend extras s t /\ abi_decoder_reentry_opcode inst.inst_opcode /\
  abi_decoder_inputs_defined inst s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step fuel ctx inst s) /\
  step_inst_base inst s = Abort Revert_abort u ==>
  ?v. gas_path_mem_edge ctx fn t 0 (Abort Revert_abort v) /\
      abi_decoder_vars_extend extras u v
Proof
  strip_tac >> drule abi_encoder_vars_extend_control >> strip_tac >>
  `revert_forward_at bb t.vs_inst_idx \/ mem_safe_step 0 ctx inst t`
    by (irule abi_decode_reentry_edge_check >> simp[] >> metis_tac[]) >>
  drule_all abi_decode_reentry_revert >> strip_tac >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS` by
    fs[abi_decoder_reentry_opcode_def] >>
  goal_assum (drule_at Any) >>
  fs[] >> simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
  simp[step_inst_non_invoke, gasCountTheory.gas_count_step_def, fragExecTheory.exit_result_def]
QED

Theorem abi_decode_reentry_edge_ok[local]:
  abi_decoder_vars_extend extras s t /\
  (!bb inst. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst ==>
    abi_decoder_reentry_opcode inst.inst_opcode) /\
  gas_path_mem_edge ctx fn s 0 (OK u) ==>
  ?v. gas_path_mem_edge ctx fn t 0 (OK v) /\ abi_decoder_vars_extend extras u v
Proof
  strip_tac >> qpat_x_assum `gas_path_mem_edge _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [gas_path_mem_edge_def]) >>
  `abi_decoder_reentry_opcode inst.inst_opcode` by metis_tac[] >>
  `inst.inst_opcode <> INVOKE` by metis_tac[abi_decoder_reentry_non_invoke] >>
  gvs[step_inst_non_invoke, fragExecTheory.exit_result_def]
  >>~- ([`~is_terminator inst.inst_opcode`],
     irule abi_decode_reentry_edge_next >> metis_tac[])
  >>~- ([`eval_phis _ _ = OK _`],
     irule abi_decode_reentry_edge_enter >> metis_tac[])
  >>~- ([`step_inst_base inst s = OK (jump_to lbl s)`],
     qexists_tac `jump_to lbl t` >> irule abi_decode_reentry_edge_jump >> metis_tac[])
  >> metis_tac[fragExecTheory.exit_result_def]
QED

Theorem abi_decode_reentry_edge_abort[local]:
  abi_decoder_vars_extend extras s t /\
  (!bb inst. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst ==>
    abi_decoder_reentry_opcode inst.inst_opcode /\ abi_decoder_inputs_defined inst s) /\
  gas_path_mem_edge ctx fn s 0 (Abort Revert_abort u) ==>
  ?v. gas_path_mem_edge ctx fn t 0 (Abort Revert_abort v) /\
      abi_decoder_vars_extend extras u v
Proof
  strip_tac >> qpat_x_assum `gas_path_mem_edge _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [gas_path_mem_edge_def]) >>
  `abi_decoder_reentry_opcode inst.inst_opcode /\ abi_decoder_inputs_defined inst s`
    by metis_tac[] >>
  `inst.inst_opcode <> INVOKE` by metis_tac[abi_decoder_reentry_non_invoke] >>
  gvs[step_inst_non_invoke] >>
  irule abi_decode_reentry_edge_revert >> metis_tac[]
QED

Theorem abi_decode_reentry_path_invariant[local]:
  (!ctx fn s n r. gas_path_mem ctx fn s n r ==>
    n = 0 ==> P s ==>
    (!a b. P a /\ gas_path_mem_edge ctx fn a 0 (OK b) ==> P b) ==>
    (!a b t. P a /\ gas_path_mem_edge ctx fn a 0 (OK b) /\
      abi_decoder_vars_extend extras a t ==>
      ?v. gas_path_mem_edge ctx fn t 0 (OK v) /\ abi_decoder_vars_extend extras b v) ==>
    (!a b t. P a /\ gas_path_mem_edge ctx fn a 0 (Abort Revert_abort b) /\
      abi_decoder_vars_extend extras a t ==>
      ?v. gas_path_mem_edge ctx fn t 0 (Abort Revert_abort v) /\
          abi_decoder_vars_extend extras b v) ==>
    !t. abi_decoder_vars_extend extras s t ==>
      (!u. r = OK u ==> ?v. gas_path_mem ctx fn t 0 (OK v) /\
          abi_decoder_vars_extend extras u v) /\
      (!u. r = Abort Revert_abort u ==> ?v. gas_path_mem ctx fn t 0 (Abort Revert_abort v) /\
          abi_decoder_vars_extend extras u v))
Proof
  ho_match_mp_tac gas_path_mem_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >>
      metis_tac[gas_path_mem_rules, abi_encoder_vars_extend_control])
  >- (rpt strip_tac >> gvs[] >>
      `P s''` by metis_tac[] >>
      qpat_assum `!a b t. P a /\ gas_path_mem_edge ctx fn a 0 (OK b) /\
        abi_decoder_vars_extend extras a t ==> _`
        (drule_all_then strip_assume_tac) >>
      qpat_x_assum `P s'' ==> _` (drule_all_then mp_tac) >>
      strip_tac >>
      goal_assum (drule_at Any) >>
      drule (cj 2 gas_path_mem_rules) >> disch_then drule >> simp[])
  >> rpt strip_tac >> gvs[] >>
  metis_tac[gas_path_mem_rules, fragExecTheory.exit_result_def]
QED

Theorem abi_decode_reentry_path:
  P s /\ gas_path_mem ctx fn s 0 r /\ abi_decoder_vars_extend extras s t /\
  (!a b. P a /\ gas_path_mem_edge ctx fn a 0 (OK b) ==> P b) /\
  (!a bb inst. P a /\ lookup_block a.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb a.vs_inst_idx = SOME inst ==>
    abi_decoder_reentry_opcode inst.inst_opcode /\ abi_decoder_inputs_defined inst a) ==>
  (!u. r = OK u ==> ?v. gas_path_mem ctx fn t 0 (OK v) /\
      abi_decoder_vars_extend extras u v) /\
  (!u. r = Abort Revert_abort u ==> ?v. gas_path_mem ctx fn t 0 (Abort Revert_abort v) /\
      abi_decoder_vars_extend extras u v)
Proof
  strip_tac >> irule abi_decode_reentry_path_invariant >>
  qexistsl_tac [`P`, `0`, `s`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> irule abi_decode_reentry_edge_ok >> metis_tac[]) >>
  reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >> drule abi_decode_reentry_edge_abort >>
  disch_then irule >> metis_tac[]
QED

Theorem abi_decode_pruned_reentry_path:
  P (abi_decoder_prune_vars next s) /\
  gas_path_mem ctx fn (abi_decoder_prune_vars next s) 0 r /\
  (!a b. P a /\ gas_path_mem_edge ctx fn a 0 (OK b) ==> P b) /\
  (!a bb inst. P a /\ lookup_block a.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb a.vs_inst_idx = SOME inst ==>
    abi_decoder_reentry_opcode inst.inst_opcode /\ abi_decoder_inputs_defined inst a) ==>
  (!u. r = OK u ==> ?v. gas_path_mem ctx fn s 0 (OK v) /\
      abi_decoder_vars_extend s.vs_vars u v) /\
  (!u. r = Abort Revert_abort u ==> ?v. gas_path_mem ctx fn s 0 (Abort Revert_abort v) /\
      abi_decoder_vars_extend s.vs_vars u v)
Proof
  strip_tac >> irule abi_decode_reentry_path >>
  qexistsl_tac [`P`, `abi_decoder_prune_vars next s`] >>
  simp[abi_decoder_prune_extension] >> metis_tac[]
QED
