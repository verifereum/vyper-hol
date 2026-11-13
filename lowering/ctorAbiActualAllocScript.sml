(* Ambient output separation is maintained at fresh and reused sites. *)
Theory ctorAbiActualAlloc
Ancestors
  ctorAbiActualFrame ctorAbiActualMemory actualAllocExec
  abiEncoderPrimitiveEffect abiEncoderRegisteredEffect
  abiDecoderIndexInit allocaFrontierBound allocaBudgetProps
  context compileEnv loweringStateRelDefs emitHelper emitHelperProps exprLoweringProps rich_list
  venomMemProps venomInstProofs1 abiDecoderReentry
  venomMemDefs venomState venomInst venomExecSemantics
  finite_map pred_set list arithmetic words

Theorem ctor_actual_scratch_fresh:
  ctor_actual_scratch fn ids d n s /\ d+n <= s.vs_alloca_next ==>
  ctor_actual_scratch fn ids d n
    (s with <|vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,32));
              vs_alloca_next := s.vs_alloca_next+32|>)
Proof
  simp_tac bool_ss [ctor_actual_scratch_def] >> strip_tac >>
  rpt gen_tac >> simp[FLOOKUP_UPDATE] >>
  Cases_on `inst.inst_id = id`
  >- (simp[] >> rpt strip_tac >> gvs[regions_disjoint_def]) >>
  simp[] >> metis_tac[]
QED

Theorem ctor_actual_scratch_update_var[simp]:
  ctor_actual_scratch fn ids d n (update_var x w s) <=>
  ctor_actual_scratch fn ids d n s
Proof
  simp[ctor_actual_scratch_def, update_var_def]
QED

Theorem ctor_actual_scratch_store[simp]:
  ctor_actual_scratch fn ids d n (mstore p w s) <=>
  ctor_actual_scratch fn ids d n s
Proof
  simp[ctor_actual_scratch_def]
QED

Theorem ctor_actual_word_alloca_run:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit 32w] /\ inst.inst_outputs = [out] /\
  inst.inst_id IN ids /\
  ctor_actual_scratch fn ids d n s /\ d+n <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  unit_alloca_budget ctx < dimword (:256) ==>
  ?t p.
    step_inst_base inst s = OK t /\
    eval_operand (Var out) t = SOME (n2w p) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (p,32) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    regions_disjoint (d,n) (p,32) /\
    ctor_actual_scratch fn ids d n t /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    abi_encoder_registered_effect ids outs s t /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (drule_all actual_word_alloca_fresh_run >> strip_tac >>
      `alloca_inv t` by (irule actual_alloca_slots_preserved >> metis_tac[]) >>
      `alloca_frontier_inv ctx fn site t` by
        (irule actual_alloca_frontier_preserved >> metis_tac[]) >>
      qexistsl [`t`, `s.vs_alloca_next`] >>
      simp[FLOOKUP_UPDATE] >>
      conj_tac
      >- simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      conj_tac >- simp[regions_disjoint_def] >>
      conj_tac >- (irule ctor_actual_scratch_fresh >> simp[]) >>
      simp[abi_encoder_registered_effect_def, update_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> Cases_on `i = inst.inst_id` >> gvs[]) >>
  PairCases_on `x` >>
  `x1 = 32 /\ regions_disjoint (d,n) (x0,x1)` by
    (gvs[ctor_actual_scratch_def] >> metis_tac[]) >>
  gvs[] >> drule_all actual_word_alloca_reuse_run >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  `alloca_inv t` by (irule actual_alloca_slots_preserved >> metis_tac[]) >>
  `alloca_frontier_inv ctx fn site t` by
    (irule actual_alloca_frontier_preserved >> metis_tac[]) >>
  qexistsl [`t`, `x0`] >> simp[] >>
  conj_tac >- simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  irule abi_encoder_registered_update_var
QED

Theorem ctor_actual_index_insts:
  abi_decode_index_init st = (ip,st') ==>
  emitted_insts st st' =
    [mk_inst st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString st.cs_next_var)];
     mk_inst (st.cs_next_id+1) MSTORE
       [Var (STRING #"%" (toString st.cs_next_var)); Lit 0w] []]
Proof
  simp[abi_decode_index_init_def, compile_alloc_buffer_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >> simp[DROP_LENGTH_APPEND]
QED

Theorem ctor_actual_index_slot_bound:
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP s.vs_allocas id = SOME (p,32) ==>
  p < dimword (:256)
Proof
  strip_tac >> drule_all alloca_frontier_inv_bound >> strip_tac >>
  `p+32 <= s.vs_alloca_next` by
    (gvs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >> decide_tac
QED

Theorem ctor_actual_index_sequence:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts fn)) /\
  st.cs_next_id IN ids /\
  ctor_actual_scratch fn ids d n s /\ d+n <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  unit_alloca_budget ctx < dimword (:256) ==>
  ?t p. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ctor_actual_scratch fn ids d n t /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    abi_encoder_registered_effect ids outs s t /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >> drule ctor_actual_index_insts >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]` >>
  `MEM inst (fn_insts fn)` by (first_x_assum irule >> simp[Abbr `inst`]) >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
   inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
   inst.inst_id IN ids` by simp[Abbr `inst`, mk_inst_def] >>
  drule_all ctor_actual_word_alloca_run >>
  disch_then (qspec_then `outs` strip_assume_tac) >>
  rename1 `step_inst_base inst s = OK allocated` >>
  `p < dimword (:256)` by (irule ctor_actual_index_slot_bound >> metis_tac[mk_inst_def]) >>
  `run_inst_seq (emitted_insts st st') s = OK (mstore p 0w allocated)` by
    (qpat_x_assum `step_inst_base inst s = OK allocated` mp_tac >>
     simp_tac bool_ss [Abbr `inst`] >> strip_tac >>
     asm_simp_tac bool_ss [run_inst_seq_def] >>
     simp[step_inst_base_opcode_eqs, exec_write2_def, mk_inst_def,
       eval_operand_def, w2n_n2w]) >>
  `abi_encoder_registered_effect ids outs allocated (mstore p 0w allocated)` by
    (irule abi_encoder_registered_slot_store >>
     qexists `st.cs_next_id` >> gvs[Abbr `inst`, mk_inst_def]) >>
  qexistsl [`mstore p 0w allocated`, `p`] >>
  simp[abi_decoder_operand_mstore, mload_mstore_same,
       abi_encoder_primitive_alloca_inv] >>
  conj_tac >- gvs[Abbr `inst`, mk_inst_def] >>
  irule abi_encoder_registered_effect_trans >> goal_assum (drule_at Any) >> simp[]
QED

Theorem ctor_actual_sequence_var_frame:
  !code s t x.
    run_inst_seq code s = OK t /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ ~MEM x i.inst_outputs) code ==>
    lookup_var x t = lookup_var x s
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >>
  drule_all step_inst_base_preserves_all >> strip_tac >>
  qpat_x_assum `!s t x. _` drule_all >> strip_tac >> metis_tac[]
QED

Theorem ctor_actual_index_var_frame:
  abi_decode_index_init st = (ip,st') /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s) /\
  t.vs_halted = s.vs_halted
Proof
  strip_tac >> drule ctor_actual_index_insts >> strip_tac >>
  `!x. x <> STRING #"%" (toString st.cs_next_var) ==>
       lookup_var x t = lookup_var x s` by
    (rpt strip_tac >> irule ctor_actual_sequence_var_frame >>
     qexists `emitted_insts st st'` >> simp[mk_inst_def, is_terminator_def]) >>
  `t.vs_labels = s.vs_labels` by
    (irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_labels` run_inst_seq_preserves_field)) >>
     qexists `emitted_insts st st'` >> simp[] >> rpt strip_tac >>
     `~is_terminator i.inst_opcode` by gvs[mk_inst_def, is_terminator_def] >>
     drule_all step_inst_base_preserves_all >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  conj_tac
  >- (Cases >> simp[abi_decoder_operand_live_def, eval_operand_def] >>
      strip_tac >> first_x_assum irule >>
      gvs[abi_decoder_older_vars_def] >> metis_tac[LESS_EQ_REFL]) >>
  irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_halted` run_inst_seq_preserves_field)) >>
  qexists `emitted_insts st st'` >> simp[] >> rpt strip_tac >>
  `~is_terminator i.inst_opcode` by gvs[mk_inst_def, is_terminator_def] >>
  drule_all step_inst_base_preserves_all >> simp[]
QED
