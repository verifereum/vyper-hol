Theory abiAllocationHistory
Ancestors
  venomExecSemantics venomExecProps venomMemProofs venomState venomInst exprLoweringProps
  finite_map list relation words abiDecoderCode abiDecoderAllocation localPtrsProps
  loweringMemSafetyDefs pred_set venomInstProofs1 abiAllocationInvariant
  abiScratchDecodeResources abiScratchDecodeInput abiBuiltinAllocation abiBuiltinDecodeSetup
  venomMemDefs compileEnv arithmetic

(* ===== Allocation History ===== *)

(* Allocation records are justified by instructions that have actually run.
   TOP-LEVEL: abi_alloca_history_sequence preserves partial allocation history
   through actual successful execution; fresh sites need no runtime entry. *)

Definition abi_alloca_history_def:
  abi_alloca_history code s <=>
    !id off sz. FLOOKUP s.vs_allocas id = SOME (off,sz) ==>
      ?inst n. MEM inst code /\ inst.inst_id = id /\
        inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit n] /\
        sz = w2n n
End

Theorem abi_alloca_history_empty:
  s.vs_allocas = FEMPTY ==> abi_alloca_history code s
Proof
  simp[abi_alloca_history_def]
QED

Theorem abi_alloca_history_frame:
  abi_alloca_history code s /\ t.vs_allocas = s.vs_allocas ==>
  abi_alloca_history code t
Proof
  simp[abi_alloca_history_def]
QED

Theorem abi_alloca_history_alloca:
  abi_alloca_history code s /\ MEM inst code /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit n] /\
  exec_alloca inst s n = OK t ==>
  abi_alloca_history code t
Proof
  simp[exec_alloca_def, AllCaseEqs(), LET_THM] >> rpt strip_tac >>
  gvs[abi_alloca_history_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem abi_alloca_history_non_alloca:
  abi_alloca_history code s /\ step_inst_base inst s = OK t /\
  inst.inst_opcode <> ALLOCA ==> abi_alloca_history code t
Proof
  strip_tac >> drule step_inst_base_OK_not_INVOKE >> strip_tac >>
  mp_tac (Q.SPECL [`inst`, `s`, `t`] step_inst_base_preserves_alloca_fields) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all abi_alloca_history_frame >> simp[]
QED

Theorem abi_alloca_history_step:
  abi_alloca_history code s /\ MEM inst code /\
  step_inst_base inst s = OK t ==> abi_alloca_history code t
Proof
  Cases_on `inst.inst_opcode = ALLOCA` >> strip_tac
  >- (qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
      asm_simp_tac (srw_ss()) [Once step_inst_base_def, AllCaseEqs()] >>
      strip_tac >> gvs[] >> drule_all abi_alloca_history_alloca >> simp[]) >>
  drule_all abi_alloca_history_non_alloca >> simp[]
QED

Theorem abi_alloca_history_sequence:
  !insts s t code.
  run_inst_seq insts s = OK t /\ abi_alloca_history code s /\
  (!inst. MEM inst insts ==> MEM inst code) ==>
  abi_alloca_history code t
Proof
  Induct_on `insts` >- simp[run_inst_seq_def] >>
  rpt gen_tac >> rename1 `run_inst_seq (inst::rest) initial = OK final` >>
  simp_tac bool_ss [Once run_inst_seq_def] >>
  Cases_on `step_inst_base inst initial` >> simp[] >> strip_tac >>
  rename1 `step_inst_base inst initial = OK middle` >>
  `abi_alloca_history code middle` by
    (irule abi_alloca_history_step >> qexistsl_tac [`inst`, `initial`] >>
     simp[]) >>
  first_x_assum (qspecl_then [`middle`, `final`, `code`] mp_tac) >>
  simp[]
QED

Theorem abi_alloca_history_reachable:
  !s t. RTC (\s t. ?inst. MEM inst code /\ step_inst_base inst s = OK t) s t ==>
    abi_alloca_history code s ==> abi_alloca_history code t
Proof
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac >>
  drule_all abi_alloca_history_step >> strip_tac >>
  first_x_assum irule >> simp[]
QED

(* ===== Code ===== *)

(* Derive declared sizes for existing runtime allocations, including reused
   decoder sites. Allocation history is partial: unexecuted sites are absent. *)

Theorem abi_alloca_history_function_size:
  abi_alloca_history (fn_insts func) s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_operands = [Lit n] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (off,sz) ==> sz = w2n n
Proof
  strip_tac >>
  qhdtm_x_assum `abi_alloca_history`
    (mp_tac o PURE_REWRITE_RULE [abi_alloca_history_def]) >>
  disch_then (qspecl_then [`inst.inst_id`, `off`, `sz`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `MEM witness (fn_insts func)` >>
  `witness = inst` by (drule_all fn_inst_ids_distinct_inj >> simp[]) >>
  gvs[]
QED

Theorem abi_alloca_history_code_sizes:
  abi_alloca_history code s /\
  (!inst. MEM inst code /\ inst.inst_id IN ids /\ inst.inst_opcode = ALLOCA ==>
    inst.inst_operands = [Lit 32w]) ==>
  !id off sz. id IN ids /\ FLOOKUP s.vs_allocas id = SOME (off,sz) ==> sz = 32
Proof
  simp_tac bool_ss [abi_alloca_history_def] >> rpt strip_tac >>
  qpat_x_assum `!id off sz. _` drule >> strip_tac >> gvs[] >>
  qpat_x_assum `!inst. _` drule_all >>
  simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem abi_alloca_history_decoder_sizes:
  abi_alloca_history code s /\ abi_decoder_code start end_st /\
  (!inst. MEM inst code /\ start.cs_next_id <= inst.inst_id /\
    inst.inst_id < end_st.cs_next_id ==> abi_decoder_code_member inst end_st) /\
  (!inst. abi_decoder_code_member inst start ==> inst.inst_id < start.cs_next_id) ==>
  !id off sz. id IN abi_decoder_ids start.cs_next_id end_st.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (off,sz) ==> sz = 32
Proof
  strip_tac >>
  match_mp_tac (Q.INST [`code` |-> `code`,
    `ids` |-> `abi_decoder_ids start.cs_next_id end_st.cs_next_id`]
    abi_alloca_history_code_sizes) >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >>
  `abi_decoder_code_member inst end_st` by
    (qpat_x_assum `!inst. MEM inst code /\ _ ==> _` irule >>
     fs[abi_decoder_ids_def]) >>
  `~abi_decoder_code_member inst start` by
    (strip_tac >> qpat_x_assum `!inst. abi_decoder_code_member inst start ==> _`
      drule >> fs[abi_decoder_ids_def]) >>
  drule_all abi_decoder_code_alloca >> simp[]
QED

Theorem abi_alloca_history_blocks_member:
  !blocks. MEM bb blocks /\ MEM inst bb.bb_instructions ==>
  MEM inst (fn_insts_blocks blocks)
Proof
  Induct >> simp[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem abi_alloca_history_fn_member:
  MEM bb func.fn_blocks /\ MEM inst bb.bb_instructions ==>
  MEM inst (fn_insts func)
Proof
  simp[fn_insts_def] >> metis_tac[abi_alloca_history_blocks_member]
QED

Theorem abi_alloca_history_function_reachable:
  reachable_by_execution func s t /\ abi_alloca_history (fn_insts func) s ==>
  abi_alloca_history (fn_insts func) t
Proof
  simp_tac bool_ss [reachable_by_execution_def] >> strip_tac >>
  irule abi_alloca_history_reachable >> qexists_tac `s` >> simp[] >>
  qpat_x_assum `RTC _ s t` mp_tac >>
  match_mp_tac RTC_MONOTONE >> simp_tac bool_ss [] >> rpt strip_tac >>
  qexists_tac `inst` >> simp[] >>
  drule_all abi_alloca_history_fn_member >> simp[]
QED

Theorem abi_alloca_history_function_initial:
  reachable_by_execution func s t /\ s.vs_allocas = FEMPTY ==>
  abi_alloca_history (fn_insts func) t
Proof
  strip_tac >> irule abi_alloca_history_function_reachable >>
  qexists_tac `s` >> simp[abi_alloca_history_empty]
QED

(* ===== Run ===== *)

(* Successful calls restore the caller allocation map. Partial allocation
   history therefore survives actual step_inst execution, including INVOKE. *)

Theorem abi_alloca_history_bind_outputs:
  bind_outputs outs vals s = SOME t ==> t.vs_allocas = s.vs_allocas
Proof
  mp_tac (Q.ISPEC `\s:venom_state. s.vs_allocas` bind_outputs_preserves) >>
  simp[update_var_def] >>
  disch_then (qspecl_then [`outs`, `vals`, `s`, `t`] ACCEPT_TAC)
QED

Theorem abi_alloca_history_invoke:
  inst.inst_opcode = INVOKE /\ step_inst fuel ctx inst s = OK t ==>
  t.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  gvs[Once step_inst_def, AllCaseEqs()] >>
  drule abi_alloca_history_bind_outputs >>
  simp[merge_callee_state_def]
QED

Theorem abi_alloca_history_step_inst:
  abi_alloca_history code s /\ MEM inst code /\
  step_inst fuel ctx inst s = OK t ==> abi_alloca_history code t
Proof
  Cases_on `inst.inst_opcode = INVOKE` >> strip_tac
  >- (drule_all abi_alloca_history_invoke >> strip_tac >>
      drule_all abi_alloca_history_frame >> simp[]) >>
  `step_inst_base inst s = OK t` by gvs[step_inst_non_invoke] >>
  drule_all abi_alloca_history_step >> simp[]
QED

Theorem abi_alloca_history_step_reachable:
  !s t. RTC (\s t. ?fuel inst. MEM inst code /\
    step_inst fuel ctx inst s = OK t) s t ==>
    abi_alloca_history code s ==> abi_alloca_history code t
Proof
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac >>
  drule_all abi_alloca_history_step_inst >> strip_tac >>
  first_x_assum irule >> simp[]
QED

(* ===== Resources ===== *)

(* Physical decoder resources from actual execution history and a code-size
   certificate. Numeric credit and live-buffer ownership remain explicit. *)

Theorem abi_alloca_history_allocate_outside:
  id <> site ==>
  FLOOKUP (abi_builtin_allocate_state site outsz s).vs_allocas id =
    FLOOKUP s.vs_allocas id
Proof
  rw[abi_builtin_allocate_state_def, FLOOKUP_UPDATE]
QED

Theorem abi_alloca_history_allocated_sizes:
  abi_alloca_history code s /\
  (!inst. MEM inst code /\ inst.inst_id IN abi_decoder_ids first last /\
    inst.inst_opcode = ALLOCA ==> inst.inst_operands = [Lit 32w]) /\
  ~(site IN abi_decoder_ids first last) ==>
  !id off sz. id IN abi_decoder_ids first last /\
    FLOOKUP (abi_builtin_allocate_state site outsz s).vs_allocas id = SOME (off,sz) ==>
    sz = 32
Proof
  strip_tac >>
  mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`,
    `code` |-> `code`, `s` |-> `s:venom_state`] abi_alloca_history_code_sizes) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `id <> site` by (strip_tac >> gvs[]) >>
  `FLOOKUP s.vs_allocas id = SOME (off,sz)` by
    gvs[abi_alloca_history_allocate_outside] >>
  first_x_assum drule_all >> simp[]
QED

Theorem abi_alloca_history_decode_resources:
  let site = abi_builtin_decode_output_site st min_size max_size in
  let allocated = abi_builtin_allocate_state site outsz initial in
  let cap = allocated.vs_alloca_next + 32 * CARD (abi_decoder_missing first last allocated) in
  RTC (\s t. ?fuel inst. MEM inst code /\ step_inst fuel ctx inst s = OK t) entry initial /\
  entry.vs_allocas = FEMPTY /\
  (!inst. MEM inst code /\ inst.inst_id IN abi_decoder_ids first last /\
    inst.inst_opcode = ALLOCA ==> inst.inst_operands = [Lit 32w]) /\
  cap < dimword (:256) /\
  min_size <= cnt /\ cnt <= max_size /\ max_size < dimword (:256) /\
  FLOOKUP initial.vs_allocas source_id = SOME (source_base,source_cap) /\ source_id <> site /\
  source_base <= p /\ p + 32 + cnt <= source_base + source_cap /\
  ((FLOOKUP initial.vs_allocas site = NONE /\ d = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas site = SOME (d,outsz)) /\
  site < first /\ first <= site + 2 /\ ~(source_id IN abi_decoder_ids first last) ==>
  abi_scratch_decode_resources st first last min_size max_size outsz cnt p d 0 cap initial
Proof
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `alloca_inv initial` by
    (mp_tac (Q.INST [`P` |-> `\inst:instruction. MEM inst code`]
      abi_alloca_invariant_initial) >> simp[]) >>
  `abi_alloca_history code entry` by simp[abi_alloca_history_empty] >>
  `abi_alloca_history code initial` by
    (drule_all abi_alloca_history_step_reachable >> simp[]) >>
  `~(abi_builtin_decode_output_site st min_size max_size IN abi_decoder_ids first last)` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`,
    `site` |-> `abi_builtin_decode_output_site st min_size max_size`,
    `outsz` |-> `outsz:num`] abi_alloca_history_allocated_sizes) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`initial` |-> `initial:venom_state`,
    `source_id` |-> `source_id:num`, `source_base` |-> `source_base:num`,
    `source_cap` |-> `source_cap:num`] abi_scratch_decode_resources_caller) >>
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >>
  disch_then match_mp_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
