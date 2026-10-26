(* Physical decoder resources from actual execution history and a code-size
   certificate. Numeric credit and live-buffer ownership remain explicit. *)
Theory abiAllocationHistoryResources
Ancestors
  abiAllocationHistoryRun abiAllocationHistoryCode abiAllocationHistory abiAllocationInvariant
  abiScratchDecodeResources abiScratchDecodeInput abiBuiltinAllocationState
  abiBuiltinDecodeSetup abiDecoderAllocation venomMemDefs venomExecSemantics
  venomState venomInst compileEnv finite_map pred_set words list arithmetic relation

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

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ALLOCATION_HISTORY_RESOURCES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI allocation history resources not kernel closed: " ^ n)
  end) (DB.thms "abiAllocationHistoryResources");

