(* Establish builtin resources from ordinary allocation history and numeric credit.
   TOP-LEVEL: abi_scratch_builtin_pre_caller derives all physical input/budget
   conditions. Complete producer memory and full method-store separation remain
   explicit; source and output allocations may both lie inside the numeric arena. *)
Theory abiScratchBuiltinCaller
Ancestors
  abiScratchBuiltinPre abiScratchBuiltinRun abiScratchBuiltinEffect abiScratchArrayEntry
  abiCallerAllocation abiBuiltinAllocationState abiEncoderInput abiBuiltinEncodeRun
  abiDecoderAllocation abiDecoderFootprint abiDecoderFrame abiDecoderReentry abiDecoderLoop abiDecoderContract
  compileEnv exprLowering builtinAbi valueEncoding contractABI venomMemDefs venomState
  finite_map pred_set words list arithmetic

Theorem abi_scratch_builtin_allocate_inv:
  alloca_inv s ==> alloca_inv (abi_builtin_allocate_state site outsz s)
Proof
  Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  simp_tac bool_ss [abi_builtin_allocate_state_def] >> asm_rewrite_tac[] >>
  fs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def, FLOOKUP_UPDATE] >>
  rw[] >> gvs[AllCaseEqs()] >> res_tac >> fs[]
QED

Theorem abi_scratch_builtin_allocate_buffers:
  alloca_inv s /\ FLOOKUP s.vs_allocas source_id = SOME (sb,source_cap) /\ source_id <> site /\
  ((FLOOKUP s.vs_allocas site = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas site = SOME (p,outsz)) ==>
  alloca_inv (abi_builtin_allocate_state site outsz s) /\
  FLOOKUP (abi_builtin_allocate_state site outsz s).vs_allocas source_id = SOME (sb,source_cap) /\
  FLOOKUP (abi_builtin_allocate_state site outsz s).vs_allocas site = SOME (p,outsz)
Proof
  strip_tac >> drule abi_scratch_builtin_allocate_inv >> disch_tac >>
  asm_simp_tac bool_ss [] >> Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  gvs[abi_builtin_allocate_state_def, FLOOKUP_UPDATE]
QED

Theorem abi_scratch_builtin_store_separate:
  (sb+source_cap <= p \/ p+(maxlen+32+(case method_id_opt of NONE => 0 | SOME (_:bytes32) => 4)) <= sb) /\
  (method_id_opt = NONE \/ sb+source_cap <= p+32 \/ p+64 <= sb) ==>
  sb+source_cap <= p+32 \/ p+32+(case method_id_opt of NONE => 0 | SOME _ => 32) <= sb
Proof
  Cases_on `method_id_opt` >> simp[] >> decide_tac
QED

Theorem abi_scratch_builtin_pre_caller:
  let outsz = maxlen+32+(case method_id_opt of NONE => 0 | SOME (_:bytes32) => 4) in
  let allocated = abi_builtin_allocate_state st.cs_next_id outsz initial in
  let cap = allocated.vs_alloca_next+32*CARD (abi_decoder_missing first last allocated) in
  alloca_inv initial /\ cap < dimword (:256) /\
  FLOOKUP initial.vs_allocas source_id = SOME (sb,source_cap) /\ source_id <> st.cs_next_id /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  st.cs_next_id < first /\ first <= st.cs_next_id+(case method_id_opt of NONE => 2 | SOME _ => 4) /\
  ~(source_id IN abi_decoder_ids first last) /\
  (!id off sz. id IN abi_decoder_ids first last /\
    FLOOKUP allocated.vs_allocas id = SOME (off,sz) ==> sz = 32) /\
  abi_encoder_input ei at av sb source_cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
  LENGTH (enc at av) <= maxlen /\
  (method_id_opt = NONE \/ sb+source_cap <= p+32 \/ p+64 <= sb) ==>
  abi_scratch_builtin_pre ei at av st method_id_opt src sb source_cap p maxlen first last 0 cap initial
Proof
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `site` |-> `st.cs_next_id`,
    `outsz` |-> `maxlen+32+(case (method_id_opt:bytes32 option) of NONE => 0 | SOME _ => 4)`]
    abi_scratch_builtin_allocate_buffers) >> impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `allocated = abi_builtin_allocate_state st.cs_next_id
    (maxlen+32+(case (method_id_opt:bytes32 option) of NONE => 0 | SOME _ => 4)) initial` >>
  qabbrev_tac `cap = allocated.vs_alloca_next+32*CARD (abi_decoder_missing first last allocated)` >>
  `abi_decoder_budget first last 0 cap allocated` by
    (qunabbrev_tac `cap` >> irule abi_caller_allocation_budget_zero >>
     asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
  `~(st.cs_next_id IN abi_decoder_ids first last)` by (simp[abi_decoder_ids_def] >> decide_tac) >>
  mp_tac (Q.INST [`initial` |-> `allocated:venom_state`, `ids` |-> `abi_decoder_ids first last`,
    `output_id` |-> `st.cs_next_id`, `d` |-> `p:num`, `b` |-> `0:num`,
    `output_size` |-> `maxlen+32+(case (method_id_opt:bytes32 option) of NONE => 0 | SOME _ => 4)`]
    abi_scratch_array_entry_buffers) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [] >> decide_tac) >> strip_tac >>
  qpat_assum `abi_footprint_disjoint sb source_cap
    [(p,maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4))]`
    (assume_tac o SIMP_RULE (srw_ss()) [abi_footprint_disjoint_def]) >>
  drule_all abi_scratch_builtin_store_separate >> disch_tac >>
  PURE_REWRITE_TAC [abi_scratch_builtin_pre_def, LET_THM] >> BETA_TAC >>
  qpat_assum `Abbrev (allocated = _)` (fn th =>
    PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem lower_abi_encode_scratch_caller:
  let outsz = maxlen+32+(case method_id_opt of NONE => 0 | SOME (_:bytes32) => 4) in
  let allocated = abi_builtin_allocate_state start.cs_next_id outsz initial in
  let cap = allocated.vs_alloca_next+32*CARD (abi_decoder_missing first last allocated) in
  lower_abi_encode ensure method_id_opt src (type_to_abi_enc_info sf ce ty) maxlen start = (out,final) /\
  fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv initial /\ cap < dimword (:256) /\
  FLOOKUP initial.vs_allocas source_id = SOME (sb,source_cap) /\ source_id <> start.cs_next_id /\
  ((FLOOKUP initial.vs_allocas start.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas start.cs_next_id = SOME (p,outsz)) /\
  start.cs_next_id < first /\ first <= start.cs_next_id+(case method_id_opt of NONE => 2 | SOME _ => 4) /\
  ~(source_id IN abi_decoder_ids first last) /\
  (!id off sz. id IN abi_decoder_ids first last /\
    FLOOKUP allocated.vs_allocas id = SOME (off,sz) ==> sz = 32) /\
  abi_encoder_input (type_to_abi_enc_info sf ce ty) at av sb source_cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live start.cs_next_var src /\
  LENGTH (enc at av) <= maxlen /\
  (method_id_opt = NONE \/ sb+source_cap <= p+32 \/ p+64 <= sb) /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH (abi_builtin_encode_prefix method_id_opt ++ enc at av)) /\
    mem_bytes_at (p+32) (LENGTH (abi_builtin_encode_prefix method_id_opt ++ enc at av)) actual.vs_memory =
      abi_builtin_encode_prefix method_id_opt ++ enc at av /\
    val_in_memory (BaseTV (BytesT (Dynamic (maxlen+LENGTH (abi_builtin_encode_prefix method_id_opt)))))
      (vyperValue$BytesV (abi_builtin_encode_prefix method_id_opt ++ enc at av)) p actual.vs_memory /\
    abi_encoder_input (type_to_abi_enc_info sf ce ty) at av sb source_cap actual.vs_memory /\
    abi_scratch_builtin_effect first last start final limit_st p outsz
      (case method_id_opt of NONE => 0 | SOME _ => 32) 0 cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
    (Q.INST [`st` |-> `start:compile_state`] abi_scratch_builtin_pre_caller))) >> disch_tac >>
  drule_all lower_abi_encode_scratch >> disch_then (qspec_then `ctx` ACCEPT_TAC)
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_BUILTIN_CALLER_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch builtin caller resources not kernel closed: " ^ n)
  end) (DB.thms "abiScratchBuiltinCaller");
