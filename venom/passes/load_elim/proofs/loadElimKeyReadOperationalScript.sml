Theory loadElimKeyReadOperational
Ancestors
  loadElimKeyRead memAliasProps mem2varBlockSimHelpers deadStoreElimProofs
  venomMemDefs venomEffects words venomInstProps
  basePtrDefs memLocDefs venomState memoryCopyElisionSound loadElimDefs venomInst
  venomExecSemantics venomExecProofs

Theorem le_memory_read_nonalias_store:
  wf_alias_sets aliases /\ ~ma_may_alias aliases readloc writeloc /\
  allocas_non_overlapping s /\ memloc_within_alloca readloc s /\
  memloc_within_alloca writeloc s /\
  memloc_runtime_region readloc s = SOME (a,addr_space_word_scale AddrSp_Memory) /\
  memloc_runtime_region writeloc s = SOME (b,addr_space_word_scale AddrSp_Memory) /\
  a < dimword (:256) /\ b < dimword (:256) ==>
  le_read_address AddrSp_Memory a (mstore b value s) =
  le_read_address AddrSp_Memory a s
Proof
  strip_tac >> drule_all ma_may_alias_sound >>
  simp[regions_disjoint_def, addr_space_word_scale_def] >>
  strip_tac >> simp[] >> irule mload_mstore_disjoint >> simp[]
QED

Theorem le_storage_read_nonalias_store:
  wf_alias_sets aliases /\ ~ma_may_alias aliases readloc writeloc /\
  allocas_non_overlapping s /\ memloc_within_alloca readloc s /\
  memloc_within_alloca writeloc s /\
  memloc_runtime_region readloc s = SOME (a,addr_space_word_scale AddrSp_Storage) /\
  memloc_runtime_region writeloc s = SOME (b,addr_space_word_scale AddrSp_Storage) /\
  a < dimword (:256) /\ b < dimword (:256) ==>
  le_read_address AddrSp_Storage a (sstore (n2w b) value s) =
  le_read_address AddrSp_Storage a s
Proof
  strip_tac >> drule_all ma_may_alias_sound >>
  simp[regions_disjoint_def, addr_space_word_scale_def] >>
  strip_tac >> simp[] >> irule sload_sstore_disjoint >>
  simp[n2w_11] >> decide_tac
QED

Theorem le_transient_read_nonalias_store:
  wf_alias_sets aliases /\ ~ma_may_alias aliases readloc writeloc /\
  allocas_non_overlapping s /\ memloc_within_alloca readloc s /\
  memloc_within_alloca writeloc s /\
  memloc_runtime_region readloc s = SOME (a,addr_space_word_scale AddrSp_Transient) /\
  memloc_runtime_region writeloc s = SOME (b,addr_space_word_scale AddrSp_Transient) /\
  a < dimword (:256) /\ b < dimword (:256) ==>
  le_read_address AddrSp_Transient a (tstore (n2w b) value s) =
  le_read_address AddrSp_Transient a s
Proof
  strip_tac >> drule_all ma_may_alias_sound >>
  simp[regions_disjoint_def, addr_space_word_scale_def] >>
  strip_tac >> simp[] >> irule tload_tstore_disjoint >>
  simp[n2w_11] >> decide_tac
QED

Theorem le_calldata_read_step_nonterminator:
  step_inst fuel ctx inst s = OK t /\
  ~is_terminator inst.inst_opcode ==>
  le_read_address AddrSp_Calldata a t = le_read_address AddrSp_Calldata a s
Proof
  strip_tac >> drule_all step_preserves_call_ctx >> simp[]
QED

Theorem le_data_read_step_nonterminator:
  step_inst fuel ctx inst s = OK t /\
  ~is_terminator inst.inst_opcode ==>
  le_read_address AddrSp_Data a t = le_read_address AddrSp_Data a s
Proof
  strip_tac >> drule_all step_preserves_data_section >> simp[]
QED

Theorem le_fixed_segment_runtime_word:
  bp_ptr_sound bp s /\ allocas_in_word s /\
  bp_segment_from_ops bp ops = ml /\ ml_is_fixed ml /\
  ops.iao_max_size = SOME (Lit (n2w (addr_space_word_scale space))) /\
  eval_operand ops.iao_ofst s = SOME w /\ memloc_within_alloca ml s ==>
  memloc_runtime_region ml s = SOME (w2n w, addr_space_word_scale space)
Proof
  strip_tac >>
  `addr_space_word_scale space < dimword (:256)` by
    (Cases_on `space` >> simp[addr_space_word_scale_def, dimword_def]) >>
  `IS_SOME (eval_operand ops.iao_ofst s)` by simp[] >>
  drule_all bp_segment_from_ops_runtime_region >>
  strip_tac >>
  Cases_on `ops.iao_ofst` >>
  gvs[bp_segment_from_ops_def, ml_is_fixed_def, ml_undefined_def,
      memloc_runtime_region_def, eval_operand_def] >>
  rename1 `bp_ptr_from_op bp (Var v)` >>
  Cases_on `bp_ptr_from_op bp (Var v)` >> gvs[] >>
  rename1 `bp_ptr_from_op bp (Var v) = SOME ptr` >>
  Cases_on `ptr` >> gvs[] >>
  rename1 `bp_ptr_from_op bp (Var v) = SOME (Ptr alloc off)` >> Cases_on `off` >> gvs[] >>
  Cases_on `alloc` >>
  gvs[memloc_within_alloca_def] >>
  rename1 `FLOOKUP s.vs_allocas aid` >>
  Cases_on `FLOOKUP s.vs_allocas aid` >> gvs[] >>
  fs[allocas_in_word_def] >>
  rename1 `FLOOKUP s.vs_allocas aid = SOME region` >>
  PairCases_on `region` >>
  first_x_assum drule >> simp[] >> decide_tac
QED

Theorem le_configured_read_location:
  MEM (inst.inst_opcode,space)
    [(MLOAD,AddrSp_Memory); (SLOAD,AddrSp_Storage);
     (TLOAD,AddrSp_Transient); (CALLDATALOAD,AddrSp_Calldata)] /\
  inst.inst_operands = [addr] ==>
  bp_get_read_location bp inst space =
    bp_segment_from_ops bp
      <|iao_ofst := addr;
        iao_size := SOME (Lit (n2w (addr_space_word_scale space)));
        iao_max_size := SOME (Lit (n2w (addr_space_word_scale space)))|>
Proof
  simp[] >> strip_tac >>
  gvs[bp_get_read_location_def, mem_read_ops_def,
      addr_space_word_scale_def, read_effects_def, is_raw_fmp_opcode_def]
QED

(* Shared location-or-normalized-operand choice for both read and write keys. *)
Theorem le_segment_key_address[local]:
  bp_segment_from_ops bp
    <|iao_ofst := addr;
      iao_size := SOME (Lit (n2w (addr_space_word_scale space)));
      iao_max_size := SOME (Lit (n2w (addr_space_word_scale space)))|> = ml /\
  eval_operand addr s = SOME w /\ eval_operand (norm addr) s = SOME w /\
  bp_ptr_sound bp s /\ allocas_in_word s /\ memloc_within_alloca ml s ==>
  le_key_address space
    (if use_loc then if ml_is_fixed ml then LK_Loc ml else LK_Op (norm addr)
     else LK_Op (norm addr)) s = SOME (w2n w)
Proof
  strip_tac >> reverse (Cases_on `use_loc`) >- simp[] >>
  reverse (Cases_on `ml_is_fixed ml`) >- simp[] >>
  `memloc_runtime_region ml s = SOME (w2n w,addr_space_word_scale space)` by
    (irule le_fixed_segment_runtime_word >> simp[] >>
     qexistsl [`bp`, `<|iao_ofst := addr;
       iao_size := SOME (Lit (n2w (addr_space_word_scale space)));
       iao_max_size := SOME (Lit (n2w (addr_space_word_scale space)))|>`] >>
     simp[]) >>
  simp[le_key_address_def, w2n_lt]
QED

Theorem le_configured_read_key_address:
  MEM (inst.inst_opcode,space)
    [(MLOAD,AddrSp_Memory); (SLOAD,AddrSp_Storage);
     (TLOAD,AddrSp_Transient); (CALLDATALOAD,AddrSp_Calldata)] /\
  inst.inst_operands = [addr] /\
  eval_operand addr s = SOME w /\ eval_operand (norm addr) s = SOME w /\
  bp_ptr_sound bp s /\ allocas_in_word s /\
  memloc_within_alloca (bp_get_read_location bp inst space) s ==>
  le_key_address space (load_get_read_key bp space norm inst) s = SOME (w2n w)
Proof
  strip_tac >> drule_all le_configured_read_location >> strip_tac >>
  simp[load_get_read_key_def] >>
  irule le_segment_key_address >> gvs[] >> qexists `bp` >> simp[]
QED

Theorem le_dload_key_address:
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [addr] /\
  eval_operand (norm addr) s = SOME w ==>
  le_key_address AddrSp_Data (load_get_read_key bp AddrSp_Data norm inst) s =
    SOME (w2n w)
Proof
  simp[load_get_read_key_def, use_memloc_for_read_def]
QED

Theorem le_configured_write_location:
  MEM (inst.inst_opcode,space)
    [(MSTORE,AddrSp_Memory); (SSTORE,AddrSp_Storage); (TSTORE,AddrSp_Transient)] /\
  inst.inst_operands = [addr;value] ==>
  bp_get_write_location bp inst space =
    bp_segment_from_ops bp
      <|iao_ofst := addr;
        iao_size := SOME (Lit (n2w (addr_space_word_scale space)));
        iao_max_size := SOME (Lit (n2w (addr_space_word_scale space)))|>
Proof
  simp[] >> strip_tac >>
  gvs[bp_get_write_location_def, mem_write_ops_def,
      addr_space_word_scale_def, write_effects_def, is_raw_fmp_opcode_def]
QED

Theorem le_configured_write_key_address:
  MEM (inst.inst_opcode,space)
    [(MSTORE,AddrSp_Memory); (SSTORE,AddrSp_Storage); (TSTORE,AddrSp_Transient)] /\
  inst.inst_operands = [addr;value] /\
  eval_operand addr s = SOME w /\ eval_operand (norm addr) s = SOME w /\
  bp_ptr_sound bp s /\ allocas_in_word s /\
  memloc_within_alloca (bp_get_write_location bp inst space) s ==>
  le_key_address space (load_get_write_key bp space norm inst) s = SOME (w2n w)
Proof
  strip_tac >> drule_all le_configured_write_location >> strip_tac >>
  simp[load_get_write_key_def] >>
  irule le_segment_key_address >> gvs[] >> qexists `bp` >> simp[]
QED

Theorem le_terminator_readonly_fields:
  step_inst fuel ctx inst s = OK t /\ is_terminator inst.inst_opcode ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[Once step_inst_def] >>
  simp[step_inst_base_opcode_eqs] >>
  simp[jump_to_def] >>
  gvs[AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >> gvs[] >>
  pairarg_tac >> gvs[]
QED

Theorem le_step_readonly_fields:
  step_inst fuel ctx inst s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- (drule_all le_terminator_readonly_fields >> simp[]) >>
  conj_tac
  >- (drule_all step_preserves_call_ctx >> simp[]) >>
  drule_all step_preserves_data_section >> simp[]
QED

Theorem le_calldata_read_step:
  step_inst fuel ctx inst s = OK t ==>
  le_read_address AddrSp_Calldata a t = le_read_address AddrSp_Calldata a s
Proof
  strip_tac >> drule le_step_readonly_fields >> simp[]
QED

Theorem le_data_read_step:
  step_inst fuel ctx inst s = OK t ==>
  le_read_address AddrSp_Data a t = le_read_address AddrSp_Data a s
Proof
  strip_tac >> drule le_step_readonly_fields >> simp[]
QED

Theorem le_calldata_read_phis:
  eval_phis s insts = OK t ==>
  le_read_address AddrSp_Calldata a t = le_read_address AddrSp_Calldata a s
Proof
  strip_tac >> drule eval_phis_only_updates_vs_vars >>
  disch_then SUBST1_TAC >> simp[]
QED

Theorem le_data_read_phis:
  eval_phis s insts = OK t ==>
  le_read_address AddrSp_Data a t = le_read_address AddrSp_Data a s
Proof
  strip_tac >> drule eval_phis_only_updates_vs_vars >>
  disch_then SUBST1_TAC >> simp[]
QED
