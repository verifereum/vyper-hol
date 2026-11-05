Theory loadElimAbsoluteKey
Ancestors
  loadElimKeyReadOperational loadElimBPEmpty loadElimKeyRead
  basePtrDefs memLocDefs venomState venomEffects words loadElimDefs

Definition le_absolute_key_def:
  (le_absolute_key space (LK_Op op) = T) /\
  (le_absolute_key space (LK_Loc ml) <=>
    ml.ml_alloca = NONE /\ ml.ml_size = SOME (addr_space_word_scale space) /\
    ?a. a < dimword (:256) /\ ml.ml_offset = SOME a)
End

Theorem le_absolute_location_address:
  le_absolute_key space (LK_Loc ml) ==>
  le_key_address space (LK_Loc ml) t = le_key_address space (LK_Loc ml) s
Proof
  simp[le_absolute_key_def] >> strip_tac
  >> simp[le_key_address_def, memloc_runtime_region_def]
QED

Theorem le_empty_segment_key_shape:
  (!v. bp_get_ptrs bp v = []) ==>
  le_absolute_key space
    (if use_loc then
       if ml_is_fixed (bp_segment_from_ops bp
         <|iao_ofst := addr;
           iao_size := SOME (Lit (n2w (addr_space_word_scale space)));
           iao_max_size := SOME (Lit (n2w (addr_space_word_scale space)))|>)
       then LK_Loc (bp_segment_from_ops bp
         <|iao_ofst := addr;
           iao_size := SOME (Lit (n2w (addr_space_word_scale space)));
           iao_max_size := SOME (Lit (n2w (addr_space_word_scale space)))|>)
       else LK_Op (norm addr)
     else LK_Op (norm addr))
Proof
  strip_tac >> Cases_on `use_loc` >> simp[le_absolute_key_def]
  >> `bp_ptr_from_op bp addr = NONE` by metis_tac[le_bp_empty_ptr_from_op]
  >> Cases_on `addr`
  >> gvs[bp_segment_from_ops_def, ml_is_fixed_def, ml_undefined_def,
         le_absolute_key_def]
  >> Cases_on `space` >> simp[addr_space_word_scale_def, w2n_lt, dimword_def]
QED

Theorem le_empty_read_key_shape:
  (!v. bp_get_ptrs bp v = []) /\
  MEM (inst.inst_opcode,space)
    [(MLOAD,AddrSp_Memory); (SLOAD,AddrSp_Storage);
     (TLOAD,AddrSp_Transient); (CALLDATALOAD,AddrSp_Calldata)] /\
  inst.inst_operands = [addr] ==>
  le_absolute_key space (load_get_read_key bp space norm inst)
Proof
  strip_tac >> drule_all le_configured_read_location >> strip_tac
  >> simp[load_get_read_key_def]
  >> irule le_empty_segment_key_shape >> simp[]
QED

Theorem le_empty_write_key_shape:
  (!v. bp_get_ptrs bp v = []) /\
  MEM (inst.inst_opcode,space)
    [(MSTORE,AddrSp_Memory); (SSTORE,AddrSp_Storage); (TSTORE,AddrSp_Transient)] /\
  inst.inst_operands = [addr;value] ==>
  le_absolute_key space (load_get_write_key bp space norm inst)
Proof
  strip_tac >> drule_all le_configured_write_location >> strip_tac
  >> simp[load_get_write_key_def]
  >> irule le_empty_segment_key_shape >> simp[]
QED

Theorem le_dload_key_shape:
  le_absolute_key AddrSp_Data (load_get_read_key bp AddrSp_Data norm inst)
Proof
  simp[load_get_read_key_def, use_memloc_for_read_def, le_absolute_key_def]
QED

Theorem le_empty_segment_key_address:
  (!v. bp_get_ptrs bp v = []) /\
  eval_operand addr s = SOME w /\ eval_operand (norm addr) s = SOME w ==>
  le_key_address space
    (if use_loc then
       if ml_is_fixed (bp_segment_from_ops bp
         <|iao_ofst := addr;
           iao_size := SOME (Lit (n2w (addr_space_word_scale space)));
           iao_max_size := SOME (Lit (n2w (addr_space_word_scale space)))|>)
       then LK_Loc (bp_segment_from_ops bp
         <|iao_ofst := addr;
           iao_size := SOME (Lit (n2w (addr_space_word_scale space)));
           iao_max_size := SOME (Lit (n2w (addr_space_word_scale space)))|>)
       else LK_Op (norm addr)
     else LK_Op (norm addr)) s = SOME (w2n w)
Proof
  strip_tac >> Cases_on `use_loc` >> simp[le_key_address_def]
  >> `bp_ptr_from_op bp addr = NONE` by metis_tac[le_bp_empty_ptr_from_op]
  >> Cases_on `addr`
  >> gvs[bp_segment_from_ops_def, ml_is_fixed_def, ml_undefined_def,
         eval_operand_def, le_key_address_def, memloc_runtime_region_def]
  >> Cases_on `space`
  >> simp[addr_space_word_scale_def, w2n_lt, dimword_def]
QED

Theorem le_empty_read_key_address:
  (!v. bp_get_ptrs bp v = []) /\
  MEM (inst.inst_opcode,space)
    [(MLOAD,AddrSp_Memory); (SLOAD,AddrSp_Storage);
     (TLOAD,AddrSp_Transient); (CALLDATALOAD,AddrSp_Calldata)] /\
  inst.inst_operands = [addr] /\
  eval_operand addr s = SOME w /\ eval_operand (norm addr) s = SOME w ==>
  le_key_address space (load_get_read_key bp space norm inst) s = SOME (w2n w)
Proof
  strip_tac >> drule_all le_configured_read_location >> strip_tac
  >> simp[load_get_read_key_def]
  >> irule le_empty_segment_key_address >> simp[]
QED

Theorem le_empty_write_key_address:
  (!v. bp_get_ptrs bp v = []) /\
  MEM (inst.inst_opcode,space)
    [(MSTORE,AddrSp_Memory); (SSTORE,AddrSp_Storage); (TSTORE,AddrSp_Transient)] /\
  inst.inst_operands = [addr;value] /\
  eval_operand addr s = SOME w /\ eval_operand (norm addr) s = SOME w ==>
  le_key_address space (load_get_write_key bp space norm inst) s = SOME (w2n w)
Proof
  strip_tac >> drule_all le_configured_write_location >> strip_tac
  >> simp[load_get_write_key_def]
  >> irule le_empty_segment_key_address >> simp[]
QED
