Theory deadStoreElimDloadGuard
Ancestors
  deadStoreElimDefs basePtrDefs memLocDefs memAliasDefs venomInst
  venomEffects finite_map list

Theorem dse_dload_locations:
  inst.inst_opcode = DLOAD ==>
  bp_get_read_location bp inst AddrSp_Memory =
    <|ml_offset := SOME 0; ml_size := SOME 32; ml_alloca := NONE; ml_volatile := F|> /\
  bp_get_write_location bp inst AddrSp_Memory =
    <|ml_offset := SOME 0; ml_size := SOME 32; ml_alloca := NONE; ml_volatile := F|>
Proof
  simp[bp_get_read_location_def, bp_get_write_location_def,
       is_raw_fmp_opcode_def]
QED

Theorem dse_dload_reads_zero:
  inst.inst_opcode = DLOAD ==>
  dse_inst_reads_alias FEMPTY bp AddrSp_Memory
    <|ml_offset := SOME 0; ml_size := SOME 32; ml_alloca := NONE; ml_volatile := F|> inst
Proof
  strip_tac >> drule dse_dload_locations >> strip_tac >>
  simp[dse_inst_reads_alias_def, ma_may_alias_def, may_overlap_def]
QED

(* For any candidate starting with MSTORE 0; DLOAD, the DLOAD read
   already witnesses liveness before its own static clobber. *)
Theorem dse_dload_successor_live:
  1 < LENGTH bb.bb_instructions /\
  (EL 1 bb.bb_instructions).inst_opcode = DLOAD ==>
  dse_mem_def_live cfg FEMPTY bp
    <|ml_offset := SOME 0; ml_size := SOME 32; ml_alloca := NONE; ml_volatile := F|>
    AddrSp_Memory fn bb 0
Proof
  strip_tac >> simp[dse_mem_def_live_def] >> disj1_tac >>
  qexists_tac `1` >> simp[dse_dload_reads_zero]
QED
