Theory abiDecodePtrRangeRun
Ancestors
  abiDecodePtrPrims bodyPtrBopScalarSeq

Theorem abi_decode_range_success_path:
  compile_abi_decode_range_check src e hi st = ((),st') /\
  src IN A /\ e IN A /\ hi IN A /\
  (!x. x IN R ==> not_fresh_at st x) /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP G' x = FLOOKUP G x /\
                    FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all abi_decode_range_scalar >> strip_tac >>
  drule_all bop_scalar_seq_path >> metis_tac[]
QED
