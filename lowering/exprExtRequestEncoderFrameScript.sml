(* Held admission for the extcall request seam: the ABI encoder run as a
   counted path, with the facts about its exit state that don't depend on
   the enclosing function's other code (memory and operands, registered
   effect, allocation growth, 32-byte scratch sites, labels) and its frame
   (static charge, fmp, call context, data section, memory length).

   Discharged at the trunk merge, from the abi-case branch
   (bot/opus/seq-1309-abi-case @ 0bfc230cd), the same composition that
   branch lists as its next-phase target in exprSimAbiEncodeFramedSuffix
   ("Exact integration target for the next phase"), here for the bare
   compile_abi_encode_to_buf:
   - exprSimAbiEncodeFramedBodyTheory.compile_abi_encode_to_buf_framed_run
     at the bridge's observer function, with singleton-ctx room as in
     abi_encode_framed_body_singleton;
   - exprSimAbiGasBridgeTheory.abi_decode_sim_gas_path (no blocks emitted;
     frag_gas_free via enc_operand_encoder_mutual) or
     abi_decode_sim_gas_path_relabel (blocks emitted; the
     exprSimAbiEncodeOblivious* facts), with Q the conjuncts below other
     than the path and endpoint, as in abi_encode_nonword_counted_suffix;
   - the observer's charge lifted to func by
     exprSimAbiEncodeChargeTransferTheory.abi_encode_charge_difference_lift,
     and window_alloca_sites agreeing on frag_ids between the observer and
     func (both contain the fragment's code, with distinct ids). *)
Theory exprExtRequestEncoderFrame
Ancestors
  abiEncoderWindowContract exprLoweringProps fragGasMode

Theorem abi_encoder_window_run_fmp:
  compile_abi_encode_to_buf dst src ei st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\
      mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
      eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
      abi_encoder_registered_effect (window_alloca_sites func (frag_ids st st'))
        [(d,LENGTH (enc at av))] s t /\
      alloca_inv t /\
      (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
         lookup_var x t = SOME w) /\
      window_alloca_growth s t /\
      (!i b sz. i IN window_alloca_sites func (frag_ids st st') /\
         FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
      t.vs_labels = s.vs_labels /\
      t.vs_alloca_next + pending_alloca_size func t <=
        s.vs_alloca_next + pending_alloca_size func s /\
      t.vs_fmp = s.vs_fmp /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_outcomes = s.vs_outcomes /\ t.vs_immutables = s.vs_immutables /\
      t.vs_data_section = s.vs_data_section /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  cheat
QED
