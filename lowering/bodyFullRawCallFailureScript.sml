(* The failure branch forwards the actual returndata on the specified run. *)
Theory bodyFullRawCallFailure
Ancestors
  rawCallFailureSteps

Theorem raw_call_failure_block_origin_ptr:
 !ctx func PG lo explicit sa sz sp sc sb zop rb s G tn t.
 emit_op RETURNDATASIZE [] sa = (zop,sz) /\
 compile_alloc_buffer 0 sz = (rb,sp) /\
 emit_void RETURNDATACOPY [rb.buf_operand;Lit 0w;zop] sp = ((),sc) /\
 emit_inst REVERT [rb.buf_operand;zop] [] sc = ((),sb) /\
 fn_has_code sa sb func /\ ~s.vs_halted /\
 (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
   s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
 allocas_from lo s /\ lo <= s.vs_alloca_next /\
 s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 LENGTH s.vs_returndata < dimword (:256) /\
 run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t ==>
 ?Gf tnf.
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (Abort Revert_abort (t with vs_inst_idx := s.vs_inst_idx + 3),Gf,tnf)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac raw_call_failure_block_steps >>
  metis_tac[]
QED
