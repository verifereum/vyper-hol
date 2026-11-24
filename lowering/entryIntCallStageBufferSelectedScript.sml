(* Publication shim for the accepted buffered-stage cut theorem.  The
   selected-stage output is exposed from the existing physical-stage theory
   without duplicating its proof. *)
Theory entryIntCallStageBufferSelected
Ancestors
  entryIntCallStageBuffer

Theorem intcall_stage_buffer_selected:
  compile_alloc_buffer n a = (buf,b) /\
  unwrap_value ce vv b = (op,c) /\
  compile_store_memory ce op buf.buf_operand dt (vv_type vv) c = ((),d) /\
  fn_has_code a d fn /\ body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions ==>
  create_operand_cut a d explicit ctx fn tops cx st0 source (es,s)
Proof
  metis_tac[intcall_stage_buffer_admin_safe]
QED
