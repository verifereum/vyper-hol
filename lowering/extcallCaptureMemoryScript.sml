(* Capacity transport when a captured result is read at a later source state. *)
Theory extcallCaptureMemory
Ancestors
  bodyMemAssignAttrStorage exprSimMemDefs

Theorem extcall_vv_bound_read_transport:
  vv_store_bound cx ty lt es tv vv s /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!v. read_result cx tv ee = (INL v,ee) ==>
       read_result cx tv es = (INL v,es)) ==>
  vv_store_bound cx ty lt ee tv vv t
Proof
  strip_tac >>
  `vv_store_bound cx ty lt es tv vv t` by
    metis_tac[vv_store_bound_frame_mem_src] >>
  fs[vv_store_bound_def] >> metis_tac[]
QED
