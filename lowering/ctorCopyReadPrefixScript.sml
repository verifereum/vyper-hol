(* Seal the allocation/unwrap laws at the materializer's selected cuts.
   The read continuation needs only the resulting store-entry sequent. *)
Theory ctorCopyReadPrefix
Ancestors
  bodyFullExtCallDefaultPrefix exprLowering
Libs ctorCopyObservationLib

val (prefix_pre,prefix_rest) = dest_imp
  (concl extcall_default_prefix_store_entry_observed);
val (alloc_law,unwrap_rest) = dest_imp prefix_rest;
val (unwrap_law,compose_rest) = dest_imp unwrap_rest;
val (compose_law,prefix_post) = dest_imp compose_rest;
val read_prefix_law = ctorCopyObservationLib.close_except
  ["R","ctx","func","cenv","ty","e","sa","vv","sm","sn","buf","op","sc",
   "explicit","PG"] (mk_imp (prefix_pre,prefix_post));

Theorem copied_head_read_prefix_of_segments:
  compile_alloc_buffer (type_memory_bytes cenv (lowered_value_type cenv e)) sm = (buf,sn) /\
  unwrap_value cenv vv sn = (op,sc) /\
  compile_store_memory cenv op buf.buf_operand (lowered_value_type cenv e)
    (lowered_value_type cenv e) sc = ((),sb) ==>
  ^alloc_law ==> ^unwrap_law ==> ^compose_law ==> ^read_prefix_law
Proof
  rpt disch_tac >> rpt gen_tac >> disch_tac >>
  mp_tac extcall_default_prefix_store_entry_observed >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED
