(* Seam 2 joint induction, a family leaf of the call step: nested internal calls, under the call-graph descent premise. *)
Theory bodyIntCallFamCallInt
Ancestors
  bodyIntCallJointContract

Theorem intcall_intcall_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (!fp' ss.
     fp'.jc_edges = fp.jc_edges /\
     CARD {z | TC (call_edge_rel fp.jc_edges) fp'.jc_owner z} <
     CARD {z | TC (call_edge_rel fp.jc_edges) fp.jc_owner z} ==>
     intcall_stmts_producer fp' ss) /\
  (?a nsid args dflt. e = Call a (IntCall nsid) args dflt) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
