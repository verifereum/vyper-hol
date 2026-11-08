(* Seam 2 joint induction step: calls and pops. *)
Theory bodyIntCallJointCall
Ancestors
  bodyIntCallJointContract

(* L-call (C1.3.15): calls (internal, external, send) and pops, given the
   smaller expressions' producers and, by call-graph descent
   (callable_graph_descent), the statement producer of every frame whose
   owner has fewer call descendants under the same edges. *)
Theorem intcall_effect_producer_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (!fp' ss.
     fp'.jc_edges = fp.jc_edges /\
     CARD {z | TC (call_edge_rel fp.jc_edges) fp'.jc_owner z} <
     CARD {z | TC (call_edge_rel fp.jc_edges) fp.jc_owner z} ==>
     intcall_stmts_producer fp' ss) /\
  ((?a tgt args dflt. e = Call a tgt args dflt) \/ (?a tgt. e = Pop a tgt)) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
