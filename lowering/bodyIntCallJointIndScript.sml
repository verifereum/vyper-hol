(* Seam 2 joint induction: every statement list meets the statement
   producer, from the five steps. *)
Theory bodyIntCallJointInd
Ancestors
  bodyIntCallJointAgg bodyIntCallJointPure bodyIntCallJointCall
  bodyIntCallJointForce bodyIntCallJointStmt

(* L-ind: the induction, on the owner's call-descendant count, then on
   expr_size and stmt_size, from the five steps above.  The seam
   intcall_callee_body_sim (bodyIntCallSeams) is proved from it: its proof
   initializes I at the prologue landing, applies this, and turns
   intcall_stmt_exit into intcall_callee_exit. *)
Theorem stmt_size_le_list_size[local]:
  !ss st. MEM st ss ==> stmt_size st <= list_size stmt_size ss
Proof
  Induct >> rw[] >> res_tac >> simp[]
QED

Theorem intcall_joint_producers_count[local]:
  !n fp. CARD {z | TC (call_edge_rel fp.jc_edges) fp.jc_owner z} = n ==>
    (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
         intcall_map_producer fp e) /\
    !ss. intcall_stmts_producer fp ss
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  `!fp' ss. fp'.jc_edges = fp.jc_edges /\
     CARD {z | TC (call_edge_rel fp.jc_edges) fp'.jc_owner z} <
     CARD {z | TC (call_edge_rel fp.jc_edges) fp.jc_owner z} ==>
     intcall_stmts_producer fp' ss` by (
    rpt strip_tac >>
    first_x_assum (qspec_then
      `CARD {z | TC (call_edge_rel fp.jc_edges) fp'.jc_owner z}` mp_tac) >>
    impl_tac >- gvs[] >>
    disch_then (qspec_then `fp'` mp_tac) >> gvs[]) >>
  `!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e` by (
    measureInduct_on `expr_size e` >>
    `intcall_expr_producer fp e /\ intcall_map_producer fp e` by (
      Cases_on `(?a t n args. e = Builtin a (MakeArray t n) args) \/
                (?a nm fields. e = StructLit a nm fields) \/
                (?a base fld. e = Attribute a base fld) \/
                (?a base idx. e = Subscript a base idx)`
      >- (irule intcall_aggregate_producer_step >> fs[]) >>
      Cases_on `(?a tgt args dflt. e = Call a tgt args dflt) \/
                (?a tgt. e = Pop a tgt)`
      >- (irule intcall_effect_producer_step >> fs[]) >>
      irule intcall_pure_producer_step >> fs[]) >>
    simp[] >> irule intcall_forced_producer_from_value >> simp[]) >>
  `!ss. (!st. MEM st ss ==> intcall_stmts_producer fp [st]) ==>
        intcall_stmts_producer fp ss` by
    metis_tac[intcall_stmt_producer_step] >>
  `!st. intcall_stmts_producer fp [st]` by (
    measureInduct_on `stmt_size st` >>
    mp_tac intcall_stmt_producer_step >> impl_tac >- simp[] >>
    strip_tac >> first_x_assum irule >> rpt strip_tac >>
    first_x_assum irule >> rpt strip_tac >>
    first_x_assum irule >>
    drule stmt_size_le_list_size >> simp[]) >>
  simp[]
QED

Theorem intcall_joint_producers:
  !fp ss. intcall_stmts_producer fp ss
Proof
  metis_tac[intcall_joint_producers_count]
QED
