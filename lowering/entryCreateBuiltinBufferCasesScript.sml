(* Scoped case interfaces for buffer-valued builtins. *)
Theory entryCreateBuiltinBufferCases
Ancestors
  entryCreateBuiltinHashSupport

(* Compatibility interface for an unguarded scoped child judgment. *)
Theorem create_keccak_vv_scoped_at:
  expr_body_pre ce cx env (Builtin ann Keccak256 [e]) es /\
  expr_vv_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx ty (Builtin ann Keccak256 [e]) es
    (st0,a,b,sha,shb,vv,s0,G0,tn0) /\
  expr_sim_scoped (DF,lo,d,C,shC,PG,f,shf) ce cx (expr_type e) e es /\
  (!x m. lower_value compile_expr ce (expr_type e) e a = (x,m) ==>
    (!marks. create_operand_focus_scope a m (gas_explicit_sites C shC) C f s0 marks ==>
             create_operand_focus_scope a b (gas_explicit_sites C shC) C f s0 marks) /\
    (!marks r. exit_result r /\ create_operand_full_scope a m (gas_explicit_sites C shC) C f s0 marks r ==>
               create_operand_full_scope a b (gas_explicit_sites C shC) C f s0 marks r) /\
    (!left t right. create_operand_full_scope a m (gas_explicit_sites C shC) C f s0 left (OK t) /\
                    create_operand_focus_scope m b (gas_explicit_sites C shC) C f t right ==>
                    create_operand_focus_scope a b (gas_explicit_sites C shC) C f s0 (left ++ right)) /\
    (!left t right r. create_operand_full_scope a m (gas_explicit_sites C shC) C f s0 left (OK t) /\
                      create_operand_full_scope m b (gas_explicit_sites C shC) C f t right r ==>
                      create_operand_full_scope a b (gas_explicit_sites C shC) C f s0 (left ++ right) r)) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) (cx_tops cx) cx st0 a b
    (eval_expr cx (Builtin ann Keccak256 [e])) (es,s0,G0,tn0)
    (expr_vv_sim_full_post (DF,lo,d,C,f) ce cx (Builtin ann Keccak256 [e]) (es,a,b,s0,vv,G0,tn0))
    (create_operand_exit_post C cx)
Proof
  strip_tac >> irule create_keccak_vv_scoped_site >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >>
  fs[entryCreateFocusSpecTheory.expr_sim_scoped_def] >> metis_tac[]
QED
