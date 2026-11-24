(* Scoped clients can retain a certificate on the actual witness. This is
   the non-exempt part of gas_outcome_full with two additional posts. *)
Theory bodyFullIntCallReturnWitness
Ancestors gasOutcomeFull exprLowering fragExec fragGasOriginPtr

Definition intcall_return_witness_def:
  intcall_return_witness (DF,lo,explicit,ctx,func,PG) cx st0 source
      (es,s,G,tn) Q R bad_scope full_scope <=>
    ?marks.
      (gas_bad_storage_at cx st0 source es s marks /\ bad_scope marks /\
       ?H leaf leaf_pg leaf_g leaf_tn finish.
         (storage_trace_domain cx st0 es.storage_trace ==>
          valid_horizon cx st0 H es.storage_trace) /\
         gas_origin_ptr_focus (DF H,lo,explicit,ctx,func,PG)
           (s,G,tn) marks (leaf,leaf_pg,leaf_g,leaf_tn,finish)) \/
      (?res ee r G' tn'.
        full_scope marks r /\
        (!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
           (res,ee with gas_obs := tail)) /\
        storage_trace_domain cx st0 ee.storage_trace /\
        !H. valid_horizon cx st0 H ee.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
            (s,G,tn) marks (r,G',tn') /\
          ((?t. r = OK t /\ Q H res (ee with gas_obs := []) G' tn' t) \/
           (exit_result r /\ R H res (ee with gas_obs := []) (G',tn') r)))
End

Theorem intcall_return_witness_full:
  intcall_return_witness (DF,lo,explicit,ctx,func,PG) cx st0 source
    (es,s,G,tn) Q R bad_scope full_scope ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q R
Proof
  rw[intcall_return_witness_def,gas_outcome_full_def] >> qexists_tac `marks` >>
  metis_tac[]
QED

(* Scope is discharged at the caller edge and, for a register return,
   the exact run of the emitted result stores. Legacy clients use True. *)
Definition intcall_return_scope_rules_def:
  intcall_return_scope_rules explicit ctx func t sm bad_scope full_scope <=>
    (!marks r. exit_result r /\ gas_origin_edge T explicit ctx func t marks r ==>
       full_scope marks r) /\
    (!marks u. gas_origin_edge T explicit ctx func t marks (OK u) /\
       u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts ==>
       full_scope marks (OK u)) /\
    (!marks u st4 root ops stored.
       gas_origin_edge T explicit ctx func t marks (OK u) /\
       store_multi_results (Var root) ops 0 st4 = ((),sm) /\ fn_has_code st4 sm func /\
       ~u.vs_halted /\ u.vs_current_bb = st4.cs_current_bb /\
       u.vs_inst_idx = LENGTH st4.cs_current_insts /\
       run_inst_seq (emitted_insts st4 sm) u = OK stored ==>
       full_scope marks (OK (stored with vs_inst_idx := LENGTH sm.cs_current_insts))) /\
    (!marks u. full_scope marks (OK u) ==> bad_scope marks)
End

Theorem intcall_return_scope_abort:
  intcall_return_scope_rules explicit ctx func t sm bad_scope full_scope /\
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (t,G,tn) marks (r,G',tn') /\
  exit_result r ==> full_scope marks r
Proof
  simp[intcall_return_scope_rules_def,gas_origin_ptr_edge_def] >> metis_tac[]
QED

Theorem intcall_return_scope_void:
  intcall_return_scope_rules explicit ctx func t sm bad_scope full_scope /\
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (t,G,tn) marks (OK u,G',tn') /\
  u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  full_scope marks (OK u)
Proof
  simp[intcall_return_scope_rules_def,gas_origin_ptr_edge_def] >> metis_tac[]
QED

Theorem intcall_return_scope_register:
  intcall_return_scope_rules explicit ctx func t sm bad_scope full_scope /\
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (t,G,tn) marks (OK u,G',tn') /\
  store_multi_results (Var root) ops 0 st4 = ((),sm) /\ fn_has_code st4 sm func /\
  ~u.vs_halted /\ u.vs_current_bb = st4.cs_current_bb /\
  u.vs_inst_idx = LENGTH st4.cs_current_insts /\
  run_inst_seq (emitted_insts st4 sm) u = OK stored ==>
  full_scope marks (OK (stored with vs_inst_idx := LENGTH sm.cs_current_insts))
Proof
  simp[intcall_return_scope_rules_def,gas_origin_ptr_edge_def] >> metis_tac[]
QED

Theorem intcall_return_scope_bad:
  intcall_return_scope_rules explicit ctx func t sm bad_scope full_scope /\
  full_scope marks (OK u) ==> bad_scope marks
Proof
  simp[intcall_return_scope_rules_def] >> metis_tac[]
QED
