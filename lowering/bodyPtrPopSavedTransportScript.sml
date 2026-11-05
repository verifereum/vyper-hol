Theory bodyPtrPopSavedTransport
Ancestors
  bodyPtrPopSavedRegion bodyPtrDefs words

val _ = Parse.hide "base";

Theorem pop_saved_storage_ptr_vv:
  op_taint tn p.ptr_operand = {} /\ p.ptr_location = LocStorage /\
  (!w ty k b. eval_operand p.ptr_operand s = SOME w /\
     evaluate_type (get_tenv cx) t = SOME ty /\
     w2n w <= w2n k /\ w2n k < w2n w + type_slot_size ty /\
     b < 32 /\ (k,b) IN tn.t_stor ==>
     dead_bytes (s.vs_accounts s.vs_call_ctx.cc_address).storage
       (w2n w) ty (w2n k) b) ==>
  ptr_vv_ok cx t result (LocatedValue t' p) es G tn s
Proof
  simp[ptr_vv_ok_def] >> metis_tac[]
QED

Theorem pop_saved_range_two_headers:
  storage_range_agree src rt w tv /\
  w2n h1 < w2n w /\ w2n h2 < w2n w ==>
  storage_range_agree
    (update_storage h2 u2 (update_storage h1 u1 src))
    (update_storage h2 v2 (update_storage h1 v1 rt)) w tv
Proof
  strip_tac >> irule pop_saved_range_header >> simp[] >>
  irule pop_saved_range_header >> simp[]
QED

Theorem pop_saved_child_taint_two_headers:
  w2n h1 < base /\ w2n h2 < base /\
  base + type_slot_size tv <= dimword (:256) /\
  inst1.inst_operands = [addr1; v1] /\
  eval_operand addr1 s0 = SOME key1 /\ op_taint tn0 v1 = {} /\
  st1 = update_storage h1 u1 st /\
  tn1 = step_taint inst1 s0 s1 tn0 /\
  inst2.inst_operands = [addr2; v2] /\
  eval_operand addr2 s1 = SOME key2 /\ op_taint tn1 v2 = {} /\
  st2 = update_storage h2 u2 st1 /\
  tn2 = step_taint inst2 s1 s2 tn1 /\
  (!k b. (k,b) IN tn0.t_stor /\ base <= w2n k /\
     w2n k < base + type_slot_size tv ==> dead_bytes st base tv (w2n k) b) ==>
  !k b. (k,b) IN tn2.t_stor /\ base <= w2n k /\
    w2n k < base + type_slot_size tv ==> dead_bytes st2 base tv (w2n k) b
Proof
  strip_tac >>
  `!k b. (k,b) IN tn1.t_stor /\ base <= w2n k /\
     w2n k < base + type_slot_size tv ==> dead_bytes st1 base tv (w2n k) b`
    by (gvs[] >> metis_tac[pop_saved_child_taint_header]) >>
  gvs[] >> metis_tac[pop_saved_child_taint_header]
QED

(* Consumer endpoint for the local taint implication, independent of liveness. *)
Theorem pop_saved_storage_ptr_at_base:
  base < dimword (:256) /\
  op_taint tn p.ptr_operand = {} /\ p.ptr_location = LocStorage /\
  eval_operand p.ptr_operand s = SOME (n2w base) /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  (!k b. (k,b) IN tn.t_stor /\ base <= w2n k /\
     w2n k < base + type_slot_size tv ==> dead_bytes st base tv (w2n k) b) /\
  (s.vs_accounts s.vs_call_ctx.cc_address).storage = st ==>
  ptr_vv_ok cx t result (LocatedValue t' p) es G tn s
Proof
  strip_tac >> irule pop_saved_storage_ptr_vv >> simp[] >>
  rpt strip_tac >> gvs[w2n_n2w] >> metis_tac[]
QED

(* Both ancestor lengths become zero; the saved child need not be globally live. *)
Theorem pop_saved_two_zero_headers_ptr:
  w2n h1 < base /\ w2n h2 < base /\
  base + type_slot_size tv <= dimword (:256) /\
  base < dimword (:256) /\ 0 < type_slot_size tv /\
  inst1.inst_operands = [addr1; v1] /\
  eval_operand addr1 s0 = SOME key1 /\ op_taint tn0 v1 = {} /\
  st1 = update_storage h1 0w st /\
  tn1 = step_taint inst1 s0 s1 tn0 /\
  inst2.inst_operands = [addr2; v2] /\
  eval_operand addr2 s1 = SOME key2 /\ op_taint tn1 v2 = {} /\
  st2 = update_storage h2 0w st1 /\
  tn2 = step_taint inst2 s1 s2 tn1 /\
  (!k b. (k,b) IN tn0.t_stor /\ base <= w2n k /\
     w2n k < base + type_slot_size tv ==> dead_bytes st base tv (w2n k) b) /\
  (s2.vs_accounts s2.vs_call_ctx.cc_address).storage = st2 /\
  eval_operand p.ptr_operand s2 = SOME (n2w base) /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  op_taint tn2 p.ptr_operand = {} /\ p.ptr_location = LocStorage ==>
  ptr_vv_ok cx t result (LocatedValue t' p) es G tn2 s2
Proof
  strip_tac >>
  `!k b. (k,b) IN tn2.t_stor /\ base <= w2n k /\
     w2n k < base + type_slot_size tv ==> dead_bytes st2 base tv (w2n k) b`
    by (metis_tac[pop_saved_child_taint_two_headers]) >>
  irule pop_saved_storage_ptr_at_base >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `base` >> gvs[]
QED
