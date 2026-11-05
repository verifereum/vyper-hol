Theory entryReachBodyExactChildOwnership
Ancestors
  entryReachBodyExactArrayLoop calldataChildFrame calldataMembers
  abiDecoderFrame valueEncoding valueEncodingProps venomMemDefs
  venomState finite_map arithmetic list

Theorem entry_child_exact_prefix:
  abi_decode_footprint_frame
    ((d+32+j*type_memory_size tv,type_memory_size tv)::scratch) s t /\ alloca_inv t /\
  (!id. id < lo \/ hi <= id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (oid < lo \/ hi <= oid) /\ FLOOKUP s.vs_allocas oid = SOME (d,cap) /\
  32+j*type_memory_size tv <= cap /\
  (!q len. MEM (q,len) scratch ==>
    ?id. lo <= id /\ id < hi /\ FLOOKUP t.vs_allocas id = SOME (q,len)) /\
  j <= LENGTH xs /\ EVERY (val_wf tv) xs /\ entry_loop_prefix tv xs d j s ==>
  entry_loop_prefix tv xs d j t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [entry_loop_prefix_def] >> rpt strip_tac >>
  `val_wf tv (EL k xs)` by (fs[EVERY_EL] >> first_x_assum irule >> decide_tac) >>
  `val_in_memory tv (EL k xs) (d+32+k*type_memory_size tv) s.vs_memory` by
    fs[entry_loop_prefix_def] >>
  `SUC k <= j` by decide_tac >>
  `SUC k*type_memory_size tv <= j*type_memory_size tv` by
    (irule LESS_MONO_MULT >> simp[]) >>
  rule_assum_tac (PURE_REWRITE_RULE [MULT_CLAUSES]) >>
  irule calldata_member_value_preserved >>
  qpat_assum `abi_decode_footprint_frame _ _ _` (irule_at Any) >>
  qpat_assum `FLOOKUP _ _ = SOME _` (irule_at Any) >>
  qexistsl_tac [`lo`,`hi`] >> asm_rewrite_tac [] >>
  rpt conj_tac >> decide_tac
QED

Theorem entry_child_exact_prefix_extend:
  abi_decode_footprint_frame
    ((d+32+j*type_memory_size tv,type_memory_size tv)::scratch) s t /\ alloca_inv t /\
  (!id. id < lo \/ hi <= id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (oid < lo \/ hi <= oid) /\ FLOOKUP s.vs_allocas oid = SOME (d,cap) /\
  32+j*type_memory_size tv <= cap /\
  (!q len. MEM (q,len) scratch ==>
    ?id. lo <= id /\ id < hi /\ FLOOKUP t.vs_allocas id = SOME (q,len)) /\
  j < LENGTH xs /\ EVERY (val_wf tv) xs /\ entry_loop_prefix tv xs d j s /\
  val_in_memory tv (EL j xs) (d+32+j*type_memory_size tv) t.vs_memory ==>
  entry_loop_prefix tv xs d (SUC j) t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `j <= LENGTH xs` by decide_tac >>
  drule_all entry_child_exact_prefix >>
  simp_tac bool_ss [entry_loop_prefix_def] >> rpt strip_tac >>
  Cases_on `k = j` >> gvs[] >> first_x_assum irule >> decide_tac
QED

(* Ownership postcondition expected by an exact-value recursive callback. *)
Theorem entry_child_exact_callback_ownership[local]:
  abi_decode_footprint_frame
    ((d+32+j*type_memory_size tv,type_memory_size tv)::scratch) s t /\ alloca_inv t /\
  (!id. id < lo \/ hi <= id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (oid < lo \/ hi <= oid) /\ FLOOKUP s.vs_allocas oid = SOME (d,cap) /\
  32+j*type_memory_size tv <= cap /\
  (!q len. MEM (q,len) scratch ==>
    ?id. lo <= id /\ id < hi /\ FLOOKUP t.vs_allocas id = SOME (q,len)) /\
  j < LENGTH xs /\ EVERY (val_wf tv) xs /\ entry_loop_prefix tv xs d j s /\
  val_in_memory tv (EL j xs) (d+32+j*type_memory_size tv) t.vs_memory /\
  (counter_id < lo \/ hi <= counter_id) /\
  FLOOKUP s.vs_allocas counter_id = SOME (counter,32) /\
  (counter+32 <= d+32+j*type_memory_size tv \/
    d+32+j*type_memory_size tv+type_memory_size tv <= counter) ==>
  entry_loop_prefix tv xs d (SUC j) t /\
  FLOOKUP t.vs_allocas counter_id = SOME (counter,32) /\
  mload counter t = mload counter s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all entry_child_exact_prefix_extend >> disch_tac >>
  drule_all calldata_child_preserves_counter >>
  strip_tac >> asm_rewrite_tac []
QED
