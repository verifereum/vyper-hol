(* Protection of completed source values across allocating decoder children. *)
Theory entryReachBodyRegisteredChild
Ancestors
  valueEncodingDefs loweringStateRelDefs ctorAbiActualMemory abiEncoderRegisteredEffect entryReachBodyExactChildOwnership
  entryReachBodyExactArrayLoop
  valueEncodingProps venomMemDefs finite_map pred_set arithmetic list

Theorem entry_registered_child_slice:
  abi_encoder_registered_effect ids [(c,k)] s t /\ alloca_inv t /\
  oid NOTIN ids /\ FLOOKUP s.vs_allocas oid = SOME (d,cap) /\
  d <= p /\ p+n <= d+cap /\ (p+n <= c \/ c+k <= p) ==>
  mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule ctor_actual_registered_window >>
  qexistsl_tac [`ids`,`[(c,k)]`] >>
  reverse conj_tac
  >- (asm_rewrite_tac[] >> simp[] >> rpt strip_tac >> decide_tac) >>
  `FLOOKUP t.vs_allocas oid = SOME (d,cap)` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  rpt strip_tac >>
  `oid <> i` by metis_tac[] >>
  `d+cap <= b \/ b+sz <= d` by
    (qpat_assum `alloca_inv t` mp_tac >>
     pure_rewrite_tac[alloca_inv_def, allocas_non_overlapping_def] >>
     metis_tac[]) >>
  simp[regions_disjoint_def] >> decide_tac
QED

Theorem entry_registered_child_prefix:
  abi_encoder_registered_effect ids
    [(d+32+j*type_memory_size tv,type_memory_size tv)] s t /\
  alloca_inv t /\ oid NOTIN ids /\
  FLOOKUP s.vs_allocas oid = SOME (d,cap) /\
  32+j*type_memory_size tv <= cap /\ j <= LENGTH xs /\
  EVERY (val_wf tv) xs /\ entry_loop_prefix tv xs d j s ==>
  entry_loop_prefix tv xs d j t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [entry_loop_prefix_def] >> rpt strip_tac >>
  `val_wf tv (EL k xs)` by
    (fs[EVERY_EL] >> first_x_assum irule >> decide_tac) >>
  `val_in_memory tv (EL k xs) (d+32+k*type_memory_size tv) s.vs_memory` by
    fs[entry_loop_prefix_def] >>
  `SUC k <= j` by decide_tac >>
  `SUC k*type_memory_size tv <= j*type_memory_size tv` by
    (irule LESS_MONO_MULT >> simp[]) >>
  rule_assum_tac (PURE_REWRITE_RULE [MULT_CLAUSES]) >>
  `mem_bytes_at (d+32+k*type_memory_size tv) (type_memory_size tv) t.vs_memory =
   mem_bytes_at (d+32+k*type_memory_size tv) (type_memory_size tv) s.vs_memory` by
    (irule entry_registered_child_slice >>
     qpat_assum `abi_encoder_registered_effect _ _ _ _` (irule_at Any) >>
     qpat_assum `FLOOKUP _ _ = SOME _` (irule_at Any) >>
     asm_rewrite_tac[] >> rpt conj_tac >> decide_tac) >>
  irule val_in_memory_mem_agree >> conj_tac >- asm_rewrite_tac[] >>
  qexistsl_tac [`type_memory_size tv`,`s.vs_memory`] >> asm_rewrite_tac[] >> simp[]
QED

Theorem entry_registered_child_prefix_extend:
  abi_encoder_registered_effect ids
    [(d+32+j*type_memory_size tv,type_memory_size tv)] s t /\
  alloca_inv t /\ oid NOTIN ids /\
  FLOOKUP s.vs_allocas oid = SOME (d,cap) /\
  32+j*type_memory_size tv <= cap /\ j < LENGTH xs /\
  EVERY (val_wf tv) xs /\ entry_loop_prefix tv xs d j s /\
  val_in_memory tv (EL j xs) (d+32+j*type_memory_size tv) t.vs_memory ==>
  entry_loop_prefix tv xs d (SUC j) t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `j <= LENGTH xs` by decide_tac >>
  drule_all entry_registered_child_prefix >>
  simp_tac bool_ss [entry_loop_prefix_def] >> rpt strip_tac >>
  Cases_on `k = j` >> gvs[] >> first_x_assum irule >> decide_tac
QED

(* Memory effects alone do not supply these observable fields. Recursive
   executions must establish fields, frontier and history at their endpoint. *)
Theorem entry_registered_fields_trans:
  entry_loop_fields s t /\ entry_loop_fields t u ==> entry_loop_fields s u
Proof
  simp[entry_loop_fields_def] >> metis_tac[]
QED
