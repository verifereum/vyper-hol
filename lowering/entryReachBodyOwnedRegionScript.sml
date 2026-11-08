(* Ownership of decoded intervals inside an enclosing argument allocation. *)
Theory entryReachBodyOwnedRegion
Ancestors
  entryReachBodyRegisteredChild entryReachBodyReentryResources
  entryReachBodyExactArrayLoop abiEncoderRegisteredEffect valueEncodingProps
  venomMemDefs finite_map pred_set arithmetic list

Definition entry_owned_region_def:
  entry_owned_region oid root extent d sz s <=>
    FLOOKUP s.vs_allocas oid = SOME (root,extent) /\
    root <= d /\ d+sz <= root+extent
End

Theorem entry_owned_region_counter_separation:
  entry_owned_region oid root extent d sz s /\ alloca_inv s /\ oid <> aid /\
  ((FLOOKUP s.vs_allocas aid = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas aid = SOME (p,32)) ==>
  (root+extent <= p \/ p+32 <= root) /\ (d+sz <= p \/ p+32 <= d)
Proof
  strip_tac >>
  `root+extent <= p \/ p+32 <= root` by
    (irule entry_index_counter_owner_separation >>
     qexistsl_tac [`aid`,`extent`,`oid`,`s`] >>
     fs[entry_owned_region_def]) >>
  fs[entry_owned_region_def] >> decide_tac
QED

Theorem entry_owned_child_prefix:
  abi_encoder_registered_effect ids
    [(d+32+j*type_memory_size tv,type_memory_size tv)] s t /\
  alloca_inv t /\ oid NOTIN ids /\ entry_owned_region oid root extent d sz s /\
  32+j*type_memory_size tv <= sz /\ j <= LENGTH xs /\
  EVERY (val_wf tv) xs /\ entry_loop_prefix tv xs d j s ==>
  entry_loop_prefix tv xs d j t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `entry_owned_region _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_owned_region_def]) >>
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

Theorem entry_owned_child_prefix_extend:
  abi_encoder_registered_effect ids
    [(d+32+j*type_memory_size tv,type_memory_size tv)] s t /\
  alloca_inv t /\ oid NOTIN ids /\ entry_owned_region oid root extent d sz s /\
  32+j*type_memory_size tv <= sz /\ j < LENGTH xs /\
  EVERY (val_wf tv) xs /\ entry_loop_prefix tv xs d j s /\
  val_in_memory tv (EL j xs) (d+32+j*type_memory_size tv) t.vs_memory ==>
  entry_loop_prefix tv xs d (SUC j) t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `j <= LENGTH xs` by decide_tac >>
  drule_all entry_owned_child_prefix >>
  simp_tac bool_ss [entry_loop_prefix_def] >> rpt strip_tac >>
  Cases_on `k = j` >> gvs[] >> first_x_assum irule >> decide_tac
QED

Theorem entry_owned_region_preserved:
  entry_owned_region oid root extent d sz s /\ oid NOTIN ids /\
  abi_encoder_registered_effect ids writes s t ==>
  entry_owned_region oid root extent d sz t
Proof
  simp_tac bool_ss [entry_owned_region_def] >> strip_tac >>
  drule_all abi_encoder_registered_effect_allocated >> simp[]
QED

(* The actual array element layout is a valid interior window of the owner. *)
Theorem entry_owned_array_element:
  entry_owned_region oid root extent d sz s /\
  32+LENGTH xs*type_memory_size tv <= sz /\ j < LENGTH xs ==>
  entry_owned_region oid root extent (d+32+j*type_memory_size tv)
    (type_memory_size tv) s
Proof
  strip_tac >>
  `SUC j*type_memory_size tv <= LENGTH xs*type_memory_size tv` by
    (irule LESS_MONO_MULT >> simp[]) >>
  qpat_x_assum `SUC j * _ <= _`
    (assume_tac o PURE_REWRITE_RULE [MULT_CLAUSES]) >>
  fs[entry_owned_region_def] >> decide_tac
QED
