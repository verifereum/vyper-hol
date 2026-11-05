(* Convert word-indexed copy taint into the natural slot coordinates used
   by storage_range_copied_robust.  The source bound permits equality at
   dimword only for the exclusive end, never for a copied key. *)
Theory exprPtrUnwrapTaintKeys
Ancestors
  exprPtrUnwrapStorageFacts exprPtrUnwrapStorageLoop abiDecodeStaticProps
  ptrSafeRun ptrDiscipline words

Theorem copy_key_nonwrapping:
  w2n (p:bytes32) + type_slot_size tv <= dimword (:256) /\
  i < type_slot_size tv ==>
  w2n (p+n2w i) = w2n p+i
Proof
  strip_tac >> irule w2n_add_n2w_lt >> simp[]
QED

Theorem copy_taint_dead_bytes:
  w2n (p:bytes32) + type_slot_size tv <= dimword (:256) /\
  (!i b. i < type_slot_size tv /\ b < 32 /\ dst+32*i+b IN m ==>
    b IN key_taint ts (p+n2w i)) /\
  (!k b. w2n p <= w2n k /\ w2n k < w2n p+type_slot_size tv /\
    b < 32 /\ (k,b) IN ts ==> dead_bytes rt (w2n p) tv (w2n k) b) ==>
  !i b. i < type_slot_size tv /\ b < 32 /\ dst+32*i+b IN m ==>
    dead_bytes rt (w2n p) tv (w2n p+i) b
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `w2n (p+n2w i) = w2n p+i` by
    (irule copy_key_nonwrapping >> qexists `tv` >> simp[]) >>
  `b IN key_taint ts (p+n2w i)` by metis_tac[] >>
  qpat_x_assum `!k b. _` (qspecl_then [`p+n2w i`, `b`] mp_tac) >>
  simp[] >> gvs[key_taint_def]
QED

Theorem copy_prefix_dead_bytes:
  w2n (p:bytes32) + type_slot_size tv <= dimword (:256) /\
  slot_copy_ghost_inv cs load p d root n G0 tn0 (type_slot_size tv) G tn s /\
  (!k b. w2n p <= w2n k /\ w2n k < w2n p+type_slot_size tv /\
    b < 32 /\ (k,b) IN (if load=SLOAD then tn0.t_stor else tn0.t_trans) ==>
    dead_bytes rt (w2n p) tv (w2n k) b) ==>
  !i b. i < type_slot_size tv /\ b < 32 /\ w2n d+32*i+b IN tn.t_mem ==>
    dead_bytes rt (w2n p) tv (w2n p+i) b
Proof
  strip_tac >>
  mp_tac (Q.INST [`dst` |-> `w2n d`, `m` |-> `tn.t_mem`,
    `ts` |-> `if load=SLOAD then tn0.t_stor else tn0.t_trans`]
    (SPEC_ALL copy_taint_dead_bytes)) >>
  (impl_tac >- (simp[] >> drule copy_prefix_taint >> simp[])) >> simp[]
QED
