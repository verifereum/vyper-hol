Theory exprPtrUnwrapStoragePost
Ancestors
  exprPtrUnwrapCopyPost exprPtrUnwrapStorageFacts exprPtrUnwrapLoopInvariant
  exprPtrUnwrapStorage ptrDiscipline bodyPtrDefs exprSimPtrProps
  abiDecodeStaticProps words pred_set exprSimMemorySource loweringPosts

(* The copied prefix may be tainted, but only in its type's dead bytes. *)
Theorem copy_prefix_storage_dead:
  ptr_vv_ok cx t tv (LocatedValue t' p) es G0 tn0 r /\
  p.ptr_location = slot_loc tr /\
  eval_operand p.ptr_operand r = SOME w /\
  evaluate_type (get_tenv cx) t = SOME ty /\
  w2n w + type_slot_size ty <= dimword (:256) /\
  slot_copy_ghost_inv cs (if tr then TLOAD else SLOAD) w d root
    (type_slot_size ty) G0 tn0 (type_slot_size ty) G tn s ==>
  !j b. j < type_slot_size ty /\ b < 32 /\ w2n d+32*j+b IN tn.t_mem ==>
    dead_bytes
      (if tr then r.vs_transient r.vs_call_ctx.cc_address
       else (r.vs_accounts r.vs_call_ctx.cc_address).storage)
      (w2n w) ty (w2n w+j) b
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `w2n (w+n2w j) = w2n w+j` by
    (irule w2n_add_n2w_lt >> simp[] >> decide_tac) >>
  drule copy_prefix_taint >>
  disch_then (qspecl_then [`j`, `b`] mp_tac) >> simp[] >> strip_tac >>
  drule ptr_vv_ok_storage_taint >>
  disch_then (qspecl_then [`w`, `ty`, `w+n2w j`, `b`] mp_tac) >> simp[] >>
  Cases_on `tr` >> gvs[slot_loc_def, key_taint_def]
QED
