(* Storage/transient For copy endpoint interpretation. *)
Theory bodyFullForStorage
Ancestors
  exprPtrUnwrapStoragePost exprPtrUnwrapCopyPost exprPtrUnwrapRuntimeFrame
  exprPtrUnwrapLoopInvariant slotCopyExecution stmtSimDefs bodyPtrDefs
  ptrDiscipline compileEnv venomState finite_map words arithmetic

(* The endpoint is supplied by the joint execution adapter. Semantic ownership
   is refreshed at its current source entry, not saved from iterator evaluation. *)
Theorem for_storage_element_copy_post:
  !cx typ ty tv tag ptr tr src root n nb id cs cenv es s G tn w
   (d:bytes32) regions z Gf tnf.
    evaluate_type (get_tenv cx) typ = SOME ty /\
    n = type_slot_size ty /\
    storage_holds cx tr typ tv w es s /\
    ptr_vv_ok cx typ tv (LocatedValue tag ptr) es G tn s /\
    ptr.ptr_location = slot_loc tr /\ ptr.ptr_operand = src /\
    eval_operand src s = SOME w /\
    local_region cenv es.scopes s id (w2n d) nb /\ 32*n <= nb /\
    (!aid off sz.
       FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
       aid < cs.cs_next_id /\
       (!name b sz'. local_region cenv es.scopes s name b sz' ==>
          off+sz <= b \/ b+sz' <= off) ==>
       off+sz <= w2n d \/ w2n d+32*n <= off) /\
    slot_copy_inv cs (if tr then TLOAD else SLOAD)
      s w d n regions n z /\
    slot_copy_ghost_inv cs (if tr then TLOAD else SLOAD)
      w d root n G tn n Gf tnf z /\
    slot_copy_runtime_frame cs d n s z ==>
    ?v.
      read_result cx tv es = (INL v,es) /\
      (!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
        val_in_memory ty v (w2n d) mem) /\
      z.vs_alloca_next = s.vs_alloca_next /\ z.vs_allocas = s.vs_allocas /\
      ptr_covers Gf tnf root z (32*n) /\
      create_memory_snapshot regions z /\
      (!j. j<n ==> mem_word_at (w2n d+32*j) z.vs_memory =
        slot_copy_word (if tr then TLOAD else SLOAD) s (w+n2w j)) /\
      (!j b. j<n /\ b<32 /\ w2n d+32*j+b IN tnf.t_mem ==>
        b IN key_taint (if tr then tn.t_trans else tn.t_stor) (w+n2w j)) /\
      (!op. slot_copy_external cs op ==>
        eval_operand op z = eval_operand op s) /\
      (!x. slot_copy_external cs (Var x) ==>
        FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tnf (Var x) = op_taint tn (Var x)) /\
      (!a k. a+k <= w2n d \/ w2n d+32*n <= a ==>
        mem_bytes_at a k z.vs_memory = mem_bytes_at a k s.vs_memory) /\
      (!a. ~(w2n d <= a /\ a < w2n d+32*n) ==>
        (a IN tnf.t_mem <=> a IN tn.t_mem)) /\
      (!aid off sz i.
        FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
        aid < cs.cs_next_id /\
        (!name b sz'. local_region cenv es.scopes s name b sz' ==>
          off+sz <= b \/ b+sz' <= off) /\ off<=i /\ i<off+sz ==>
        mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  drule copy_prefix_words >> strip_tac >>
  drule copy_prefix_taint >> strip_tac >>
  `!j b. j<n /\ b<32 /\ w2n d+32*j+b IN tnf.t_mem ==>
    b IN key_taint (if tr then tn.t_trans else tn.t_stor) (w+n2w j)` by
    (Cases_on `tr` >> gvs[]) >>
  `?v. read_result cx tv es = (INL v,es) /\
    !mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
      val_in_memory ty v (w2n d) mem` by
    (irule unwrap_storage_copied_robust >>
     goal_assum (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
     qexistsl [`tr`, `w`] >> gvs[]) >>
  qexists `v` >>
  gvs[slot_copy_inv_def, slot_copy_ghost_inv_def, slot_copy_runtime_frame_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `off+sz <= w2n d \/ 32*type_slot_size ty+w2n d <= off` by
    (qpat_x_assum `!aid off sz. _` irule >> metis_tac[]) >>
  `~(w2n d <= i /\ i < 32*type_slot_size ty+w2n d)` by decide_tac >>
  metis_tac[]
QED
