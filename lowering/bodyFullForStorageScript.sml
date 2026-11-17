(* Joint execution and interpretation for the existing storage-copy destination. *)
Theory bodyFullForStorage
Ancestors
  bodyFullToplevelSlotEntry bodyFullToplevelSlotLoopFrame
  exprPtrUnwrapLoopInvariant exprPtrUnwrapRuntimeFrame exprSimStorageCopy
  copyExecution slotCopyExecution stmtLowering loweringPosts
  fragGasOriginPtr venomState arithmetic
  exprPtrUnwrapStoragePost exprPtrUnwrapCopyPost stmtSimDefs bodyPtrDefs
  ptrDiscipline compileEnv finite_map words

Theorem for_storage_element_copy_run:
  !ce tyarr ann nid ca place cb cenv typ tr src root n cs sb lo ctx func
   PG s G tn w (d:bytes32) regions.
    compile_expr ce tyarr (TopLevelName ann nid) ca = (place,cb) /\
    compile_iter_elem_copy cenv src (Var root) n (slot_loc tr) T
      typ typ cs = ((),sb) /\
    compile_slot_to_memory src (Var root) n (slot_loc tr) cs =
      (slot_copy_body cs,sb) /\
    eval_operand src s = SOME w /\ lookup_var root s = SOME d /\
    op_taint tn src = {} /\
    slot_copy_external cs src /\ slot_copy_external cs (Var root) /\
    ptr_covers G tn root s (32*n) /\
    n < 2**256 /\ w2n d+32*n < 2**256 /\
    w2n d+32*n <= s.vs_alloca_next /\
    create_memory_snapshot regions s /\
    EVERY (\(off,bs). off+LENGTH bs <= LENGTH s.vs_memory /\
      (off+LENGTH bs <= w2n d \/ w2n d+32*n <= off)) regions /\
    s.vs_current_bb = cs.cs_current_bb /\
    s.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~s.vs_halted /\
    lookup_block cs.cs_current_bb func.fn_blocks =
      SOME <|bb_label := cs.cs_current_bb;
             bb_instructions := cs.cs_current_insts ++ slot_copy_init_insts cs|> /\
    lookup_block (slot_copy_cond cs) func.fn_blocks =
      SOME <|bb_label := slot_copy_cond cs;
             bb_instructions := slot_copy_cond_insts cs n|> /\
    lookup_block (slot_copy_body cs) func.fn_blocks =
      SOME <|bb_label := slot_copy_body cs;
             bb_instructions := slot_copy_body_insts cs src (Var root)
               (if tr then TLOAD else SLOAD)|> /\
    allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
    ?z Gf tnf.
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK z,Gf,tnf)) /\
      z.vs_current_bb = slot_copy_exit cs /\ z.vs_inst_idx = 0 /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~z.vs_halted /\
      slot_copy_inv cs (if tr then TLOAD else SLOAD) s w d n regions n z /\
      slot_copy_ghost_inv cs (if tr then TLOAD else SLOAD)
        w d root n G tn n Gf tnf z /\
      slot_copy_runtime_frame cs d n s z /\
      allocas_from lo z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
      z.vs_alloca_next = s.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks =
    SOME <|bb_label := cs.cs_current_bb;
           bb_instructions := cs.cs_current_insts ++ slot_copy_init_insts cs|>`
    by simp[] >>
  qmatch_asmsub_abbrev_tac `lookup_block s.vs_current_bb func.fn_blocks = SOME initbb` >>
  `initbb.bb_instructions = cs.cs_current_insts ++ slot_copy_init_insts cs`
    by simp[Abbr `initbb`] >>
  drule_all toplevel_slot_copy_initial_joint >>
  disch_then (qspecl_then [`w`, `if tr then TLOAD else SLOAD`, `PG`]
    strip_assume_tac) >>
  qabbrev_tac `h = slot_copy_initial cs s` >>
  `slot_copy_runtime_frame cs d 0 s h` by
    simp[Abbr `h`, slot_copy_runtime_frame_initial] >>
  `~h.vs_halted /\ h.vs_current_bb = slot_copy_cond cs /\
   h.vs_inst_idx = 0 /\ h.vs_alloca_next = s.vs_alloca_next` by
    simp[Abbr `h`, slot_copy_initial_def, jump_to_def, update_var_def] >>
  `op_taint tn1 src = {}` by metis_tac[copy_ghost_external_taint] >>
  qmatch_asmsub_abbrev_tac `lookup_block (slot_copy_cond cs) func.fn_blocks = SOME condbb` >>
  qmatch_asmsub_abbrev_tac `lookup_block (slot_copy_body cs) func.fn_blocks = SOME bodybb` >>
  `condbb.bb_instructions = slot_copy_cond_insts cs n /\
   bodybb.bb_instructions = slot_copy_body_insts cs src (Var root)
     (if tr then TLOAD else SLOAD)` by simp[Abbr `condbb`, Abbr `bodybb`] >>
  `0 <= n /\ w2n d+32*n <= h.vs_alloca_next` by simp[] >>
  Q.SUBGOAL_THEN `(if tr then TLOAD else SLOAD) = SLOAD \/
    (if tr then TLOAD else SLOAD) = TLOAD` assume_tac
    >- (Cases_on `tr` >> simp[]) >>
  drule_all toplevel_slot_copy_joint_finish_framed >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `~t.vs_halted` by
    (qpat_x_assum `slot_copy_runtime_frame cs d n s t` mp_tac >>
     simp[slot_copy_runtime_frame_def] >> strip_tac >>
     drule copy_static_fields >> simp[]) >>
  Q.SUBGOAL_THEN `slot_loc tr = LocStorage \/ slot_loc tr = LocTransient` assume_tac
    >- (Cases_on `tr` >> simp[slot_loc_def]) >>
  drule_all compile_slot_to_memory_boundary >> strip_tac >>
  qexistsl [`t`, `Gf`, `tnf`] >> simp[] >>
  rpt gen_tac >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspecl_then [`D`, `explicit`]
      (mp_then Any mp_tac gas_origin_ptr_path_append)) >>
  disch_then (qspecl_then [`h`, `G1`, `tn1`, `[]`] mp_tac) >>
  simp[] >> disch_then irule >> simp[]
QED

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
