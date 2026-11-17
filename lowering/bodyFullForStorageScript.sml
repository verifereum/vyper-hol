(* Joint execution for the existing loop-local storage-copy destination. *)
Theory bodyFullForStorage
Ancestors
  bodyFullToplevelSlotEntry bodyFullToplevelSlotLoopFrame
  exprPtrUnwrapLoopInvariant exprPtrUnwrapRuntimeFrame exprSimStorageCopy
  copyExecution slotCopyExecution stmtLowering loweringPosts
  fragGasOriginPtr venomState arithmetic

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
