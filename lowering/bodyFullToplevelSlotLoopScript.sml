(* Joint operational boundaries for the TopLevelName slot-copy loop. *)
Theory bodyFullToplevelSlotLoop
Ancestors
  exprPtrUnwrapLoopInvariant exprPtrUnwrapGeneratedBody
  exprPtrUnwrapCopyEdges exprPtrUnwrapCondition exprPtrUnwrapBackedge
  slotCopyExecution copyExecution fragGasSeqPtr fragGasOriginPtr
  fragGasOrigin fragGasPathPtr fragGasPathMem gasEvents gasCount
  memSafeRun fragExecMem instMemFrontier unitTransformDefs exprLoweringProps exprLowering
  bodyPtrDefs ptrDiscipline ptrSafeRun venomExecSemantics venomState venomInst
  codegenRel contextCodegenRel finite_map pred_set list rich_list arithmetic words

Theorem toplevel_slot_copy_control_edge[local]:
  compile_expr cenv ty (TopLevelName ann nsid) ca = (place,cb) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (inst.inst_opcode = EQ \/ inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ) /\
  gas_path_ptr_edge D lo ctx func PG G tn s 0 G' tn' r ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (r,G',tn')
Proof
  strip_tac >> simp[gas_origin_ptr_edge_def] >>
  irule gas_path_mem_edge_zero_origin >>
  qpat_x_assum `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_path_ptr_edge_def, gas_path_mem_edge_def] >> strip_tac >>
  `mem_safe_step fuel ctx inst s` by
    (simp[mem_safe_step_non_invoke, inst_mem_below_frontier_def,
      inst_dload_in_section_def, source_memory_read_ranges_def,
      source_memory_write_ranges_def] >> gvs[]) >>
  metis_tac[]
QED

Theorem toplevel_slot_copy_condition_joint[local]:
  compile_expr cenv ty (TopLevelName ann nsid) ca = (place,cb) /\
  eval_operand (Var ctr) s = SOME x /\ op_taint tn (Var ctr) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id EQ [Var ctr; Lit bound] [out]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst jid JNZ [Var out; Label yes; Label no] []) /\
  u = (update_var out (bool_to_word (x=bound)) s
    with vs_inst_idx := SUC s.vs_inst_idx) /\
  G1 = step_prov PG G (mk_inst id EQ [Var ctr; Lit bound] [out])
    (update_var out (bool_to_word (x=bound)) s) /\
  tn1 = step_taint (mk_inst id EQ [Var ctr; Lit bound] [out]) s
    (update_var out (bool_to_word (x=bound)) s) tn ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (jump_to (if x=bound then yes else no) u),G1,tn1)
Proof
  strip_tac >>
  `gas_path_ptr_edge D lo ctx fn PG G tn s 0 G1 tn1 (OK u)` by
    (simp[] >> irule copy_eq_counted_edge >> metis_tac[]) >>
  `op_taint tn1 (Var out) = {}` by
    simp[step_taint_def, set_var_taint_def, out_taint_def,
         op_taint_def, mk_inst_def, FLOOKUP_UPDATE] >>
  `eval_operand (Var out) u = SOME (bool_to_word (x=bound)) /\
   allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
   ~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
   u.vs_inst_idx = SUC s.vs_inst_idx` by
    (gvs[update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
         allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `gas_path_ptr_edge D lo ctx fn PG G1 tn1 u 0 G1 tn1
     (OK (jump_to (if x=bound then yes else no) u))` by
    (irule copy_jnz_counted_edge >> simp[] >>
     qexistsl [`jid`, `Var out`] >>
     Cases_on `x=bound` >> gvs[venomExecSemanticsTheory.bool_to_word_def]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,G1,tn1)` by
    (irule toplevel_slot_copy_control_edge >>
     goal_assum (drule_at Any) >> simp[mk_inst_def] >> metis_tac[]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (u,G1,tn1) []
     (OK (jump_to (if x=bound then yes else no) u),G1,tn1)` by
    (irule toplevel_slot_copy_control_edge >>
     goal_assum (drule_at Any) >> simp[mk_inst_def] >> metis_tac[]) >>
  `~(jump_to (if x=bound then yes else no) u).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

Theorem toplevel_slot_copy_header_joint:
  compile_expr cenv ty (TopLevelName ann nsid) ca = (place,cb) /\
  slot_copy_inv cs load original p d n regions i s /\
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s /\
  slot_copy_external cs (Var root) /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = slot_copy_cond_insts cs n /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?G1 tn1.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (slot_copy_cond_result cs n i s),G1,tn1)) /\
    slot_copy_inv cs load original p d n regions i (slot_copy_cond_result cs n i s) /\
    slot_copy_ghost_inv cs load p d root n G0 tn0 i G1 tn1
      (slot_copy_cond_result cs n i s) /\
    allocas_from lo (slot_copy_cond_result cs n i s) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp (slot_copy_cond_result cs n i s))
Proof
  strip_tac >>
  `i < 2**256 /\ n < 2**256 /\
   lookup_var (slot_copy_var cs 0) s = SOME (n2w i)` by
    (fs[slot_copy_inv_def] >> decide_tac) >>
  `((n2w i:bytes32)=n2w n) <=> (i=n)` by
    (pure_rewrite_tac[n2w_11] >> fs[dimword_def]) >>
  qabbrev_tac `inst = mk_inst (cs.cs_next_id+2) EQ
    [Var (slot_copy_var cs 0); Lit (n2w n)] [slot_copy_var cs 1]` >>
  qabbrev_tac `u = update_var (slot_copy_var cs 1) (bool_to_word (i=n)) s` >>
  qabbrev_tac `G1 = step_prov PG G inst u` >>
  qabbrev_tac `tn1 = step_taint inst s u tn` >>
  qexistsl [`G1`, `tn1`] >> conj_tac
  >- (rpt gen_tac >>
      `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
        (OK (jump_to (if (n2w i:bytes32)=n2w n then slot_copy_exit cs else slot_copy_body cs)
          (u with vs_inst_idx := SUC s.vs_inst_idx)),G1,tn1)` by
        (irule toplevel_slot_copy_condition_joint >>
         simp[Abbr `G1`, Abbr `tn1`, Abbr `inst`, Abbr `u`] >>
         conj_tac >- metis_tac[] >>
         qexistsl [`slot_copy_var cs 0`, `cs.cs_next_id+2`,
                   `cs.cs_next_id+3`, `slot_copy_var cs 1`] >>
         simp[slot_copy_cond_insts_def, get_instruction_def, eval_operand_def] >>
         fs[slot_copy_ghost_inv_def]) >>
      gvs[slot_copy_cond_result_def, Abbr `u`, jump_to_def]) >>
  `tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
   allocas_from lo (slot_copy_cond_result cs n i s) = allocas_from lo s /\
   allocas_below_fmp (slot_copy_cond_result cs n i s) = allocas_below_fmp s /\
   (!v. v <> slot_copy_var cs 1 ==>
      FLOOKUP G1 v = FLOOKUP G v /\ op_taint tn1 (Var v) = op_taint tn (Var v)) /\
   (!v c. v <> slot_copy_var cs 1 /\ ptr_covers G tn v s c ==>
      ptr_covers G1 tn1 v (slot_copy_cond_result cs n i s) c)` by
    (irule copy_eq_jump_frames >>
     simp[Abbr `G1`, Abbr `tn1`, Abbr `inst`, Abbr `u`, slot_copy_cond_result_def] >>
     metis_tac[]) >>
  simp[slot_copy_condition_invariant] >> irule copy_condition_ghost_frame >>
  simp[] >> conj_tac
  >- (qpat_x_assum `!v. v <> _ ==> _ /\ _`
        (qspec_then `slot_copy_var cs 0` mp_tac) >>
      fs[slot_copy_ghost_inv_def, slot_copy_var_distinct]) >>
  qexistsl [`G`, `s`, `tn`] >> simp[]
QED

Theorem toplevel_slot_copy_joint_exit:
  compile_expr cenv ty (TopLevelName ann nsid) ca = (place,cb) /\
  slot_copy_inv cs load original p d n regions n s /\
  slot_copy_ghost_inv cs load p d root n G0 tn0 n G tn s /\
  slot_copy_external cs (Var root) /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = slot_copy_cond_insts cs n /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?t G1 tn1.
    t = slot_copy_cond_result cs n n s /\
    t.vs_current_bb = slot_copy_exit cs /\ t.vs_inst_idx = 0 /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK t,G1,tn1)) /\
    slot_copy_inv cs load original p d n regions n t /\
    slot_copy_ghost_inv cs load p d root n G0 tn0 n G1 tn1 t /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)
Proof
  strip_tac >> drule_all toplevel_slot_copy_header_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl [`slot_copy_cond_result cs n n s`, `G1`, `tn1`] >>
  simp[slot_copy_cond_frame]
QED

Theorem toplevel_slot_copy_body_mem_ok[local]:
  compile_expr cenv ty (TopLevelName ann nsid) ca = (place,cb) /\
  (load = SLOAD \/ load = TLOAD) /\
  slot_copy_external cs src /\ slot_copy_external cs (Var root) /\
  eval_operand src s = SOME p /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME (n2w i) /\
  lookup_var root s = SOME d /\
  w2n (d+n2w i*32w)+32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (TAKE 7 (slot_copy_body_insts cs src (Var root) load)) s
Proof
  strip_tac >>
  `root <> slot_copy_var cs 2 /\ root <> slot_copy_var cs 3 /\
   root <> slot_copy_var cs 4` by
    (fs[slot_copy_external_def] >> metis_tac[DECIDE ``2<7 /\ 3<7 /\ 4<7``]) >>
  Cases_on `load = SLOAD` >> gvs[] >>
  simp[slot_copy_body_insts_def, TAKE_def, run_inst_seq_mem_ok_def,
    step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, exec_read1_def,
    exec_write2_def, exec_pure1_def, eval_operand_def, lookup_var_def,
    slot_copy_var_distinct, FLOOKUP_UPDATE,
    inst_mem_below_frontier_def, source_memory_read_ranges_def,
    source_memory_write_ranges_def, fixed_source_write_range_def,
    inst_dload_in_section_def, update_var_def, mstore_def] >>
  gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, slot_copy_var_distinct]
QED

Theorem toplevel_slot_copy_backedge_joint[local]:
  compile_expr cenv ty (TopLevelName ann nsid) ca = (place,cb) /\
  (load = SLOAD \/ load = TLOAD) /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = slot_copy_body_insts cs src (Var root) load /\
  run_inst_seq (TAKE 7 bb.bb_instructions) s = OK t /\
  run_inst_seq_mem_ok (TAKE 7 bb.bb_instructions) s /\
  inst_seq_ptr D lo ctx fn PG G tn (TAKE 7 bb.bb_instructions) s Gf tnf /\
  t.vs_current_bb = s.vs_current_bb /\ allocas_from lo t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (jump_to (slot_copy_cond cs) (t with vs_inst_idx := 7)),Gf,tnf)
Proof
  strip_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := 7),Gf,tnf)` by
    (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
       run_inst_seq_gas_origin_ptr_path >>
     disch_then (qspecl_then [`explicit`, `t`, `bb`] mp_tac) >>
     (impl_tac >- fs[slot_copy_body_insts_def, TAKE_def, mk_inst_def, is_terminator_def]) >>
     simp[slot_copy_body_insts_def, TAKE_def, mk_inst_def]) >>
  `~(t with vs_inst_idx := 7).vs_halted` by
    (drule gas_origin_ptr_path_projections >> metis_tac[gas_path_ptr_ok_not_halted]) >>
  `gas_path_ptr_edge D lo ctx fn PG Gf tnf (t with vs_inst_idx := 7) 0 Gf tnf
    (OK (jump_to (slot_copy_cond cs) (t with vs_inst_idx := 7)))` by
    (irule copy_jmp_counted_edge >> simp[] >>
     qexists `cs.cs_next_id+11` >>
     simp[slot_copy_body_insts_def, get_instruction_def]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (t with vs_inst_idx := 7,Gf,tnf) []
    (OK (jump_to (slot_copy_cond cs) (t with vs_inst_idx := 7)),Gf,tnf)` by
    (irule toplevel_slot_copy_control_edge >> goal_assum (drule_at Any) >>
     simp[] >> conj_tac >- metis_tac[] >>
     qexists `mk_inst (cs.cs_next_id+11) JMP [Label (slot_copy_cond cs)] []` >>
     simp[slot_copy_body_insts_def, get_instruction_def, mk_inst_def] >> metis_tac[]) >>
  drule gas_origin_ptr_path_append >>
  disch_then (qspecl_then [`t with vs_inst_idx := 7`, `Gf`, `tnf`, `[]`] mp_tac) >>
  simp[] >> disch_then irule >>
  `~(jump_to (slot_copy_cond cs) (t with vs_inst_idx := 7)).vs_halted` by fs[jump_to_def] >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

Theorem toplevel_slot_copy_body_joint:
  compile_expr cenv ty (TopLevelName ann nsid) ca = (place,cb) /\
  (load=SLOAD \/ load=TLOAD) /\
  slot_copy_inv cs load original p d n regions i s /\ i < n /\
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s /\
  slot_copy_external cs src /\ slot_copy_external cs (Var root) /\
  eval_operand src original = SOME p /\ lookup_var root original = SOME d /\
  op_taint tn src = {} /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = slot_copy_body_insts cs src (Var root) load /\
  w2n d+32*n <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (slot_copy_body_result cs p d load i s),Gf,tnf)) /\
    slot_copy_inv cs load original p d n regions (i+1) (slot_copy_body_result cs p d load i s) /\
    slot_copy_ghost_inv cs load p d root n G0 tn0 (i+1) Gf tnf
      (slot_copy_body_result cs p d load i s) /\
    allocas_from lo (slot_copy_body_result cs p d load i s) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp (slot_copy_body_result cs p d load i s))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  drule_all copy_body_parameters >> strip_tac >>
  `op_taint tn (Var (slot_copy_var cs 0)) = {} /\
   ptr_covers G tn root s (32*n)` by fs[slot_copy_ghost_inv_def] >>
  `root <> slot_copy_var cs 2 /\ root <> slot_copy_var cs 3 /\
   root <> slot_copy_var cs 4 /\ root <> slot_copy_var cs 5` by simp[] >>
  qpat_x_assum `eval_operand src s = SOME p` assume_tac >>
  drule_all copy_generated_body_segment >>
  disch_then (qspecl_then [`fn`, `PG`, `ARB`] strip_assume_tac) >>
  `!D. inst_seq_ptr D lo ctx fn PG G tn
    (TAKE 7 (slot_copy_body_insts cs src (Var root) load)) s Gf tnf` by
    (gen_tac >> qpat_x_assum `eval_operand src s = SOME p` assume_tac >>
  drule_all copy_generated_body_segment >>
     disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
     `!ix. inst_seq_ptr D lo ctx fn PG G tn
       (TAKE 7 (slot_copy_body_insts cs src (Var root) load))
       (s with vs_inst_idx := ix) Gf tnf` by
       metis_tac[inst_seq_ptr_ghost_unique] >>
     first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  `jump_to (slot_copy_cond cs) (t with vs_inst_idx := 7) =
   slot_copy_body_result cs p d load i s` by
    simp[slot_copy_body_result_def, jump_to_def, update_var_def] >>
  qexistsl [`Gf`, `tnf`] >> conj_tac
  >- (rpt gen_tac >>
      qpat_x_assum `jump_to _ _ = slot_copy_body_result _ _ _ _ _ _`
        (fn th => rewrite_tac[GSYM th]) >>
      irule toplevel_slot_copy_backedge_joint >>
      goal_assum (drule_at Any) >> simp[] >>
      conj_tac >- simp[update_var_def, mstore_def] >>
      conj_tac >- metis_tac[] >>
      qexistsl [`load`, `root`, `src`] >> simp[] >>
      irule toplevel_slot_copy_body_mem_ok >>
      goal_assum (drule_at Any) >> simp[] >>
      reverse conj_tac >- metis_tac[] >> qexists `i` >>
      `i < dimword(:256)` by (fs[slot_copy_inv_def, dimword_def] >> decide_tac) >>
      simp[] >> decide_tac) >>
  qpat_x_assum `t = _` kall_tac >> gnvs[] >> simp[slot_copy_body_invariant] >>
  reverse conj_tac
  >- (qpat_x_assum `jump_to _ _ = slot_copy_body_result _ _ _ _ _ _`
        (fn th => rewrite_tac[GSYM th]) >>
      simp[jump_to_def, allocas_from_def, allocas_below_fmp_def] >>
      fs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  irule copy_body_ghost_frame >> conj_tac >- simp[] >> conj_tac
  >- (`ptr_covers Gf tnf root t (32*n)` by
        (qpat_x_assum `!v c. _ ==> ptr_covers _ _ _ _ _` irule >>
         simp[] >> metis_tac[DECIDE ``0<7 /\ 2<7 /\ 3<7 /\ 4<7 /\ 5<7 /\ 6<7``]) >>
      qpat_x_assum `jump_to _ _ = slot_copy_body_result _ _ _ _ _ _`
        (fn th => rewrite_tac[GSYM th]) >>
      fs[jump_to_def, ptr_covers_def, lookup_var_def]) >>
  qexistsl [`G`, `s`, `tn`] >> simp[] >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_x_assum `!v. _ ==> FLOOKUP _ _ = _ /\ _` (qspec_then `v` mp_tac) >>
      (impl_tac >- (fs[slot_copy_external_def] >>
        metis_tac[DECIDE ``0<7 /\ 2<7 /\ 3<7 /\ 4<7 /\ 5<7 /\ 6<7``])) >> simp[]) >>
  AP_TERM_TAC >> POP_ASSUM_LIST (K ALL_TAC) >> simp[EXTENSION] >>
  metis_tac[DECIDE ``!x y z:num. x+(y+z)=y+(x+z)``]
QED

Theorem toplevel_slot_copy_joint_step:
  compile_expr cenv ty (TopLevelName ann nsid) ca = (place,cb) /\
  (load=SLOAD \/ load=TLOAD) /\
  slot_copy_inv cs load original p d n regions i s /\ i < n /\
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s /\
  slot_copy_external cs src /\ slot_copy_external cs (Var root) /\
  eval_operand src original = SOME p /\ lookup_var root original = SOME d /\
  op_taint tn src = {} /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME cond /\
  cond.bb_instructions = slot_copy_cond_insts cs n /\
  lookup_block (slot_copy_body cs) fn.fn_blocks = SOME bodybb /\
  bodybb.bb_instructions = slot_copy_body_insts cs src (Var root) load /\
  w2n d+32*n <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (slot_copy_body_result cs p d load i (slot_copy_cond_result cs n i s)),Gf,tnf)) /\
    slot_copy_inv cs load original p d n regions (i+1)
      (slot_copy_body_result cs p d load i (slot_copy_cond_result cs n i s)) /\
    slot_copy_ghost_inv cs load p d root n G0 tn0 (i+1) Gf tnf
      (slot_copy_body_result cs p d load i (slot_copy_cond_result cs n i s)) /\
    allocas_from lo (slot_copy_body_result cs p d load i (slot_copy_cond_result cs n i s)) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp
      (slot_copy_body_result cs p d load i (slot_copy_cond_result cs n i s))) /\
    (slot_copy_body_result cs p d load i (slot_copy_cond_result cs n i s)).vs_alloca_next =
      s.vs_alloca_next
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  drule_all toplevel_slot_copy_header_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `op_taint tn1 src = {}` by metis_tac[copy_ghost_external_taint] >>
  `~(slot_copy_cond_result cs n i s).vs_halted /\
   w2n d+32*n <= (slot_copy_cond_result cs n i s).vs_alloca_next` by
    simp[slot_copy_cond_result_def, update_var_def, jump_to_def] >>
  `i <> n` by decide_tac >>
  `(slot_copy_cond_result cs n i s).vs_inst_idx = 0 /\
   lookup_block (slot_copy_cond_result cs n i s).vs_current_bb fn.fn_blocks = SOME bodybb`
    by simp[slot_copy_cond_frame] >>
  drule_all toplevel_slot_copy_body_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl [`Gf`, `tnf`] >> simp[] >> conj_tac
  >- (rpt gen_tac >>
      qpat_x_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) _ _`
        (qspecl_then [`D`, `explicit`] mp_tac) >>
      disch_tac >> drule gas_origin_ptr_path_append >>
      disch_then (qspecl_then
        [`slot_copy_cond_result cs n i s`, `G1`, `tn1`, `[]`] mp_tac) >>
      simp[] >> disch_then irule >> simp[]) >>
  simp[slot_copy_body_result_def, slot_copy_cond_result_def,
       jump_to_def, update_var_def, mstore_def]
QED

Theorem toplevel_slot_copy_joint_finish:
  compile_expr cenv ty (TopLevelName ann nsid) ca = (place,cb) /\
  (load=SLOAD \/ load=TLOAD) /\ i <= n /\
  slot_copy_inv cs load original p d n regions i s /\
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s /\
  slot_copy_external cs src /\ slot_copy_external cs (Var root) /\
  eval_operand src original = SOME p /\ lookup_var root original = SOME d /\
  op_taint tn src = {} /\ ~s.vs_halted /\
  s.vs_current_bb = slot_copy_cond cs /\ s.vs_inst_idx = 0 /\
  lookup_block (slot_copy_cond cs) fn.fn_blocks = SOME cond /\
  cond.bb_instructions = slot_copy_cond_insts cs n /\
  lookup_block (slot_copy_body cs) fn.fn_blocks = SOME bodybb /\
  bodybb.bb_instructions = slot_copy_body_insts cs src (Var root) load /\
  w2n d+32*n <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?t Gf tnf.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK t,Gf,tnf)) /\
    t.vs_current_bb = slot_copy_exit cs /\ t.vs_inst_idx = 0 /\
    slot_copy_inv cs load original p d n regions n t /\
    slot_copy_ghost_inv cs load p d root n G0 tn0 n Gf tnf t /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  map_every qid_spec_tac [`tn`, `G`, `s`] >>
  measureInduct_on `n-i` >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  Cases_on `i=n`
  >- (gvs[] >>
      `lookup_block s.vs_current_bb fn.fn_blocks = SOME cond` by simp[] >>
      drule_all toplevel_slot_copy_joint_exit >>
      disch_then (qspec_then `PG` strip_assume_tac) >>
      qexistsl [`t`, `G1`, `tn1`] >>
      simp[slot_copy_cond_result_def, jump_to_def, update_var_def]) >>
  `i<n` by decide_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME cond` by simp[] >>
  drule_all toplevel_slot_copy_joint_step >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `slot_copy_inv cs load original p d n regions (i+1) mid` >>
  `~mid.vs_halted /\ mid.vs_current_bb = slot_copy_cond cs /\ mid.vs_inst_idx = 0` by
    simp[Abbr `mid`, slot_copy_body_result_def, slot_copy_cond_result_def,
         update_var_def, jump_to_def, mstore_def] >>
  `op_taint tnf src = {}` by metis_tac[copy_ghost_external_taint] >>
  first_x_assum (qspec_then `i+1` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`mid`, `Gf`, `tnf`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  qexistsl [`t`, `Gf'`, `tnf'`] >> simp[] >>
  rpt gen_tac >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspecl_then [`D`, `explicit`] mp_tac) >> disch_tac >>
  drule gas_origin_ptr_path_append >>
  disch_then (qspecl_then [`mid`, `Gf`, `tnf`, `[]`] mp_tac) >>
  simp[] >> disch_then irule >> simp[]
QED
