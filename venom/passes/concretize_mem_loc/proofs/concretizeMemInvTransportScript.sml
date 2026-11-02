(*
 * ConcretizeMemLoc transports the shared memory invariant (unitMemInv):
 * from the site phase on its input to the static phase on its output.
 *
 * The representative case is a single function without INVOKE, the scope
 * of concretize_function_correct.  Its hypotheses are that theorem's,
 * bundled: concretize_fn_ok (the syntactic facts and the step and block
 * preservation hypotheses of the pass theorem) and concretize_state_ok
 * (the per-state facts).  concretize_function_correct_bundled checks
 * that the bundles are exactly the pass theorem's premises.
 *
 * The transport is mem_inv_transport with the pass's simulation relation
 * concretize_rel: concretize_raw_reachable_sim relates every raw-reachable
 * state of the output function to one of the input function, and
 * concretize_rel_static_mem_ok carries the memory fact across (an access
 * inside a site at displacement d lands at the site's static address plus
 * d, below the layout end).
 *
 * TOP-LEVEL:
 *   concretize_fn_ok, concretize_state_ok      - bundled pass premises
 *   concretize_function_correct_bundled        - the pass theorem, bundled
 *   concretize_rel_static_mem_ok               - memory fact across the relation
 *   concretize_raw_reachable_sim               - reachable states simulate
 *   concretize_mem_inv_transport               - the transport
 *)

Theory concretizeMemInvTransport
Ancestors
  list pair words finite_map unitMemInv contextRawReachable
  contextCodegenRel unitTransformDefs concretizeMemLocDefs
  concretizeMemLocProofs concretizeMemLocCorrectness allocaRemapDefs
  allocaRemapSSA pointerConfinedDefs venomMemDefs venomWf venomInst venomState
  passSharedDefs passSimulationDefs venomMemProps
  venomExecSemantics stateEquiv

(* ===== The pass theorem's premises, bundled ===== *)

(* Syntactic facts about the input function, and the pass theorem's
   preservation hypotheses for the per-state facts along its steps. *)
Definition concretize_fn_ok_def:
  concretize_fn_ok amap fn livesets <=>
    fn_inst_wf fn /\ ssa_form fn /\ fn_inst_ids_distinct fn /\
    all_allocas_mapped fn amap /\
    amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    affine_pointer_ops fn (FDOM amap) /\
    pointer_arith_in_region fn (FDOM amap) /\
    phi_pv_all_var fn (FDOM amap) /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_size_non_pv fn (FDOM amap) /\
    mem_write_tail_non_pv fn (FDOM amap) /\
    live_non_overlapping livesets amap fn /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> NOP) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> MEMTOP) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> LOG) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> MCOPY) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> EXTCODECOPY) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> DRET) bb.bb_instructions /\
                EVERY (\i. ~is_ext_call_op i.inst_opcode) bb.bb_instructions)
      fn.fn_blocks /\
    (!bb s s' n.
       MEM bb fn.fn_blocks /\ eval_phis s bb.bb_instructions = OK s' /\
       alloca_safe_access fn (FDOM amap) s ==>
       alloca_safe_access fn (FDOM amap) (s' with vs_inst_idx := n)) /\
    (!fuel ctx bb s s'.
       MEM bb fn.fn_blocks /\ exec_block fuel ctx bb s = OK s' /\
       alloca_safe_access fn (FDOM amap) s ==>
       alloca_safe_access fn (FDOM amap) s') /\
    (!fuel ctx bb s s' init0 init1.
       MEM bb fn.fn_blocks /\ exec_block fuel ctx bb s = OK s' /\
       alloca_write_before_read fn (FDOM amap) livesets init0 s ==>
       alloca_write_before_read fn (FDOM amap) livesets init1 s') /\
    (!fuel ctx bb s s'.
       MEM bb fn.fn_blocks /\ exec_block fuel ctx bb s = OK s' /\
       concrete_allocas_non_overlapping amap fn s ==>
       concrete_allocas_non_overlapping amap fn s') /\
    (!fuel0 ctx0 bb inst0 s s'.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_overflow_safe fn amap s ==>
       alloca_overflow_safe fn amap s') /\
    (!fuel0 ctx0 bb inst0 s s' init0 init1.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_write_before_read fn (FDOM amap) livesets init0 s ==>
       alloca_write_before_read fn (FDOM amap) livesets init1 s') /\
    (!fuel0 ctx0 bb inst0 s s'.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_safe_access fn (FDOM amap) s ==>
       alloca_safe_access fn (FDOM amap) s') /\
    (!fuel0 ctx0 bb inst0 s s'.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       concrete_allocas_non_overlapping amap fn s ==>
       concrete_allocas_non_overlapping amap fn s')
End

(* Per-state facts about the input run. *)
Definition concretize_state_ok_def:
  concretize_state_ok amap fn livesets init s <=>
    alloca_inv s /\
    alloca_overflow_safe fn amap s /\
    alloca_write_before_read fn (FDOM amap) livesets init s /\
    alloca_safe_access fn (FDOM amap) s /\
    concrete_allocas_non_overlapping amap fn s /\
    alloca_sizes_match fn s
End

(* The bundles are the pass theorem's premises. *)
Theorem concretize_function_correct_bundled:
  venom_wf ctx /\ concretize_fn_ok amap fn livesets /\
  concretize_state_ok amap fn livesets init s1 /\
  concretize_rel amap fn livesets init s1 s2 ==>
  ?init'.
    lift_result
      (concretize_rel amap fn livesets init')
      (concretize_rel amap fn livesets init')
      (concretize_rel amap fn livesets init')
      (run_blocks fuel ctx fn s1)
      (run_blocks fuel ctx (concretize_function amap fn) s2)
Proof
  rw[concretize_fn_ok_def, concretize_state_ok_def] >>
  irule concretize_function_correct >> simp[] >>
  rpt conj_tac >> metis_tac[]
QED

(* ===== The memory fact across the relation ===== *)

Theorem cr_eval_operand_none[local]:
  concretize_rel amap fn livesets init s s' ==>
  (eval_operand op s = NONE <=> eval_operand op s' = NONE)
Proof
  strip_tac >> Cases_on `op`
  >- simp[eval_operand_def]
  >- (simp[eval_operand_def] >>
  rename1 `lookup_var v s` >>
  Cases_on `v IN pointer_derived_vars fn (FDOM amap)`
  >- (Cases_on `lookup_var v s`
      >- metis_tac[cr_pv_var_none]
      >> `lookup_var v s <> NONE` by simp[]
      >> drule_all cr_pv_var_displacement >> strip_tac >> simp[])
  >> drule cr_eval_operand_non_pv >>
  disch_then (qspec_then `Var v` mp_tac) >> simp[eval_operand_def])
  >> rename1 `Label lbl` >> drule cr_eval_operand_non_pv >>
  disch_then (qspec_then `Label lbl` mp_tac) >> simp[]
QED

Theorem cr_eval_operands_none[local]:
  !ops. concretize_rel amap fn livesets init s s' ==>
  (eval_operands ops s = NONE <=> eval_operands ops s' = NONE)
Proof
  Induct >- simp[eval_operands_def] >> gen_tac >> disch_tac >>
  simp[eval_operands_def] >>
  `eval_operand h s = NONE <=> eval_operand h s' = NONE` by
    metis_tac[cr_eval_operand_none] >>
  Cases_on `eval_operand h s` >> Cases_on `eval_operand h s'` >> gvs[] >>
  Cases_on `eval_operands ops s` >> Cases_on `eval_operands ops s'` >> gvs[]
QED

Theorem cr_target_pointer_displacement[local]:
  concretize_rel amap fn livesets init s s' /\
  v IN pointer_derived_vars fn (FDOM amap) /\
  lookup_var v s' = SOME w' ==>
  ?w aid b sz addr.
    lookup_var v s = SOME w /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
    alloca_concrete_addr amap fn aid = SOME addr /\
    b <= w2n w /\ w2n w < b + sz /\
    w2n w' = w2n addr + (w2n w - b)
Proof
  strip_tac >>
  `lookup_var v s <> NONE` by metis_tac[cr_pv_var_none, optionTheory.NOT_NONE_SOME] >>
  drule_all cr_pv_var_displacement >> strip_tac >> gvs[] >>
  drule word_displ_to_nat >> disch_then (qspec_then `sz` mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`aid`, `orig_off`, `sz`, `addr`] >> simp[]
QED

Theorem simple_read_ranges[local]:
  inst.inst_opcode <> MCOPY /\ inst.inst_opcode <> DRET /\
  inst.inst_opcode <> LOG /\ ~is_ext_call_op inst.inst_opcode ==>
  source_memory_read_ranges inst s =
    case mem_read_ops inst of
      NONE => []
    | SOME ops =>
        case ops.iao_size of
          NONE => []
        | SOME len_op => memory_range_of_operands ops.iao_ofst len_op s
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  gvs[is_ext_call_op_def, source_memory_read_ranges_def,
      memLocDefsTheory.mem_read_ops_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[memory_range_of_operands_def, eval_operand_def, dimword_def] >>
  Cases_on `t'` >> simp[]
QED

Theorem simple_write_ranges[local]:
  inst.inst_opcode <> MCOPY /\ inst.inst_opcode <> DRET /\
  inst.inst_opcode <> EXTCODECOPY /\ ~is_ext_call_op inst.inst_opcode ==>
  codegenRel$source_memory_write_ranges inst s =
    if eval_operands (TL inst.inst_operands) s = NONE then []
    else case mem_write_ops inst of
      NONE => []
    | SOME ops =>
        case ops.iao_size of
          NONE => []
        | SOME len_op => memory_range_of_operands ops.iao_ofst len_op s
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  gvs[is_ext_call_op_def, codegenRelTheory.source_memory_write_ranges_def,
      memLocDefsTheory.mem_write_ops_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[]
  >>~- ([`codegenRel$fixed_source_write_range s dst value _ = _`],
    simp[codegenRelTheory.fixed_source_write_range_def,
         memory_range_of_operands_def, eval_operand_def, eval_operands_def,
         dimword_def] >> rpt (CASE_TAC >> simp[]))
  >> Cases_on `t` >> simp[] >>
  simp[codegenRelTheory.sized_source_write_range_def,
       memory_range_of_operands_def, eval_operands_def] >>
  rpt (CASE_TAC >> simp[])
QED

Theorem cr_memory_range_operands[local]:
  concretize_rel amap fn livesets init s s' /\
  v IN pointer_derived_vars fn (FDOM amap) /\
  (!u. len_op = Var u ==> u NOTIN pointer_derived_vars fn (FDOM amap)) /\
  MEM (off',len) (memory_range_of_operands (Var v) len_op s') ==>
  ?off aid b sz addr.
    MEM (off,len) (memory_range_of_operands (Var v) len_op s) /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
    alloca_concrete_addr amap fn aid = SOME addr /\
    b <= off /\ off < b + sz /\ off' = w2n addr + (off-b)
Proof
  strip_tac >>
  `eval_operand len_op s = eval_operand len_op s'` by
    (drule cr_eval_operand_non_pv >> disch_then irule >> simp[]) >>
  Cases_on `lookup_var v s'` >>
  gvs[memory_range_of_operands_def, eval_operand_def] >>
  Cases_on `eval_operand len_op s'` >> gvs[] >>
  drule_all cr_target_pointer_displacement >> strip_tac >>
  qexistsl [`w2n w`, `aid`, `b`, `sz`, `addr`] >>
  simp[memory_range_of_operands_def, eval_operand_def]
QED

Theorem cr_read_ranges[local]:
  concretize_rel amap fn livesets init s s' /\
  (!ops. mem_read_ops inst = SOME ops ==>
    (?v. ops.iao_ofst = Var v /\ v IN pointer_derived_vars fn (FDOM amap)) /\
    (!u. ops.iao_size = SOME (Var u) ==>
         u NOTIN pointer_derived_vars fn (FDOM amap))) /\
  inst.inst_opcode <> MCOPY /\ inst.inst_opcode <> DRET /\
  inst.inst_opcode <> LOG /\ ~is_ext_call_op inst.inst_opcode /\
  MEM (off',len) (source_memory_read_ranges inst s') ==>
  ?off aid b sz addr.
    MEM (off,len) (source_memory_read_ranges inst s) /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
    alloca_concrete_addr amap fn aid = SOME addr /\
    b <= off /\ off < b + sz /\ off' = w2n addr + (off-b)
Proof
  strip_tac >>
  gvs[simple_read_ranges] >>
  Cases_on `mem_read_ops inst` >> gvs[] >>
  rename1 `mem_read_ops inst = SOME ops` >>
  Cases_on `ops.iao_size` >> gvs[] >>
  drule_all cr_memory_range_operands >> simp[]
QED

Theorem cr_write_ranges[local]:
  concretize_rel amap fn livesets init s s' /\
  (!ops. mem_write_ops inst = SOME ops ==>
    (?v. ops.iao_ofst = Var v /\ v IN pointer_derived_vars fn (FDOM amap)) /\
    (!u. ops.iao_size = SOME (Var u) ==>
         u NOTIN pointer_derived_vars fn (FDOM amap))) /\
  inst.inst_opcode <> MCOPY /\ inst.inst_opcode <> DRET /\
  inst.inst_opcode <> EXTCODECOPY /\ ~is_ext_call_op inst.inst_opcode /\
  MEM (off',len) (codegenRel$source_memory_write_ranges inst s') ==>
  ?off aid b sz addr.
    MEM (off,len) (codegenRel$source_memory_write_ranges inst s) /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
    alloca_concrete_addr amap fn aid = SOME addr /\
    b <= off /\ off < b + sz /\ off' = w2n addr + (off-b)
Proof
  strip_tac >>
  `eval_operands (TL inst.inst_operands) s = NONE <=>
   eval_operands (TL inst.inst_operands) s' = NONE` by
    metis_tac[cr_eval_operands_none] >>
  gvs[simple_write_ranges] >>
  Cases_on `eval_operands (TL inst.inst_operands) s' = NONE` >> gvs[] >>
  Cases_on `mem_write_ops inst` >> gvs[] >>
  rename1 `mem_write_ops inst = SOME ops` >>
  Cases_on `ops.iao_size` >> gvs[] >>
  drule_all cr_memory_range_operands >> simp[]
QED

Theorem concretize_inst_mem_ranges[local]:
  inst_mem_ranges (concretize_inst amap inst) s = inst_mem_ranges inst s
Proof
  Cases_on `is_alloca_op inst.inst_opcode`
  >- (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def] >>
      simp[concretize_inst_def, is_alloca_op_def] >>
      Cases_on `inst.inst_outputs` >> simp[] >>
      Cases_on `t` >> simp[] >>
      Cases_on `FLOOKUP amap h` >>
      simp[inst_mem_ranges_def, source_memory_read_ranges_def,
           codegenRelTheory.source_memory_write_ranges_def,
           mk_assign_inst_def, mk_nop_inst_def])
  >> simp[concretize_inst_def]
QED

Theorem cr_inst_mem_ranges[local]:
  concretize_fn_ok amap fn livesets /\
  concretize_rel amap fn livesets init s s' /\
  MEM inst (fn_insts fn) /\
  MEM (off',len) (inst_mem_ranges (concretize_inst amap inst) s') /\
  len <> 0 ==>
  ?off aid b sz addr.
    MEM (off,len) (inst_mem_ranges inst s) /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
    alloca_concrete_addr amap fn aid = SOME addr /\
    b <= off /\ off < b + sz /\ off' = w2n addr + (off-b)
Proof
  strip_tac >>
  `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
    (qpat_x_assum `MEM inst (fn_insts fn)` mp_tac >>
     simp[fn_insts_def] >> qspec_tac (`fn.fn_blocks`, `bbs`) >>
     Induct >> rw[fn_insts_blocks_def] >> metis_tac[]) >>
  `all_mem_via_pointer fn (FDOM amap) /\ mem_size_non_pv fn (FDOM amap)` by
    fs[concretize_fn_ok_def] >>
  `inst.inst_opcode <> MCOPY /\ inst.inst_opcode <> DRET /\
   inst.inst_opcode <> LOG /\ inst.inst_opcode <> EXTCODECOPY /\
   ~is_ext_call_op inst.inst_opcode` by
    (fs[concretize_fn_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `!ops. mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops ==>
    (?v. ops.iao_ofst = Var v /\ v IN pointer_derived_vars fn (FDOM amap)) /\
    (!u. ops.iao_size = SOME (Var u) ==>
         u NOTIN pointer_derived_vars fn (FDOM amap))` by
    (fs[all_mem_via_pointer_def, mem_size_non_pv_def] >> metis_tac[]) >>
  qpat_x_assum `concretize_fn_ok _ _ _` kall_tac >>
  qpat_x_assum `all_mem_via_pointer _ _` kall_tac >>
  qpat_x_assum `mem_size_non_pv _ _` kall_tac >>
  gvs[concretize_inst_mem_ranges, inst_mem_ranges_def, MEM_APPEND]
  >- (drule cr_read_ranges >>
      disch_then (qspecl_then [`off'`, `len`, `inst`] mp_tac) >>
      simp[] >> strip_tac >> qexistsl [`off`, `aid`, `b`, `sz`, `addr`] >> simp[])
  >> drule cr_write_ranges >>
  disch_then (qspecl_then [`off'`, `len`, `inst`] mp_tac) >>
  simp[] >> strip_tac >> qexistsl [`off`, `aid`, `b`, `sz`, `addr`] >> simp[]
QED

Theorem site_displaced_range_bound[local]:
  site_mem_ok ctx fn inst s /\ alloca_sizes_match fn s /\
  (!aid addr. alloca_concrete_addr amap fn aid = SOME addr ==>
              w2n addr + get_alloca_size fn (Allocation aid) <= eom) /\
  MEM (off,len) (inst_mem_ranges inst s) /\ len <> 0 /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  alloca_concrete_addr amap fn aid = SOME addr /\
  b <= off /\ off < b + sz /\ off' = w2n addr + (off-b) ==>
  off' + len <= eom
Proof
  strip_tac >>
  `allocas_non_overlapping s /\
   ?aid2 b2 sz2. FLOOKUP s.vs_allocas aid2 = SOME (b2,sz2) /\
                 b2 <= off /\ off + len <= b2 + sz2` by
    (fs[site_mem_ok_def, alloca_inv_def, EVERY_MEM] >>
     first_x_assum (qspec_then `(off,len)` mp_tac) >> simp[]) >>
  `off < b2 + sz2` by decide_tac >>
  `aid = aid2` by metis_tac[allocas_non_overlapping_shared_point] >>
  gvs[] >>
  `sz = get_alloca_size fn (Allocation aid)` by
    (fs[alloca_sizes_match_def] >> metis_tac[]) >>
  `w2n addr + sz <= eom` by metis_tac[] >> decide_tac
QED

(* Every memory access of inst in s lies inside a site (site_mem_ok); its
   offset operand is a pointer-derived variable (all_mem_via_pointer) whose
   value concretize_rel displaces by the site's static address, and its size
   operand is not (mem_size_non_pv), so the concretized instruction accesses
   the same displacement inside the static region, which ends below eom. *)
Theorem concretize_rel_static_mem_ok:
  concretize_fn_ok amap fn livesets /\
  concretize_state_ok amap fn livesets init s /\
  (!aid addr. alloca_concrete_addr amap fn aid = SOME addr ==>
              w2n addr + get_alloca_size fn (Allocation aid) <= eom) /\
  MEM inst (fn_insts fn) /\
  concretize_rel amap fn livesets init s s' /\
  site_mem_ok ctx fn inst s ==>
  static_mem_ok eom ctx' (concretize_function amap fn)
    (concretize_inst amap inst) s'
Proof
  strip_tac >>
  `alloca_sizes_match fn s` by fs[concretize_state_ok_def] >>
  simp[static_mem_ok_def, EVERY_MEM, FORALL_PROD] >>
  map_every qx_gen_tac [`off'`, `len`] >> strip_tac >>
  Cases_on `len = 0` >- simp[] >>
  drule_all cr_inst_mem_ranges >> strip_tac >>
  disj2_tac >> irule site_displaced_range_bound >>
  metis_tac[]
QED

(* ===== Index-preserving transformation boundaries ===== *)

Theorem concretize_function_blocks[local]:
  concretize_fn_ok amap fn livesets ==>
  (concretize_function amap fn).fn_blocks =
    MAP (block_map_transform (concretize_inst amap)) fn.fn_blocks
Proof
  strip_tac >>
  simp[concretize_function_def, clear_nops_function_def,
       function_map_transform_def, MAP_MAP_o] >>
  irule MAP_CONG >> simp[] >> rpt strip_tac >>
  irule clear_nops_bmt_identity >>
  fs[concretize_fn_ok_def, EVERY_MEM] >> metis_tac[]
QED

Theorem concretize_lookup_block[local]:
  concretize_fn_ok amap fn livesets ==>
  lookup_block lbl (concretize_function amap fn).fn_blocks =
    OPTION_MAP (block_map_transform (concretize_inst amap))
      (lookup_block lbl fn.fn_blocks)
Proof
  strip_tac >> drule concretize_function_blocks >>
  disch_then SUBST1_TAC >>
  irule passSimulationPropsTheory.lookup_block_map >>
  simp[block_map_transform_def]
QED

Theorem concretize_active_inst_inverse[local]:
  concretize_fn_ok amap fn livesets /\
  active_inst (concretize_function amap fn) inst' s' /\
  s'.vs_current_bb = s.vs_current_bb /\
  s'.vs_inst_idx = s.vs_inst_idx ==>
  ?inst. active_inst fn inst s /\ inst' = concretize_inst amap inst
Proof
  strip_tac >>
  drule concretize_function_blocks >> strip_tac >>
  fs[active_inst_def, MEM_MAP] >>
  gvs[block_map_transform_def, EL_MAP] >>
  qexists `EL s.vs_inst_idx y.bb_instructions` >>
  simp[] >> qexists `y` >> simp[]
QED

Theorem concretize_inst_invoke_iff[local]:
  (concretize_inst amap inst).inst_opcode = INVOKE <=>
  inst.inst_opcode = INVOKE
Proof
  rw[concretize_inst_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >>
       gvs[mk_assign_inst_def, mk_nop_inst_def, is_alloca_op_def]) >>
  Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def]
QED

Theorem concretize_active_not_invoke[local]:
  concretize_fn_ok amap fn livesets /\
  active_inst (concretize_function amap fn) inst s ==>
  inst.inst_opcode <> INVOKE
Proof
  strip_tac >>
  `?i. active_inst fn i s /\ inst = concretize_inst amap i` by
    (irule concretize_active_inst_inverse >> simp[] >>
     conj_tac >- (qexists `s` >> simp[]) >>
     qexists `livesets` >> simp[]) >>
  gvs[concretize_inst_invoke_iff, active_inst_def] >>
  qpat_x_assum `concretize_fn_ok _ _ _` mp_tac >>
  simp[concretize_fn_ok_def, EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!bb. MEM bb _ ==> _` drule >>
  strip_tac >> metis_tac[EL_MEM]
QED

(* ===== Initial and index-update boundaries ===== *)

Theorem concretize_state_ok_update_inst_idx[local]:
  concretize_state_ok amap fn livesets init s ==>
  concretize_state_ok amap fn livesets init (s with vs_inst_idx := n)
Proof
  rw[concretize_state_ok_def] >>
  metis_tac[alloca_inv_update_inst_idx,
    alloca_overflow_safe_update_inst_idx,
    alloca_write_before_read_update_inst_idx,
    alloca_safe_access_update_inst_idx,
    concrete_allocas_non_overlapping_update_inst_idx,
    alloca_sizes_match_update_inst_idx]
QED

Theorem concretize_initial_entry[local]:
  o1_initial_state_ok vs /\ concretize_state_ok amap fn livesets init vs ==>
  concretize_state_ok amap fn livesets init
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) /\
  concretize_rel amap fn livesets init
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
Proof
  rw[o1_initial_state_ok_def, concretize_state_ok_def,
     concretize_rel_def, alloca_inv_def, alloca_overflow_safe_def,
     alloca_write_before_read_def, alloca_safe_access_def,
     concrete_allocas_non_overlapping_def, alloca_sizes_match_def,
     allocas_non_overlapping_def, lookup_var_def] >>
  gvs[alloca_next_valid_def, fn_remaining_alloca_size_def] >>
  metis_tac[]
QED

(* ===== Reverse successful instruction boundary ===== *)

Theorem concretize_step_sim_bundled[local]:
  concretize_fn_ok amap fn livesets /\
  concretize_state_ok amap fn livesets init s /\
  active_inst fn inst s /\ concretize_rel amap fn livesets init s t ==>
  ?init1. lift_result
    (concretize_rel amap fn livesets init1)
    (concretize_rel amap fn livesets init1)
    (concretize_rel amap fn livesets init1)
    (step_inst fuel ctx inst s)
    (step_inst fuel ctx (concretize_inst amap inst) t)
Proof
  strip_tac >>
  fs[active_inst_def] >>
  `MEM inst bb.bb_instructions` by metis_tac[EL_MEM] >>
  Cases_on `is_alloca_op inst.inst_opcode`
  >- (irule alloca_step_inst_sim >>
      fs[concretize_fn_ok_def, concretize_state_ok_def] >>
      metis_tac[]) >>
  `concretize_inst amap inst = inst` by simp[concretize_inst_def] >>
  `inst.inst_opcode <> INVOKE` by
    (fs[concretize_fn_ok_def, EVERY_MEM] >> metis_tac[]) >>
  simp[step_inst_non_invoke] >>
  irule concretize_step_inst_base_identity >>
  fs[concretize_fn_ok_def, concretize_state_ok_def, EVERY_MEM] >>
  qpat_x_assum `!bb. MEM bb _ ==> _`
    (qspec_then `bb` mp_tac) >> simp[] >> strip_tac >>
  rpt conj_tac >> metis_tac[]
QED

Theorem concretize_step_reverse_ok[local]:
  concretize_fn_ok amap fn livesets /\
  concretize_state_ok amap fn livesets init s /\
  active_inst fn inst s /\ concretize_rel amap fn livesets init s t /\
  step_inst fuel ctx' (concretize_inst amap inst) t = OK t1 ==>
  ?s1 init1. step_inst fuel ctx inst s = OK s1 /\
    concretize_rel amap fn livesets init1 s1 t1
Proof
  strip_tac >>
  drule_all concretize_step_sim_bundled >>
  disch_then (qspecl_then [`fuel`, `ctx'`] mp_tac) >>
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (fs[active_inst_def, concretize_fn_ok_def, EVERY_MEM] >>
     qpat_x_assum `!bb. MEM bb _ ==> _`
       (qspec_then `bb` mp_tac) >> simp[] >>
     metis_tac[EL_MEM]) >>
  gvs[step_inst_non_invoke] >>
  Cases_on `step_inst_base inst s` >>
  gvs[lift_result_def] >> metis_tac[]
QED

(* ===== Source state preservation boundary ===== *)

Theorem concretize_state_ok_next[local]:
  concretize_fn_ok amap fn livesets /\
  concretize_state_ok amap fn livesets init s /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst s = OK s1 ==>
  concretize_state_ok amap fn livesets init1
    (s1 with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> irule concretize_state_ok_update_inst_idx >>
  fs[active_inst_def] >>
  `MEM inst bb.bb_instructions` by metis_tac[EL_MEM] >>
  `inst.inst_opcode <> INVOKE` by
    (fs[concretize_fn_ok_def, EVERY_MEM] >>
     qpat_x_assum `!bb. MEM bb _ ==> _`
       (qspec_then `bb` mp_tac) >> simp[] >> metis_tac[]) >>
  fs[concretize_state_ok_def, concretize_fn_ok_def] >>
  simp[concretize_state_ok_def] >> rpt conj_tac
  >- metis_tac[alloca_inv_step_inst]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[] >>
  metis_tac[alloca_sizes_match_step_inst]
QED

Theorem concretize_state_ok_terminator[local]:
  concretize_fn_ok amap fn livesets /\
  concretize_state_ok amap fn livesets init s /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst s = OK s1 /\ ~s1.vs_halted ==>
  concretize_state_ok amap fn livesets init1 s1
Proof
  strip_tac >> fs[active_inst_def] >>
  `MEM inst bb.bb_instructions` by metis_tac[EL_MEM] >>
  `exec_block fuel ctx bb s = OK s1` by
    (simp[Once exec_block_def, get_instruction_def]) >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> DRET` by
    (fs[concretize_fn_ok_def, EVERY_MEM] >>
     qpat_x_assum `!bb. MEM bb _ ==> _`
       (qspec_then `bb` mp_tac) >> simp[] >> metis_tac[]) >>
  fs[concretize_state_ok_def, concretize_fn_ok_def] >>
  simp[concretize_state_ok_def] >> rpt conj_tac
  >- metis_tac[alloca_inv_step_inst]
  >- metis_tac[step_terminator_ok_preserves_alloca_overflow_safe]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[] >>
  metis_tac[alloca_sizes_match_step_inst]
QED

Theorem concretize_rel_halted[local]:
  concretize_rel amap fn livesets init s t ==> s.vs_halted = t.vs_halted
Proof
  rw[concretize_rel_def] >>
  fs[passResidualFrameTheory.concretize_frame_def,
     venom_state_component_equality]
QED

Theorem concretize_rel_current_bb[local]:
  concretize_rel amap fn livesets init s t ==>
  s.vs_current_bb = t.vs_current_bb
Proof
  rw[concretize_rel_def] >>
  fs[passResidualFrameTheory.concretize_frame_def,
     venom_state_component_equality]
QED

(* ===== Reverse block-entry boundary ===== *)

Theorem concretize_enters_block_reverse[local]:
  concretize_fn_ok amap fn livesets /\
  concretize_state_ok amap fn livesets init s /\
  concretize_rel amap fn livesets init s t /\
  enters_block (concretize_function amap fn) t t1 ==>
  ?s1. enters_block fn s s1 /\
    t1.vs_inst_idx = s1.vs_inst_idx /\
    concretize_state_ok amap fn livesets init s1 /\
    concretize_rel amap fn livesets init s1 t1
Proof
  strip_tac >>
  `s.vs_current_bb = t.vs_current_bb` by
    metis_tac[concretize_rel_current_bb] >>
  fs[enters_block_def] >>
  drule concretize_lookup_block >>
  disch_then (qspec_then `t.vs_current_bb` mp_tac) >>
  Cases_on `lookup_block t.vs_current_bb fn.fn_blocks` >> simp[] >>
  strip_tac >> gvs[] >>
  rename1 `lookup_block t.vs_current_bb fn.fn_blocks = SOME bb0` >>
  `MEM bb0 fn.fn_blocks` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  qpat_x_assum `eval_phis _ _ = OK _` mp_tac >>
  simp[block_map_transform_def, concretize_eval_phis_same_state] >>
  strip_tac >>
  `lift_result (concretize_rel amap fn livesets init)
     (concretize_rel amap fn livesets init)
     (concretize_rel amap fn livesets init)
     (eval_phis s bb0.bb_instructions) (eval_phis t bb0.bb_instructions)` by
    (irule concretize_eval_phis_rel >>
     fs[concretize_fn_ok_def] >> metis_tac[]) >>
  Cases_on `eval_phis s bb0.bb_instructions` >>
  gvs[lift_result_def] >>
  `phi_prefix_length (MAP (concretize_inst amap) bb0.bb_instructions) =
   phi_prefix_length bb0.bb_instructions` by
    (qspecl_then [`amap`, `bb0`] mp_tac concretize_bmt_phi_prefix_length >>
     simp[block_map_transform_def]) >>
  simp[] >> reverse conj_tac
  >- (irule concretize_rel_update_inst_idx >> simp[]) >>
  fs[concretize_state_ok_def, concretize_fn_ok_def] >>
  rpt conj_tac
  >- metis_tac[eval_phis_alloca_inv_update_inst_idx]
  >- metis_tac[eval_phis_alloca_overflow_safe_update_inst_idx]
  >- (irule eval_phis_alloca_write_before_read_update_inst_idx >>
      simp[] >> metis_tac[])
  >- metis_tac[]
  >- metis_tac[eval_phis_concrete_allocas_non_overlapping_update_inst_idx] >>
  metis_tac[eval_phis_alloca_sizes_match_update_inst_idx]
QED

Theorem concretize_function_fn_name[local]:
  (concretize_function amap fn).fn_name = fn.fn_name
Proof
  simp[concretize_function_def, clear_nops_function_def,
       function_map_transform_def]
QED

Theorem concretize_function_entry_label[local]:
  fn_entry_label (concretize_function amap fn) = fn_entry_label fn
Proof
  simp[concretize_function_def, clear_nops_function_def,
       function_map_transform_def, fn_entry_label_def, entry_block_def] >>
  Cases_on `fn.fn_blocks` >>
  simp[clear_nops_block_def, block_map_transform_def]
QED

Theorem raw_reachable_active_inst[local]:
  raw_reachable vs ctx fn inst s ==> active_inst fn inst s
Proof
  Induct_on `raw_reachable` >> rw[]
QED

(* One helper per raw_reachable rule; each relates the target-side state
   the rule reaches to a raw-reachable input state. *)
Theorem concretize_raw_reachable_entry[local]:
  concretize_fn_ok amap fn livesets /\
  ctx.ctx_entry = SOME fn.fn_name /\ ctx.ctx_functions = [fn] /\
  o1_initial_state_ok vs /\
  concretize_state_ok amap fn livesets init0 vs /\
  fn_entry_label (concretize_function amap fn) = SOME lbl /\
  enters_block (concretize_function amap fn)
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
    t /\
  active_inst (concretize_function amap fn) inst' t ==>
  ?inst s init.
    inst' = concretize_inst amap inst /\
    raw_reachable vs ctx fn inst s /\
    t.vs_inst_idx = s.vs_inst_idx /\
    concretize_state_ok amap fn livesets init s /\
    concretize_rel amap fn livesets init s t
Proof
  strip_tac >>
  drule_all concretize_initial_entry >>
  disch_then (qspec_then `lbl` strip_assume_tac) >>
  drule_all concretize_enters_block_reverse >> strip_tac >>
  `?inst. active_inst fn inst s1 /\ inst' = concretize_inst amap inst` by
    (irule concretize_active_inst_inverse >> simp[] >>
     metis_tac[concretize_rel_current_bb]) >>
  qexistsl [`inst`, `s1`, `init0`] >> simp[] >>
  irule raw_reachable_entry >> simp[] >>
  simp[lookup_function_def, FIND_thm] >> qexists `lbl` >> simp[] >>
  metis_tac[concretize_function_entry_label]
QED

Theorem concretize_raw_reachable_next[local]:
  concretize_fn_ok amap fn livesets /\
  raw_reachable vs ctx fn inst s /\
  concretize_state_ok amap fn livesets init s /\
  concretize_rel amap fn livesets init s t /\
  t.vs_inst_idx = s.vs_inst_idx /\
  ~is_terminator (concretize_inst amap inst).inst_opcode /\
  step_inst fuel ctx' (concretize_inst amap inst) t = OK t1 /\
  active_inst (concretize_function amap fn) inst'
    (t1 with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?i s2 init2.
    inst' = concretize_inst amap i /\
    raw_reachable vs ctx fn i s2 /\
    SUC s.vs_inst_idx = s2.vs_inst_idx /\
    concretize_state_ok amap fn livesets init2 s2 /\
    concretize_rel amap fn livesets init2 s2
      (t1 with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `active_inst fn inst s` by metis_tac[raw_reachable_active_inst] >>
  drule_all concretize_step_reverse_ok >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `~is_terminator inst.inst_opcode` by
    metis_tac[concretize_inst_is_terminator] >>
  `concretize_state_ok amap fn livesets init1
    (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule concretize_state_ok_next >> metis_tac[]) >>
  `concretize_rel amap fn livesets init1
    (s1 with vs_inst_idx := SUC s.vs_inst_idx)
    (t1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule concretize_rel_update_inst_idx >> simp[]) >>
  `?i. active_inst fn i (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
       inst' = concretize_inst amap i` by
    (irule concretize_active_inst_inverse >> simp[] >> conj_tac
     >- (qexists `t1 with vs_inst_idx := SUC s.vs_inst_idx` >>
         simp[] >> metis_tac[concretize_rel_current_bb]) >>
     qexists `livesets` >> simp[]) >>
  qexistsl [`i`, `s1 with vs_inst_idx := SUC s.vs_inst_idx`, `init1`] >>
  simp[] >> irule raw_reachable_next >> metis_tac[]
QED

Theorem concretize_raw_reachable_block[local]:
  concretize_fn_ok amap fn livesets /\
  raw_reachable vs ctx fn inst s /\
  concretize_state_ok amap fn livesets init s /\
  concretize_rel amap fn livesets init s t /\
  is_terminator (concretize_inst amap inst).inst_opcode /\
  step_inst fuel ctx' (concretize_inst amap inst) t = OK t1 /\
  ~t1.vs_halted /\ enters_block (concretize_function amap fn) t1 t2 /\
  active_inst (concretize_function amap fn) inst' t2 ==>
  ?i s2 init2.
    inst' = concretize_inst amap i /\
    raw_reachable vs ctx fn i s2 /\
    t2.vs_inst_idx = s2.vs_inst_idx /\
    concretize_state_ok amap fn livesets init2 s2 /\
    concretize_rel amap fn livesets init2 s2 t2
Proof
  strip_tac >>
  `active_inst fn inst s` by metis_tac[raw_reachable_active_inst] >>
  drule_all concretize_step_reverse_ok >>
  disch_then (qspec_then `ctx`
    (qx_choose_then `post` (qx_choose_then `init1` strip_assume_tac))) >>
  `is_terminator inst.inst_opcode` by
    metis_tac[concretize_inst_is_terminator] >>
  `~post.vs_halted` by metis_tac[concretize_rel_halted] >>
  `concretize_state_ok amap fn livesets init1 post` by
    (irule concretize_state_ok_terminator >> metis_tac[]) >>
  drule_all concretize_enters_block_reverse >>
  disch_then (qx_choose_then `entry` strip_assume_tac) >>
  `?i. active_inst fn i entry /\ inst' = concretize_inst amap i` by
    (irule concretize_active_inst_inverse >> simp[] >>
     metis_tac[concretize_rel_current_bb]) >>
  qexistsl [`i`, `entry`, `init1`] >> simp[] >>
  irule raw_reachable_block >> metis_tac[]
QED

Theorem concretize_raw_reachable_induction[local]:
  !vs ctx' fn' inst' s'. raw_reachable vs ctx' fn' inst' s' ==>
  !ctx amap fn livesets init0.
    concretize_fn_ok amap fn livesets /\
    ctx.ctx_entry = SOME fn.fn_name /\ ctx.ctx_functions = [fn] /\
    o1_initial_state_ok vs /\
    concretize_state_ok amap fn livesets init0 vs /\
    ctx' = (ctx with ctx_functions := [concretize_function amap fn]) ==>
    ?inst s init.
      fn' = concretize_function amap fn /\
      inst' = concretize_inst amap inst /\
      raw_reachable vs ctx fn inst s /\
      s'.vs_inst_idx = s.vs_inst_idx /\
      concretize_state_ok amap fn livesets init s /\
      concretize_rel amap fn livesets init s s'
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[lookup_function_def, FIND_thm, concretize_function_fn_name] >>
      metis_tac[concretize_raw_reachable_entry])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      first_x_assum drule_all >> strip_tac >> gvs[] >>
      metis_tac[concretize_raw_reachable_next])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      first_x_assum drule_all >> strip_tac >> gvs[] >>
      metis_tac[concretize_raw_reachable_block]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  metis_tac[concretize_active_not_invoke]
QED

(* ===== Reachable states simulate ===== *)

(* In a context whose only function is fn, every raw-reachable state of the
   concretized function is reached in lockstep from a raw-reachable state
   of fn, at the same instruction index, with concretize_rel between them
   and the per-state facts holding on the input side.  The initial state
   is o1's (no variables, no allocas), where concretize_rel is reflexive. *)
Theorem concretize_raw_reachable_sim:
  concretize_fn_ok amap fn livesets /\
  ctx.ctx_entry = SOME fn.fn_name /\ ctx.ctx_functions = [fn] /\
  o1_initial_state_ok vs /\
  concretize_state_ok amap fn livesets init0 vs /\
  raw_reachable vs (ctx with ctx_functions := [concretize_function amap fn])
    fn' inst' s' ==>
  ?inst s init.
    fn' = concretize_function amap fn /\
    inst' = concretize_inst amap inst /\
    raw_reachable vs ctx fn inst s /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    concretize_state_ok amap fn livesets init s /\
    concretize_rel amap fn livesets init s s'
Proof
  strip_tac >> drule concretize_raw_reachable_induction >>
  disch_then (qspecl_then [`ctx`, `amap`, `fn`, `livesets`, `init0`] mp_tac) >>
  simp[]
QED

(* ===== The transport ===== *)

Theorem active_inst_mem_fn_insts[local]:
  active_inst fn inst s ==> MEM inst (fn_insts fn)
Proof
  rw[active_inst_def] >> irule mem_fn_insts_intro >> metis_tac[EL_MEM]
QED

(* TOP-LEVEL: the site phase on fn's run becomes the static phase on the
   concretized function's run. *)
Theorem concretize_mem_inv_transport:
  concretize_fn_ok amap fn livesets /\
  ctx.ctx_entry = SOME fn.fn_name /\ ctx.ctx_functions = [fn] /\
  o1_initial_state_ok vs /\
  concretize_state_ok amap fn livesets init0 vs /\
  (!aid addr. alloca_concrete_addr amap fn aid = SOME addr ==>
              w2n addr + get_alloca_size fn (Allocation aid) <= eom) /\
  mem_inv site_mem_ok ctx vs ==>
  mem_inv (static_mem_ok eom)
    (ctx with ctx_functions := [concretize_function amap fn]) vs
Proof
  strip_tac >>
  qpat_x_assum `mem_inv _ _ _` mp_tac >>
  simp[mem_inv_raw_reachable] >> strip_tac >>
  conj_tac
  >- (fs[lookup_function_def, FIND_thm] >> gvs[] >>
      simp[concretize_function_fn_name, concretize_function_entry_label])
  >> rpt strip_tac >>
  drule_all concretize_raw_reachable_sim >> strip_tac >> gvs[] >>
  metis_tac[concretize_rel_static_mem_ok, raw_reachable_active_inst,
            active_inst_mem_fn_insts]
QED
