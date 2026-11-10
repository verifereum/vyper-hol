(* Control paths for the runtime-length memory-to-storage loop.
   Reuse typed_memory_array_condition_path_mem for LT/ISZERO/JNZ,
   and typed_memory_array_backedge_path_mem for increment/ASSIGN/JMP. *)
Theory assignPlaceDynStoragePaths
Ancestors
  assignPlaceDynStorageLayout placeTypedCopyPrimitiveMem bodyMemAssignTopCopyPaths
  fragExecMem fragExec memSafeRun instMemFrontier fragGasMode venomExecSemantics venomState
  venomInst emitHelperProps exprLoweringProps storageCopyGasPath compileEnv
  fragGasPathMem stmtSimStoreCopy words arithmetic list rich_list finite_map

Theorem dyn_storage_entry_path_mem:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst id1 MLOAD [src] [lv];
     mk_inst id2 ASSIGN [Lit 0w] [cv]; mk_inst id3 JMP [Label hdr] []] /\
  eval_operand src s = SOME b /\ w2n b + 32 <= s.vs_alloca_next ==>
  gas_path_mem ctx func s 0
    (OK (jump_to hdr
      ((update_var cv 0w (update_var lv (mload (w2n b) s) s)) with
        vs_inst_idx := s.vs_inst_idx + 2)))
Proof
  strip_tac >> irule typed_memory_prefix_jump_path_mem >> simp[] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_read1_def, eval_operand_def,
       lookup_var_update_var, fragExecMemTheory.run_inst_seq_mem_ok_def,
       inst_dload_in_section_def, below_frontier_MLOAD] >>
  rpt conj_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem dyn_storage_length_store_path_mem:
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id (if tr then TSTORE else SSTORE) [dst;len] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand dst s = SOME k /\ eval_operand len s = SOME n ==>
  gas_marked_path T ctx func s 0
    (OK (((if tr then tstore else sstore) k n s) with
           vs_inst_idx := s.vs_inst_idx + 1))
Proof
  strip_tac >>
  irule (SIMP_RULE (srw_ss()) []
    (Q.SPEC `[mk_inst id (if tr then TSTORE else SSTORE) [dst;len] []]`
      topcopy_seq_path)) >>
  conj_tac >- simp[] >>
  qexistsl_tac [`bb`, `dst`, `id`, `len`, `tr`] >> simp[] >>
  Cases_on `tr` >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_write2_def,
       run_inst_seq_mem_ok_last, below_frontier_no_ranges] >>
  gvs[mk_inst_def] >>
  Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[]
QED

Theorem dyn_storage_scaled_address_run[local]:
  eval_operand (Var cv) s = SOME i /\ eval_operand src s = SOME b /\
  (!x. src = Var x ==> x <> mv /\ x <> ov) ==>
  run_inst_seq
    [mk_inst id MUL [Var cv;Lit stride] [mv];
     mk_inst (id+1) ADD [Lit bias;Var mv] [ov];
     mk_inst (id+2) ADD [src;Var ov] [pv]] s =
  OK (update_var pv (b + (bias + i * stride))
       (update_var ov (bias + i * stride) (update_var mv (i * stride) s)))
Proof
  strip_tac >>
  `eval_operand src (update_var ov (bias + i * stride)
      (update_var mv (i * stride) s)) = SOME b` by
    (Cases_on `src` >> gvs[eval_operand_def, lookup_var_update_var]) >>
  simp[run_inst_seq_def, mk_inst_def, step_inst_base_opcode_eqs,
       exec_pure2_def, eval_operand_def, lookup_var_update_var] >>
  gvs[eval_operand_def]
QED

Theorem dyn_storage_scaled_address_path_mem:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX
    [mk_inst id MUL [Var cv;Lit stride] [mv];
     mk_inst (id+1) ADD [Lit bias;Var mv] [ov];
     mk_inst (id+2) ADD [src;Var ov] [pv]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand (Var cv) s = SOME i /\ eval_operand src s = SOME b /\
  (!x. src = Var x ==> x <> mv /\ x <> ov) ==>
  gas_marked_path T ctx func s 0
    (OK ((update_var pv (b + (bias + i * stride))
       (update_var ov (bias + i * stride) (update_var mv (i * stride) s)))
         with vs_inst_idx := s.vs_inst_idx + 3))
Proof
  strip_tac >> drule_all dyn_storage_scaled_address_run >>
  disch_then (qspecl_then [`stride`, `pv`, `id`, `bias`] assume_tac) >>
  drule_at (Pat `run_inst_seq _ _ = _`) topcopy_seq_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_mem_ok_def,
       below_frontier_no_ranges, inst_dload_in_section_def,
       step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def,
       lookup_var_update_var] >>
  gvs[eval_operand_def] >> Cases_on `src` >>
  gvs[eval_operand_def, lookup_var_update_var]
QED

Theorem dyn_storage_singleton_run[local]:
  eval_operand sp s = SOME b /\ eval_operand dst s = SOME k /\
  eval_operand (Var cv) s = SOME i /\ cv <> vv /\
  (!x. dst = Var x ==> x <> vv /\ x <> ov) /\
  vv <> ov /\ vv <> pv /\ ~s.vs_call_ctx.cc_static ==>
  run_inst_seq
    [mk_inst id MLOAD [sp] [vv];
     mk_inst (id+1) ADD [Var cv;Lit 1w] [ov];
     mk_inst (id+2) ADD [dst;Var ov] [pv];
     mk_inst (id+3) (if tr then TSTORE else SSTORE) [Var pv;Var vv] []] s =
  OK ((if tr then tstore else sstore) (k + (i + 1w)) (mload (w2n b) s)
    (update_var pv (k + (i + 1w))
      (update_var ov (i + 1w) (update_var vv (mload (w2n b) s) s))))
Proof
  strip_tac >>
  `eval_operand dst (update_var ov (i + 1w)
      (update_var vv (mload (w2n b) s) s)) = SOME k` by
    (Cases_on `dst` >> gvs[eval_operand_def, lookup_var_update_var]) >>
  Cases_on `tr` >>
  simp[run_inst_seq_def, mk_inst_def, step_inst_base_opcode_eqs,
       exec_read1_def, exec_pure2_def, exec_write2_def,
       eval_operand_def, lookup_var_update_var] >>
  gvs[eval_operand_def, lookup_var_def, update_var_def,
      finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem dyn_storage_singleton_path_mem:
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX
    [mk_inst id MLOAD [sp] [vv];
     mk_inst (id+1) ADD [Var cv;Lit 1w] [ov];
     mk_inst (id+2) ADD [dst;Var ov] [pv];
     mk_inst (id+3) (if tr then TSTORE else SSTORE) [Var pv;Var vv] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand sp s = SOME b /\ eval_operand dst s = SOME k /\
  eval_operand (Var cv) s = SOME i /\ cv <> vv /\
  (!x. dst = Var x ==> x <> vv /\ x <> ov) /\
  vv <> ov /\ vv <> pv /\ w2n b + 32 <= s.vs_alloca_next ==>
  gas_marked_path T ctx func s 0
    (OK (((if tr then tstore else sstore) (k + (i + 1w)) (mload (w2n b) s)
      (update_var pv (k + (i + 1w))
       (update_var ov (i + 1w) (update_var vv (mload (w2n b) s) s))))
      with vs_inst_idx := s.vs_inst_idx + 4))
Proof
  strip_tac >>
  qpat_assum `eval_operand sp s = SOME b`
    (mp_then (Pos hd) mp_tac dyn_storage_singleton_run) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`tr`, `id`] assume_tac) >>
  drule_at (Pat `run_inst_seq _ _ = _`) topcopy_seq_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  Cases_on `tr` >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_mem_ok_def,
       below_frontier_MLOAD, below_frontier_no_ranges,
       inst_dload_in_section_def, step_inst_base_opcode_eqs,
       exec_read1_def, exec_pure2_def, exec_write2_def,
       eval_operand_def, lookup_var_update_var] >>
  gvs[eval_operand_def] >> Cases_on `dst` >>
  gvs[eval_operand_def, lookup_var_update_var]
QED

Theorem dyn_storage_scaled_address_compile_path_mem:
  emit_op MUL [Var cv;Lit (n2w stride)] sa = (scaled,s1) /\
  emit_op ADD [Lit bias;scaled] s1 = (off,s2) /\
  emit_op ADD [src;off] s2 = (sp,sb) /\ fn_has_code sa sb func /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand (Var cv) s = SOME i /\ eval_operand src s = SOME b /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    eval_operand sp t = SOME (b + (bias + i * n2w stride)) /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all dyn_storage_scaled_address_layout >> strip_tac >>
  drule_all storage_copy_code_prefix >> strip_tac >>
  `!x. src = Var x ==> x <> mv /\ x <> ov` by gvs[] >>
  `gas_marked_path T ctx func s 0
    (OK ((update_var pv (b + (bias + i * n2w stride))
      (update_var ov (bias + i * n2w stride)
        (update_var mv (i * n2w stride) s)))
      with vs_inst_idx := s.vs_inst_idx + 3))` by
    (irule dyn_storage_scaled_address_path_mem >> simp[] >>
     qexistsl_tac [`cv`, `sa.cs_next_id`, `src`] >> gvs[]) >>
  qexists_tac `(update_var pv (b + (bias + i * n2w stride))
      (update_var ov (bias + i * n2w stride)
        (update_var mv (i * n2w stride) s)))
      with vs_inst_idx := s.vs_inst_idx + 3` >>
  gvs[same_blocks_def, ALL_DISTINCT, eval_operand_def,
      lookup_var_update_var, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[venom_state_component_equality] >>
  qpat_x_assum `emitted_insts sa sb = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
  simp[emitted_insts_def, LENGTH_DROP] >>
  drule IS_PREFIX_LENGTH >> decide_tac
QED
