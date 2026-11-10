Theory extRetLeafAllocationFramePtr
Ancestors
  list rich_list arithmetic fragExec emitHelperProps fragGasPathPtr ptrSafeRun
  ptrDiscipline contextCodegenRel venomInst venomState venomExecSemantics
  venomMemProofs venomMemProps venomInstProofs1

Definition leaf_cut_function_def:
  leaf_cut_function (sb:compile_state) (fn:ir_function) =
    fn with fn_blocks :=
      [<|bb_label := sb.cs_current_bb;
         bb_instructions := sb.cs_current_insts|>]
End

Theorem leaf_cut_function_has_code:
  sb.cs_blocks = sa.cs_blocks ==>
  fn_has_code sa sb (leaf_cut_function sb fn)
Proof
  simp[fn_has_code_def, emitted_blocks_def, leaf_cut_function_def,
       lookup_block_def, FIND_thm]
QED

Theorem leaf_nonforward_instruction:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> RETURNDATACOPY /\ inst.inst_opcode <> REVERT ==>
  ~in_revert_forward fn s
Proof
  rpt strip_tac >>
  gvs[in_revert_forward_def, revert_forward_at_def,
      revert_forward_pair_def] >>
  metis_tac[]
QED

Theorem leaf_ptr_safe_step_function:
  MEM inst.inst_opcode [MLOAD; MSTORE; MCOPY; ADD; AND] /\
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  (ptr_safe_step D lo fuel ctx f PG G tn inst s ==>
   ptr_safe_step D lo fuel ctx fn PG G tn inst s)
Proof
  rpt strip_tac >>
  `~in_revert_forward f s` by
    (irule leaf_nonforward_instruction >> qexistsl [`bb`, `inst`] >>
     gvs[]) >>
  gvs[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def,
      taint_ok_def, about_to_revert_def] >>
  metis_tac[]
QED

Theorem leaf_step_fields:
  MEM inst.inst_opcode [MLOAD; MSTORE; MCOPY; ADD; AND] /\
  step_inst fuel ctx inst s = OK t ==>
  t.vs_current_bb = s.vs_current_bb /\
  t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp
Proof
  strip_tac >>
  `~is_terminator inst.inst_opcode /\
   inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA /\
   inst.inst_opcode <> SETFMP /\ inst.inst_opcode <> DALLOCA /\
   ~is_alloca_op inst.inst_opcode` by
    gvs[is_terminator_def, is_alloca_op_def] >>
  gvs[step_inst_non_invoke] >>
  drule step_inst_base_preserves_all >>
  simp[is_terminator_def, is_alloca_op_def] >> strip_tac >>
  drule step_inst_base_preserves_alloca_state >> simp[]
QED

Theorem leaf_cut_fetch:
  lookup_block s.vs_current_bb (leaf_cut_function sb fn).fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  sa.cs_current_bb = sb.cs_current_bb /\ inst_extends sa sb /\
  LENGTH sa.cs_current_insts <= s.vs_inst_idx /\
  EVERY (\i. MEM i.inst_opcode [MLOAD; MSTORE; MCOPY; ADD; AND])
    (emitted_insts sa sb) ==>
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx < LENGTH sb.cs_current_insts /\
  MEM inst.inst_opcode [MLOAD; MSTORE; MCOPY; ADD; AND]
Proof
  simp[leaf_cut_function_def, lookup_block_def, FIND_thm] >>
  strip_tac >> gvs[get_instruction_def, inst_extends_def] >>
  gvs[EL_APPEND_EQN, EVERY_EL] >>
  first_x_assum (qspec_then `s.vs_inst_idx - LENGTH sa.cs_current_insts` mp_tac) >>
  simp[]
QED

Theorem leaf_cut_fetch_original:
  fn_has_code sa sb fn /\
  lookup_block s.vs_current_bb (leaf_cut_function sb fn).fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  ?bb'. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb' /\
        get_instruction bb' s.vs_inst_idx = SOME inst
Proof
  simp[fn_has_code_def, leaf_cut_function_def, lookup_block_def, FIND_thm] >>
  rpt strip_tac >> gvs[] >>
  gvs[get_instruction_def, IS_PREFIX_APPEND] >>
  simp[EL_APPEND_EQN]
QED

Theorem leaf_cut_edge:
  fn_has_code sa sb fn /\ sa.cs_current_bb = sb.cs_current_bb /\
  inst_extends sa sb /\
  EVERY (\i. MEM i.inst_opcode [MLOAD; MSTORE; MCOPY; ADD; AND])
    (emitted_insts sa sb) /\
  LENGTH sa.cs_current_insts <= s.vs_inst_idx /\
  gas_path_ptr_edge D lo ctx (leaf_cut_function sb fn) PG G tn s n Gf tnf (OK t)
  ==>
  gas_path_ptr_edge D lo ctx fn PG G tn s n Gf tnf (OK t) /\
  LENGTH sa.cs_current_insts <= t.vs_inst_idx /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp
Proof
  strip_tac >>
  qpat_x_assum `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [gas_path_ptr_edge_def]) >>
  drule_all leaf_cut_fetch >> strip_tac >>
  drule_all leaf_cut_fetch_original >> strip_tac >>
  `ptr_safe_step D lo fuel ctx fn PG G tn inst s` by
    (irule leaf_ptr_safe_step_function >> metis_tac[]) >>
  `~is_terminator inst.inst_opcode` by gvs[is_terminator_def] >>
  gnvs[exit_result_def]
  >~ [`OK _ = step_inst _ _ _ _`]
  >- (qpat_x_assum `OK _ = step_inst _ _ _ _`
        (fn th => fs[GSYM th, exit_result_def])) >>
  gvs[] >>
  `t'.vs_current_bb = s.vs_current_bb /\
   t'.vs_allocas = s.vs_allocas /\
   t'.vs_alloca_next = s.vs_alloca_next /\ t'.vs_fmp = s.vs_fmp` by
    metis_tac[leaf_step_fields, MEM] >>
  gvs[] >>
  simp[gas_path_ptr_edge_def] >>
  metis_tac[]
QED

Theorem leaf_cut_path_transport:
  !D lo ctx f PG G tn s n Gf tnf r.
  gas_path_ptr D lo ctx f PG G tn s n Gf tnf r ==>
  !sa sb fn sf.
    f = leaf_cut_function sb fn /\ r = OK sf /\
    fn_has_code sa sb fn /\ sa.cs_current_bb = sb.cs_current_bb /\
    inst_extends sa sb /\
    EVERY (\i. MEM i.inst_opcode [MLOAD; MSTORE; MCOPY; ADD; AND])
      (emitted_insts sa sb) /\
    LENGTH sa.cs_current_insts <= s.vs_inst_idx ==>
    gas_path_ptr D lo ctx fn PG G tn s n Gf tnf (OK sf) /\
    sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\ sf.vs_fmp = s.vs_fmp
Proof
  ho_match_mp_tac gas_path_ptr_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >> simp[gas_path_ptr_rules])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
      drule_all (SRULE [] leaf_cut_edge) >> strip_tac >>
      first_x_assum (qspecl_then [`sa`, `sb`, `fn`] mp_tac) >>
      simp[] >> strip_tac >>
      simp[] >> metis_tac[gas_path_ptr_rules])
  >> rpt strip_tac >> gvs[exit_result_def]
QED

(* The cut is a genuine execution boundary, including for an empty suffix. *)
Theorem leaf_cut_at_end_no_edge:
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ~gas_path_ptr_edge D lo ctx (leaf_cut_function sb fn) PG G tn s n Gf tnf r
Proof
  simp[gas_path_ptr_edge_def, leaf_cut_function_def,
       lookup_block_def, FIND_thm, get_instruction_def] >>
  metis_tac[]
QED

Theorem leaf_cut_empty_probe:
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  gas_path_ptr D lo ctx (leaf_cut_function sb fn) PG G tn s n Gf tnf r ==>
  n = 0 /\ Gf = G /\ tnf = tn /\ r = OK s
Proof
  once_rewrite_tac[gas_path_ptr_cases] >>
  metis_tac[leaf_cut_at_end_no_edge]
QED

(* A one-store suffix exercises fetch confinement even if the prefix
   contains allocations. No condition is imposed on that prefix. *)
Theorem leaf_cut_store_probe:
  inst.inst_opcode = MSTORE /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ [inst] /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb (leaf_cut_function sb fn).fn_blocks = SOME bb /\
       get_instruction bb s.vs_inst_idx = SOME inst /\
       ~in_revert_forward (leaf_cut_function sb fn) s
Proof
  rpt strip_tac >>
  `?bb. lookup_block s.vs_current_bb (leaf_cut_function sb fn).fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst` by
    simp[leaf_cut_function_def, lookup_block_def, FIND_thm,
         get_instruction_def, EL_APPEND_EQN] >>
  `~in_revert_forward (leaf_cut_function sb fn) s` by
    (irule leaf_nonforward_instruction >> qexistsl [`bb`, `inst`] >> simp[]) >>
  metis_tac[]
QED
