(* Arbitrary-input constructor contract.  Head readability belongs to the
   caller of an unguarded primitive, not to the allocated byte window. *)
Theory abiMalformedConstructorContract
Ancestors
  abiMalformedTraversal abiMalformedLeafProbe abiMalformedRecursiveInterface
  abiMalformedPruneState exprSimAlloc abiDecoderCoherence abiEncoder
  exprLoweringProps localPtrsProps compileEnv loweringStateRelDefs venomMemProps venomMemDefs
  venomState valueEncoding valueEncodingProps abiDecoderReentry
  freshWrites abiDecoderClampedWord abiDecoderClamp abiDecoderContract
  emitHelper emitHelperProps abiDecoderReentryPointer abiDecoderAbortReentry
  abiDecoderVarSequence abiDecoderWordTyped abiBoundedLeafReflection
  contractABI vyperABI fragExec abiDecoderEmpty abiDecoderComplexGuard
  abiDecoderComplexHead exprLowering abiVyperAdmissible vyperValue
  venomInst venomExecSemantics rich_list
  finite_map pred_set words list arithmetic

Definition abi_malformed_constructor_def:
  abi_malformed_constructor env ty di ctx func cenv cx es st en
      base_op hi src dst outsz <=>
    fn_has_code st en func ==>
    !B L xs p d dstid live ceiling incoming.
      en.cs_next_var <= ceiling.cs_next_var /\
      (case di of DecPrimWord clamp => p + 32 <= L | _ => T) ==>
      frag_exec ctx st en
        (\v. v = incoming /\
          abi_malformed_entry ctx func cenv cx es st
            (abi_malformed_scratch_sites st en func) dstid live
            base_op hi src dst B L xs p d outsz v /\
          fresh_vars_wrt ceiling v)
        (\u. abi_malformed_reflected_post env ty
          (if is_dynamic (vyper_to_abi_type env ty) then DROP p xs
           else TAKE (static_length (vyper_to_abi_type env ty)) (DROP p xs))
          ctx func cenv cx es st.cs_next_var
            (abi_malformed_scratch_sites st en func) dstid incoming u /\
          fresh_vars_wrt ceiling u)
        (\r. ?v. r = Abort Revert_abort v)
End

(* Exact single-store boundary used by primitive constructors.  The register
   assignment is a proof description of real execution, not a runtime prune. *)
Theorem abi_malformed_destination_store_resource:
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  32 <= outsz /\ fn_inst_ids_distinct func /\
  (!x. not_fresh_at st x ==> FLOOKUP vars x = FLOOKUP s.vs_vars x) ==>
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s
    (mstore d w (s with vs_vars := vars))
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es (s with vs_vars := vars)` by
    (irule abi_malformed_reserved_vars_state >>
     fs[abi_malformed_entry_def] >> qexists_tac `st` >>
     simp[lookup_var_def]) >>
  `abi_malformed_destination func cenv es.scopes dstid d outsz s` by
    fs[abi_malformed_entry_def] >>
  fs[abi_malformed_destination_def] >>
  `stmt_state_rel ctx func cenv cx es
     (mstore d w (s with vs_vars := vars))` by
    (irule literal_mstore_state_rel >> simp[] >>
     qexistsl_tac [`b`, `inst`, `sz`] >> simp[] >>
     rpt strip_tac >>
     `local_ptrs_rel func cenv es.scopes (s with vs_vars := vars)` by
       gvs[stmt_state_rel_def, state_rel_def] >>
     `alloca_inv (s with vs_vars := vars)` by fs[stmt_state_rel_def] >>
     `FLOOKUP (s with vs_vars := vars).vs_allocas inst.inst_id = SOME (b,sz)` by simp[] >>
     drule_all local_ptrs_rel_alloca_disjoint >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  ` (mstore d w (s with vs_vars := vars)).vs_allocas = s.vs_allocas /\
    (mstore d w (s with vs_vars := vars)).vs_alloca_next = s.vs_alloca_next /\
    (mstore d w (s with vs_vars := vars)).vs_vars = vars` by
    simp[mstore_def, write_memory_with_expansion_def] >>
  simp[abi_malformed_resource_post_def] >> conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at B' L' (mstore d w (s with vs_vars := vars)).vs_memory =
       mem_bytes_at B' L' (s with vs_vars := vars).vs_memory` suffices_by simp[] >>
      irule mstore_mem_bytes_at_disjoint >>
      `allocas_non_overlapping s` by
        fs[abi_malformed_entry_def, stmt_state_rel_def, alloca_inv_def] >>
      fs[allocas_non_overlapping_def] >>
      qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule_all >> decide_tac) >>
  rpt strip_tac >> Cases_on `op` >>
  fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
     not_fresh_at_def, eval_operand_def, lookup_var_def] >> metis_tac[]
QED

Theorem abi_malformed_clamp_writes_fresh:
  compile_abi_clamp_basetype val_op clamp st = ((),en) ==>
  writes_fresh st (emitted_insts st en)
Proof
  Cases_on `clamp` >>
  FIRST [rename1 `IntClamp bits signed` >> Cases_on `signed`, all_tac] >>
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, writes_fresh_def, fresh_write_op_def,
       mk_inst_def, not_fresh_at_def] >> metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]
QED

(* Successful memory/source reads, like arithmetic, update only their output. *)
Theorem abi_malformed_read_step_frame:
  (fresh_write_op inst.inst_opcode \/
   abi_decode_source_opcode inst.inst_opcode) /\
  step_inst_base inst s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  !x. ~MEM x inst.inst_outputs ==>
    FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  strip_tac
  >- (drule_all step_fresh_write_op >> simp[]) >>
  fs[abi_decode_source_opcode_def] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  simp[update_var_def, FLOOKUP_UPDATE, venom_state_component_equality] >>
  metis_tac[]
QED

Theorem abi_malformed_read_sequence_frame:
  EVERY (\i. (fresh_write_op i.inst_opcode \/
               abi_decode_source_opcode i.inst_opcode) /\
             EVERY (\x. ~not_fresh_at st x) i.inst_outputs) is /\
  run_inst_seq is s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  !x. not_fresh_at st x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  strip_tac >> irule run_inst_seq_protected_frame >>
  qexists_tac `is` >> simp[] >> rpt gen_tac >> strip_tac >>
  `t' = s' with vs_vars := t'.vs_vars /\
   !x. ~MEM x i.inst_outputs ==>
     FLOOKUP t'.vs_vars x = FLOOKUP s'.vs_vars x` by
    (irule abi_malformed_read_step_frame >> fs[EVERY_MEM]) >>
  simp[] >> rpt strip_tac >> first_x_assum irule >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem abi_malformed_primitive_store_shape:
  compile_abi_decode_to_buf dst src opc base_op hi (DecPrimWord clamp) st = ((),en) /\
  abi_decode_source_opcode opc ==>
  emitted_insts st en <> [] /\
  EVERY (\i. (fresh_write_op i.inst_opcode \/
               abi_decode_source_opcode i.inst_opcode) /\
             EVERY (\x. ~not_fresh_at st x) i.inst_outputs)
    (FRONT (emitted_insts st en)) /\
  ?id val_op. LAST (emitted_insts st en) =
    mk_inst id MSTORE [dst; val_op] []
Proof
  Cases_on `base_op = Lit 0w` >> Cases_on `clamp` >>
  FIRST [rename1 `IntClamp bits signed` >> Cases_on `signed`, all_tac] >>
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
       compile_abi_decode_static_def, compile_abi_clamp_basetype_def,
       compile_abi_int_clamp_def, compile_abi_bytes_clamp_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
       emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp_tac list_ss [FRONT_DEF, LAST_DEF] >>
  reverse conj_tac >- (irule_at Any EQ_REFL) >>
  simp[fresh_write_op_def, mk_inst_def, not_fresh_at_def] >>
  metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]
QED

Theorem abi_malformed_primitive_exact_store:
  compile_abi_decode_to_buf dst src opc base_op hi (DecPrimWord clamp) st = ((),en) /\
  abi_decode_source_opcode opc /\
  abi_decoder_operand_live st.cs_next_var dst /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  run_inst_seq (emitted_insts st en) s = OK t ==>
  ?w. t = mstore d w (s with vs_vars := t.vs_vars) /\
      !x. not_fresh_at st x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  strip_tac >> drule_all abi_malformed_primitive_store_shape >> strip_tac >>
  `emitted_insts st en = FRONT (emitted_insts st en) ++
      [mk_inst id MSTORE [dst;val_op] []]` by
    metis_tac[APPEND_FRONT_LAST] >>
  `?u. run_inst_seq (FRONT (emitted_insts st en)) s = OK u` by
    (spose_not_then assume_tac >>
     drule run_inst_seq_append_err >>
     disch_then (qspec_then `[mk_inst id MSTORE [dst;val_op] []]` mp_tac) >>
     metis_tac[]) >>
  drule_all abi_malformed_read_sequence_frame >> strip_tac >>
  `u.vs_labels = s.vs_labels` by
    (qpat_x_assum `u = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `eval_operand dst u = SOME (n2w d)` by
    (Cases_on `dst` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
         not_fresh_at_def, eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  `run_inst_seq [mk_inst id MSTORE [dst;val_op] []] u = OK t` by
    metis_tac[run_inst_seq_append] >>
  fs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
     exec_write2_def, AllCaseEqs()] >>
  gvs[w2n_n2w] >>
  `(mstore d val u).vs_vars = u.vs_vars` by
    simp[mstore_def, write_memory_with_expansion_def] >>
  qexists_tac `val` >> simp[] >> AP_TERM_TAC >>
  first_assum ACCEPT_TAC
QED

Theorem abi_malformed_primitive_run_resource:
  compile_abi_decode_to_buf dst src opc base_op hi (DecPrimWord clamp) st = ((),en) /\
  abi_decode_source_opcode opc /\ fn_inst_ids_distinct func /\ 32 <= outsz /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  run_inst_seq (emitted_insts st en) s = OK t ==>
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t
Proof
  strip_tac >>
  `abi_decoder_operand_live st.cs_next_var dst /\
   eval_operand dst s = SOME (n2w d) /\ d < dimword (:256)` by
    fs[abi_malformed_entry_def] >>
  drule_all abi_malformed_primitive_exact_store >> strip_tac >>
  qpat_x_assum `t = mstore _ _ _` SUBST1_TAC >>
  irule abi_malformed_destination_store_resource >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_malformed_primitive_reentry_code:
  compile_abi_decode_to_buf dst src opc base_op hi (DecPrimWord clamp) st = ((),en) /\
  abi_decode_source_opcode opc ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st en)
Proof
  Cases_on `base_op = Lit 0w` >> Cases_on `clamp` >>
  FIRST [rename1 `IntClamp bits signed` >> Cases_on `signed`, all_tac] >>
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
       compile_abi_decode_static_def, compile_abi_clamp_basetype_def,
       compile_abi_int_clamp_def, compile_abi_bytes_clamp_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
       emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, abi_decoder_reentry_opcode_def,
      abi_decode_source_opcode_def, mk_inst_def]
QED

Theorem abi_malformed_primitive_reflected_run:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecPrimWord clamp) st = ((),en) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  (?av. has_type (vyper_to_abi_type env ty) av) /\
  fn_inst_ids_distinct func /\ 32 <= outsz /\ p + 32 <= L /\
  en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s ==>
  (?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
  (?t. run_inst_seq (emitted_insts st en) s = OK t /\
    abi_malformed_reflected_post env ty (TAKE 32 (DROP p xs))
      ctx func cenv cx es st.cs_next_var sites dstid s t /\
    fresh_vars_wrt ceiling t)
Proof
  strip_tac >>
  `abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz
      (abi_decoder_prune_vars st.cs_next_var s)` by
    (irule abi_malformed_entry_prune >> simp[]) >>
  `abi_decode_source_opcode MLOAD /\
   fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s)` by
    simp[abi_decode_source_opcode_def, abi_decoder_prune_fresh] >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var s) = SOME (n2w (p+0)) /\
   eval_operand base_op (abi_decoder_prune_vars st.cs_next_var s) = SOME (n2w B) /\
   eval_operand dst (abi_decoder_prune_vars st.cs_next_var s) = SOME (n2w d) /\
   d < dimword (:256) /\ B+L < dimword (:256) /\
   mem_bytes_at B L (abi_decode_source MLOAD
     (abi_decoder_prune_vars st.cs_next_var s)) = xs` by
    fs[abi_malformed_entry_def, abi_malformed_allocated_window_def,
       abi_decode_source_def] >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st en)` by
    (drule_all abi_malformed_primitive_reentry_code >> simp[]) >>
  fs[ADD_0] >>
  drule_all (SRULE [PULL_EXISTS] (Q.INST [`off` |-> `0`, `H` |-> `32`,
    `s` |-> `abi_decoder_prune_vars st.cs_next_var s`]
    abi_aggregate_primitive_reflected_total)) >> strip_tac
  >- (disj1_tac >> drule_all abi_decoder_sequence_revert_reentry >> simp[]) >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s actual` by
    (qpat_x_assum `run_inst_seq _ (abi_decoder_prune_vars _ _) = OK _` kall_tac >>
     drule_all abi_malformed_primitive_run_resource >> simp[]) >>
  disj2_tac >> goal_assum (drule_at Any) >>
  simp[abi_malformed_reflected_post_def]
QED

Theorem abi_malformed_reflected_post_inst_idx:
  abi_malformed_reflected_post env ty bytes ctx func cenv cx es
    next sites dstid s (t with vs_inst_idx := n) <=>
  abi_malformed_reflected_post env ty bytes ctx func cenv cx es
    next sites dstid s t
Proof
  simp[abi_malformed_reflected_post_def, abi_malformed_resource_post_def,
       stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def]
QED

Theorem abi_malformed_primitive_reflected_fragment:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecPrimWord clamp) st = ((),en) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  (?av. has_type (vyper_to_abi_type env ty) av) /\
  fn_inst_ids_distinct func /\ 32 <= outsz /\ p + 32 <= L /\
  en.cs_next_var <= ceiling.cs_next_var ==>
  frag_exec ctx st en
    (\v. v = incoming /\
      abi_malformed_entry ctx func cenv cx es st sites dstid live
        base_op hi src dst B L xs p d outsz v /\ fresh_vars_wrt ceiling v)
    (\u. abi_malformed_reflected_post env ty (TAKE 32 (DROP p xs))
      ctx func cenv cx es st.cs_next_var sites dstid incoming u /\
      fresh_vars_wrt ceiling u)
    (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st en)` by (fs[EVERY_MEM] >> metis_tac[]) >>
  irule frag_exec_run_inst_seq >> simp[] >>
  rpt strip_tac >> gvs[] >>
  drule_all (SRULE [PULL_EXISTS] abi_malformed_primitive_reflected_run) >> strip_tac
  >- (disj2_tac >> goal_assum (drule_at Any) >> simp[]) >>
  disj1_tac >> goal_assum (drule_at Any) >>
  fs[abi_malformed_reflected_post_inst_idx, fresh_vars_wrt_def]
QED

Theorem abi_malformed_primitive_constructor:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecPrimWord clamp) st = ((),en) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  (?av. has_type (vyper_to_abi_type env ty) av) /\
  fn_inst_ids_distinct func /\ 32 <= outsz ==>
  abi_malformed_constructor env ty (DecPrimWord clamp) ctx func cenv cx es st en
    base_op hi src dst outsz
Proof
  strip_tac >>
  `type_memory_bytes ce ty = 32 /\ ~is_abi_dynamic ce.ce_struct_fields ty` by
    (drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
     simp[] >> metis_tac[]) >>
  `~is_dynamic (vyper_to_abi_type env ty) /\
   static_length (vyper_to_abi_type env ty) = 32` by
    (drule abi_decoder_coherent_header >> simp[abi_decoder_header_def] >>
     metis_tac[]) >>
  simp[abi_malformed_constructor_def] >> rpt strip_tac >>
  irule abi_malformed_primitive_reflected_fragment >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem abi_malformed_complex_guard_writes:
  abi_decode_complex_head_guard src hi H st = ((),en) ==>
  EVERY (\i. (fresh_write_op i.inst_opcode \/
               abi_decode_source_opcode i.inst_opcode) /\
             EVERY (\x. ~not_fresh_at st x) i.inst_outputs)
    (emitted_insts st en)
Proof
  Cases_on `hi = Lit 0w` >>
  simp[abi_decode_complex_head_guard_def, compile_abi_decode_range_check_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
       emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, fresh_write_op_def, mk_inst_def, not_fresh_at_def] >>
  metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]
QED

Theorem abi_malformed_read_sequence_resource:
  EVERY (\i. (fresh_write_op i.inst_opcode \/
               abi_decode_source_opcode i.inst_opcode) /\
             EVERY (\x. ~not_fresh_at st x) i.inst_outputs) is /\
  run_inst_seq is s = OK t /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st ==>
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t
Proof
  strip_tac >> drule_all abi_malformed_read_sequence_frame >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es t` by
    (qpat_assum `t = s with vs_vars := _` SUBST1_TAC >>
     irule abi_malformed_reserved_vars_state >> simp[] >> qexists_tac `st` >>
     simp[lookup_var_def]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels` by
    (qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  simp[abi_malformed_resource_post_def] >> rpt strip_tac >> Cases_on `op` >>
  fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
     not_fresh_at_def, eval_operand_def, lookup_var_def]
QED

Theorem abi_malformed_empty_reflected_run:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecComplex dynamic []) st = ((),en) /\
  en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s ==>
  (?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
  (?t. run_inst_seq (emitted_insts st en) s = OK t /\ p <= L /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t /\
    fresh_vars_wrt ceiling t)
Proof
  simp_tac bool_ss [abi_decode_empty_complex_phases] >> strip_tac >>
  `hi <> Lit 0w /\ eval_operand src s = SOME (n2w p) /\
   eval_operand hi s = SOME (n2w L) /\ p < dimword (:256) /\
   L < dimword (:256) /\
   abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var hi` by
    (fs[abi_malformed_entry_def, abi_malformed_allocated_window_def] >> decide_tac) >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st en)` by
    fs[EVERY_CONJ] >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var s) = SOME (n2w p) /\
   eval_operand hi (abi_decoder_prune_vars st.cs_next_var s) = SOME (n2w L) /\
   fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s)` by
    simp[abi_decoder_prune_eval, abi_decoder_prune_fresh] >>
  `comp_bind (emit_op ADD [src; Lit 0w])
      (\e. compile_abi_decode_range_check src e hi) st = ((),en)` by
    fs[abi_decode_complex_head_guard_def] >>
  `0 < dimword (:256) /\
   eval_operand (Lit 0w) (abi_decoder_prune_vars st.cs_next_var s) =
     SOME (n2w 0 : bytes32)` by simp[eval_operand_def] >>
  drule_all (Q.INST [`H` |-> `0`, `s` |-> `abi_decoder_prune_vars st.cs_next_var s`,
      `sz` |-> `Lit 0w`] abi_aggregate_head_guard_total) >> simp[] >> strip_tac
  >- (disj1_tac >> drule_all abi_decoder_sequence_revert_reentry >> simp[]) >>
  `p <= L` by fs[w2n_n2w] >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s actual` by
    (irule abi_malformed_read_sequence_resource >>
     conj_tac
     >- (qexists_tac `emitted_insts st en` >> simp[] >>
         drule_all abi_malformed_complex_guard_writes >> simp[]) >>
     fs[abi_malformed_entry_def]) >>
  disj2_tac >> goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_malformed_empty_source:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  !dynamic bytes. type_to_abi_dec_info sf ce ty = DecComplex dynamic [] ==>
    vyper_decode_valid_enc (vyper_to_abi_type env ty) bytes /\
    abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bytes)
Proof
  ho_match_mp_tac abi_decoder_coherent_strongind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `bt` >>
      FIRST [rename1 `BytesT bd` >> Cases_on `bd`, all_tac] >>
      simp[Once type_to_abi_dec_info_def])
  >- simp[Once type_to_abi_dec_info_def]
  >- (rpt gen_tac >> strip_tac >> Cases_on `bound` >>
      simp[Once type_to_abi_dec_info_def] >> rpt strip_tac >>
      gvs[GENLIST_EQ_NIL] >>
      simp[vyper_decode_valid_enc_def, dec_def] >>
      simp[abi_vyper_admissible_array_iff, abi_vyper_admissible_list_nil,
           compatible_bound_def] >>
      metis_tac[abi_decoder_coherent_header, abi_decoder_header_def])
  >- (rpt gen_tac >> strip_tac >> simp[Once type_to_abi_dec_info_def] >>
      rpt strip_tac >> gvs[] >>
      simp[vyper_decode_valid_enc_def, dec_def] >>
      metis_tac[abi_vyper_admissible_rules]) >>
  rpt gen_tac >> strip_tac >> simp[Once type_to_abi_dec_info_def] >>
  rpt strip_tac >> gvs[] >>
  simp[vyper_decode_valid_enc_def, dec_def, abi_vyper_admissible_struct_iff,
       abi_vyper_admissible_list_nil]
QED

Theorem abi_malformed_empty_constructor:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecComplex dynamic []) st = ((),en) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecComplex dynamic [] ==>
  abi_malformed_constructor env ty (DecComplex dynamic []) ctx func cenv cx es st en
    base_op hi src dst outsz
Proof
  strip_tac >> simp[abi_malformed_constructor_def] >> rpt strip_tac >>
  `abi_decode_complex_head_guard src hi 0 st = ((),en)` by
    fs[abi_decode_empty_complex_phases] >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st en)` by fs[EVERY_CONJ] >>
  irule frag_exec_run_inst_seq >> simp[] >> rpt strip_tac >> gvs[] >>
  `en.cs_next_var <= ceiling.cs_next_var` by fs[] >>
  drule_all abi_malformed_empty_reflected_run >> strip_tac
  >- (disj2_tac >> goal_assum (drule_at Any) >> simp[]) >>
  disj1_tac >> goal_assum (drule_at Any) >>
  fs[abi_malformed_reflected_post_inst_idx, abi_malformed_reflected_post_def,
     fresh_vars_wrt_def] >>
  drule_all abi_malformed_empty_source >> simp[]
QED
