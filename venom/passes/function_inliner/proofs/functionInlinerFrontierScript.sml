(* Allocation frontier sidecar: independent of the live storage abstraction. *)
Theory functionInlinerFrontier
Ancestors
  functionInlinerLiveInvariant functionInlinerOrigin functionInlinerContract
  venomMemProofs venomExecProofs venomExecSemantics venomState venomInst stateFrame
  functionInlinerFrame functionInlinerDefs indexedLists list

Definition inline_frontier_result_def:
  (inline_frontier_result n (OK s) <=> s.vs_alloca_next = n) /\
  (inline_frontier_result n (Halt s) <=> s.vs_alloca_next = n) /\
  (inline_frontier_result n (Abort a s) <=> s.vs_alloca_next = n) /\
  (inline_frontier_result n (IntRet ir s) <=> s.vs_alloca_next = n) /\
  (inline_frontier_result n (Error e) <=> T)
End

Definition inline_frontier_instruction_def:
  inline_frontier_instruction inst <=> inst.inst_opcode <> ALLOCA
End

Definition inline_frontier_function_def:
  inline_frontier_function fn <=>
    EVERY (\bb. EVERY inline_frontier_instruction bb.bb_instructions) fn.fn_blocks
End

Definition inline_frontier_context_def:
  inline_frontier_context C <=> EVERY inline_frontier_function C.ctx_functions
End

Theorem inline_frontier_update_var[simp]:
  (update_var x w s).vs_alloca_next = s.vs_alloca_next
Proof simp[update_var_def]
QED

Theorem inline_frontier_assignments[simp]:
  !pairs s. (FOLDL (\s (x,w). update_var x w s) s pairs).vs_alloca_next =
    s.vs_alloca_next
Proof
  Induct >> simp[] >> Cases_on `h` >> simp[]
QED

Theorem inline_frontier_bind_outputs:
  bind_outputs outs vals s = SOME t ==> t.vs_alloca_next = s.vs_alloca_next
Proof
  simp[bind_outputs_def] >> strip_tac >> gvs[]
QED

Theorem inline_frontier_merge[simp]:
  (merge_callee_state s t).vs_alloca_next = s.vs_alloca_next
Proof simp[merge_callee_state_def]
QED

Theorem inline_frontier_adopt[simp]:
  (adopt_return_fmp ir s).vs_alloca_next = s.vs_alloca_next
Proof Cases_on `ir.iret_adopt_fmp` >> simp[adopt_return_fmp_def]
QED

Theorem inline_frontier_setup:
  setup_callee fn args s = SOME t ==> t.vs_alloca_next = s.vs_alloca_next
Proof simp[setup_callee_def] >> strip_tac >> gvs[]
QED

Theorem inline_frontier_base:
  inline_frontier_instruction inst /\ inst.inst_opcode <> INVOKE ==>
  inline_frontier_result s.vs_alloca_next (step_inst_base inst s)
Proof
  strip_tac >> Cases_on `step_inst_base inst s` >>
  gvs[inline_frontier_result_def, inline_frontier_instruction_def] >>
  metis_tac[step_inst_base_preserves_alloca_next]
QED

Theorem inline_frontier_setup_compare:
  inline_shared_frame s = inline_shared_frame t /\
  s.vs_alloca_next = t.vs_alloca_next /\
  fn.fn_blocks <> [] /\ gn.fn_blocks <> [] /\
  (HD fn.fn_blocks).bb_label = (HD gn.fn_blocks).bb_label /\
  ~s.vs_halted /\ ~t.vs_halted ==>
  setup_callee fn args s = setup_callee gn args t
Proof
  simp[inline_shared_frame_def, execution_frame_def,
       venom_state_component_equality] >>
  rpt strip_tac >>
  simp[setup_callee_def, NULL_EQ, venom_state_component_equality]
QED

Theorem inline_frontier_phis:
  eval_phis s insts = OK t ==> t.vs_alloca_next = s.vs_alloca_next
Proof metis_tac[eval_phis_preserves_alloca_fields]
QED

Theorem inline_frontier_evaluation:
  (!fuel C inst s. inline_frontier_context C /\ inline_frontier_instruction inst ==>
    inline_frontier_result s.vs_alloca_next (step_inst fuel C inst s)) /\
  (!fuel C bb s. inline_frontier_context C /\
    EVERY inline_frontier_instruction bb.bb_instructions ==>
    inline_frontier_result s.vs_alloca_next (exec_block fuel C bb s)) /\
  (!fuel C fn s. inline_frontier_context C /\ inline_frontier_function fn ==>
    inline_frontier_result s.vs_alloca_next (run_blocks fuel C fn s))
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac >> rpt strip_tac
  >- (Cases_on `inst.inst_opcode = INVOKE`
      >- (once_rewrite_tac[step_inst_def] >> simp[] >>
          rpt (BasicProvers.TOP_CASE_TAC >> simp[inline_frontier_result_def]) >>
          rename1 `lookup_function _ C.ctx_functions = SOME callee` >>
          `inline_frontier_function callee` by
            (gvs[inline_frontier_context_def, EVERY_MEM] >>
             metis_tac[lookup_function_MEM]) >>
          gvs[inline_frontier_result_def] >>
          metis_tac[inline_frontier_setup, inline_frontier_bind_outputs,
                    inline_frontier_merge, inline_frontier_adopt]) >>
      simp[step_inst_non_invoke] >> irule inline_frontier_base >> simp[])
  >- (once_rewrite_tac[exec_block_def] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >>
      simp[inline_frontier_result_def] >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
      `inline_frontier_instruction inst` by
        (gvs[get_instruction_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
      `inline_frontier_result s.vs_alloca_next (step_inst fuel C inst s)` by
        metis_tac[] >>
      Cases_on `step_inst fuel C inst s` >>
      gvs[inline_frontier_result_def] >>
      Cases_on `is_terminator inst.inst_opcode` >> simp[inline_frontier_result_def] >>
      Cases_on `v.vs_halted` >> simp[inline_frontier_result_def] >>
      metis_tac[])
  >> once_rewrite_tac[run_blocks_def] >> Cases_on `fuel` >>
  simp[inline_frontier_result_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[inline_frontier_result_def] >> rename1 `lookup_block _ _ = SOME bb` >>
  `EVERY inline_frontier_instruction bb.bb_instructions` by
    (gvs[inline_frontier_function_def, EVERY_MEM] >>
     metis_tac[lookup_block_MEM]) >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs
  >- (simp[] >>
      `s'.vs_alloca_next = s.vs_alloca_next` by metis_tac[inline_frontier_phis] >>
      `inline_frontier_result s.vs_alloca_next
         (exec_block n C bb (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions))` by
        (gvs[] >> metis_tac[]) >>
      Cases_on `exec_block n C bb (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
      gvs[inline_frontier_result_def] >>
      Cases_on `v.vs_halted` >> simp[inline_frontier_result_def] >> metis_tac[]) >>
  simp[inline_frontier_result_def]
QED

Theorem inline_frontier_input:
  inliner_input_ok C ==> inline_frontier_context C
Proof
  simp[inline_frontier_context_def, inline_frontier_function_def, EVERY_MEM,
       inline_frontier_instruction_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  fs[inliner_input_ok_def, EVERY_MEM] >>
  metis_tac[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff]
QED

(* All snapshots, including immutable activation entries, share the root's
   allocation frontier.  This is deliberately separate from storage/Live. *)
Definition inline_frontier_stack_def:
  inline_frontier_stack entries frame <=>
    frame.ipf_state.vs_alloca_next = frame.ipf_anchor.vs_alloca_next /\
    EVERY (\(p,a,route,snap).
      snap.ils_state.vs_alloca_next = frame.ipf_anchor.vs_alloca_next /\
      snap.ils_saved.vs_alloca_next = frame.ipf_anchor.vs_alloca_next /\
      snap.ils_entry.vs_alloca_next = frame.ipf_anchor.vs_alloca_next /\
      a.ia_entry.vs_alloca_next = frame.ipf_anchor.vs_alloca_next) entries
End

Theorem inline_frontier_stack_head:
  inline_frontier_stack ((p,a,route,snap)::rest) frame ==>
    snap.ils_state.vs_alloca_next = frame.ipf_state.vs_alloca_next /\
    snap.ils_saved.vs_alloca_next = frame.ipf_state.vs_alloca_next /\
    snap.ils_entry.vs_alloca_next = frame.ipf_state.vs_alloca_next /\
    a.ia_entry.vs_alloca_next = frame.ipf_state.vs_alloca_next
Proof simp[inline_frontier_stack_def]
QED

Theorem inline_frontier_stack_pop:
  inline_frontier_stack (entry::rest) frame ==>
  inline_frontier_stack rest frame
Proof simp[inline_frontier_stack_def]
QED

Theorem inline_frontier_stack_physical_update:
  inline_frontier_stack entries frame /\
  t.vs_alloca_next = frame.ipf_state.vs_alloca_next ==>
  inline_frontier_stack entries (frame with ipf_state := t)
Proof simp[inline_frontier_stack_def]
QED

Theorem inline_frontier_stack_push:
  inline_frontier_stack entries frame /\
  snap.ils_state.vs_alloca_next = frame.ipf_state.vs_alloca_next /\
  snap.ils_saved.vs_alloca_next = frame.ipf_state.vs_alloca_next /\
  snap.ils_entry.vs_alloca_next = frame.ipf_state.vs_alloca_next /\
  a.ia_entry.vs_alloca_next = frame.ipf_state.vs_alloca_next ==>
  inline_frontier_stack ((p,a,route,snap)::entries) frame
Proof simp[inline_frontier_stack_def]
QED

Theorem inline_frontier_stack_root:
  snap.ils_state = s /\ snap.ils_saved = s /\ snap.ils_entry = s /\
  a.ia_entry = s ==>
  inline_frontier_stack [(p,a,route,snap)]
    <|ipf_state := s; ipf_anchor := s|>
Proof simp[inline_frontier_stack_def]
QED

Theorem inline_frontier_stack_head_update:
  inline_frontier_stack ((p,a,route,snap)::rest) frame /\
  s.vs_alloca_next = snap.ils_state.vs_alloca_next /\
  t.vs_alloca_next = frame.ipf_state.vs_alloca_next ==>
  inline_frontier_stack
    ((p,a,route,snap with ils_state := s)::rest)
    (frame with ipf_state := t)
Proof simp[inline_frontier_stack_def] >> metis_tac[]
QED

Theorem inline_frontier_rewrite_inst:
  inline_frontier_instruction inst /\
  rewrite_inline_inst ops outs ret inst q = (xs,q') ==>
  EVERY inline_frontier_instruction xs
Proof
  simp[rewrite_inline_inst_def] >>
  Cases_on `is_param_opcode inst.inst_opcode` >> simp[]
  >- (IF_CASES_TAC >> simp[inline_frontier_instruction_def] >>
      strip_tac >> gvs[inline_frontier_instruction_def]) >>
  Cases_on `inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP` >>
  simp[inline_frontier_instruction_def, EVERY_MAP, EVERY_MEM, indexedListsTheory.MEM_MAPi] >>
  strip_tac >> gvs[] >> rpt strip_tac >>
  gvs[indexedListsTheory.MEM_MAPi] >> simp[]
QED

Theorem inline_frontier_rewrite_insts:
  !insts ops outs ret q xs q'.
  EVERY inline_frontier_instruction insts /\
  rewrite_inline_insts ops outs ret insts q = (xs,q') ==>
  EVERY inline_frontier_instruction xs
Proof
  Induct >> simp[rewrite_inline_insts_def] >> rpt gen_tac >>
  pairarg_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  metis_tac[inline_frontier_rewrite_inst, EVERY_APPEND]
QED

Theorem inline_frontier_rewrite_blocks:
  !bbs ops outs ret q bs q'.
  EVERY (\bb. EVERY inline_frontier_instruction bb.bb_instructions) bbs /\
  rewrite_inline_blocks ops outs ret bbs q = (bs,q') ==>
  EVERY (\bb. EVERY inline_frontier_instruction bb.bb_instructions) bs
Proof
  Induct >> simp[rewrite_inline_blocks_def] >> rpt gen_tac >>
  pairarg_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `rewrite_inline_block _ _ _ _ _ = _` mp_tac >>
  simp[rewrite_inline_block_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  metis_tac[inline_frontier_rewrite_insts]
QED

Theorem inline_frontier_clone:
  inline_frontier_function fn ==> inline_frontier_function (clone_function p fn)
Proof
  simp[inline_frontier_function_def, clone_function_def, EVERY_MAP,
       clone_basic_block_def, clone_instruction_def,
       inline_frontier_instruction_def, EVERY_MEM, MEM_MAP] >>
  rpt strip_tac >> gvs[clone_basic_block_def, MEM_MAP, clone_instruction_def] >>
  metis_tac[]
QED

Theorem inline_frontier_control[simp]:
  (jump_to lbl s).vs_alloca_next = s.vs_alloca_next
Proof simp[jump_to_def]
QED

Theorem inline_frontier_fix_phis:
  inline_frontier_function fn ==>
  inline_frontier_function (fix_inline_phis old new bb fn)
Proof
  simp[inline_frontier_function_def, fix_inline_phis_def, EVERY_MAP,
       EVERY_MEM, inline_frontier_instruction_def] >>
  rpt strip_tac >>
  gvs[MEM_MAP, cfgTransformTheory.subst_label_inst_def] >>
  Cases_on `MEM bb''.bb_label (bb_succs bb)` >>
  gvs[MEM_MAP] >>
  gvs[COND_RAND, COND_RATOR] >> metis_tac[]
QED

Theorem inline_frontier_renumber:
  inline_frontier_function fn ==>
  inline_frontier_function (renumber_fn_inst_ids fn)
Proof
  `MAP inline_frontier_instruction (fn_insts (renumber_fn_inst_ids fn)) =
   MAP inline_frontier_instruction (fn_insts fn)` by
    (irule renumber_fn_projection >> simp[inline_frontier_instruction_def]) >>
  `!f. inline_frontier_function f <=> EVERY I (MAP inline_frontier_instruction (fn_insts f))` by
    (simp[inline_frontier_function_def, EVERY_MAP, EVERY_MEM, fn_insts_def,
          unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem inline_frontier_call_site:
  inline_frontier_function caller /\ inline_frontier_function callee ==>
  inline_frontier_function (inline_call_site p ret caller callee lbl idx)
Proof
  strip_tac >> simp[inline_call_site_def] >>
  Cases_on `lookup_block lbl caller.fn_blocks` >> simp[] >>
  rename1 `lookup_block lbl caller.fn_blocks = SOME bb` >>
  `EVERY inline_frontier_instruction bb.bb_instructions` by
    (gvs[inline_frontier_function_def, EVERY_MEM] >> metis_tac[lookup_block_MEM]) >>
  pairarg_tac >> simp[inline_frontier_function_def, EVERY_APPEND] >>
  `inline_frontier_function (clone_function p callee)` by
    metis_tac[inline_frontier_clone] >>
  `EVERY (\b. EVERY inline_frontier_instruction b.bb_instructions) rewritten_blocks` by
    metis_tac[inline_frontier_rewrite_blocks, inline_frontier_function_def] >>
  `EVERY inline_frontier_instruction (TAKE idx bb.bb_instructions)` by
    simp[rich_listTheory.EVERY_TAKE] >>
  simp[] >> conj_tac
  >- (simp[cfgTransformTheory.replace_block_def, EVERY_MAP, EVERY_MEM] >>
      rpt strip_tac >> gvs[MEM_MAP] >>
      Cases_on `bb''.bb_label = lbl` >>
      gvs[inline_frontier_instruction_def, inline_frontier_function_def, EVERY_MEM] >>
      metis_tac[]) >>
  metis_tac[rich_listTheory.EVERY_DROP]
QED

Theorem inline_frontier_one_site:
  inline_frontier_function caller /\ inline_frontier_function callee /\
  inline_one_site caller callee ist = SOME (out,ist') ==>
  inline_frontier_function out
Proof
  simp[inline_one_site_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >> strip_tac >> gvs[] >>
  irule inline_frontier_renumber >>
  metis_tac[inline_frontier_fix_phis, inline_frontier_call_site]
QED

Theorem inline_frontier_origin:
  !C n fn. inliner_fn_origin C n fn ==> inline_frontier_function fn
Proof
  ho_match_mp_tac inliner_fn_origin_ind >> rpt conj_tac >> rpt strip_tac
  >- (drule inline_frontier_input >>
      simp[inline_frontier_context_def, EVERY_MEM])
  >> metis_tac[inline_frontier_one_site]
QED

Theorem inline_frontier_annotated_origin:
  inline_annotated_origin C n fn cert ==> inline_frontier_function fn
Proof
  metis_tac[functionInlinerEnvelopesTheory.inline_annotated_origin_erasure,
            qualified_origin_erasure,
            inline_frontier_origin]
QED

(* Actual child snapshots save the parent's current state, not its entry. *)
Theorem inline_frontier_stack_child_entry:
  inline_frontier_stack ((p,a,proute,psnap)::rest) frame /\
  inline_original_child C fuel parent q call psnap.ils_state r child cr ==>
  inline_frontier_stack
    ((cp,child,route,
      <|ils_state := child.ia_entry; ils_saved := psnap.ils_state;
        ils_entry := child.ia_entry; ils_defined := {};
        ils_opaque := retpc_var child.ia_function;
        ils_protected := (psnap.ils_defined DIFF psnap.ils_opaque)
                          DIFF set call.inst_outputs;
        ils_parent_rename := proute.ir_rename|>)::
     (p,a,proute,psnap)::rest) frame
Proof
  strip_tac >>
  `child.ia_entry.vs_alloca_next = psnap.ils_state.vs_alloca_next` by
    (fs[functionInlinerActivationTheory.inline_original_child_def] >> metis_tac[inline_frontier_setup]) >>
  irule inline_frontier_stack_push >>
  gvs[inline_frontier_stack_def]
QED
