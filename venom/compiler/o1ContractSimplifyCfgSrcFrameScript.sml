(* Ghost boundary facts for SimplifyCFG source-frame transport. *)
Theory o1ContractSimplifyCfgSrcFrame
Ancestors
  o1PassContract ptrDiscipline simplifyCfgPhiSemantics simplifyCfgShape
  simplifyCfgDefs venomInst list contextCodegenRel codegenRel memLocDefs
  stateFrame venomState simplifyCfgBypassExec relation venomExecSemantics
  simplifyCfgMergeExec simplifyCfgFramePrefixes simplifyCfgFragments o1PassLift
  simplifyCfgBypassEntry simplifyCfgControl simplifyCfgControlExec venomInstProofs1
  simplifyCfgMergeSegment simplifyCfgMergePaths ptrSafeRun simplifyCfgMergeSemantics
  cfgTransform simplifyCfgPhiProps simplifyCfgBypassClosure simplifyCfgBypassShape
  simplifyCfgRoundSemantics simplifyCfgMergeClosure simplifyCfgBypassWrapper
  simplifyCfgStaticInterface simplifyCfgBypassPrecondition simplifyCfgSimTools
  simplifyCfgInvariant lowerDloadDefs unitMemInv
  simplifyCfgPhiBlockSemantics simplifyCfgGeneratedSubst simplifyCfgCleanup
  simplifyCfgBypassPrefix simplifyCfgBypassRuns simplifyCfgRestrictionSemantics
  simplifyCfgStruct venomWf opcodeClass simplifyCfgBypassSemantics o1ComposeSupport

Theorem scfg_phis_prov_no_phi:
  EVERY (\i. i.inst_opcode <> PHI) xs ==>
  phis_prov prev G xs = G
Proof
  Cases_on `xs` >> simp[phis_prov_def]
QED

Theorem scfg_phis_taint_no_phi:
  EVERY (\i. i.inst_opcode <> PHI) xs ==>
  phis_taint prev tn xs = tn.t_var
Proof
  Cases_on `xs` >> simp[phis_taint_def]
QED

Theorem scfg_entry_prov_no_phi:
  (!bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
        EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) ==>
  entry_prov fn s G = G
Proof
  strip_tac >> simp[entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  metis_tac[scfg_phis_prov_no_phi]
QED

Theorem scfg_entry_taint_no_phi:
  (!bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
        EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) ==>
  entry_taint_vars fn s tn = tn
Proof
  strip_tac >> simp[entry_taint_vars_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  gvs[] >> simp[scfg_phis_taint_no_phi]
QED

(* A canonical branch has no variable operands or memory observations. *)
Theorem scfg_jmp_label_safe:
  i.inst_opcode = JMP /\ i.inst_operands = [Label lbl] ==>
  access_ok lo G fn i s /\ taint_ok fn tn i s
Proof
  strip_tac >>
  simp[access_ok_def, taint_ok_def, op_taint_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       mem_write_ops_def, mem_read_ops_def]
QED

Definition scfg_data_agree_def:
  scfg_data_agree s t <=>
    execution_frame s = execution_frame t /\ s.vs_vars = t.vs_vars
End

Theorem scfg_data_agree_refl[simp]:
  scfg_data_agree s s
Proof
  simp[scfg_data_agree_def]
QED

Theorem scfg_data_agree_sym:
  scfg_data_agree s t ==> scfg_data_agree t s
Proof
  simp[scfg_data_agree_def] >> metis_tac[]
QED

Theorem scfg_data_agree_trans:
  scfg_data_agree s t /\ scfg_data_agree t u ==> scfg_data_agree s u
Proof
  simp[scfg_data_agree_def] >> metis_tac[]
QED

Theorem scfg_data_agree_reconstruct:
  scfg_data_agree s t <=>
  (s with <|vs_current_bb := t.vs_current_bb;
            vs_inst_idx := t.vs_inst_idx; vs_prev_bb := t.vs_prev_bb|>) = t
Proof
  simp[scfg_data_agree_def, execution_frame_def,
       venom_state_component_equality] >> metis_tac[]
QED

Theorem scfg_data_agree_lookup_var:
  scfg_data_agree s t ==> lookup_var v s = lookup_var v t
Proof
  simp[scfg_data_agree_def, lookup_var_def]
QED

Theorem scfg_data_agree_eval_operand:
  scfg_data_agree s t ==> eval_operand op s = eval_operand op t
Proof
  strip_tac >> Cases_on `op` >>
  simp[eval_operand_def, scfg_data_agree_lookup_var] >>
  gvs[scfg_data_agree_def, execution_frame_def,
      venom_state_component_equality]
QED

Theorem scfg_data_agree_step_prov:
  scfg_data_agree s t ==> step_prov PG G inst s = step_prov PG G inst t
Proof
  strip_tac >>
  `s.vs_allocas = t.vs_allocas /\ s.vs_fmp = t.vs_fmp` by
    gvs[scfg_data_agree_def, execution_frame_def,
        venom_state_component_equality] >>
  `s.vs_vars = t.vs_vars` by fs[scfg_data_agree_def] >>
  simp[step_prov_def, out_prov_def, lookup_var_def]
QED

Theorem scfg_data_agree_written_taint:
  scfg_data_agree s t ==> written_taint tn inst s = written_taint tn inst t
Proof
  strip_tac >>
  `(!op. eval_operand op s = eval_operand op t)` by
    metis_tac[scfg_data_agree_eval_operand] >>
  simp[written_taint_def]
QED

Theorem scfg_data_agree_out_taint:
  scfg_data_agree s t ==> out_taint tn inst s = out_taint tn inst t
Proof
  strip_tac >>
  `(!op. eval_operand op s = eval_operand op t)` by
    metis_tac[scfg_data_agree_eval_operand] >>
  simp[out_taint_def]
QED

Theorem scfg_data_agree_store_taint:
  scfg_data_agree s t ==>
  store_taint opc tn inst s X = store_taint opc tn inst t X
Proof
  strip_tac >>
  `(!op. eval_operand op s = eval_operand op t)` by
    metis_tac[scfg_data_agree_eval_operand] >>
  simp[store_taint_def]
QED

Theorem scfg_data_agree_imm_taint:
  scfg_data_agree s t ==> imm_taint tn inst s = imm_taint tn inst t
Proof
  strip_tac >>
  `(!op. eval_operand op s = eval_operand op t)` by
    metis_tac[scfg_data_agree_eval_operand] >>
  simp[imm_taint_def]
QED

Theorem scfg_data_agree_eval_operands:
  scfg_data_agree s t ==> eval_operands ops s = eval_operands ops t
Proof
  strip_tac >>
  `(!op. eval_operand op s = eval_operand op t)` by
    metis_tac[scfg_data_agree_eval_operand] >>
  Induct_on `ops` >> simp[eval_operands_def]
QED

Theorem scfg_data_agree_write_ranges:
  scfg_data_agree s t ==>
  source_memory_write_ranges inst s = source_memory_write_ranges inst t
Proof
  strip_tac >>
  `(!op. eval_operand op s = eval_operand op t)` by
    metis_tac[scfg_data_agree_eval_operand] >>
  `(!ops. eval_operands ops s = eval_operands ops t)` by
    metis_tac[scfg_data_agree_eval_operands] >>
  `s.vs_call_entry_fmp = t.vs_call_entry_fmp` by
    gvs[scfg_data_agree_def, execution_frame_def,
        venom_state_component_equality] >>
  `(!dst value (n:num). fixed_source_write_range s dst value n =
                   fixed_source_write_range t dst value n)` by
    simp[fixed_source_write_range_def] >>
  `(!dst src n. sized_source_write_range s dst src n =
                 sized_source_write_range t dst src n)` by
    simp[sized_source_write_range_def] >>
  Cases_on `inst.inst_opcode` >> simp[source_memory_write_ranges_def]
QED

Theorem scfg_data_agree_step_writes:
  scfg_data_agree s t /\ scfg_data_agree s' t' ==>
  step_writes inst s s' = step_writes inst t t'
Proof
  strip_tac >>
  `s'.vs_returndata = t'.vs_returndata` by
    gvs[scfg_data_agree_def, execution_frame_def,
        venom_state_component_equality] >>
  `source_memory_write_ranges inst s = source_memory_write_ranges inst t` by
    metis_tac[scfg_data_agree_write_ranges] >>
  simp[step_writes_def]
QED

Theorem scfg_data_agree_new_site_bytes:
  scfg_data_agree s t /\ scfg_data_agree s' t' ==>
  new_site_bytes s s' = new_site_bytes t t'
Proof
  simp[scfg_data_agree_def, execution_frame_def,
       venom_state_component_equality] >>
  strip_tac >> simp[new_site_bytes_def]
QED

Theorem scfg_data_agree_mem_taint:
  scfg_data_agree s t /\ scfg_data_agree s' t' ==>
  mem_taint tn inst s s' = mem_taint tn inst t t'
Proof
  strip_tac >>
  simp[mem_taint_def] >>
  metis_tac[scfg_data_agree_new_site_bytes,
            scfg_data_agree_step_writes, scfg_data_agree_written_taint]
QED

Theorem scfg_data_agree_step_taint:
  scfg_data_agree s t /\ scfg_data_agree s' t' ==>
  step_taint inst s s' tn = step_taint inst t t' tn
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx /\
   s.vs_requests = t.vs_requests /\ s'.vs_requests = t'.vs_requests /\
   s.vs_outcomes = t.vs_outcomes /\ s'.vs_outcomes = t'.vs_outcomes` by
    gvs[scfg_data_agree_def, execution_frame_def,
        venom_state_component_equality] >>
  simp[step_taint_def, scfg_data_agree_mem_taint,
       scfg_data_agree_out_taint, scfg_data_agree_store_taint,
       scfg_data_agree_imm_taint] >>
  metis_tac[scfg_data_agree_out_taint, scfg_data_agree_store_taint]
QED

Definition scfg_jmp_edge_def:
  scfg_jmp_edge fn s t <=>
    ?i l. active_inst fn i s /\ i.inst_opcode = JMP /\
          i.inst_operands = [Label l] /\ ~(jump_to l s).vs_halted /\
          enters_block fn (jump_to l s) t
End

Definition scfg_jmp_prefix_def:
  scfg_jmp_prefix fn = RTC (scfg_jmp_edge fn)
End

Theorem scfg_frame_reachable_reindex:
  frame_reachable vs C stk PG G tn fn i s ==>
  !j. active_inst fn j s ==> frame_reachable vs C stk PG G tn fn j s
Proof
  simp[Once frame_reachable_cases] >> rpt strip_tac >>
  metis_tac[frame_reachable_rules]
QED

Theorem scfg_enters_no_phi_agree:
  (!l bb. lookup_block l fn.fn_blocks = SOME bb ==>
          EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) /\
  enters_block fn s t ==> scfg_data_agree s t
Proof
  simp[enters_block_def] >> rpt strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions` by metis_tac[] >>
  Cases_on `bb.bb_instructions` >>
  gvs[eval_phis_def, phi_prefix_length_def] >>
  simp[scfg_data_agree_def]
QED

Theorem scfg_jmp_edge_agree:
  (!l bb. lookup_block l fn.fn_blocks = SOME bb ==>
          EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) /\
  scfg_jmp_edge fn s t ==> scfg_data_agree s t
Proof
  simp[scfg_jmp_edge_def] >> rpt strip_tac >>
  `scfg_data_agree (jump_to l s) t` by
    metis_tac[scfg_enters_no_phi_agree] >>
  fs[scfg_data_agree_def, jump_to_def]
QED

Theorem scfg_jmp_edge_reachable:
  (!l bb. lookup_block l fn.fn_blocks = SOME bb ==>
          EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) /\
  frame_reachable vs C stk PG G tn fn i s /\
  scfg_jmp_edge fn s t /\ active_inst fn j t ==>
  frame_reachable vs C stk PG G tn fn j t
Proof
  simp[scfg_jmp_edge_def] >> rpt strip_tac >>
  `entry_prov fn (jump_to l s) G = G` by
    (irule scfg_entry_prov_no_phi >> metis_tac[]) >>
  `entry_taint_vars fn (jump_to l s) tn = tn` by
    (irule scfg_entry_taint_no_phi >> metis_tac[]) >>
  `frame_reachable vs C stk PG G tn fn i' s` by
    metis_tac[scfg_frame_reachable_reindex] >>
  `step_inst 0 C i' s = OK (jump_to l s)` by
    metis_tac[scfg_step_jmp] >>
  `is_terminator i'.inst_opcode` by simp[is_terminator_def] >>
  `~(jump_to l s).vs_halted` by simp[jump_to_def] >>
  drule_all frame_reachable_block >> simp[]
QED

Theorem scfg_jmp_prefix_agree:
  (!l bb. lookup_block l fn.fn_blocks = SOME bb ==>
          EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) ==>
  !s t. scfg_jmp_prefix fn s t ==> scfg_data_agree s t
Proof
  strip_tac >> simp[scfg_jmp_prefix_def] >>
  ho_match_mp_tac RTC_INDUCT >>
  metis_tac[scfg_jmp_edge_agree, scfg_data_agree_refl,
            scfg_data_agree_trans]
QED

Theorem scfg_jmp_prefix_reachable:
  (!l bb. lookup_block l fn.fn_blocks = SOME bb ==>
          EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) ==>
  !s t. scfg_jmp_prefix fn s t ==>
  !i j. frame_reachable vs C stk PG G tn fn i s /\ active_inst fn j t ==>
  frame_reachable vs C stk PG G tn fn j t
Proof
  strip_tac >> simp[scfg_jmp_prefix_def] >>
  ho_match_mp_tac RTC_STRONG_INDUCT_RIGHT1 >> rpt strip_tac
  >- metis_tac[scfg_frame_reachable_reindex] >>
  qpat_assum `scfg_jmp_edge fn _ _`
    (strip_assume_tac o REWRITE_RULE[scfg_jmp_edge_def]) >>
  rename1 `active_inst fn k t` >>
  `frame_reachable vs C stk PG G tn fn k t` by metis_tac[] >>
  irule scfg_jmp_edge_reachable >> metis_tac[]
QED

Definition scfg_saved_frame_def:
  scfg_saved_frame R f g <=>
    R f.cf_fn f.cf_inst f.cf_state g.cf_fn g.cf_inst g.cf_state /\
    scfg_data_agree f.cf_state g.cf_state /\
    f.cf_inst.inst_outputs = g.cf_inst.inst_outputs /\
    f.cf_params = g.cf_params /\ f.cf_prov = g.cf_prov /\ f.cf_tvar = g.cf_tvar
End

Theorem scfg_data_agree_merge:
  scfg_data_agree s t /\ scfg_data_agree u v ==>
  scfg_data_agree (merge_callee_state s u) (merge_callee_state t v)
Proof
  simp[scfg_data_agree_def, execution_frame_def,
       venom_state_component_equality, merge_callee_state_def]
QED

Theorem scfg_data_agree_adopt:
  scfg_data_agree s t ==>
  scfg_data_agree (adopt_return_fmp ret s) (adopt_return_fmp ret t)
Proof
  Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, scfg_data_agree_def, execution_frame_def,
       venom_state_component_equality]
QED

Theorem scfg_data_agree_bind_fold[local]:
  !s t. scfg_data_agree s t ==>
  scfg_data_agree
    (FOLDL (\st (out,value). update_var out value st) s pairs)
    (FOLDL (\st (out,value). update_var out value st) t pairs)
Proof
  Induct_on `pairs` >> simp[] >> Cases_on `h` >> rpt strip_tac >>
  first_x_assum irule >>
  gvs[scfg_data_agree_def, execution_frame_def, update_var_def,
      venom_state_component_equality]
QED

Theorem scfg_data_agree_bind:
  scfg_data_agree s t /\ bind_outputs outs vals s = SOME s' ==>
  ?t'. bind_outputs outs vals t = SOME t' /\ scfg_data_agree s' t'
Proof
  simp[bind_outputs_def] >> strip_tac >> gvs[] >>
  irule scfg_data_agree_bind_fold >> simp[]
QED

Theorem scfg_data_agree_index:
  scfg_data_agree s t ==>
  scfg_data_agree (s with vs_inst_idx := n) (t with vs_inst_idx := m)
Proof
  simp[scfg_data_agree_def]
QED

Theorem scfg_saved_return:
  scfg_saved_frame R f g /\ scfg_data_agree u v /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state u)) = SOME s' ==>
  ?t'. bind_outputs g.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state g.cf_state v)) = SOME t' /\
    scfg_data_agree (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
                    (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx)
Proof
  simp[scfg_saved_frame_def] >> rpt strip_tac >>
  `scfg_data_agree (adopt_return_fmp ret (merge_callee_state f.cf_state u))
                   (adopt_return_fmp ret (merge_callee_state g.cf_state v))` by
    metis_tac[scfg_data_agree_merge, scfg_data_agree_adopt] >>
  drule_all scfg_data_agree_bind >> strip_tac >>
  qexists_tac `t'` >> simp[scfg_data_agree_index] >> metis_tac[]
QED

Theorem scfg_saved_frame_ghosts:
  scfg_saved_frame R f g ==>
  f.cf_inst.inst_outputs = g.cf_inst.inst_outputs /\
  f.cf_params = g.cf_params /\ f.cf_prov = g.cf_prov /\ f.cf_tvar = g.cf_tvar
Proof
  simp[scfg_saved_frame_def]
QED

Theorem scfg_jump_enter_agree:
  (!l bb. lookup_block l fn.fn_blocks = SOME bb ==>
          EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) /\
  enters_block fn (jump_to lbl s) u ==> scfg_data_agree s u
Proof
  strip_tac >>
  `scfg_data_agree (jump_to lbl s) u` by
    metis_tac[scfg_enters_no_phi_agree] >>
  fs[scfg_data_agree_def, jump_to_def]
QED
Theorem scfg_transfer_ghosts:
  (!l bb. lookup_block l fn.fn_blocks = SOME bb ==>
          EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) /\
  frame_reachable vs C stk PG G tn fn i s /\
  is_terminator i.inst_opcode /\
  step_inst k C i s = OK (jump_to lbl s) /\
  ~(jump_to lbl s).vs_halted /\
  enters_block fn (jump_to lbl s) u /\ active_inst fn j u ==>
  frame_reachable vs C stk PG G tn fn j u
Proof
  rpt strip_tac >>
  `entry_prov fn (jump_to lbl s) G = G` by
    (irule scfg_entry_prov_no_phi >> metis_tac[]) >>
  `entry_taint_vars fn (jump_to lbl s) tn = tn` by
    (irule scfg_entry_taint_no_phi >> metis_tac[]) >>
  `active_inst fn i s` by fs[Once frame_reachable_cases] >>
  metis_tac[frame_reachable_block]
QED


Theorem scfg_chain_transfer_ghosts:
  scfg_chain_hyp fn a b /\
  (!l bb. lookup_block l fn.fn_blocks = SOME bb ==>
          EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) /\
  fn_entry_state fn s0 /\
  frame_reach C fn s0 (LAST a.bb_instructions) s /\
  frame_reachable vs C stk PG G tn fn (LAST a.bb_instructions) s /\
  ~(jump_to b.bb_label s).vs_halted /\
  enters_block fn (jump_to b.bb_label s) u /\ active_inst fn j u ==>
  frame_reachable vs C stk PG G tn fn j u
Proof
  rpt strip_tac >> irule scfg_transfer_ghosts >>
  `is_terminator (LAST a.bb_instructions).inst_opcode` by
    metis_tac[scfg_chain_transfer_shape, is_terminator_def] >>
  metis_tac[scfg_chain_transfer_step]
QED

Theorem scfg_bypass_singleton_ghosts:
  scfg_bypass_hyp fn a b fn' /\
  (!l bb. lookup_block l fn.fn_blocks = SOME bb ==>
          EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) /\
  fn_entry_state fn s0 /\
  frame_reach C fn s0 (LAST b.bb_instructions) s /\
  frame_reachable vs C stk PG G tn fn (LAST b.bb_instructions) s /\
  ~(jump_to (HD (bb_succs b)) s).vs_halted /\
  enters_block fn (jump_to (HD (bb_succs b)) s) u /\ active_inst fn j u ==>
  frame_reachable vs C stk PG G tn fn j u
Proof
  rpt strip_tac >> irule scfg_transfer_ghosts >>
  `is_terminator (LAST b.bb_instructions).inst_opcode` by
    metis_tac[scfg_bypass_singleton_shape, is_terminator_def] >>
  metis_tac[scfg_bypass_singleton_step]
QED

Theorem scfg_invoke_return_step:
  !inv nm ops C callee args s cs fuel ret s_end u.
  inv.inst_opcode = INVOKE /\ decode_invoke inv = SOME (nm, ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  run_blocks fuel C callee cs = IntRet ret s_end /\
  bind_outputs inv.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s s_end)) = SOME u ==>
  step_inst fuel C inv s = OK u
Proof
  rpt strip_tac >> simp[Once step_inst_def]
QED

Theorem scfg_frame_reach_intret_complete:
  wf_function fn /\ frame_reach C fn cs i s /\
  step_inst n C i s = IntRet ret s_end ==>
  ?m. run_blocks m C fn cs = IntRet ret s_end
Proof
  strip_tac >> drule_all scfg_frame_reach_decompose >> strip_tac >>
  rename1 `scfg_bprefix C fn cs se` >>
  `exec_block n C bb s = IntRet ret s_end` by
    simp[Once exec_block_def] >>
  `?m. exec_block m C bb a = IntRet ret s_end` by
    metis_tac[scfg_iprefix_continue, exec_result_distinct] >>
  `run_blocks (SUC m) C fn se = IntRet ret s_end` by
    (gvs[] >> simp[run_blocks_unfold, run_block_def]) >>
  metis_tac[scfg_bprefix_continue, exec_result_distinct]
QED

Theorem scfg_rooted_invoke_return_step:
  !callee inv nm ops C args s cs i t n ret s_end u.
  wf_function callee /\ inv.inst_opcode = INVOKE /\
  decode_invoke inv = SOME (nm, ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  frame_reach C callee cs i t /\ step_inst n C i t = IntRet ret s_end /\
  bind_outputs inv.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s s_end)) = SOME u ==>
  ?fuel. step_inst fuel C inv s = OK u
Proof
  rpt strip_tac >> drule_all scfg_frame_reach_intret_complete >> strip_tac >>
  metis_tac[scfg_invoke_return_step]
QED

Inductive scfg_root_history:
[~base:]
  (!C name fn r.
    lookup_function name C.ctx_functions = SOME fn /\ fn_entry_state fn r ==>
    scfg_root_history C [] [] fn r)
[~push:]
  (!C stk rs caller cr inv s nm ops callee args cs PG G tv.
    scfg_root_history C stk rs caller cr /\
    frame_reach C caller cr inv s /\ inv.inst_opcode = INVOKE /\
    decode_invoke inv = SOME (nm, ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
    scfg_root_history C
      (<| cf_fn := caller; cf_inst := inv; cf_state := s;
          cf_params := PG; cf_prov := G; cf_tvar := tv |> :: stk)
      (cr :: rs) callee cs)
End

Definition scfg_rooted_def:
  scfg_rooted C stk fn inst s <=>
    ?rs r. scfg_root_history C stk rs fn r /\ frame_reach C fn r inst s
End

Theorem scfg_root_history_entry:
  scfg_root_history C stk rs fn r ==> fn_entry_state fn r
Proof
  Induct_on `scfg_root_history` >> metis_tac[setup_callee_fn_entry_state]
QED

Theorem scfg_root_history_lookup:
  scfg_root_history C stk rs fn r ==>
  ?name. lookup_function name C.ctx_functions = SOME fn
Proof
  Induct_on `scfg_root_history` >> metis_tac[]
QED

Theorem scfg_root_history_nil:
  scfg_root_history C [] rs fn r <=>
  rs = [] /\ fn_entry_state fn r /\
  ?name. lookup_function name C.ctx_functions = SOME fn
Proof
  simp[Once scfg_root_history_cases] >> metis_tac[]
QED

Theorem scfg_root_history_cons:
  scfg_root_history C (f::stk) rs fn r ==>
  ?cr rest nm ops args.
    rs = cr::rest /\ scfg_root_history C stk rest f.cf_fn cr /\
    frame_reach C f.cf_fn cr f.cf_inst f.cf_state /\
    f.cf_inst.inst_opcode = INVOKE /\
    decode_invoke f.cf_inst = SOME (nm, ops) /\
    lookup_function nm C.ctx_functions = SOME fn /\
    eval_operands ops f.cf_state = SOME args /\
    setup_callee fn args f.cf_state = SOME r
Proof
  simp[Once scfg_root_history_cases] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem scfg_rooted_intro:
  scfg_root_history C stk rs fn r /\ frame_reach C fn r inst s ==>
  scfg_rooted C stk fn inst s
Proof
  metis_tac[scfg_rooted_def]
QED

Theorem scfg_rooted_elim:
  scfg_rooted C stk fn inst s ==>
  ?rs r. scfg_root_history C stk rs fn r /\ frame_reach C fn r inst s /\
         fn_entry_state fn r /\
         ?name. lookup_function name C.ctx_functions = SOME fn
Proof
  metis_tac[scfg_rooted_def, scfg_root_history_entry, scfg_root_history_lookup]
QED

Theorem scfg_rooted_entry:
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s1 /\
  active_inst fn inst s1 ==> scfg_rooted C [] fn inst s1
Proof
  rpt strip_tac >> irule scfg_rooted_intro >>
  irule_at Any scfg_root_history_base >>
  metis_tac[context_fn_entry_state, frame_reach_start]
QED

Theorem scfg_rooted_next:
  scfg_rooted C stk fn inst s /\ ~is_terminator inst.inst_opcode /\
  step_inst fuel C inst s = OK s' /\
  active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
  scfg_rooted C stk fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> gvs[scfg_rooted_def] >>
  goal_assum (drule_at Any) >> irule frame_reach_next >> metis_tac[]
QED

Theorem scfg_rooted_block:
  scfg_rooted C stk fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel C inst s = OK s' /\ ~s'.vs_halted /\
  enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
  scfg_rooted C stk fn inst' s1
Proof
  strip_tac >> gvs[scfg_rooted_def] >>
  goal_assum (drule_at Any) >> irule frame_reach_block >> metis_tac[]
QED

Theorem scfg_rooted_call:
  !C stk caller inv s nm ops callee args cs s1 inst PG G tv.
  scfg_rooted C stk caller inv s /\ inv.inst_opcode = INVOKE /\
  decode_invoke inv = SOME (nm, ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 ==>
  scfg_rooted C
    (<|cf_fn := caller; cf_inst := inv; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tv|> :: stk) callee inst s1
Proof
  rpt strip_tac >> gvs[scfg_rooted_def] >>
  irule_at Any scfg_root_history_push >>
  metis_tac[frame_reach_start]
QED

Theorem scfg_rooted_ret:
  (!nm fn. lookup_function nm C.ctx_functions = SOME fn ==> wf_function fn) /\
  scfg_rooted C (f::stk) fn rinst s /\
  step_inst fuel C rinst s = IntRet ret s_end /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) = SOME s' /\
  active_inst f.cf_fn inst'
    (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  scfg_rooted C stk f.cf_fn inst'
    (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  strip_tac >> gvs[scfg_rooted_def] >>
  drule scfg_root_history_cons >> strip_tac >>
  `wf_function fn` by metis_tac[] >>
  drule_all scfg_rooted_invoke_return_step >> strip_tac >>
  goal_assum (drule_at Any) >> irule frame_reach_next >>
  metis_tac[is_terminator_def]
QED

Theorem scfg_frame_reachable_rooted:
  !vs C stk PG G tn fn inst s.
  frame_reachable vs C stk PG G tn fn inst s ==>
  (!nm f. lookup_function nm C.ctx_functions = SOME f ==> wf_function f) /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted ==> scfg_rooted C stk fn inst s
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >> rpt strip_tac
  >- (irule scfg_rooted_entry >> metis_tac[])
  >- (irule scfg_rooted_next >> metis_tac[])
  >- (irule scfg_rooted_block >> metis_tac[])
  >- (irule scfg_rooted_call >> metis_tac[])
  >> irule scfg_rooted_ret >> metis_tac[]
QED

Theorem scfg_frame_reachable_entry_root:
  (!nm f. lookup_function nm C.ctx_functions = SOME f ==> wf_function f) /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  frame_reachable vs C stk PG G tn fn inst s ==>
  ?r. fn_entry_state fn r /\ frame_reach C fn r inst s
Proof
  metis_tac[scfg_frame_reachable_rooted, scfg_rooted_elim]
QED

Definition scfg_saved_call_def:
  scfg_saved_call R f g <=>
    scfg_saved_frame R f g /\ f.cf_inst = g.cf_inst
End

Definition scfg_saved_stack_def:
  scfg_saved_stack R fs gs <=> LIST_REL (scfg_saved_call R) fs gs
End

Theorem scfg_bypass_return_coordinates:
  scfg_bypass_aligned a b saved saved' /\ scfg_data_agree u v ==>
  scfg_bypass_aligned a b
    (u with <|vs_current_bb := saved.vs_current_bb;
              vs_prev_bb := saved.vs_prev_bb;
              vs_inst_idx := SUC saved.vs_inst_idx|>)
    (v with <|vs_current_bb := saved'.vs_current_bb;
              vs_prev_bb := saved'.vs_prev_bb;
              vs_inst_idx := SUC saved'.vs_inst_idx|>)
Proof
  simp[scfg_bypass_aligned_def, scfg_ctrl_def] >> strip_tac >>
  gvs[scfg_data_agree_reconstruct, venom_state_component_equality]
QED

Theorem scfg_return_control:
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state saved u)) =
    SOME s ==>
  s.vs_current_bb = saved.vs_current_bb /\
  s.vs_prev_bb = saved.vs_prev_bb /\ s.vs_inst_idx = saved.vs_inst_idx
Proof
  strip_tac >>
  qspec_then `\st. (st.vs_current_bb, st.vs_prev_bb, st.vs_inst_idx)` mp_tac
    bind_outputs_preserves >> simp[update_var_def] >>
  disch_then drule >> Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem scfg_bypass_saved_return:
  scfg_saved_call R f g /\ scfg_bypass_aligned a b f.cf_state g.cf_state /\
  scfg_data_agree u v /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state u)) = SOME s' ==>
  ?t'. bind_outputs g.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state g.cf_state v)) = SOME t' /\
    scfg_data_agree (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
                    (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx) /\
    scfg_bypass_aligned a b
      (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx)
Proof
  simp[scfg_saved_call_def] >> rpt strip_tac >>
  drule_all scfg_saved_return >> strip_tac >>
  qexists_tac `t'` >> simp[] >>
  `s'.vs_current_bb = f.cf_state.vs_current_bb /\
   s'.vs_prev_bb = f.cf_state.vs_prev_bb /\
   t'.vs_current_bb = g.cf_state.vs_current_bb /\
   t'.vs_prev_bb = g.cf_state.vs_prev_bb` by
    metis_tac[scfg_return_control] >>
  `scfg_data_agree s' t'` by
    gvs[scfg_data_agree_def, execution_frame_def] >>
  drule_all scfg_bypass_return_coordinates >>
  simp[scfg_bypass_aligned_def, scfg_ctrl_def, venom_state_component_equality]
QED

Theorem scfg_bypass_saved_return_back:
  scfg_saved_call R f g /\ scfg_bypass_aligned a b f.cf_state g.cf_state /\
  scfg_data_agree u v /\
  bind_outputs g.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state g.cf_state v)) = SOME t' ==>
  ?s'. bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state u)) = SOME s' /\
    scfg_data_agree (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
                    (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx) /\
    scfg_bypass_aligned a b
      (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx)
Proof
  strip_tac >>
  `scfg_data_agree g.cf_state f.cf_state /\
   g.cf_inst.inst_outputs = f.cf_inst.inst_outputs` by
    metis_tac[scfg_saved_call_def, scfg_saved_frame_def, scfg_data_agree_sym] >>
  `scfg_data_agree v u` by metis_tac[scfg_data_agree_sym] >>
  `scfg_data_agree (adopt_return_fmp ret (merge_callee_state g.cf_state v))
                   (adopt_return_fmp ret (merge_callee_state f.cf_state u))` by
    metis_tac[scfg_data_agree_merge, scfg_data_agree_adopt] >>
  drule_all scfg_data_agree_bind >> strip_tac >>
  `?s'. bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state u)) = SOME s'` by
    metis_tac[] >>
  pop_assum strip_assume_tac >>
  drule_all scfg_bypass_saved_return >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem scfg_chain_return_coordinates:
  scfg_chain_segment a b saved saved' /\ scfg_data_agree u v /\
  u.vs_current_bb = saved.vs_current_bb /\
  v.vs_current_bb = saved'.vs_current_bb ==>
  scfg_chain_segment a b (u with vs_inst_idx := SUC saved.vs_inst_idx)
    (v with vs_inst_idx := SUC saved'.vs_inst_idx) \/
  scfg_chain_splice a (u with vs_inst_idx := SUC saved.vs_inst_idx)
    (v with vs_inst_idx := SUC saved'.vs_inst_idx)
Proof
  strip_tac >>
  `scfg_payload (u with vs_inst_idx := SUC saved.vs_inst_idx)
                (v with vs_inst_idx := SUC saved'.vs_inst_idx)` by
    (simp[scfg_payload_def, scfg_ctrl_def] >>
     gvs[scfg_data_agree_reconstruct, venom_state_component_equality]) >>
  gvs[scfg_chain_segment_def, scfg_chain_splice_def] >>
  `SUC saved'.vs_inst_idx < LENGTH (FRONT a.bb_instructions) \/
   SUC saved'.vs_inst_idx = LENGTH (FRONT a.bb_instructions)` by
    (qpat_x_assum `_ < LENGTH _` mp_tac >> decide_tac) >> simp[]
QED

Theorem scfg_chain_saved_return:
  scfg_saved_call R f g /\ scfg_chain_segment a b f.cf_state g.cf_state /\
  scfg_data_agree u v /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state u)) = SOME s' ==>
  ?t'. bind_outputs g.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state g.cf_state v)) = SOME t' /\
    scfg_data_agree (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
                    (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx) /\
    (scfg_chain_segment a b
      (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx) \/
     scfg_chain_splice a
      (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx))
Proof
  simp[scfg_saved_call_def] >> rpt strip_tac >>
  drule_all scfg_saved_return >> strip_tac >>
  qexists_tac `t'` >> simp[] >>
  `s'.vs_current_bb = f.cf_state.vs_current_bb /\
   t'.vs_current_bb = g.cf_state.vs_current_bb` by
    metis_tac[scfg_return_control] >>
  `scfg_data_agree s' t'` by
    gvs[scfg_data_agree_def, execution_frame_def] >>
  irule scfg_chain_return_coordinates >> metis_tac[]
QED

Theorem scfg_chain_splice_ghosts:
  scfg_chain_hyp fn a b /\
  (!l bb. lookup_block l fn.fn_blocks = SOME bb ==>
          EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) /\
  (!nm f. lookup_function nm C.ctx_functions = SOME f ==> wf_function f) /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  frame_reachable vs C stk PG G tn fn (LAST a.bb_instructions) s /\
  scfg_chain_splice a s t /\ ~s.vs_halted /\ scfg_data_agree s t /\
  active_inst (scfg_chain fn a b) j t /\ j.inst_opcode <> PHI ==>
  frame_reachable vs C stk PG G tn fn j (jump_to b.bb_label s) /\
  scfg_chain_segment a b (jump_to b.bb_label s) t /\
  scfg_data_agree (jump_to b.bb_label s) t
Proof
  strip_tac >>
  `?r. fn_entry_state fn r /\
       frame_reach C fn r (LAST a.bb_instructions) s` by
    metis_tac[scfg_frame_reachable_entry_root] >>
  drule_all scfg_chain_splice_transfer >>
  disch_then (qspec_then `0` strip_assume_tac) >>
  `active_inst fn j (jump_to b.bb_label s)` by
    (fs[active_inst_def] >>
     `ALL_DISTINCT (MAP (\bb. bb.bb_label) (scfg_chain fn a b).fn_blocks)` by
       metis_tac[scfg_chain_labels_distinct, fn_labels_def] >>
     `lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bb` by
       metis_tac[venomExecProofsTheory.MEM_lookup_block] >>
     `lookup_block (jump_to b.bb_label s).vs_current_bb fn.fn_blocks = SOME b` by
       gvs[scfg_chain_hyp_def, jump_to_def] >>
     `get_instruction bb t.vs_inst_idx = SOME j` by simp[get_instruction_def] >>
     drule_all scfg_chain_segment_instruction_inverse >> strip_tac >>
     qexists_tac `b` >>
     `MEM b fn.fn_blocks /\ b.bb_label = (jump_to b.bb_label s).vs_current_bb` by
       metis_tac[lookup_block_member_label] >>
     gvs[get_instruction_def]) >>
  conj_tac
  >- (`~(jump_to b.bb_label s).vs_halted` by simp[jump_to_def] >>
      drule_all scfg_chain_transfer_ghosts >> simp[]) >>
  simp[scfg_data_agree_def, execution_frame_def, jump_to_def] >>
  gvs[scfg_data_agree_def]
QED

Theorem scfg_chain_saved_return_back:
  scfg_saved_call R f g /\ scfg_chain_segment a b f.cf_state g.cf_state /\
  scfg_data_agree u v /\
  bind_outputs g.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state g.cf_state v)) = SOME t' ==>
  ?s'. bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state u)) = SOME s' /\
    scfg_data_agree (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
                    (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx) /\
    (scfg_chain_segment a b
       (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
       (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx) \/
     scfg_chain_splice a
       (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
       (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx))
Proof
  strip_tac >>
  `scfg_data_agree g.cf_state f.cf_state /\
   g.cf_inst.inst_outputs = f.cf_inst.inst_outputs` by
    metis_tac[scfg_saved_call_def, scfg_saved_frame_def, scfg_data_agree_sym] >>
  `scfg_data_agree v u` by metis_tac[scfg_data_agree_sym] >>
  `scfg_data_agree (adopt_return_fmp ret (merge_callee_state g.cf_state v))
                   (adopt_return_fmp ret (merge_callee_state f.cf_state u))` by
    metis_tac[scfg_data_agree_merge, scfg_data_agree_adopt] >>
  drule_all scfg_data_agree_bind >> strip_tac >>
  `?s'. bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state u)) = SOME s'` by
    metis_tac[] >>
  pop_assum strip_assume_tac >>
  drule_all scfg_chain_saved_return >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem scfg_data_agree_payload:
  scfg_data_agree s t <=> scfg_payload s t
Proof
  simp[scfg_data_agree_reconstruct, scfg_payload_def, scfg_ctrl_def,
       EQ_SYM_EQ]
QED

Theorem scfg_data_agree_intret:
  scfg_data_agree s t /\ step_inst k C' i t = IntRet ret v ==>
  ?u. step_inst k C i s = IntRet ret u /\ scfg_data_agree u v
Proof
  strip_tac >>
  `i.inst_opcode <> INVOKE` by metis_tac[step_inst_intret_not_invoke] >>
  `scfg_payload t s` by
    metis_tac[scfg_data_agree_sym, scfg_data_agree_payload] >>
  drule scfg_payload_step >>
  disch_then (qspecl_then [`k`, `i`, `C'`] mp_tac) >>
  simp[] >>
  Cases_on `step_inst k C' i s` >> simp[scfg_result_def] >>
  strip_tac >>
  gvs[step_inst_non_invoke, scfg_data_agree_payload] >>
  metis_tac[scfg_data_agree_sym, scfg_data_agree_payload]
QED

Theorem scfg_chain_frame_return_back:
  scfg_saved_call R f g /\ scfg_chain_segment a b f.cf_state g.cf_state /\
  frame_reachable vs C (f::stk) PG G tn fn ri s /\ active_inst fn ri s /\
  scfg_data_agree s t /\ step_inst k C' ri t = IntRet ret v /\
  bind_outputs g.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state g.cf_state v)) = SOME t' /\
  (!u s'. step_inst k C ri s = IntRet ret u /\
    bind_outputs f.cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state f.cf_state u)) = SOME s' ==>
    active_inst f.cf_fn j (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)) ==>
  ?q. frame_reachable vs C stk g.cf_params
       (DRESTRICT g.cf_prov (COMPL (set g.cf_inst.inst_outputs)))
       (tn with t_var := DRESTRICT g.cf_tvar (COMPL (set g.cf_inst.inst_outputs)))
       f.cf_fn j q /\
    scfg_data_agree q (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx) /\
    (scfg_chain_segment a b q (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx) \/
     scfg_chain_splice a q (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx))
Proof
  strip_tac >>
  drule_all scfg_data_agree_intret >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  drule_all scfg_chain_saved_return_back >> strip_tac >>
  qexists_tac `s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx` >>
  simp[] >>
  `f.cf_inst.inst_outputs = g.cf_inst.inst_outputs /\
   f.cf_params = g.cf_params /\ f.cf_prov = g.cf_prov /\ f.cf_tvar = g.cf_tvar` by
    metis_tac[scfg_saved_frame_ghosts, scfg_saved_call_def] >>
  `active_inst f.cf_fn j (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)` by
    metis_tac[] >>
  `frame_reachable vs C stk f.cf_params
       (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
       (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
       f.cf_fn j (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)` by
    (irule frame_reachable_ret >> metis_tac[]) >>
  gvs[]
QED

Theorem scfg_chain_active_back:
  scfg_chain_hyp fn a b /\ scfg_chain_segment a b s t /\
  active_inst (scfg_chain fn a b) i t /\ i.inst_opcode <> PHI ==>
  active_inst fn i s
Proof
  strip_tac >>
  `?bt. lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
        get_instruction bt t.vs_inst_idx = SOME i` by
    (fs[active_inst_def, get_instruction_def] >>
     metis_tac[venomExecProofsTheory.MEM_lookup_block,
               scfg_chain_labels_distinct, fn_labels_def]) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    (fs[scfg_chain_segment_def]
     >- metis_tac[scfg_chain_hyp_def]
     >- metis_tac[scfg_chain_hyp_def] >>
     drule scfg_chain_lookup_eq >>
     disch_then (qspec_then `s.vs_current_bb` mp_tac) >>
     Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[]) >>
  drule_all scfg_chain_segment_instruction_inverse >> strip_tac >>
  simp[active_inst_def] >> qexists_tac `bb` >>
  drule lookup_block_member_label >> strip_tac >>
  gvs[get_instruction_def]
QED

Theorem scfg_chain_active_dispatch:
  scfg_chain_hyp fn a b /\
  (scfg_chain_segment a b s t \/ scfg_chain_splice a s t) /\
  active_inst (scfg_chain fn a b) i t /\ i.inst_opcode <> PHI ==>
  (scfg_chain_segment a b s t /\ active_inst fn i s) \/
  (scfg_chain_splice a s t /\ active_inst fn (LAST a.bb_instructions) s)
Proof
  metis_tac[scfg_chain_active_back, scfg_chain_splice_active]
QED

Theorem scfg_chain_normalize_ghosts:
  scfg_chain_hyp fn a b /\
  (!l bb. lookup_block l fn.fn_blocks = SOME bb ==>
          EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) /\
  (!nm f. lookup_function nm C.ctx_functions = SOME f ==> wf_function f) /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  (!j. active_inst fn j s ==> frame_reachable vs C stk PG G tn fn j s) /\
  (scfg_chain_segment a b s t \/ scfg_chain_splice a s t) /\
  ~s.vs_halted /\ scfg_data_agree s t /\
  active_inst (scfg_chain fn a b) i t /\ i.inst_opcode <> PHI ==>
  ?q. frame_reachable vs C stk PG G tn fn i q /\
      scfg_chain_segment a b q t /\ scfg_data_agree q t
Proof
  strip_tac >>
  Cases_on `scfg_chain_segment a b s t`
  >- (qexists_tac `s` >> simp[] >>
      drule_all scfg_chain_active_back >> metis_tac[]) >>
  `scfg_chain_splice a s t` by metis_tac[] >>
  `active_inst fn (LAST a.bb_instructions) s` by
    metis_tac[scfg_chain_splice_active] >>
  `frame_reachable vs C stk PG G tn fn (LAST a.bb_instructions) s` by
    metis_tac[] >>
  drule_all scfg_chain_splice_ghosts >>
  metis_tac[]
QED

Theorem scfg_setup_callee_agree:
  scfg_data_agree s t /\ fn_entry_label f = fn_entry_label g ==>
  setup_callee f args s = setup_callee g args t
Proof
  simp[fn_entry_label_def, entry_block_def] >>
  Cases_on `NULL f.fn_blocks` >> Cases_on `NULL g.fn_blocks` >>
  simp[setup_callee_def] >> rpt strip_tac >>
  gvs[scfg_data_agree_def, execution_frame_def, venom_state_component_equality]
QED

Theorem scfg_chain_setup_entry_back:
  scfg_chain_hyp fn a b /\
  EVERY (\i. i.inst_opcode <> PHI) (fn_insts fn) /\
  scfg_data_agree s t /\
  setup_callee (scfg_chain fn a b) args t = SOME ct /\
  enters_block (scfg_chain fn a b) ct t1 /\
  active_inst (scfg_chain fn a b) i t1 ==>
  ?cs s1. setup_callee fn args s = SOME cs /\ enters_block fn cs s1 /\
    scfg_data_agree s1 t1 /\
    (scfg_chain_segment a b s1 t1 \/ scfg_chain_splice a s1 t1)
Proof
  strip_tac >>
  `setup_callee fn args s = SOME ct` by
    metis_tac[scfg_setup_callee_agree, scfg_chain_entry_eq] >>
  `fn_entry_state fn ct` by metis_tac[setup_callee_fn_entry_state] >>
  `scfg_chain_exit a b ct ct` by metis_tac[scfg_chain_initial_exit] >>
  `?bt. lookup_block ct.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt` by
    (fs[enters_block_def] >> metis_tac[]) >>
  drule_all scfg_chain_exit_lookup >> strip_tac >>
  `scfg_bprefix C fn ct ct` by simp[scfg_bprefix_rules] >>
  drule_all scfg_chain_rooted_enter >> strip_tac >>
  qexistsl_tac [`ct`, `s1`] >> simp[] >>
  metis_tac[scfg_data_agree_payload, scfg_chain_segment_payload, scfg_chain_splice_def]
QED

Theorem scfg_chain_no_phi_insts:
  scfg_chain_hyp fn a b /\ EVERY (\i. i.inst_opcode <> PHI) (fn_insts fn) ==>
  EVERY (\i. i.inst_opcode <> PHI) (fn_insts (scfg_chain fn a b))
Proof
  strip_tac >>
  `EVERY no_phis fn.fn_blocks` by
    (gvs[fn_insts_def, EVERY_MEM, fn_insts_blocks_MEM, no_phis_def] >>
     metis_tac[]) >>
  `no_phis a /\ no_phis b` by
    metis_tac[scfg_chain_hyp_def, lookup_block_member_label, EVERY_MEM] >>
  `EVERY no_phis (scfg_chain fn a b).fn_blocks` by
    (simp[scfg_chain_def] >>
     irule update_succ_phi_labels_no_phi >>
     irule replace_block_no_phi >>
     simp[merge_blocks_no_phi, remove_block_no_phi]) >>
  gvs[fn_insts_def, EVERY_MEM, fn_insts_blocks_MEM, no_phis_def] >>
  metis_tac[]
QED

Theorem scfg_chain_setup_entry_dispatch:
  scfg_chain_hyp fn a b /\
  EVERY (\i. i.inst_opcode <> PHI) (fn_insts fn) /\
  scfg_data_agree s t /\
  setup_callee (scfg_chain fn a b) args t = SOME ct /\
  enters_block (scfg_chain fn a b) ct t1 /\
  active_inst (scfg_chain fn a b) i t1 ==>
  ?cs s1. setup_callee fn args s = SOME cs /\ enters_block fn cs s1 /\
    scfg_data_agree s1 t1 /\
    ((scfg_chain_segment a b s1 t1 /\ active_inst fn i s1) \/
     (scfg_chain_splice a s1 t1 /\ active_inst fn (LAST a.bb_instructions) s1))
Proof
  strip_tac >>
  drule_all scfg_chain_setup_entry_back >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) (fn_insts (scfg_chain fn a b))` by
    metis_tac[scfg_chain_no_phi_insts] >>
  `i.inst_opcode <> PHI` by
    (fs[active_inst_def, fn_insts_def, EVERY_MEM, fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  metis_tac[scfg_chain_active_back, scfg_chain_splice_active]
QED

Theorem scfg_bypass_active_back:
  scfg_bypass_hyp fn a b fn' /\ scfg_bypass_aligned a b s t /\
  active_inst fn' j t ==>
  ?i. active_inst fn i s /\
    j = scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i
Proof
  strip_tac >>
  drule scfg_bypass_lookup_eq >>
  disch_then (qspec_then `s.vs_current_bb` assume_tac) >>
  fs[active_inst_def, scfg_bypass_aligned_def, scfg_ctrl_def] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks)` by
    metis_tac[scfg_bypass_labels_distinct_new, fn_labels_def] >>
  drule_all venomExecProofsTheory.MEM_lookup_block >> strip_tac >>
  gvs[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[] >>
  gvs[scfg_bypass_block_def, EL_MAP] >>
  metis_tac[lookup_block_member_label]
QED

Theorem scfg_bypass_active_ordinary_back:
  scfg_bypass_hyp fn a b fn' /\ scfg_bypass_aligned a b s t /\
  active_inst fn' j t /\ ~is_terminator j.inst_opcode /\ j.inst_opcode <> PHI ==>
  active_inst fn j s
Proof
  strip_tac >> drule_all scfg_bypass_active_back >> strip_tac >>
  metis_tac[scfg_bypass_image_ordinary_inv]
QED

Theorem scfg_bypass_active_invoke_back:
  scfg_bypass_hyp fn a b fn' /\ scfg_bypass_aligned a b s t /\
  active_inst fn' j t /\ j.inst_opcode = INVOKE ==>
  active_inst fn j s
Proof
  strip_tac >> irule scfg_bypass_active_ordinary_back >>
  simp[is_terminator_def] >> metis_tac[]
QED

Theorem scfg_bypass_no_phi_entry_back:
  scfg_bypass_hyp fn a b fn' /\
  (!l bb. lookup_block l fn.fn_blocks = SOME bb ==>
          EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) /\
  scfg_bypass_aligned a b s t /\ enters_block fn' t y ==>
  enters_block fn s (s with vs_inst_idx := 0) /\
  scfg_bypass_aligned a b (s with vs_inst_idx := 0) y
Proof
  strip_tac >>
  `s.vs_current_bb <> b.bb_label /\ t.vs_current_bb = s.vs_current_bb` by
    fs[scfg_bypass_aligned_def, scfg_ctrl_def] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        lookup_block t.vs_current_bb fn'.fn_blocks =
          SOME (scfg_bypass_block a b bb)` by
    (drule scfg_bypass_lookup_eq >>
     disch_then (qspec_then `s.vs_current_bb` mp_tac) >>
     fs[enters_block_def] >>
     Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[]) >>
  `no_phis bb /\ no_phis (scfg_bypass_block a b bb)` by
    (simp[no_phis_def, scfg_bypass_block_def, EVERY_MAP] >>
     fs[EVERY_MEM] >> rpt strip_tac >>
     metis_tac[scfg_bypass_image_opcode]) >>
  fs[no_phis_def] >>
  fs[enters_block_def, venomExecProofsTheory.eval_phis_no_phis,
     venomExecProofsTheory.no_phis_phi_prefix_length_zero] >>
  gvs[scfg_bypass_aligned_def, scfg_ctrl_def, venom_state_component_equality]
QED

Theorem scfg_bypass_jump_ghosts_back:
  scfg_bypass_hyp fn a b fn' /\
  (!l bb. lookup_block l fn.fn_blocks = SOME bb ==>
          EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) /\
  frame_reach C fn s0 i s /\ frame_reachable vs C stk PG G tn fn i s /\
  is_terminator i.inst_opcode /\
  step_inst k C i s = OK (jump_to lbl s) /\ ~s.vs_halted /\
  scfg_bypass_aligned a b (jump_to lbl s) v /\
  enters_block fn' v y /\ active_inst fn' j y ==>
  ?x h. frame_reachable vs C stk PG G tn fn h x /\
        frame_reach C fn s0 h x /\ scfg_bypass_aligned a b x y /\
        j = scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b))
              x.vs_current_bb h
Proof
  strip_tac >>
  drule_all scfg_bypass_no_phi_entry_back >> strip_tac >>
  drule_all scfg_bypass_active_back >> strip_tac >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  qexistsl_tac [`(jump_to lbl s) with vs_inst_idx := 0`, `i'`] >>
  simp[] >> conj_tac
  >- (irule scfg_transfer_ghosts >> metis_tac[]) >>
  irule (cj 3 frame_reach_rules) >> metis_tac[]
QED

Theorem scfg_bypass_nonsource_ghosts_back:
  scfg_bypass_hyp fn a b fn' /\
  (!l bb. lookup_block l fn.fn_blocks = SOME bb ==>
          EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) /\
  fn_entry_state fn s0 /\ frame_reach C fn s0 i s /\
  frame_reachable vs C stk PG G tn fn i s /\
  is_terminator i.inst_opcode /\ scfg_bypass_aligned a b s t /\
  s.vs_current_bb <> a.bb_label /\
  step_inst k C'
    (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i)
    t = OK v /\ ~v.vs_halted /\
  enters_block fn' v y /\ active_inst fn' j y ==>
  ?x h. frame_reachable vs C stk PG G tn fn h x /\
        frame_reach C fn s0 h x /\ scfg_bypass_aligned a b x y /\
        j = scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b))
              x.vs_current_bb h
Proof
  strip_tac >>
  drule_all scfg_bypass_terminator_context_back >> strip_tac >>
  `active_inst fn i s` by metis_tac[frame_reach_active] >>
  drule_all scfg_bypass_nonsource_branch >> strip_tac >>
  `is_terminator (scfg_bypass_image a.bb_label b.bb_label
     (HD (bb_succs b)) s.vs_current_bb i).inst_opcode` by
    metis_tac[scfg_bypass_image_opcode, is_terminator_def] >>
  `(scfg_bypass_image a.bb_label b.bb_label
     (HD (bb_succs b)) s.vs_current_bb i).inst_opcode <> INVOKE` by
    (Cases_on `(scfg_bypass_image a.bb_label b.bb_label
       (HD (bb_succs b)) s.vs_current_bb i).inst_opcode` >> fs[is_terminator_def]) >>
  `step_inst k C (scfg_bypass_image a.bb_label b.bb_label
     (HD (bb_succs b)) s.vs_current_bb i) t = OK v` by
    metis_tac[venomExecPropsTheory.step_inst_ctx_irrel] >>
  gvs[] >> drule_all simplifyCfgMergeRunsTheory.scfg_terminator_jump >> strip_tac >>
  `~s.vs_halted` by
    (qpat_x_assum `u = jump_to _ s` mp_tac >>
     simp[jump_to_def, venom_state_component_equality] >>
     strip_tac >> gvs[]) >>
  irule scfg_bypass_jump_ghosts_back >> metis_tac[]
QED

Theorem scfg_bypass_source_path_back:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  frame_reach C fn s0 i s /\ is_terminator i.inst_opcode /\
  s.vs_current_bb = a.bb_label /\ scfg_bypass_aligned a b s t /\
  step_inst k C'
    (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i)
    t = OK v /\ ~v.vs_halted ==>
  ?l. step_inst k C i s = OK (jump_to l s) /\ ~s.vs_halted /\
      scfg_bypass_aligned a b
        (if l = b.bb_label then jump_to (HD (bb_succs b)) (jump_to l s)
         else jump_to l s) v
Proof
  strip_tac >>
  drule_all scfg_bypass_terminator_context_back >> strip_tac >>
  `active_inst fn i s /\ wf_function fn` by
    metis_tac[frame_reach_active, scfg_bypass_old_static,
              simplifyCfgStaticInterfaceTheory.scfg_static_wf] >>
  drule_all simplifyCfgMergeRunsTheory.scfg_active_terminator_last >> strip_tac >>
  `MEM a fn.fn_blocks` by
    (fs[scfg_bypass_hyp_def] >> metis_tac[lookup_block_member_label]) >>
  `bb = a` by metis_tac[venomExecProofsTheory.same_label_same_block] >> gvs[] >>
  drule_all simplifyCfgMergeRunsTheory.scfg_terminator_jump >> strip_tac >>
  `~s.vs_halted` by
    (qpat_x_assum `u = jump_to _ s` mp_tac >>
     simp[jump_to_def, venom_state_component_equality] >> strip_tac >> gvs[]) >>
  `t = scfg_ctrl a.bb_label
     (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb)
     s.vs_inst_idx s` by fs[scfg_bypass_aligned_def] >>
  `?l z. step_inst k C (LAST a.bb_instructions) s = OK (jump_to l s) /\
     step_inst k C' (scfg_bypass_term b.bb_label (HD (bb_succs b))
       (LAST a.bb_instructions)) t = OK z /\
     scfg_bypass_aligned a b
       (if l = b.bb_label then jump_to (HD (bb_succs b)) (jump_to l s)
        else jump_to l s) z` by
    metis_tac[scfg_bypass_source_successor_rooted] >>
  `step_inst k C' (scfg_bypass_term b.bb_label (HD (bb_succs b))
       (LAST a.bb_instructions)) t = OK v` by
    (gvs[scfg_bypass_image_def, update_phi_bypass_def, is_terminator_def]) >>
  qexists_tac `l` >> gvs[] >> Cases_on `l = b.bb_label` >> gvs[]
QED

Theorem scfg_bypass_redirected_ghosts_back:
  scfg_bypass_hyp fn a b fn' /\
  (!l bb. lookup_block l fn.fn_blocks = SOME bb ==>
          EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) /\
  fn_entry_state fn s0 /\ frame_reach C fn s0 i s /\
  frame_reachable vs C stk PG G tn fn i s /\
  is_terminator i.inst_opcode /\
  step_inst k C i s = OK (jump_to b.bb_label s) /\ ~s.vs_halted /\
  scfg_bypass_aligned a b
    (jump_to (HD (bb_succs b)) (jump_to b.bb_label s)) v /\
  enters_block fn' v y /\ active_inst fn' j y ==>
  ?x h. frame_reachable vs C stk PG G tn fn h x /\
        frame_reach C fn s0 h x /\ scfg_bypass_aligned a b x y /\
        j = scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b))
              x.vs_current_bb h
Proof
  strip_tac >>
  `enters_block fn (jump_to b.bb_label s) (jump_to b.bb_label s) /\
   active_inst fn (LAST b.bb_instructions) (jump_to b.bb_label s)` by
    metis_tac[scfg_bypass_singleton_enters] >>
  `~(jump_to b.bb_label s).vs_halted` by simp[jump_to_def] >>
  `frame_reachable vs C stk PG G tn fn (LAST b.bb_instructions)
     (jump_to b.bb_label s)` by
    (irule scfg_transfer_ghosts >> metis_tac[]) >>
  `frame_reach C fn s0 (LAST b.bb_instructions) (jump_to b.bb_label s)` by
    metis_tac[scfg_bypass_singleton_reach] >>
  `step_inst 0 C (LAST b.bb_instructions) (jump_to b.bb_label s) =
     OK (jump_to (HD (bb_succs b)) (jump_to b.bb_label s))` by
    metis_tac[scfg_bypass_singleton_step] >>
  `is_terminator (LAST b.bb_instructions).inst_opcode` by
    metis_tac[scfg_bypass_singleton_shape, is_terminator_def] >>
  irule scfg_bypass_jump_ghosts_back >> metis_tac[]
QED

Theorem scfg_bypass_block_ghosts_back:
  scfg_bypass_hyp fn a b fn' /\
  (!l bb. lookup_block l fn.fn_blocks = SOME bb ==>
          EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) /\
  fn_entry_state fn s0 /\ frame_reach C fn s0 i s /\
  frame_reachable vs C stk PG G tn fn i s /\
  is_terminator i.inst_opcode /\ scfg_bypass_aligned a b s t /\
  step_inst k C'
    (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i)
    t = OK v /\ ~v.vs_halted /\
  enters_block fn' v y /\ active_inst fn' j y ==>
  ?x h. frame_reachable vs C stk PG G tn fn h x /\
        frame_reach C fn s0 h x /\ scfg_bypass_aligned a b x y /\
        j = scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b))
              x.vs_current_bb h
Proof
  strip_tac >> Cases_on `s.vs_current_bb = a.bb_label`
  >- (drule_all scfg_bypass_source_path_back >> strip_tac >>
      Cases_on `l = b.bb_label` >> gvs[]
      >- (irule scfg_bypass_redirected_ghosts_back >> metis_tac[]) >>
      irule scfg_bypass_jump_ghosts_back >> metis_tac[]) >>
  irule scfg_bypass_nonsource_ghosts_back >> metis_tac[]
QED

Theorem scfg_bypass_frame_return_back:
  scfg_bypass_hyp f.cf_fn a b g.cf_fn /\
  scfg_saved_call R f g /\
  scfg_bypass_aligned a b f.cf_state g.cf_state /\
  frame_reachable vs C (f::stk) PG G tn fn ri s /\
  active_inst fn ri s /\ scfg_data_agree s t /\
  step_inst k C' ri t = IntRet ret v /\
  bind_outputs g.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state g.cf_state v)) = SOME t' /\
  active_inst g.cf_fn j (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx) ==>
  ?q h. frame_reachable vs C stk g.cf_params
       (DRESTRICT g.cf_prov (COMPL (set g.cf_inst.inst_outputs)))
       (tn with t_var := DRESTRICT g.cf_tvar (COMPL (set g.cf_inst.inst_outputs)))
       f.cf_fn h q /\
    scfg_data_agree q (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx) /\
    scfg_bypass_aligned a b q (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx) /\
    j = scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) q.vs_current_bb h
Proof
  strip_tac >>
  drule_all scfg_data_agree_intret >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  drule_all scfg_bypass_saved_return_back >> strip_tac >>
  drule_all scfg_bypass_active_back >> strip_tac >>
  qexistsl_tac [`s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx`, `i`] >>
  simp[] >>
  `f.cf_inst.inst_outputs = g.cf_inst.inst_outputs /\
   f.cf_params = g.cf_params /\ f.cf_prov = g.cf_prov /\ f.cf_tvar = g.cf_tvar` by
    metis_tac[scfg_saved_frame_ghosts, scfg_saved_call_def] >>
  `frame_reachable vs C stk f.cf_params
       (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
       (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
       f.cf_fn i (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)` by
    (irule frame_reachable_ret >> metis_tac[]) >>
  gvs[]
QED

(* Normalized one-merge context simulation interface. *)
Definition scfg_merge_pair_def:
  scfg_merge_pair f g <=>
    f = g \/ ?a b. scfg_chain_hyp f a b /\ g = scfg_chain f a b
End

Definition scfg_merge_pos_def:
  scfg_merge_pos f i s g j t <=>
    i = j /\ ((f = g /\ s = t) \/
      ?a b. scfg_chain_hyp f a b /\ g = scfg_chain f a b /\
            scfg_chain_segment a b s t)
End

Definition scfg_merge_context_def:
  scfg_merge_context C C' <=>
    C'.ctx_entry = C.ctx_entry /\
    (!nm f. lookup_function nm C.ctx_functions = SOME f ==>
      wf_function f /\ EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)) /\
    (!nm g. lookup_function nm C'.ctx_functions = SOME g ==>
      ?f. lookup_function nm C.ctx_functions = SOME f /\ scfg_merge_pair f g)
End

Definition scfg_merge_witness_def:
  scfg_merge_witness vs C stk PG G tn g i t <=>
    ?fs f s. frame_reachable vs C fs PG G tn f i s /\
      scfg_saved_stack scfg_merge_pos fs stk /\ scfg_merge_pos f i s g i t
End

Theorem scfg_merge_context_lookup:
  scfg_merge_context C C' /\
  lookup_function nm C'.ctx_functions = SOME g ==>
  ?f. lookup_function nm C.ctx_functions = SOME f /\ scfg_merge_pair f g /\
      wf_function f /\ EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)
Proof
  simp[scfg_merge_context_def] >> metis_tac[]
QED

Theorem scfg_merge_pair_entry:
  scfg_merge_pair f g ==> fn_entry_label f = fn_entry_label g
Proof
  simp[scfg_merge_pair_def] >> metis_tac[scfg_chain_entry_eq]
QED

Theorem scfg_merge_pair_no_phi:
  scfg_merge_pair f g /\ EVERY (\i. i.inst_opcode <> PHI) (fn_insts f) ==>
  EVERY (\i. i.inst_opcode <> PHI) (fn_insts g)
Proof
  simp[scfg_merge_pair_def] >> metis_tac[scfg_chain_no_phi_insts]
QED

Theorem scfg_merge_pos_data:
  scfg_merge_pos f i s g j t ==> i = j /\ scfg_data_agree s t
Proof
  simp[scfg_merge_pos_def] >>
  metis_tac[scfg_chain_segment_payload, scfg_data_agree_payload,
            scfg_data_agree_refl]
QED

Theorem scfg_merge_pos_pair:
  scfg_merge_pos f i s g j t ==> scfg_merge_pair f g
Proof
  simp[scfg_merge_pos_def, scfg_merge_pair_def] >> metis_tac[]
QED

Theorem scfg_saved_stack_nil[simp]:
  scfg_saved_stack R [] gs <=> gs = []
Proof
  Cases_on `gs` >> simp[scfg_saved_stack_def]
QED

Theorem scfg_saved_stack_cons:
  scfg_saved_stack R fs (g::gs) <=>
  ?f rest. fs = f::rest /\ scfg_saved_call R f g /\ scfg_saved_stack R rest gs
Proof
  Cases_on `fs` >> simp[scfg_saved_stack_def]
QED

Theorem scfg_merge_witness_root:
  scfg_merge_context C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  scfg_merge_witness vs C stk PG G tn g i t ==>
  ?fs f s r. frame_reachable vs C fs PG G tn f i s /\
    scfg_saved_stack scfg_merge_pos fs stk /\ scfg_merge_pos f i s g i t /\
    scfg_data_agree s t /\ fn_entry_state f r /\ frame_reach C f r i s
Proof
  simp[scfg_merge_context_def, scfg_merge_witness_def] >> rpt strip_tac >>
  `?r. fn_entry_state f r /\ frame_reach C f r i s` by
    metis_tac[scfg_frame_reachable_entry_root] >>
  metis_tac[scfg_merge_pos_data]
QED

Theorem scfg_merge_witness_not_halted:
  scfg_merge_context C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  scfg_merge_witness vs C stk PG G tn g i t ==> ~t.vs_halted
Proof
  strip_tac >> drule_all scfg_merge_witness_root >> strip_tac >>
  `~s.vs_halted` by
    metis_tac[supply_frame_reach_not_halted, fn_entry_state_def] >>
  gvs[scfg_data_agree_reconstruct, scfg_ctrl_def,
      venom_state_component_equality]
QED

Theorem scfg_merge_witness_entry:
  scfg_merge_context C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  C'.ctx_entry = SOME name /\
  lookup_function name C'.ctx_functions = SOME g /\
  fn_entry_label g = SOME lbl /\
  enters_block g
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t /\
  active_inst g i t ==>
  scfg_merge_witness vs C [] [] FEMPTY entry_taint g i t
Proof
  strip_tac >> drule_all scfg_merge_context_lookup >> strip_tac >>
  `C.ctx_entry = SOME name` by fs[scfg_merge_context_def] >>
  `fn_entry_label f = SOME lbl` by metis_tac[scfg_merge_pair_entry] >>
  qpat_x_assum `scfg_merge_pair f g` mp_tac >>
  simp[scfg_merge_pair_def] >> strip_tac
  >- (gvs[] >> simp[scfg_merge_witness_def] >>
      qexistsl_tac [`[]`, `f`, `t`] >>
      simp[scfg_merge_pos_def] >> irule frame_reachable_entry >> metis_tac[]) >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `enters_block (scfg_chain f a b) v t` >>
  `fn_entry_state f v` by simp[fn_entry_state_def, Abbr `v`] >>
  `scfg_chain_exit a b v v` by metis_tac[scfg_chain_initial_exit] >>
  `?bt. lookup_block v.vs_current_bb (scfg_chain f a b).fn_blocks = SOME bt` by
    (fs[enters_block_def] >> metis_tac[]) >>
  `?bb. lookup_block v.vs_current_bb f.fn_blocks = SOME bb` by
    metis_tac[scfg_chain_exit_lookup] >>
  `scfg_bprefix C f v v` by simp[scfg_bprefix_rules] >>
  drule_all scfg_chain_rooted_enter >> strip_tac >>
  `!j. active_inst f j s1 ==>
       frame_reachable vs C [] [] FEMPTY entry_taint f j s1` by
    (rpt strip_tac >> irule frame_reachable_entry >>
     gvs[Abbr `v`] >> metis_tac[]) >>
  `!l bb. lookup_block l f.fn_blocks = SOME bb ==>
          EVERY (\j. j.inst_opcode <> PHI) bb.bb_instructions` by
    (fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[lookup_block_member_label]) >>
  `scfg_data_agree s1 t` by
    metis_tac[scfg_data_agree_payload, scfg_chain_segment_payload,
              scfg_chain_splice_def] >>
  `~s1.vs_halted` by
    (fs[enters_block_def] >>
     metis_tac[venomExecProofsTheory.eval_phis_preserves_halted, fn_entry_state_def]) >>
  `i.inst_opcode <> PHI` by
    (drule_all scfg_chain_no_phi_insts >>
     fs[active_inst_def, fn_insts_def, EVERY_MEM, fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `?q. frame_reachable vs C [] [] FEMPTY entry_taint f i q /\
       scfg_chain_segment a b q t /\ scfg_data_agree q t` by
    (irule scfg_chain_normalize_ghosts >>
     fs[scfg_merge_context_def] >> metis_tac[]) >>
  simp[scfg_merge_witness_def] >> qexistsl_tac [`[]`, `f`, `q`] >>
  simp[scfg_merge_pos_def] >> metis_tac[]
QED

Theorem scfg_merge_witness_call:
  scfg_merge_context C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  scfg_merge_witness vs C stk PG G tn caller inst t /\
  active_inst caller inst t /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm, ops) /\
  lookup_function nm C'.ctx_functions = SOME callee /\
  eval_operands ops t = SOME args /\ setup_callee callee args t = SOME ct /\
  enters_block callee ct t1 /\ active_inst callee i t1 ==>
  scfg_merge_witness vs C
    (<|cf_fn := caller; cf_inst := inst; cf_state := t;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee i t1
Proof
  strip_tac >> drule_all scfg_merge_context_lookup >> strip_tac >>
  qpat_x_assum `scfg_merge_witness _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[scfg_merge_witness_def] >> strip_tac >>
  `scfg_data_agree s t` by metis_tac[scfg_merge_pos_data] >>
  `active_inst f' inst s` by
    (fs[scfg_merge_pos_def] >> gvs[] >>
     irule scfg_chain_active_back >> simp[] >> metis_tac[]) >>
  `eval_operands ops s = SOME args` by
    metis_tac[scfg_data_agree_eval_operands] >>
  qmatch_goalsub_abbrev_tac `scfg_saved_stack scfg_merge_pos _ (saved::stk)` >>
  qabbrev_tac `src = <|cf_fn := f'; cf_inst := inst; cf_state := s;
    cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|>` >>
  `scfg_saved_stack scfg_merge_pos (src::fs) (saved::stk)` by
    (fs[scfg_saved_stack_def] >>
     simp[scfg_saved_call_def, scfg_saved_frame_def, Abbr `src`, Abbr `saved`]) >>
  qpat_x_assum `scfg_merge_pair f callee` mp_tac >>
  simp[scfg_merge_pair_def] >> strip_tac
  >- (gvs[] >>
      `setup_callee callee args s = SOME ct` by
        metis_tac[scfg_setup_callee_agree] >>
      qexistsl_tac [`src::fs`, `callee`, `t1`] >> simp[scfg_merge_pos_def] >>
      simp[Abbr `src`] >> irule frame_reachable_call >> metis_tac[]) >>
  gvs[] >> drule_all scfg_chain_setup_entry_dispatch >> strip_tac >>
  `!j. active_inst f j s1 ==>
     frame_reachable vs C (src::fs) (MAP (op_prov G) ops) FEMPTY
       (tn with t_var := FEMPTY) f j s1` by
    (rpt strip_tac >> simp[Abbr `src`] >>
     irule frame_reachable_call >> metis_tac[]) >>
  `!l bb. lookup_block l f.fn_blocks = SOME bb ==>
          EVERY (\j. j.inst_opcode <> PHI) bb.bb_instructions` by
    (fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[lookup_block_member_label]) >>
  `i.inst_opcode <> PHI` by
    (drule_all scfg_chain_no_phi_insts >>
     fs[active_inst_def, fn_insts_def, EVERY_MEM, fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `fn_entry_state f cs` by metis_tac[setup_callee_fn_entry_state] >>
  `~s1.vs_halted` by
    (fs[enters_block_def] >>
     metis_tac[venomExecProofsTheory.eval_phis_preserves_halted, fn_entry_state_def]) >>
  `?q. frame_reachable vs C (src::fs) (MAP (op_prov G) ops) FEMPTY
       (tn with t_var := FEMPTY) f i q /\
       scfg_chain_segment a b q t1 /\ scfg_data_agree q t1` by
    (irule scfg_chain_normalize_ghosts >>
     fs[scfg_merge_context_def] >> metis_tac[]) >>
  qexistsl_tac [`src::fs`, `f`, `q`] >>
  simp[scfg_merge_pos_def] >> metis_tac[]
QED

Theorem scfg_data_agree_ok_back:
  scfg_data_agree s t /\ i.inst_opcode <> INVOKE /\
  step_inst k C' i t = OK v ==>
  ?u. step_inst k C i s = OK u /\ scfg_data_agree u v
Proof
  strip_tac >>
  `scfg_payload t s` by
    metis_tac[scfg_data_agree_sym, scfg_data_agree_payload] >>
  drule scfg_payload_step >>
  disch_then (qspecl_then [`k`, `i`, `C'`] mp_tac) >> simp[] >>
  Cases_on `step_inst k C' i s` >> simp[scfg_result_def] >>
  strip_tac >> gvs[step_inst_non_invoke, scfg_data_agree_payload] >>
  metis_tac[scfg_payload_sym, scfg_data_agree_payload]
QED

Theorem scfg_chain_witness_next:
  scfg_merge_context C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  scfg_chain_hyp f a b /\ EVERY (\i. i.inst_opcode <> PHI) (fn_insts f) /\
  frame_reachable vs C fs PG G tn f inst s /\
  scfg_saved_stack scfg_merge_pos fs stk /\ scfg_chain_segment a b s t /\
  active_inst f inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst k C' inst t = OK v /\
  active_inst (scfg_chain f a b) j (v with vs_inst_idx := SUC t.vs_inst_idx) ==>
  scfg_merge_witness vs C stk PG (step_prov PG G inst v)
    (step_taint inst t v tn) (scfg_chain f a b) j
    (v with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >>
  `scfg_data_agree s t` by
    metis_tac[scfg_chain_segment_payload, scfg_data_agree_payload] >>
  drule_all scfg_data_agree_ok_back >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  `step_inst k C inst t = OK v` by gvs[step_inst_non_invoke] >>
  drule_all scfg_chain_segment_advance_back >> strip_tac >>
  `u' = u` by metis_tac[exec_result_11] >> gvs[] >>
  `step_prov PG G inst u = step_prov PG G inst v /\
   step_taint inst s u tn = step_taint inst t v tn` by
    metis_tac[scfg_data_agree_step_prov, scfg_data_agree_step_taint] >>
  `!h. active_inst f h (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
    frame_reachable vs C fs PG (step_prov PG G inst v)
      (step_taint inst t v tn) f h (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (rpt strip_tac >>
     `frame_reachable vs C fs PG (step_prov PG G inst u)
       (step_taint inst s u tn) f h (u with vs_inst_idx := SUC s.vs_inst_idx)` by
       (irule frame_reachable_next >> metis_tac[]) >> metis_tac[]) >>
  `!l bb. lookup_block l f.fn_blocks = SOME bb ==>
    EVERY (\h. h.inst_opcode <> PHI) bb.bb_instructions` by
    (fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[lookup_block_member_label]) >>
  `j.inst_opcode <> PHI` by
    (drule_all scfg_chain_no_phi_insts >>
     fs[active_inst_def, fn_insts_def, EVERY_MEM, fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `~(u with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by
    (`?r. fn_entry_state f r /\ frame_reach C f r inst s` by
       (irule scfg_frame_reachable_entry_root >>
        fs[scfg_merge_context_def] >> metis_tac[]) >>
     `~s.vs_halted` by
       metis_tac[supply_frame_reach_not_halted, fn_entry_state_def] >>
     drule venomStepPropsTheory.step_inst_ok_halted >> simp[] >> metis_tac[]) >>
  `scfg_data_agree (u with vs_inst_idx := SUC s.vs_inst_idx)
    (v with vs_inst_idx := SUC t.vs_inst_idx)` by
    metis_tac[scfg_data_agree_index] >>
  `?q. frame_reachable vs C fs PG (step_prov PG G inst v)
    (step_taint inst t v tn) f j q /\
    scfg_chain_segment a b q (v with vs_inst_idx := SUC t.vs_inst_idx) /\
    scfg_data_agree q (v with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule scfg_chain_normalize_ghosts >>
     fs[scfg_merge_context_def] >>
     conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     qexists_tac `u with vs_inst_idx := SUC s.vs_inst_idx` >> simp[]) >>
  simp[scfg_merge_witness_def] >> qexistsl_tac [`fs`, `f`, `q`] >>
  simp[scfg_merge_pos_def] >> metis_tac[]
QED

Theorem scfg_merge_witness_next:
  scfg_merge_context C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  scfg_merge_witness vs C stk PG G tn g inst t /\ active_inst g inst t /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst k C' inst t = OK v /\
  active_inst g j (v with vs_inst_idx := SUC t.vs_inst_idx) ==>
  scfg_merge_witness vs C stk PG (step_prov PG G inst v)
    (step_taint inst t v tn) g j (v with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >>
  qpat_x_assum `scfg_merge_witness _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[scfg_merge_witness_def] >> strip_tac >>
  qpat_x_assum `scfg_merge_pos _ _ _ _ _ _` mp_tac >>
  simp[scfg_merge_pos_def] >> strip_tac
  >- (gvs[] >>
      `step_inst k C inst s = OK v` by gvs[step_inst_non_invoke] >>
      simp[scfg_merge_witness_def] >>
      qexistsl_tac [`fs`, `f`, `v with vs_inst_idx := SUC s.vs_inst_idx`] >>
      simp[scfg_merge_pos_def] >> irule frame_reachable_next >> metis_tac[]) >>
  gvs[] >>
  `scfg_rooted C fs f inst s` by
    (irule scfg_frame_reachable_rooted >>
     fs[scfg_merge_context_def] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)` by
    (fs[scfg_rooted_def] >> drule scfg_root_history_lookup >>
     fs[scfg_merge_context_def] >> metis_tac[]) >>
  `inst.inst_opcode <> PHI` by
    (drule_all scfg_chain_no_phi_insts >>
     fs[active_inst_def, fn_insts_def, EVERY_MEM, fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `active_inst f inst s` by metis_tac[scfg_chain_active_back] >>
  drule_all scfg_chain_witness_next >>
  simp[scfg_merge_witness_def, scfg_merge_pos_def]
QED

Theorem scfg_frame_reach_exit_prefix:
  wf_function f /\ frame_reach C f r i s /\ is_terminator i.inst_opcode /\
  step_inst k C i s = OK u /\ ~u.vs_halted ==>
  scfg_bprefix C f r u
Proof
  strip_tac >> drule_all scfg_frame_reach_decompose >> strip_tac >>
  drule_all scfg_prefix_terminator >> strip_tac >>
  irule scfg_bprefix_trans >> goal_assum (drule_at Any) >>
  irule scfg_bprefix_single >> metis_tac[]
QED

Theorem scfg_chain_block_entry_back:
  scfg_chain_hyp f a b /\ fn_entry_state f r /\ frame_reach C f r inst s /\
  ~s.vs_halted /\ scfg_chain_segment a b s t /\
  is_terminator inst.inst_opcode /\ step_inst k C' inst t = OK v /\
  ~v.vs_halted /\ enters_block (scfg_chain f a b) v t1 ==>
  ?u s1. step_inst k C inst s = OK u /\ ~u.vs_halted /\
    enters_block f u s1 /\
    (scfg_chain_segment a b s1 t1 \/ scfg_chain_splice a s1 t1) /\
    scfg_data_agree s1 t1
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  `step_inst k C inst t = OK v` by gvs[step_inst_non_invoke] >>
  drule_all simplifyCfgMergeRunsTheory.scfg_chain_segment_terminator_back >> strip_tac >>
  Cases_on `step_inst k C inst s` >> gvs[scfg_result_def] >>
  rename1 `step_inst k C inst s = OK u` >>
  `~u.vs_halted` by
    (drule venomStepPropsTheory.step_inst_ok_halted >> metis_tac[]) >>
  `wf_function f` by metis_tac[scfg_chain_old_wf] >>
  `scfg_bprefix C f r u` by metis_tac[scfg_frame_reach_exit_prefix] >>
  `?bt. lookup_block v.vs_current_bb (scfg_chain f a b).fn_blocks = SOME bt` by
    (fs[enters_block_def] >> metis_tac[]) >>
  `?bb. lookup_block u.vs_current_bb f.fn_blocks = SOME bb` by
    metis_tac[scfg_chain_exit_lookup] >>
  drule_all scfg_chain_rooted_enter >> strip_tac >>
  qexists_tac `s1` >> simp[] >>
  metis_tac[scfg_chain_segment_payload, scfg_chain_splice_def,
            scfg_data_agree_payload]
QED

Theorem scfg_chain_witness_block:
  scfg_merge_context C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  scfg_chain_hyp f a b /\ EVERY (\i. i.inst_opcode <> PHI) (fn_insts f) /\
  frame_reachable vs C fs PG G tn f inst s /\
  scfg_saved_stack scfg_merge_pos fs stk /\ scfg_chain_segment a b s t /\
  active_inst f inst s /\ is_terminator inst.inst_opcode /\
  step_inst k C' inst t = OK v /\ ~v.vs_halted /\
  enters_block (scfg_chain f a b) v t1 /\ active_inst (scfg_chain f a b) j t1 ==>
  scfg_merge_witness vs C stk PG G tn (scfg_chain f a b) j t1
Proof
  strip_tac >>
  `?r. fn_entry_state f r /\ frame_reach C f r inst s` by
    (irule scfg_frame_reachable_entry_root >>
     fs[scfg_merge_context_def] >> metis_tac[]) >>
  `~s.vs_halted` by
    metis_tac[supply_frame_reach_not_halted, fn_entry_state_def] >>
  drule_all scfg_chain_block_entry_back >> strip_tac >>
  `!l bb. lookup_block l f.fn_blocks = SOME bb ==>
    EVERY (\h. h.inst_opcode <> PHI) bb.bb_instructions` by
    (fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[lookup_block_member_label]) >>
  `entry_prov f u G = G /\ entry_taint_vars f u tn = tn` by
    metis_tac[scfg_entry_prov_no_phi, scfg_entry_taint_no_phi] >>
  `!h. active_inst f h s1 ==> frame_reachable vs C fs PG G tn f h s1` by
    (rpt strip_tac >>
     `frame_reachable vs C fs PG (entry_prov f u G)
       (entry_taint_vars f u tn) f h s1` by
       (irule frame_reachable_block >> metis_tac[]) >> metis_tac[]) >>
  `~s1.vs_halted` by
    (fs[enters_block_def] >>
     metis_tac[venomExecProofsTheory.eval_phis_preserves_halted]) >>
  `j.inst_opcode <> PHI` by
    (drule_all scfg_chain_no_phi_insts >>
     fs[active_inst_def, fn_insts_def, EVERY_MEM, fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `?q. frame_reachable vs C fs PG G tn f j q /\
       scfg_chain_segment a b q t1 /\ scfg_data_agree q t1` by
    (irule scfg_chain_normalize_ghosts >>
     fs[scfg_merge_context_def] >>
     conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     qexists_tac `s1` >> simp[]) >>
  simp[scfg_merge_witness_def] >> qexistsl_tac [`fs`, `f`, `q`] >>
  simp[scfg_merge_pos_def] >> metis_tac[]
QED

Theorem scfg_merge_witness_block:
  scfg_merge_context C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  scfg_merge_witness vs C stk PG G tn g inst t /\ active_inst g inst t /\
  is_terminator inst.inst_opcode /\ step_inst k C' inst t = OK v /\
  ~v.vs_halted /\ enters_block g v t1 /\ active_inst g j t1 ==>
  scfg_merge_witness vs C stk PG (entry_prov g v G)
    (entry_taint_vars g v tn) g j t1
Proof
  strip_tac >>
  qpat_x_assum `scfg_merge_witness _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[scfg_merge_witness_def] >> strip_tac >>
  qpat_x_assum `scfg_merge_pos _ _ _ _ _ _` mp_tac >>
  simp[scfg_merge_pos_def] >> strip_tac
  >- (gvs[] >>
      `inst.inst_opcode <> INVOKE` by
        (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
      `step_inst k C inst s = OK v` by gvs[step_inst_non_invoke] >>
      qexistsl_tac [`fs`, `f`, `t1`] >> simp[] >>
      irule frame_reachable_block >> metis_tac[]) >>
  gvs[] >>
  `scfg_rooted C fs f inst s` by
    (irule scfg_frame_reachable_rooted >>
     fs[scfg_merge_context_def] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)` by
    (fs[scfg_rooted_def] >> drule scfg_root_history_lookup >>
     fs[scfg_merge_context_def] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> PHI) (fn_insts (scfg_chain f a b))` by
    metis_tac[scfg_chain_no_phi_insts] >>
  `!l bb. lookup_block l (scfg_chain f a b).fn_blocks = SOME bb ==>
    EVERY (\h. h.inst_opcode <> PHI) bb.bb_instructions` by
    (fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[lookup_block_member_label]) >>
  `entry_prov (scfg_chain f a b) v G = G /\
   entry_taint_vars (scfg_chain f a b) v tn = tn` by
    metis_tac[scfg_entry_prov_no_phi, scfg_entry_taint_no_phi] >>
  `inst.inst_opcode <> PHI` by
    (fs[active_inst_def, fn_insts_def, EVERY_MEM, fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `active_inst f inst s` by metis_tac[scfg_chain_active_back] >>
  drule_all scfg_chain_witness_block >>
  simp[scfg_merge_witness_def, scfg_merge_pos_def]
QED

Theorem scfg_same_saved_return_back:
  scfg_saved_call R f g /\ f.cf_state = g.cf_state /\
  scfg_data_agree u v /\
  bind_outputs g.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state g.cf_state v)) = SOME t' ==>
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state u)) = SOME t'
Proof
  strip_tac >>
  `f.cf_inst = g.cf_inst` by fs[scfg_saved_call_def] >>
  `scfg_data_agree (adopt_return_fmp ret (merge_callee_state g.cf_state v))
                   (adopt_return_fmp ret (merge_callee_state f.cf_state u))` by
    metis_tac[scfg_data_agree_merge, scfg_data_agree_adopt,
              scfg_data_agree_sym, scfg_data_agree_refl] >>
  drule_all scfg_data_agree_bind >> strip_tac >>
  `t'.vs_current_bb = t''.vs_current_bb /\
   t'.vs_prev_bb = t''.vs_prev_bb /\ t'.vs_inst_idx = t''.vs_inst_idx` by
    metis_tac[scfg_return_control] >>
  `t' = t''` by
    gvs[scfg_data_agree_reconstruct, scfg_ctrl_def,
        venom_state_component_equality] >> gvs[]
QED

Theorem scfg_chain_witness_ret:
  scfg_merge_context C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  scfg_chain_hyp f.cf_fn a b /\ g.cf_fn = scfg_chain f.cf_fn a b /\
  EVERY (\i. i.inst_opcode <> PHI) (fn_insts f.cf_fn) /\
  scfg_saved_call scfg_merge_pos f g /\
  scfg_chain_segment a b f.cf_state g.cf_state /\
  frame_reachable vs C (f::fs) PG G tn fn ri s /\ active_inst fn ri s /\
  scfg_saved_stack scfg_merge_pos fs stk /\ scfg_data_agree s t /\
  step_inst k C' ri t = IntRet ret v /\
  bind_outputs g.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state g.cf_state v)) = SOME t' /\
  active_inst g.cf_fn j (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx) ==>
  scfg_merge_witness vs C stk g.cf_params
    (DRESTRICT g.cf_prov (COMPL (set g.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT g.cf_tvar (COMPL (set g.cf_inst.inst_outputs)))
    g.cf_fn j (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx)
Proof
  strip_tac >>
  drule_all scfg_data_agree_intret >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  drule_all scfg_chain_saved_return_back >> strip_tac >>
  `f.cf_inst.inst_outputs = g.cf_inst.inst_outputs /\
   f.cf_params = g.cf_params /\ f.cf_prov = g.cf_prov /\ f.cf_tvar = g.cf_tvar` by
    metis_tac[scfg_saved_frame_ghosts, scfg_saved_call_def] >>
  `!h. active_inst f.cf_fn h (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
    frame_reachable vs C fs g.cf_params
      (DRESTRICT g.cf_prov (COMPL (set g.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT g.cf_tvar (COMPL (set g.cf_inst.inst_outputs)))
      f.cf_fn h (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)` by
    (rpt strip_tac >>
     `frame_reachable vs C fs f.cf_params
       (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
       (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
       f.cf_fn h (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)` by
       (irule frame_reachable_ret >> metis_tac[]) >> metis_tac[]) >>
  `!l bb. lookup_block l f.cf_fn.fn_blocks = SOME bb ==>
    EVERY (\h. h.inst_opcode <> PHI) bb.bb_instructions` by
    (fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[lookup_block_member_label]) >>
  `j.inst_opcode <> PHI` by
    (drule_all scfg_chain_no_phi_insts >>
     fs[active_inst_def, fn_insts_def, EVERY_MEM, fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `?h. active_inst f.cf_fn h (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)` by
    metis_tac[scfg_chain_active_dispatch] >>
  `?r. fn_entry_state f.cf_fn r /\
    frame_reach C f.cf_fn r h (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)` by
    (irule scfg_frame_reachable_entry_root >>
     fs[scfg_merge_context_def] >> metis_tac[]) >>
  `~(s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx).vs_halted` by
    metis_tac[supply_frame_reach_not_halted, fn_entry_state_def] >>
  `?q. frame_reachable vs C fs g.cf_params
    (DRESTRICT g.cf_prov (COMPL (set g.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT g.cf_tvar (COMPL (set g.cf_inst.inst_outputs)))
    f.cf_fn j q /\ scfg_chain_segment a b q
      (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx) /\
    scfg_data_agree q (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx)` by
    (irule scfg_chain_normalize_ghosts >>
     fs[scfg_merge_context_def] >>
     conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     reverse conj_tac >- metis_tac[] >>
     qexists_tac `s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx` >> simp[]) >>
  simp[scfg_merge_witness_def] >> qexistsl_tac [`fs`, `f.cf_fn`, `q`] >>
  simp[scfg_merge_pos_def] >> metis_tac[]
QED

Theorem scfg_merge_witness_ret:
  scfg_merge_context C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  scfg_merge_witness vs C (g::stk) PG G tn callee ri t /\
  active_inst callee ri t /\ step_inst k C' ri t = IntRet ret v /\
  bind_outputs g.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state g.cf_state v)) = SOME t' /\
  active_inst g.cf_fn j (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx) ==>
  scfg_merge_witness vs C stk g.cf_params
    (DRESTRICT g.cf_prov (COMPL (set g.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT g.cf_tvar (COMPL (set g.cf_inst.inst_outputs)))
    g.cf_fn j (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx)
Proof
  strip_tac >> drule_all scfg_merge_witness_root >> strip_tac >>
  `active_inst f ri s` by metis_tac[frame_reach_active] >>
  fs[scfg_saved_stack_cons] >> gvs[] >> rename1 `scfg_saved_call scfg_merge_pos saved g` >>
  `scfg_merge_pos saved.cf_fn saved.cf_inst saved.cf_state
     g.cf_fn g.cf_inst g.cf_state` by
    fs[scfg_saved_call_def, scfg_saved_frame_def] >>
  qpat_x_assum `scfg_merge_pos saved.cf_fn _ _ _ _ _` mp_tac >>
  simp[scfg_merge_pos_def] >> strip_tac
  >- (drule_all scfg_data_agree_intret >>
      disch_then (qspec_then `C` strip_assume_tac) >>
      `bind_outputs saved.cf_inst.inst_outputs ret.iret_values
        (adopt_return_fmp ret (merge_callee_state saved.cf_state u)) = SOME t'` by
        metis_tac[scfg_same_saved_return_back] >>
      `saved.cf_params = g.cf_params /\ saved.cf_prov = g.cf_prov /\
       saved.cf_tvar = g.cf_tvar /\ saved.cf_inst.inst_outputs = g.cf_inst.inst_outputs` by
        metis_tac[scfg_saved_call_def, scfg_saved_frame_ghosts] >>
      `frame_reachable vs C rest saved.cf_params
        (DRESTRICT saved.cf_prov (COMPL (set saved.cf_inst.inst_outputs)))
        (tn with t_var := DRESTRICT saved.cf_tvar (COMPL (set saved.cf_inst.inst_outputs)))
        saved.cf_fn j (t' with vs_inst_idx := SUC saved.cf_state.vs_inst_idx)` by
        (irule frame_reachable_ret >> metis_tac[]) >>
      simp[scfg_merge_witness_def] >>
      qexistsl_tac [`rest`, `saved.cf_fn`, `t' with vs_inst_idx := SUC saved.cf_state.vs_inst_idx`] >>
      simp[scfg_merge_pos_def] >> metis_tac[]) >>
  `scfg_rooted C (saved::rest) f ri s` by
    (irule scfg_frame_reachable_rooted >>
     fs[scfg_merge_context_def] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> PHI) (fn_insts saved.cf_fn)` by
    (fs[scfg_rooted_def] >> drule scfg_root_history_cons >> strip_tac >>
     drule scfg_root_history_lookup >> fs[scfg_merge_context_def] >> metis_tac[]) >>
  irule scfg_chain_witness_ret >> metis_tac[]
QED

Theorem scfg_merge_frame_witness:
  !vs C' stk PG G tn g i t.
  frame_reachable vs C' stk PG G tn g i t ==>
  !C. scfg_merge_context C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted ==>
  scfg_merge_witness vs C stk PG G tn g i t
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >> rpt strip_tac
  >- (irule scfg_merge_witness_entry >> metis_tac[])
  >- (irule scfg_merge_witness_next >> metis_tac[])
  >- (irule scfg_merge_witness_block >> metis_tac[])
  >- (irule scfg_merge_witness_call >> metis_tac[])
  >> irule scfg_merge_witness_ret >> metis_tac[]
QED

Theorem scfg_merge_frame_back:
  scfg_merge_context C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  frame_reachable vs C' stk PG G tn g i t ==>
  ?fs f s. frame_reachable vs C fs PG G tn f i s /\
    scfg_saved_stack scfg_merge_pos fs stk /\
    scfg_merge_pos f i s g i t /\ scfg_data_agree s t
Proof
  strip_tac >> drule_all scfg_merge_frame_witness >>
  simp[scfg_merge_witness_def] >> metis_tac[scfg_merge_pos_data]
QED

Definition scfg_restrict_pos_def:
  scfg_restrict_pos f i s g j t <=>
    g = remove_unreachable_blocks f /\ i = j /\ s = t
End

Definition scfg_restrict_context_def:
  scfg_restrict_context C C' <=>
    C'.ctx_entry = C.ctx_entry /\
    C'.ctx_functions = MAP remove_unreachable_blocks C.ctx_functions /\
    EVERY wf_function C.ctx_functions /\
    EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)) C.ctx_functions
End

Definition scfg_restrict_witness_def:
  scfg_restrict_witness vs C stk PG G tn g i s <=>
    ?fs f nm. lookup_function nm C.ctx_functions = SOME f /\
      frame_reachable vs C fs PG G tn f i s /\
      scfg_saved_stack scfg_restrict_pos fs stk /\ g = remove_unreachable_blocks f
End

Theorem scfg_restrict_lookup:
  scfg_restrict_context C C' /\ lookup_function nm C'.ctx_functions = SOME g ==>
  ?f. lookup_function nm C.ctx_functions = SOME f /\
    g = remove_unreachable_blocks f /\ wf_function f /\
    EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)
Proof
  strip_tac >>
  `!f. (remove_unreachable_blocks f).fn_name = f.fn_name` by
    (gen_tac >> Cases_on `fn_entry_label f` >> simp[remove_unreachable_blocks_def]) >>
  `lookup_function nm C'.ctx_functions =
    OPTION_MAP remove_unreachable_blocks (lookup_function nm C.ctx_functions)` by
    (fs[scfg_restrict_context_def] >>
     metis_tac[lookup_function_map, optionTheory.OPTION_MAP_EQ_SOME]) >>
  Cases_on `lookup_function nm C.ctx_functions` >> gvs[] >>
  fs[scfg_restrict_context_def, EVERY_MEM] >> metis_tac[lookup_function_MEM]
QED

Theorem scfg_restrict_setup:
  wf_function f ==>
  setup_callee (remove_unreachable_blocks f) args s = setup_callee f args s
Proof
  strip_tac >> irule scfg_setup_callee_agree >>
  simp[scfg_data_agree_refl, remove_unreachable_blocks_entry, wf_function_def]
QED

Theorem scfg_restrict_witness_entry:
  scfg_restrict_context C C' /\ C'.ctx_entry = SOME name /\
  lookup_function name C'.ctx_functions = SOME g /\ fn_entry_label g = SOME lbl /\
  enters_block g
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s /\
  active_inst g i s ==>
  scfg_restrict_witness vs C [] [] FEMPTY entry_taint g i s
Proof
  strip_tac >> drule_all scfg_restrict_lookup >> strip_tac >> gvs[] >>
  `ALL_DISTINCT (fn_labels f)` by metis_tac[wf_function_def] >>
  `fn_entry_label f = SOME lbl` by
    metis_tac[remove_unreachable_blocks_entry, wf_function_def] >>
  `enters_block f
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s` by
    metis_tac[scfg_restriction_enters_back] >>
  `active_inst f i s` by metis_tac[scfg_restriction_active_back] >>
  simp[scfg_restrict_witness_def] >> qexistsl_tac [`[]`, `f`, `name`] >> simp[] >>
  irule frame_reachable_entry >> fs[scfg_restrict_context_def] >> metis_tac[]
QED

Theorem scfg_restrict_entry_ghosts:
  EVERY (\i. i.inst_opcode <> PHI) (fn_insts f) ==>
  entry_prov f s G = G /\ entry_taint_vars f s tn = tn /\
  entry_prov (remove_unreachable_blocks f) s G = G /\
  entry_taint_vars (remove_unreachable_blocks f) s tn = tn
Proof
  strip_tac >>
  `!l bb. lookup_block l f.fn_blocks = SOME bb ==>
    EVERY (\h. h.inst_opcode <> PHI) bb.bb_instructions` by
    (fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[lookup_block_member_label]) >>
  `EVERY (\i. i.inst_opcode <> PHI) (fn_insts (remove_unreachable_blocks f))` by
    (fs[EVERY_MEM] >> ho_match_mp_tac remove_unreachable_blocks_inst_property >> metis_tac[]) >>
  `!l bb. lookup_block l (remove_unreachable_blocks f).fn_blocks = SOME bb ==>
    EVERY (\h. h.inst_opcode <> PHI) bb.bb_instructions` by
    (fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[lookup_block_member_label]) >>
  metis_tac[scfg_entry_prov_no_phi, scfg_entry_taint_no_phi]
QED

Theorem scfg_restrict_witness_next:
  scfg_restrict_witness vs C stk PG G tn g inst s /\ active_inst g inst s /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst k C' inst s = OK v /\
  active_inst g j (v with vs_inst_idx := SUC s.vs_inst_idx) ==>
  scfg_restrict_witness vs C stk PG (step_prov PG G inst v)
    (step_taint inst s v tn) g j (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  simp[scfg_restrict_witness_def] >> rpt strip_tac >> gvs[] >>
  `step_inst k C inst s = OK v` by gvs[step_inst_non_invoke] >>
  qexistsl_tac [`fs`, `f`, `nm`] >> simp[] >>
  irule frame_reachable_next >>
  metis_tac[scfg_restriction_active_back]
QED

Theorem scfg_restrict_witness_block:
  scfg_restrict_context C C' /\
  scfg_restrict_witness vs C stk PG G tn g inst s /\ active_inst g inst s /\
  is_terminator inst.inst_opcode /\ step_inst k C' inst s = OK v /\
  ~v.vs_halted /\ enters_block g v t /\ active_inst g j t ==>
  scfg_restrict_witness vs C stk PG (entry_prov g v G)
    (entry_taint_vars g v tn) g j t
Proof
  simp[scfg_restrict_witness_def] >> rpt strip_tac >> gvs[] >>
  `wf_function f /\ EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)` by
    (fs[scfg_restrict_context_def, EVERY_MEM] >> metis_tac[lookup_function_MEM]) >>
  `ALL_DISTINCT (fn_labels f)` by metis_tac[wf_function_def] >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  `step_inst k C inst s = OK v` by gvs[step_inst_non_invoke] >>
  drule_all scfg_restrict_entry_ghosts >> strip_tac >>
  qexistsl_tac [`fs`, `f`, `nm`] >> simp[] >>
  `frame_reachable vs C fs PG (entry_prov f v G)
    (entry_taint_vars f v tn) f j t` by
    (irule frame_reachable_block >>
     metis_tac[scfg_restriction_active_back, scfg_restriction_enters_back]) >>
  metis_tac[]
QED

Theorem scfg_restrict_witness_call:
  scfg_restrict_context C C' /\
  scfg_restrict_witness vs C stk PG G tn caller inst s /\
  active_inst caller inst s /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm, ops) /\
  lookup_function nm C'.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME ct /\
  enters_block callee ct t /\ active_inst callee i t ==>
  scfg_restrict_witness vs C
    (<|cf_fn := caller; cf_inst := inst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee i t
Proof
  strip_tac >> drule_all scfg_restrict_lookup >> strip_tac >>
  qpat_x_assum `scfg_restrict_witness _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[scfg_restrict_witness_def] >> strip_tac >> gvs[] >>
  rename1 `frame_reachable vs C fs PG G tn caller0 inst s` >>
  `setup_callee f args s = SOME ct` by metis_tac[scfg_restrict_setup] >>
  `ALL_DISTINCT (fn_labels f)` by metis_tac[wf_function_def] >>
  `active_inst caller0 inst s /\ enters_block f ct t /\ active_inst f i t` by
    metis_tac[scfg_restriction_active_back, scfg_restriction_enters_back] >>
  qexistsl_tac [`<|cf_fn := caller0; cf_inst := inst; cf_state := s;
     cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: fs`, `f`, `nm`] >>
  simp[scfg_saved_stack_def, scfg_saved_call_def, scfg_saved_frame_def,
       scfg_restrict_pos_def, scfg_data_agree_refl] >>
  conj_tac >- (irule frame_reachable_call >> metis_tac[]) >>
  fs[scfg_saved_stack_def]
QED

Theorem scfg_restrict_witness_ret:
  scfg_restrict_context C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  scfg_restrict_witness vs C (g::stk) PG G tn callee ri s /\
  active_inst callee ri s /\ step_inst k C' ri s = IntRet ret v /\
  bind_outputs g.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state g.cf_state v)) = SOME t /\
  active_inst g.cf_fn j (t with vs_inst_idx := SUC g.cf_state.vs_inst_idx) ==>
  scfg_restrict_witness vs C stk g.cf_params
    (DRESTRICT g.cf_prov (COMPL (set g.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT g.cf_tvar (COMPL (set g.cf_inst.inst_outputs)))
    g.cf_fn j (t with vs_inst_idx := SUC g.cf_state.vs_inst_idx)
Proof
  simp[scfg_restrict_witness_def] >> rpt strip_tac >>
  fs[scfg_saved_stack_cons, scfg_saved_call_def, scfg_saved_frame_def,
     scfg_restrict_pos_def] >> gvs[] >>
  `ri.inst_opcode <> INVOKE` by metis_tac[step_inst_intret_not_invoke] >>
  `step_inst k C ri s = IntRet ret v` by gvs[step_inst_non_invoke] >>
  `scfg_rooted C (f'::rest) f ri s` by
    (irule scfg_frame_reachable_rooted >>
     fs[scfg_restrict_context_def, EVERY_MEM] >>
     metis_tac[lookup_function_MEM]) >>
  `?name. lookup_function name C.ctx_functions = SOME f'.cf_fn` by
    (fs[scfg_rooted_def] >> drule scfg_root_history_cons >> strip_tac >>
     metis_tac[scfg_root_history_lookup]) >>
  `frame_reachable vs C rest f'.cf_params
    (DRESTRICT f'.cf_prov (COMPL (set f'.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f'.cf_tvar (COMPL (set f'.cf_inst.inst_outputs)))
    f'.cf_fn j (t with vs_inst_idx := SUC f'.cf_state.vs_inst_idx)` by
    (irule frame_reachable_ret >> metis_tac[scfg_restriction_active_back]) >>
  qexistsl_tac [`rest`, `f'.cf_fn`, `name`] >> gvs[]
QED

Theorem scfg_restrict_frame_witness:
  !vs C' stk PG G tn g i s.
  frame_reachable vs C' stk PG G tn g i s ==>
  !C. scfg_restrict_context C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted ==>
  scfg_restrict_witness vs C stk PG G tn g i s
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >> rpt strip_tac
  >- (irule scfg_restrict_witness_entry >> metis_tac[])
  >- (irule scfg_restrict_witness_next >> metis_tac[])
  >- (irule scfg_restrict_witness_block >> metis_tac[])
  >- (irule scfg_restrict_witness_call >> metis_tac[])
  >> irule scfg_restrict_witness_ret >> metis_tac[]
QED

Theorem scfg_restrict_stack_states:
  !fs gs. scfg_saved_stack scfg_restrict_pos fs gs ==>
  LIST_REL (\f g. f.cf_state = g.cf_state) fs gs
Proof
  Induct_on `fs` >> Cases_on `gs` >>
  simp[scfg_saved_stack_def, scfg_saved_call_def, scfg_saved_frame_def,
       scfg_restrict_pos_def] >> metis_tac[]
QED

Theorem scfg_restrict_frame_back:
  scfg_restrict_context C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  frame_reachable vs C' stk PG G tn g i s ==>
  ?fs f nm. lookup_function nm C.ctx_functions = SOME f /\
    g = remove_unreachable_blocks f /\ frame_reachable vs C fs PG G tn f i s /\
    scfg_saved_stack scfg_restrict_pos fs stk /\
    LIST_REL (\f g. f.cf_state = g.cf_state) fs stk
Proof
  strip_tac >> drule_all scfg_restrict_frame_witness >>
  simp[scfg_restrict_witness_def] >> metis_tac[scfg_restrict_stack_states]
QED

Definition scfg_bypass_pair_def:
  scfg_bypass_pair f g <=>
    EVERY (\i. i.inst_opcode <> PHI) (fn_insts f) /\
    (f = g \/ ?a b. scfg_bypass_hyp f a b g)
End

Definition scfg_bypass_pos_def:
  scfg_bypass_pos f i s g j t <=>
    EVERY (\h. h.inst_opcode <> PHI) (fn_insts f) /\
    ((f = g /\ i = j /\ s = t) \/
     ?a b. scfg_bypass_hyp f a b g /\ scfg_data_agree s t /\
       scfg_bypass_aligned a b s t /\
       j = scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i)
End

Definition scfg_bypass_context_def:
  scfg_bypass_context C C' <=> C.ctx_entry = C'.ctx_entry /\
    (!nm g. lookup_function nm C'.ctx_functions = SOME g ==>
      ?f. lookup_function nm C.ctx_functions = SOME f /\ scfg_bypass_pair f g)
End

Theorem scfg_bypass_pair_entry:
  scfg_bypass_pair f g ==> fn_entry_label f = fn_entry_label g
Proof
  simp[scfg_bypass_pair_def] >> metis_tac[scfg_bypass_entry_eq]
QED

Theorem scfg_bypass_pos_data:
  scfg_bypass_pos f i s g j t ==> scfg_data_agree s t
Proof
  simp[scfg_bypass_pos_def] >> metis_tac[scfg_data_agree_refl]
QED

Theorem scfg_bypass_pos_pair:
  scfg_bypass_pos f i s g j t ==> scfg_bypass_pair f g
Proof
  simp[scfg_bypass_pos_def, scfg_bypass_pair_def] >> metis_tac[]
QED

Theorem scfg_bypass_pos_cases:
  scfg_bypass_pos f i s g j t ==>
  EVERY (\h. h.inst_opcode <> PHI) (fn_insts f) /\
  ((f = g /\ i = j /\ s = t) \/
   ?a b. scfg_bypass_hyp f a b g /\ scfg_data_agree s t /\
     scfg_bypass_aligned a b s t /\
     j = scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i)
Proof
  simp[scfg_bypass_pos_def]
QED

Theorem scfg_bypass_pair_enter:
  scfg_bypass_pair f g /\ fn_entry_label f = SOME r.vs_current_bb /\
  r.vs_prev_bb = NONE /\ enters_block g r t /\ active_inst g j t ==>
  ?s i. enters_block f r s /\ active_inst f i s /\ scfg_bypass_pos f i s g j t
Proof
  simp[scfg_bypass_pair_def] >> strip_tac
  >- (gvs[] >> qexistsl_tac [`t`, `j`] >> simp[scfg_bypass_pos_def]) >>
  `scfg_bypass_aligned a b r r` by
    (fs[fn_entry_state_def, scfg_bypass_aligned_def, scfg_ctrl_def,
        venom_state_component_equality] >>
     metis_tac[scfg_bypass_not_entry_label]) >>
  `!l bb. lookup_block l f.fn_blocks = SOME bb ==>
    EVERY (\h. h.inst_opcode <> PHI) bb.bb_instructions` by
    (fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[lookup_block_member_label]) >>
  drule_all scfg_bypass_no_phi_entry_back >> strip_tac >>
  drule_all scfg_bypass_active_back >> strip_tac >>
  `scfg_data_agree (r with vs_inst_idx := 0) t` by
    fs[scfg_bypass_aligned_def, scfg_ctrl_def, scfg_data_agree_def] >>
  qexistsl_tac [`r with vs_inst_idx := 0`, `i`] >>
  simp[scfg_bypass_pos_def] >> metis_tac[]
QED

Theorem scfg_bypass_pair_initial:
  scfg_bypass_pair f g /\ fn_entry_label g = SOME l /\
  enters_block g
    (vs with <|vs_prev_bb := NONE; vs_current_bb := l; vs_inst_idx := 0|>) t /\
  active_inst g j t ==>
  ?s i. enters_block f
    (vs with <|vs_prev_bb := NONE; vs_current_bb := l; vs_inst_idx := 0|>) s /\
    fn_entry_label f = SOME l /\ active_inst f i s /\ scfg_bypass_pos f i s g j t
Proof
  strip_tac >>
  `fn_entry_label f = SOME l` by metis_tac[scfg_bypass_pair_entry] >>
  `?s i. enters_block f
    (vs with <|vs_prev_bb := NONE; vs_current_bb := l; vs_inst_idx := 0|>) s /\
    active_inst f i s /\ scfg_bypass_pos f i s g j t` by
    (irule scfg_bypass_pair_enter >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem scfg_bypass_pair_callee:
  scfg_bypass_pair f g /\ scfg_data_agree s t /\
  setup_callee g args t = SOME ct /\ enters_block g ct u /\ active_inst g j u ==>
  ?cs v i. setup_callee f args s = SOME cs /\ enters_block f cs v /\
    active_inst f i v /\ scfg_bypass_pos f i v g j u
Proof
  strip_tac >>
  `fn_entry_label f = fn_entry_label g` by metis_tac[scfg_bypass_pair_entry] >>
  `setup_callee f args s = SOME ct` by metis_tac[scfg_setup_callee_agree] >>
  `fn_entry_state f ct` by metis_tac[setup_callee_fn_entry_state] >>
  `?v i. enters_block f ct v /\ active_inst f i v /\ scfg_bypass_pos f i v g j u` by
    (irule scfg_bypass_pair_enter >> fs[fn_entry_state_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem scfg_bypass_context_lookup:
  scfg_bypass_context C C' /\ lookup_function nm C'.ctx_functions = SOME g ==>
  ?f. lookup_function nm C.ctx_functions = SOME f /\ scfg_bypass_pair f g
Proof
  simp[scfg_bypass_context_def]
QED

Theorem scfg_saved_stack_push:
  scfg_saved_stack R fs gs /\ scfg_saved_call R f g ==>
  scfg_saved_stack R (f::fs) (g::gs)
Proof
  simp[scfg_saved_stack_def]
QED

Theorem scfg_bypass_pos_ordinary:
  scfg_bypass_pos f i s g j t /\ active_inst f i s /\
  ~is_terminator j.inst_opcode ==> i = j
Proof
  simp[scfg_bypass_pos_def] >> strip_tac >>
  `i.inst_opcode <> PHI` by
    (fs[active_inst_def, fn_insts_def, EVERY_MEM, fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `j.inst_opcode <> PHI` by gvs[scfg_bypass_image_classes] >>
  metis_tac[scfg_bypass_image_ordinary_inv]
QED

Theorem scfg_bypass_pos_next:
  scfg_bypass_pos f i s g j t /\ active_inst f i s /\
  frame_reachable vs C fs PG G tn f i s /\
  ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
  step_inst k C' j t = OK v /\
  active_inst g h (v with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ?u q. frame_reachable vs C fs PG (step_prov PG G j v)
    (step_taint j t v tn) f q u /\ active_inst f q u /\
    scfg_bypass_pos f q u g h (v with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >> `i = j` by metis_tac[scfg_bypass_pos_ordinary] >> gvs[] >>
  drule scfg_bypass_pos_cases >> strip_tac
  >- (gvs[] >> qexistsl_tac [`v with vs_inst_idx := SUC s.vs_inst_idx`, `h`] >>
      simp[scfg_bypass_pos_def] >> irule frame_reachable_next >>
      gvs[step_inst_non_invoke] >> metis_tac[]) >>
  drule_all scfg_data_agree_ok_back >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  drule_all scfg_bypass_ordinary_advance >> strip_tac >>
  `step_inst k C i t = OK v` by gvs[step_inst_non_invoke] >>
  `scfg_bypass_aligned a b (u with vs_inst_idx := SUC s.vs_inst_idx)
    (v with vs_inst_idx := SUC t.vs_inst_idx)` by metis_tac[exec_result_11] >>
  drule_all scfg_bypass_active_back >> strip_tac >>
  `step_prov PG G i u = step_prov PG G i v /\
   step_taint i s u tn = step_taint i t v tn` by
    metis_tac[scfg_data_agree_step_prov, scfg_data_agree_step_taint] >>
  qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`, `i'`] >>
  conj_tac
  >- (`frame_reachable vs C fs PG (step_prov PG G i u)
         (step_taint i s u tn) f i' (u with vs_inst_idx := SUC s.vs_inst_idx)` by
        (irule frame_reachable_next >> metis_tac[]) >> metis_tac[]) >>
  simp[scfg_bypass_pos_def] >>
  metis_tac[scfg_data_agree_index]
QED

(* Moved from o1ContractSimplifyCfg for the shared return-image boundary. *)
Theorem step_inst_intret_opcodes:
  step_inst fuel C inst s = IntRet vals t ==>
  MEM inst.inst_opcode [RET; RETFMP; DRET]
Proof
  Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[Once step_inst_def] >>
      gvs[AllCaseEqs(), bind_outputs_def]) >>
  simp[step_inst_non_invoke] >> strip_tac >>
  drule step_inst_base_intret_opcodes >> simp[] >> metis_tac[]
QED

Theorem scfg_bypass_pos_intret:
  scfg_bypass_pos f i s g j t /\ active_inst f i s /\
  step_inst k C' j t = IntRet ret u ==> i = j
Proof
  strip_tac >> drule step_inst_intret_opcodes >>
  simp[] >> strip_tac >>
  fs[scfg_bypass_pos_def] >>
  `j.inst_opcode <> JMP` by gvs[] >>
  `i.inst_opcode = j.inst_opcode` by metis_tac[scfg_bypass_image_opcode] >>
  `i.inst_opcode <> PHI /\ is_terminator i.inst_opcode` by
    gvs[is_terminator_def] >>
  `s.vs_current_bb <> a.bb_label` by
    (strip_tac >> drule_all scfg_bypass_active_source_terminator >> gvs[]) >>
  gvs[scfg_bypass_image_def, update_phi_bypass_def]
QED

Theorem scfg_bypass_same_frame_return:
  scfg_saved_call scfg_bypass_pos f g /\ f.cf_fn = g.cf_fn /\
  f.cf_state = g.cf_state /\
  frame_reachable vs C (f::fs) PG G tn fn ri s /\ active_inst fn ri s /\
  scfg_data_agree s t /\ step_inst k C' ri t = IntRet ret v /\
  bind_outputs g.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state g.cf_state v)) = SOME t' /\
  active_inst g.cf_fn j (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx) ==>
  frame_reachable vs C fs g.cf_params
    (DRESTRICT g.cf_prov (COMPL (set g.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT g.cf_tvar (COMPL (set g.cf_inst.inst_outputs)))
    g.cf_fn j (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx)
Proof
  strip_tac >> drule_all scfg_data_agree_intret >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  `bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state u)) = SOME t'` by
    (irule scfg_same_saved_return_back >> metis_tac[]) >>
  `frame_reachable vs C fs f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn j (t' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)` by
    (irule frame_reachable_ret >> metis_tac[]) >>
  gvs[scfg_saved_call_def, scfg_saved_frame_def]
QED

Definition scfg_bypass_witness_def:
  scfg_bypass_witness vs C stk PG G tn g j t <=>
    ?fs f i s. frame_reachable vs C fs PG G tn f i s /\ active_inst f i s /\
      scfg_saved_stack scfg_bypass_pos fs stk /\ scfg_bypass_pos f i s g j t
End

Theorem scfg_bypass_witness_entry:
  scfg_bypass_context C C' /\ C'.ctx_entry = SOME name /\
  lookup_function name C'.ctx_functions = SOME g /\ fn_entry_label g = SOME lbl /\
  enters_block g
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t /\
  active_inst g j t ==>
  scfg_bypass_witness vs C [] [] FEMPTY entry_taint g j t
Proof
  strip_tac >> drule_all scfg_bypass_context_lookup >> strip_tac >>
  drule_all scfg_bypass_pair_initial >> strip_tac >>
  simp[scfg_bypass_witness_def] >> qexistsl_tac [`[]`, `f`, `i`, `s`] >>
  simp[scfg_saved_stack_def] >> irule frame_reachable_entry >>
  fs[scfg_bypass_context_def] >> metis_tac[]
QED

Theorem scfg_bypass_witness_call:
  scfg_bypass_context C C' /\ scfg_bypass_witness vs C stk PG G tn caller inst t /\
  active_inst caller inst t /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm, ops) /\
  lookup_function nm C'.ctx_functions = SOME callee /\
  eval_operands ops t = SOME args /\ setup_callee callee args t = SOME ct /\
  enters_block callee ct v /\ active_inst callee j v ==>
  scfg_bypass_witness vs C
    (<|cf_fn := caller; cf_inst := inst; cf_state := t;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee j v
Proof
  strip_tac >> drule_all scfg_bypass_context_lookup >> strip_tac >>
  qpat_x_assum `scfg_bypass_witness _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[scfg_bypass_witness_def] >> strip_tac >>
  `i = inst` by
    (irule scfg_bypass_pos_ordinary >> simp[is_terminator_def] >> metis_tac[]) >>
  qpat_x_assum `i = inst` SUBST_ALL_TAC >>
  `scfg_data_agree s t` by metis_tac[scfg_bypass_pos_data] >>
  `eval_operands ops s = SOME args` by metis_tac[scfg_data_agree_eval_operands] >>
  drule_all scfg_bypass_pair_callee >> strip_tac >>
  qexistsl_tac [`<|cf_fn := f'; cf_inst := inst; cf_state := s;
    cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: fs`, `f`, `i`, `v'`] >>
  simp[] >> conj_tac
  >- (irule frame_reachable_call >> metis_tac[]) >>
  irule scfg_saved_stack_push >> simp[scfg_saved_call_def, scfg_saved_frame_def] >>
  metis_tac[]
QED

Theorem scfg_bypass_witness_next:
  scfg_bypass_witness vs C stk PG G tn g j t /\
  ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
  step_inst k C' j t = OK v /\
  active_inst g h (v with vs_inst_idx := SUC t.vs_inst_idx) ==>
  scfg_bypass_witness vs C stk PG (step_prov PG G j v)
    (step_taint j t v tn) g h (v with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  simp[scfg_bypass_witness_def] >> strip_tac >>
  drule_all scfg_bypass_pos_next >> strip_tac >> metis_tac[]
QED

Theorem scfg_bypass_witness_block:
  (!nm f. lookup_function nm C.ctx_functions = SOME f ==> wf_function f) /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  scfg_bypass_witness vs C stk PG G tn g j t /\
  is_terminator j.inst_opcode /\ step_inst k C' j t = OK v /\ ~v.vs_halted /\
  enters_block g v y /\ active_inst g h y ==>
  scfg_bypass_witness vs C stk PG (entry_prov g v G) (entry_taint_vars g v tn) g h y
Proof
  simp[scfg_bypass_witness_def] >> strip_tac >>
  drule scfg_bypass_pos_cases >> strip_tac
  >- (gvs[] >> qexistsl_tac [`fs`, `f`, `h`, `y`] >>
      simp[scfg_bypass_pos_def] >> irule frame_reachable_block >>
      `i.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
      simp[] >> qexistsl_tac [`k`, `i`, `s`] >> simp[step_inst_non_invoke] >>
      gvs[step_inst_non_invoke]) >>
  `?r. fn_entry_state f r /\ frame_reach C f r i s` by
    (irule scfg_frame_reachable_entry_root >> metis_tac[]) >>
  `!l bb. lookup_block l f.fn_blocks = SOME bb ==>
    EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions` by
    (fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[lookup_block_member_label]) >>
  `is_terminator i.inst_opcode` by gvs[scfg_bypass_image_classes] >>
  qpat_x_assum `j = _` SUBST_ALL_TAC >>
  drule_all scfg_bypass_block_ghosts_back >> strip_tac >>
  `!l bb. lookup_block l g.fn_blocks = SOME bb ==>
    EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions` by
    (rpt strip_tac >> drule scfg_bypass_lookup_eq >>
     disch_then (qspec_then `l` mp_tac) >>
     Cases_on `lookup_block l f.fn_blocks` >> gvs[] >> strip_tac >>
     gvs[scfg_bypass_block_def, EVERY_MAP] >> metis_tac[]) >>
  `entry_prov g v G = G /\ entry_taint_vars g v tn = tn` by
    metis_tac[scfg_entry_prov_no_phi, scfg_entry_taint_no_phi] >>
  `active_inst f h' x` by metis_tac[frame_reach_active] >>
  `scfg_data_agree x y` by
    fs[scfg_bypass_aligned_def, scfg_ctrl_def, scfg_data_agree_def] >>
  qexistsl_tac [`fs`, `f`, `h'`, `x`] >> simp[scfg_bypass_pos_def] >> metis_tac[]
QED

Theorem scfg_frame_reachable_active:
  !vs C stk PG G tn f i s. frame_reachable vs C stk PG G tn f i s ==>
    active_inst f i s
Proof
  ho_match_mp_tac frame_reachable_ind >> simp[]
QED

Theorem scfg_bypass_witness_ret:
  scfg_bypass_witness vs C (g::stk) PG G tn callee ri t /\
  step_inst k C' ri t = IntRet ret v /\
  bind_outputs g.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state g.cf_state v)) = SOME t' /\
  active_inst g.cf_fn j (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx) ==>
  scfg_bypass_witness vs C stk g.cf_params
    (DRESTRICT g.cf_prov (COMPL (set g.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT g.cf_tvar (COMPL (set g.cf_inst.inst_outputs)))
    g.cf_fn j (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx)
Proof
  simp[scfg_bypass_witness_def] >> strip_tac >>
  `i = ri` by metis_tac[scfg_bypass_pos_intret] >>
  qpat_x_assum `i = ri` SUBST_ALL_TAC >>
  `scfg_data_agree s t` by metis_tac[scfg_bypass_pos_data] >>
  qpat_x_assum `scfg_saved_stack _ _ (_::_)` mp_tac >>
  simp[scfg_saved_stack_cons] >> strip_tac >> gvs[] >>
  `scfg_bypass_pos f'.cf_fn f'.cf_inst f'.cf_state
     g.cf_fn g.cf_inst g.cf_state` by fs[scfg_saved_call_def, scfg_saved_frame_def] >>
  drule scfg_bypass_pos_cases >> strip_tac
  >- (qexistsl_tac [`rest`, `g.cf_fn`, `j`,
        `t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx`] >>
      simp[scfg_bypass_pos_def] >> conj_tac
      >- (irule scfg_bypass_same_frame_return >> metis_tac[]) >> gvs[]) >>
  drule_all scfg_bypass_frame_return_back >> strip_tac >>
  `active_inst f'.cf_fn h q` by metis_tac[scfg_frame_reachable_active] >>
  qexistsl_tac [`rest`, `f'.cf_fn`, `h`, `q`] >>
  simp[scfg_bypass_pos_def] >> metis_tac[]
QED

Theorem scfg_bypass_context_reachable:
  !vs C' stk PG G tn g j t.
  frame_reachable vs C' stk PG G tn g j t ==>
  !C. scfg_bypass_context C C' /\
  (!nm f. lookup_function nm C.ctx_functions = SOME f ==> wf_function f) /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted ==>
  scfg_bypass_witness vs C stk PG G tn g j t
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >> rpt strip_tac
  >- (irule scfg_bypass_witness_entry >> metis_tac[])
  >- (irule scfg_bypass_witness_next >> metis_tac[])
  >- (irule scfg_bypass_witness_block >> metis_tac[])
  >- (irule scfg_bypass_witness_call >> metis_tac[])
  >> irule scfg_bypass_witness_ret >> metis_tac[]
QED

Theorem scfg_restrict_pos_observations:
  wf_function f /\ scfg_restrict_pos f i s g j t /\ active_inst g j t ==>
  scfg_data_agree s t /\ i = j /\
  (in_revert_forward f s ==> in_revert_forward g t) /\
  (about_to_revert f i s ==> about_to_revert g j t)
Proof
  strip_tac >> fs[scfg_restrict_pos_def] >> gvs[] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) (remove_unreachable_blocks f).fn_blocks)` by
    metis_tac[simplifyCfgLabelPropsTheory.fn_labels_remove_unreachable_all_distinct,
              wf_function_def, fn_labels_def] >>
  `?bb. lookup_block s.vs_current_bb (remove_unreachable_blocks f).fn_blocks = SOME bb` by
    (fs[active_inst_def] >> metis_tac[venomExecProofsTheory.MEM_lookup_block]) >>
  `lookup_block s.vs_current_bb f.fn_blocks = SOME bb` by
    metis_tac[simplifyCfgRestrictionTheory.scfg_restriction_lookup_back, wf_function_def] >>
  simp[scfg_data_agree_def, in_revert_forward_def, about_to_revert_def,
       active_inst_def] >>
  fs[wf_function_def, fn_labels_def] >>
  metis_tac[venomExecProofsTheory.MEM_lookup_block,
    venomExecProofsTheory.lookup_block_MEM, venomExecProofsTheory.lookup_block_label]
QED

Theorem scfg_same_after_assigns_append:
  !xs op1 op2. same_after_assigns xs op1 op2 ==>
    !ys. same_after_assigns (xs ++ ys) op1 op2
Proof
  Induct_on `xs`
  >- (simp[same_after_assigns_def] >> rpt strip_tac >>
      Cases_on `ys` >> simp[same_after_assigns_def]) >>
  simp[same_after_assigns_def] >> rpt gen_tac >>
  Cases_on `op1 = op2` >> simp[] >>
  Cases_on `step_back_assign h op1` >> simp[] >>
  Cases_on `step_back_assign h op2` >> simp[]
QED

Theorem scfg_revert_forward_pair_cons:
  revert_forward_pair bb i j ==>
  revert_forward_pair (bb with bb_instructions := h::bb.bb_instructions) (SUC i) (SUC j)
Proof
  simp[revert_forward_pair_def, get_instruction_def] >> strip_tac >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> Cases_on `k` >> gvs[] >> metis_tac[]) >>
  metis_tac[scfg_same_after_assigns_append]
QED

Theorem scfg_revert_forward_pair_prefix:
  !xs bb i j. revert_forward_pair bb i j ==>
  revert_forward_pair (bb with bb_instructions := xs ++ bb.bb_instructions)
    (LENGTH xs + i) (LENGTH xs + j)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule scfg_revert_forward_pair_cons >>
  disch_then (qspec_then `h` mp_tac) >> simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem scfg_revert_forward_pair_suffix:
  revert_forward_pair bb i j ==>
  revert_forward_pair (bb with bb_instructions := bb.bb_instructions ++ ys) i j
Proof
  simp[revert_forward_pair_def, get_instruction_def] >> strip_tac >>
  `i - LENGTH bb.bb_instructions = 0 /\
   SUC i - LENGTH bb.bb_instructions = 0 /\
   (j - SUC i) - LENGTH (DROP (SUC i) bb.bb_instructions) = 0` by
    (simp[] >> decide_tac) >>
  simp[listTheory.EL_APPEND_EQN, rich_listTheory.TAKE_APPEND, DROP_APPEND]
QED

Theorem scfg_revert_forward_pair_take:
  revert_forward_pair bb i j /\ j < n ==>
  revert_forward_pair (bb with bb_instructions := TAKE n bb.bb_instructions) i j
Proof
  simp[revert_forward_pair_def, get_instruction_def] >> strip_tac >>
  simp[listTheory.EL_TAKE, rich_listTheory.TAKE_TAKE, listTheory.DROP_TAKE] >>
  simp[listTheory.LENGTH_TAKE_EQ, listTheory.TAKE_TAKE_MIN, arithmeticTheory.MIN_DEF]
QED

Theorem scfg_chain_block_no_phi_instructions:
  no_phis a /\ no_phis b /\ no_phis bb ==>
  (scfg_chain_block a b bb).bb_instructions =
    if bb.bb_label = a.bb_label then FRONT a.bb_instructions ++ b.bb_instructions
    else bb.bb_instructions
Proof
  strip_tac >> simp[scfg_chain_block_def] >>
  GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM MAP_ID] >>
  irule MAP_CONG >> simp[] >>
  fs[no_phis_def, EVERY_MEM] >> rpt strip_tac >>
  irule scfg_phi_image_nonphi >>
  Cases_on `bb.bb_label = a.bb_label` >> gvs[MEM_APPEND] >>
  Cases_on `a.bb_instructions = []` >> gvs[] >>
  qspec_then `a.bb_instructions` mp_tac listTheory.APPEND_FRONT_LAST >>
  simp[] >> metis_tac[MEM_APPEND]
QED

Theorem scfg_chain_left_no_revert:
  scfg_chain_hyp f a b /\ get_instruction a k = SOME r ==>
  r.inst_opcode <> REVERT
Proof
  strip_tac >> drule scfg_chain_transfer_shape >> strip_tac >>
  `bb_well_formed a` by
    (drule scfg_chain_old_wf >>
     fs[wf_function_def, EVERY_MEM, scfg_chain_hyp_def] >>
     metis_tac[lookup_block_member_label]) >>
  strip_tac >>
  `MEM r a.bb_instructions` by
    (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[EL_MEM]) >>
  `r = LAST a.bb_instructions` by
    (irule bb_well_formed_terminator_last >> simp[is_terminator_def]) >> gvs[]
QED

Theorem scfg_chain_block_pair_right:
  no_phis a /\ no_phis b /\ revert_forward_pair b i j ==>
  revert_forward_pair (scfg_chain_block a b a)
    (LENGTH (FRONT a.bb_instructions) + i)
    (LENGTH (FRONT a.bb_instructions) + j)
Proof
  strip_tac >> drule scfg_revert_forward_pair_prefix >>
  disch_then (qspec_then `FRONT a.bb_instructions` mp_tac) >>
  simp[revert_forward_pair_def, get_instruction_def,
       scfg_chain_block_no_phi_instructions]
QED

Theorem scfg_chain_block_pair_other:
  no_phis a /\ no_phis b /\ no_phis bb /\ bb.bb_label <> a.bb_label /\
  revert_forward_pair bb i j ==>
  revert_forward_pair (scfg_chain_block a b bb) i j
Proof
  simp[revert_forward_pair_def, get_instruction_def,
       scfg_chain_block_no_phi_instructions]
QED

Theorem scfg_bypass_left_no_revert:
  scfg_bypass_hyp f a b g /\ get_instruction a k = SOME r ==>
  r.inst_opcode <> REVERT
Proof
  strip_tac >>
  `wf_function f` by metis_tac[scfg_bypass_base_hyp] >>
  `bb_well_formed a` by
    (fs[wf_function_def, EVERY_MEM, scfg_bypass_hyp_def] >>
     metis_tac[lookup_block_member_label]) >>
  strip_tac >>
  `MEM r a.bb_instructions` by
    (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[EL_MEM]) >>
  `r = LAST a.bb_instructions` by
    (irule bb_well_formed_terminator_last >> simp[is_terminator_def]) >>
  drule scfg_bypass_source_shape >> gvs[]
QED

Theorem scfg_bypass_block_no_phi_other:
  no_phis bb /\ bb.bb_label <> a.bb_label ==>
  (scfg_bypass_block a b bb).bb_instructions = bb.bb_instructions
Proof
  strip_tac >> simp[scfg_bypass_block_def] >>
  GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM MAP_ID] >>
  irule MAP_CONG >> simp[] >>
  fs[no_phis_def, EVERY_MEM] >> rpt strip_tac >>
  simp[scfg_bypass_image_def, update_phi_bypass_def]
QED

Theorem scfg_bypass_block_revert_instructions:
  scfg_bypass_hyp f a b g /\ lookup_block bb.bb_label f.fn_blocks = SOME bb /\
  no_phis bb /\ get_instruction bb k = SOME r /\ r.inst_opcode = REVERT ==>
  (scfg_bypass_block a b bb).bb_instructions = bb.bb_instructions
Proof
  strip_tac >> irule scfg_bypass_block_no_phi_other >> simp[] >>
  strip_tac >>
  `bb = a` by metis_tac[scfg_bypass_hyp_def, optionTheory.SOME_11] >>
  metis_tac[scfg_bypass_left_no_revert]
QED

Theorem scfg_bypass_block_pair:
  scfg_bypass_hyp f a b g /\ lookup_block bb.bb_label f.fn_blocks = SOME bb /\
  no_phis bb /\ revert_forward_pair bb i j ==>
  revert_forward_pair (scfg_bypass_block a b bb) i j
Proof
  strip_tac >>
  `(scfg_bypass_block a b bb).bb_instructions = bb.bb_instructions` by
    (irule scfg_bypass_block_revert_instructions >>
     fs[revert_forward_pair_def] >> metis_tac[]) >>
  fs[revert_forward_pair_def, get_instruction_def]
QED

Theorem scfg_chain_block_revert_adjacent_right:
  scfg_chain_hyp f a b /\ get_instruction b k = SOME i /\
  get_instruction b (SUC k) = SOME r /\
  i.inst_opcode = RETURNDATACOPY /\ r.inst_opcode = REVERT ==>
  get_instruction (scfg_chain_block a b a)
    (LENGTH (FRONT a.bb_instructions) + k) = SOME i /\
  get_instruction (scfg_chain_block a b a)
    (SUC (LENGTH (FRONT a.bb_instructions) + k)) = SOME r
Proof
  strip_tac >>
  `k < LENGTH b.bb_instructions /\ SUC k < LENGTH b.bb_instructions /\
   EL k b.bb_instructions = i /\ EL (SUC k) b.bb_instructions = r` by
    fs[get_instruction_def, AllCaseEqs()] >>
  `get_instruction (scfg_chain_block a b a)
    (LENGTH (FRONT a.bb_instructions) + k) = SOME i` by
    metis_tac[scfg_chain_instruction_right_nonphi] >>
  `get_instruction (scfg_chain_block a b a)
    (LENGTH (FRONT a.bb_instructions) + SUC k) = SOME r` by
    metis_tac[scfg_chain_instruction_right_nonphi] >>
  gvs[arithmeticTheory.ADD_CLAUSES]
QED

Theorem scfg_bypass_block_revert_adjacent:
  scfg_bypass_hyp f a b g /\ lookup_block bb.bb_label f.fn_blocks = SOME bb /\
  no_phis bb /\ get_instruction bb k = SOME i /\
  get_instruction bb (SUC k) = SOME r /\
  i.inst_opcode = RETURNDATACOPY /\ r.inst_opcode = REVERT ==>
  get_instruction (scfg_bypass_block a b bb) k = SOME i /\
  get_instruction (scfg_bypass_block a b bb) (SUC k) = SOME r
Proof
  strip_tac >>
  `(scfg_bypass_block a b bb).bb_instructions = bb.bb_instructions` by
    (irule scfg_bypass_block_revert_instructions >> metis_tac[]) >>
  fs[get_instruction_def]
QED

Theorem scfg_bypass_pos_revert_forward:
  wf_function f /\ scfg_bypass_pos f i s g j t /\
  active_inst f i s /\ active_inst g j t ==>
  (in_revert_forward f s ==> in_revert_forward g t)
Proof
  strip_tac >> drule scfg_bypass_pos_cases >> strip_tac
  >- gvs[] >>
  simp[in_revert_forward_def, revert_forward_at_def] >> strip_tac >>
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_member_label] >>
  `no_phis bb` by
    (fs[no_phis_def, EVERY_MEM] >>
     metis_tac[unitLabelMapIdentityTheory.fn_insts_MEM, lookup_block_member_label]) >>
  `lookup_block t.vs_current_bb g.fn_blocks = SOME (scfg_bypass_block a b bb)` by
    (drule scfg_bypass_lookup_eq >>
     disch_then (qspec_then `s.vs_current_bb` mp_tac) >>
     fs[scfg_bypass_aligned_def, scfg_ctrl_def]) >>
  `t.vs_inst_idx = s.vs_inst_idx` by fs[scfg_bypass_aligned_def, scfg_ctrl_def] >>
  qexists_tac `scfg_bypass_block a b bb` >> simp[] >>
  metis_tac[scfg_bypass_block_pair]
QED

Theorem scfg_bypass_pos_about_to_revert:
  wf_function f /\ scfg_bypass_pos f i s g j t /\
  active_inst f i s /\ active_inst g j t ==>
  (about_to_revert f i s ==> about_to_revert g j t)
Proof
  strip_tac >> drule scfg_bypass_pos_cases >> strip_tac
  >- gvs[] >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb f.fn_blocks = SOME bb` by
    (fs[active_inst_def, wf_function_def, fn_labels_def] >>
     metis_tac[venomExecProofsTheory.MEM_lookup_block]) >>
  `get_instruction bb s.vs_inst_idx = SOME i` by metis_tac[scfg_active_lookup] >>
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_member_label] >>
  `no_phis bb` by
    (fs[no_phis_def, EVERY_MEM] >>
     metis_tac[unitLabelMapIdentityTheory.fn_insts_MEM, lookup_block_member_label]) >>
  `?k r. get_instruction bb k = SOME r /\ r.inst_opcode = REVERT` by
    (Cases_on `i.inst_opcode = REVERT`
     >- (qexistsl_tac [`s.vs_inst_idx`, `i`] >> simp[]) >>
     fs[about_to_revert_def] >>
     qexistsl_tac [`SUC s.vs_inst_idx`, `rinst`] >> simp[] >>
     qspecl_then [`f`, `rinst`, `s with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac
       (Q.GENL [`fn`, `i`, `t`] scfg_active_lookup) >> simp[]) >>
  `(scfg_bypass_block a b bb).bb_instructions = bb.bb_instructions` by
    (irule scfg_bypass_block_revert_instructions >> metis_tac[]) >>
  `lookup_block t.vs_current_bb g.fn_blocks = SOME (scfg_bypass_block a b bb)` by
    (drule scfg_bypass_lookup_eq >>
     disch_then (qspec_then `s.vs_current_bb` mp_tac) >>
     fs[scfg_bypass_aligned_def, scfg_ctrl_def]) >>
  `wf_function g` by
    metis_tac[simplifyCfgBypassPreconditionTheory.scfg_bypass_normalized,
      simplifyCfgStaticInterfaceTheory.scfg_normalized_static,
      simplifyCfgStaticInterfaceTheory.scfg_static_wf] >>
  `get_instruction (scfg_bypass_block a b bb) t.vs_inst_idx = SOME j` by
    metis_tac[scfg_active_lookup] >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx` by
    fs[scfg_bypass_aligned_def, scfg_ctrl_def] >>
  `i = j` by gvs[get_instruction_def] >>
  qpat_x_assum `j = scfg_bypass_image _ _ _ _ _` kall_tac >>
  qpat_x_assum `i = j` SUBST_ALL_TAC >>
  fs[about_to_revert_def] >>
  qexists_tac `rinst` >> simp[] >>
  irule scfg_lookup_active >>
  qexistsl_tac [`t`, `scfg_bypass_block a b bb`] >> simp[] >>
  qspecl_then [`f`, `rinst`, `s with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac
    (Q.GENL [`fn`, `i`, `t`] scfg_active_lookup) >>
  simp[get_instruction_def]
QED

Theorem scfg_merge_pos_revert_forward:
  wf_function f /\ EVERY (\h. h.inst_opcode <> PHI) (fn_insts f) /\
  scfg_merge_pos f i s g j t /\ active_inst f i s /\ active_inst g j t ==>
  (in_revert_forward f s ==> in_revert_forward g t)
Proof
  simp[scfg_merge_pos_def] >> strip_tac
  >- gvs[] >>
  simp[in_revert_forward_def] >> strip_tac >>
  `MEM bb f.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_member_label] >>
  `no_phis a /\ no_phis b /\ no_phis bb` by
    (fs[no_phis_def, EVERY_MEM, scfg_chain_hyp_def] >>
     metis_tac[unitLabelMapIdentityTheory.fn_insts_MEM, lookup_block_member_label]) >>
  fs[scfg_chain_segment_def]
  >- (`bb = a` by (fs[scfg_chain_hyp_def] >> gvs[]) >> gvs[] >>
      fs[revert_forward_at_def, revert_forward_pair_def] >>
      metis_tac[scfg_chain_left_no_revert])
  >- (`bb = b` by (fs[scfg_chain_hyp_def] >> gvs[]) >> gvs[] >>
      qexists_tac `scfg_chain_block a b a` >> conj_tac
      >- metis_tac[scfg_chain_lookup_member, scfg_chain_hyp_def,
           lookup_block_member_label, scfg_chain_distinct_labels] >>
      fs[revert_forward_at_def] >>
      metis_tac[scfg_chain_block_pair_right]) >>
  qexists_tac `scfg_chain_block a b bb` >> conj_tac
  >- metis_tac[scfg_chain_lookup_member] >>
  fs[revert_forward_at_def] >> metis_tac[scfg_chain_block_pair_other]
QED

Theorem scfg_merge_pos_about_to_revert:
  wf_function f /\ EVERY (\h. h.inst_opcode <> PHI) (fn_insts f) /\
  scfg_merge_pos f i s g j t /\ active_inst f i s /\ active_inst g j t ==>
  (about_to_revert f i s ==> about_to_revert g j t)
Proof
  simp[scfg_merge_pos_def] >> strip_tac
  >- gvs[] >>
  simp[about_to_revert_def] >> strip_tac >- simp[] >>
  simp[] >>
  `?bb. lookup_block s.vs_current_bb f.fn_blocks = SOME bb` by
    (fs[active_inst_def, wf_function_def, fn_labels_def] >>
     metis_tac[venomExecProofsTheory.MEM_lookup_block]) >>
  `get_instruction bb (SUC s.vs_inst_idx) = SOME rinst` by
    (qspecl_then [`f`, `rinst`, `s with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac
       (Q.GENL [`fn`, `i`, `t`] scfg_active_lookup) >> simp[]) >>
  `s.vs_current_bb <> a.bb_label` by
    (strip_tac >>
     `bb = a` by (fs[scfg_chain_hyp_def] >> gvs[]) >>
     metis_tac[scfg_chain_left_no_revert]) >>
  `scfg_chain_segment a b (s with vs_inst_idx := SUC s.vs_inst_idx)
     (t with vs_inst_idx := SUC t.vs_inst_idx)` by
    (fs[scfg_chain_segment_def] >>
     simp[scfg_chain_segment_def, scfg_payload_def, scfg_ctrl_def] >>
     fs[scfg_payload_def, scfg_ctrl_def] >>
     qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >>
     simp[venom_state_component_equality]) >>
  `?bt. lookup_block t.vs_current_bb (scfg_chain f a b).fn_blocks = SOME bt /\
     get_instruction bt (SUC t.vs_inst_idx) = SOME rinst` by
    (qpat_assum `scfg_chain_segment _ _ (s with vs_inst_idx := _) _`
       (mp_then Any mp_tac scfg_chain_segment_instruction) >>
     simp[]) >>
  qexists_tac `rinst` >> simp[] >>
  irule scfg_lookup_active >> qexistsl_tac [`t`, `bt`] >> simp[] >>
  metis_tac[lookup_block_member_label]
QED

Theorem scfg_data_agree_read_ranges:
  scfg_data_agree s t ==>
  source_memory_read_ranges inst s = source_memory_read_ranges inst t
Proof
  strip_tac >>
  `(!op. eval_operand op s = eval_operand op t)` by
    metis_tac[scfg_data_agree_eval_operand] >>
  `(!ops. eval_operands ops s = eval_operands ops t)` by
    metis_tac[scfg_data_agree_eval_operands] >>
  simp[source_memory_read_ranges_def, memory_range_of_operands_def,
       dret_memory_read_ranges_def]
QED

Theorem scfg_taint_ok_transport:
  scfg_data_agree s t /\
  (about_to_revert f i s ==> about_to_revert g i t) /\
  taint_ok f tn i s ==> taint_ok g tn i t
Proof
  strip_tac >>
  `source_memory_read_ranges i s = source_memory_read_ranges i t` by
    metis_tac[scfg_data_agree_read_ranges] >>
  fs[taint_ok_def] >> metis_tac[]
QED

Theorem scfg_merge_pos_taint_ok:
  wf_function f /\ EVERY (\h. h.inst_opcode <> PHI) (fn_insts f) /\
  scfg_merge_pos f i s g j t /\ active_inst f i s /\ active_inst g j t /\
  taint_ok f tn i s ==> taint_ok g tn j t
Proof
  strip_tac >>
  `i = j` by fs[scfg_merge_pos_def] >> gvs[] >>
  irule scfg_taint_ok_transport >>
  metis_tac[scfg_merge_pos_data, scfg_merge_pos_about_to_revert]
QED

Theorem scfg_restrict_pos_taint_ok:
  wf_function f /\ scfg_restrict_pos f i s g j t /\
  active_inst f i s /\ active_inst g j t /\ taint_ok f tn i s ==>
  taint_ok g tn j t
Proof
  strip_tac >> drule_all scfg_restrict_pos_observations >> strip_tac >>
  gvs[] >> irule scfg_taint_ok_transport >> metis_tac[]
QED

Theorem scfg_bypass_pos_taint_ok:
  wf_function f /\ scfg_bypass_pos f i s g j t /\
  active_inst f i s /\ active_inst g j t /\ taint_ok f tn i s ==>
  taint_ok g tn j t
Proof
  strip_tac >> drule scfg_bypass_pos_cases >> strip_tac
  >- gvs[] >>
  `i.inst_opcode <> PHI` by
    (fs[EVERY_MEM, active_inst_def] >>
     metis_tac[unitLabelMapIdentityTheory.fn_insts_MEM, EL_MEM]) >>
  reverse (Cases_on `s.vs_current_bb = a.bb_label /\ is_terminator i.inst_opcode`)
  >- (`j = i` by
        (Cases_on `is_terminator i.inst_opcode`
         >- (fs[] >> simp[scfg_bypass_image_def, update_phi_bypass_def]) >>
         simp[scfg_bypass_image_ordinary]) >>
      qpat_x_assum `j = scfg_bypass_image _ _ _ _ _` kall_tac >>
      qpat_x_assum `j = i` SUBST_ALL_TAC >>
      irule scfg_taint_ok_transport >>
      metis_tac[scfg_bypass_pos_about_to_revert]) >>
  `i.inst_opcode = JNZ` by metis_tac[scfg_bypass_active_source_terminator] >>
  `j.inst_opcode = JNZ \/ j.inst_opcode = JMP` by
    metis_tac[scfg_bypass_image_opcode] >>
  `!v. MEM (Var v) i.inst_operands ==> op_taint tn (Var v) = {}` by
    (fs[taint_ok_def] >> metis_tac[]) >>
  `!op. MEM op j.inst_operands ==> op_taint tn op = {}` by
    (rpt strip_tac >> Cases_on `op` >> gvs[op_taint_def] >>
     metis_tac[scfg_bypass_image_var]) >>
  gvs[taint_ok_def, source_memory_read_ranges_def] >> metis_tac[]
QED

Definition scfg_function_edge_def:
  scfg_function_edge f g <=>
    wf_function f /\ EVERY no_phis f.fn_blocks /\
    (g = remove_unreachable_blocks f \/
     (?a b. scfg_chain_hyp f a b /\ g = scfg_chain f a b) \/
     (?a b. scfg_bypass_hyp f a b g))
End

Definition scfg_function_trace_def:
  scfg_function_trace f g <=> RTC scfg_function_edge f g
End

Theorem scfg_function_trace_refl[simp]:
  scfg_function_trace f f
Proof
  simp[scfg_function_trace_def]
QED

Theorem scfg_function_trace_trans:
  scfg_function_trace f g /\ scfg_function_trace g h ==>
  scfg_function_trace f h
Proof
  simp[scfg_function_trace_def] >> metis_tac[RTC_TRANS]
QED

Theorem scfg_function_trace_edge:
  scfg_function_edge f g ==> scfg_function_trace f g
Proof
  simp[scfg_function_trace_def, RTC_SINGLE]
QED

Theorem scfg_function_trace_chain:
  scfg_chain_hyp f a b /\ EVERY no_phis f.fn_blocks ==>
  scfg_function_trace f (scfg_chain f a b) /\
  EVERY no_phis (scfg_chain f a b).fn_blocks /\
  scfg_normalized (scfg_chain f a b)
Proof
  strip_tac >> rpt conj_tac
  >- (irule scfg_function_trace_edge >> simp[scfg_function_edge_def] >>
      metis_tac[scfg_chain_old_wf])
  >- (fs[scfg_chain_def, scfg_chain_hyp_def] >>
      metis_tac[chain_merge_no_phi]) >>
  metis_tac[scfg_chain_normalized]
QED

Theorem scfg_function_trace_try_bypass:
  scfg_normalized f /\ EVERY no_phis f.fn_blocks /\
  lookup_block bb.bb_label f.fn_blocks = SOME bb /\
  try_bypass f lm bb candidates = (g,lm',changed) ==>
  scfg_function_trace f g /\ EVERY no_phis g.fn_blocks /\ scfg_normalized g
Proof
  strip_tac >>
  `EVERY no_phis g.fn_blocks` by
    (irule try_bypass_no_phi >>
     metis_tac[lookup_block_member_label, EVERY_MEM]) >>
  drule_all scfg_try_bypass_choice >> strip_tac
  >- gvs[] >>
  `wf_function f` by metis_tac[scfg_normalized_static, scfg_static_wf] >>
  simp[] >> conj_tac
  >- (irule scfg_function_trace_edge >> simp[scfg_function_edge_def] >>
      metis_tac[]) >>
  metis_tac[scfg_bypass_normalized]
QED

Definition scfg_trace_result_def:
  scfg_trace_result f g <=> scfg_function_trace f g /\
    scfg_normalized g /\ EVERY no_phis g.fn_blocks
End

Theorem scfg_function_trace_dfs_joint:
  (!fn lm visited lbl. scfg_normalized fn /\ EVERY no_phis fn.fn_blocks ==>
    scfg_trace_result fn (FST (collapse_dfs fn lm visited lbl))) /\
  (!fn lm visited succs. scfg_normalized fn /\ EVERY no_phis fn.fn_blocks ==>
    scfg_trace_result fn (FST (collapse_dfs_succs fn lm visited succs)))
Proof
  ho_match_mp_tac collapse_dfs_ind >> rpt conj_tac
  >- suspend "dfs"
  >- suspend "nil"
  >> suspend "succs"
QED

Resume scfg_function_trace_dfs_joint[dfs]:
  rpt (gen_tac ORELSE disch_tac) >> fs[] >>
  simp[NoAsms, Once collapse_dfs_def] >> fs[scfg_trace_result_def] >>
  Cases_on `lookup_block lbl fn.fn_blocks` >- simp[] >>
  rename1 `lookup_block lbl fn.fn_blocks = SOME bb` >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_member_label] >>
  namedCases_on `bb_succs bb` ["", "s1 rest"]
  >- (Cases_on `MEM lbl visited` >- simp[try_bypass_def] >>
      gvs[try_bypass_def]) >>
  namedCases_on `rest` ["", "s2 rest2"]
  >- (Cases_on `lookup_block s1 fn.fn_blocks`
      >- (Cases_on `MEM lbl visited` >> simp[]) >>
      rename1 `lookup_block s1 fn.fn_blocks = SOME next_bb` >>
      Cases_on `can_merge_blocks fn bb next_bb`
      >- suspend "merge" >>
      Cases_on `MEM lbl visited` >- simp[] >> gvs[]) >>
  suspend "bypass"
QED

Resume scfg_function_trace_dfs_joint[merge]:
  gvs[] >>
  `next_bb.bb_label = s1` by metis_tac[lookup_block_member_label] >>
  `scfg_chain_hyp fn bb next_bb` by
    (simp[scfg_chain_hyp_def] >> metis_tac[]) >>
  drule_all scfg_function_trace_chain >> strip_tac >>
  fs[scfg_chain_def] >> gvs[GSYM scfg_chain_def] >>
  metis_tac[scfg_function_trace_trans]
QED

Resume scfg_function_trace_dfs_joint[bypass]:
  Cases_on `try_bypass fn lm bb (s1::s2::rest2)` >> PairCases_on `r` >>
  `scfg_function_trace fn q /\ EVERY no_phis q.fn_blocks /\ scfg_normalized q` by
    (irule scfg_function_trace_try_bypass >> simp[] >>
     qexistsl_tac [`bb`, `s1::s2::rest2`, `r1`, `lm`, `r0`] >> simp[]) >>
  Cases_on `r1` >> gvs[]
  >- metis_tac[scfg_function_trace_trans] >>
  Cases_on `MEM bb.bb_label visited` >> gvs[] >>
  metis_tac[scfg_function_trace_trans]
QED

Resume scfg_function_trace_dfs_joint[nil]:
  simp[collapse_dfs_def, scfg_trace_result_def]
QED

Resume scfg_function_trace_dfs_joint[succs]:
  rpt (gen_tac ORELSE disch_tac) >> fs[] >> simp[Once collapse_dfs_def] >>
  Cases_on `collapse_dfs fn lm visited lbl` >> PairCases_on `r` >>
  gvs[scfg_trace_result_def] >> metis_tac[scfg_function_trace_trans]
QED

Finalise scfg_function_trace_dfs_joint

Theorem scfg_fix_all_phis_identity:
  EVERY no_phis f.fn_blocks ==> fix_all_phis f = f
Proof
  strip_tac >>
  `MAP (\bb. fix_phis_in_block (pred_labels f bb.bb_label) bb) f.fn_blocks =
   f.fn_blocks` by
    (irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
     fs[EVERY_EL, no_phis_def] >>
     irule scfg_fix_phis_no_phi >> simp[EVERY_EL]) >>
  simp[fix_all_phis_def]
QED

Theorem scfg_function_trace_cleanup:
  scfg_static f /\ EVERY no_phis f.fn_blocks ==>
  scfg_trace_result f (fix_all_phis (remove_unreachable_blocks f))
Proof
  strip_tac >>
  `EVERY no_phis (remove_unreachable_blocks f).fn_blocks` by
    metis_tac[remove_unreachable_blocks_no_phi] >>
  `fix_all_phis (remove_unreachable_blocks f) = remove_unreachable_blocks f` by
    metis_tac[scfg_fix_all_phis_identity] >>
  simp[scfg_trace_result_def] >> conj_tac
  >- (irule scfg_function_trace_edge >> simp[scfg_function_edge_def] >>
      metis_tac[scfg_static_wf]) >>
  metis_tac[scfg_normalized_cleanup]
QED

Theorem scfg_function_trace_round:
  scfg_static fn /\ EVERY no_phis fn.fn_blocks ==>
  scfg_trace_result fn (FST (simplify_cfg_round_with_labels fn))
Proof
  strip_tac >> Cases_on `fn_entry_label fn`
  >- (fs[scfg_static_def, wf_function_def, fn_has_entry_def,
         fn_entry_label_def, entry_block_def] >> Cases_on `fn.fn_blocks` >> gvs[]) >>
  qabbrev_tac `clean = fix_all_phis (remove_unreachable_blocks fn)` >>
  `scfg_trace_result fn clean` by
    metis_tac[scfg_function_trace_cleanup] >>
  `scfg_normalized clean /\ EVERY no_phis clean.fn_blocks` by
    fs[scfg_trace_result_def] >>
  Cases_on `collapse_dfs clean [] [] x` >> PairCases_on `r` >>
  `scfg_trace_result clean q` by
    metis_tac[scfg_function_trace_dfs_joint, pairTheory.FST] >>
  `scfg_normalized q /\ EVERY no_phis q.fn_blocks` by
    fs[scfg_trace_result_def] >>
  `ALL_DISTINCT (fn_labels clean)` by
    fs[scfg_normalized_def, scfg_static_def, wf_function_def, fn_labels_def] >>
  `subst_block_labels_fn r0 q = q` by
    metis_tac[scfg_collapse_subst_identity] >>
  `scfg_trace_result q (fix_all_phis (remove_unreachable_blocks q))` by
    metis_tac[scfg_function_trace_cleanup, scfg_normalized_static] >>
  Cases_on `r0 = []` >>
  gvs[simplify_cfg_round_with_labels_def, Abbr `clean`, scfg_trace_result_def] >>
  metis_tac[scfg_function_trace_trans]
QED

Theorem scfg_function_trace_iter:
  !n fn. scfg_static fn /\ EVERY no_phis fn.fn_blocks ==>
    scfg_function_trace fn (FST (simplify_cfg_iter_with_labels n fn)) /\
    scfg_static (FST (simplify_cfg_iter_with_labels n fn)) /\
    EVERY no_phis (FST (simplify_cfg_iter_with_labels n fn)).fn_blocks
Proof
  Induct >- simp[simplify_cfg_iter_with_labels_def] >>
  gen_tac >> strip_tac >>
  Cases_on `simplify_cfg_round_with_labels fn` >>
  `scfg_trace_result fn q` by metis_tac[scfg_function_trace_round, pairTheory.FST] >>
  Cases_on `q.fn_blocks = fn.fn_blocks`
  >- simp[simplify_cfg_iter_with_labels_def] >>
  `scfg_static q /\ EVERY no_phis q.fn_blocks` by
    metis_tac[scfg_trace_result_def, scfg_normalized_static] >>
  first_x_assum drule >> strip_tac >>
  Cases_on `simplify_cfg_iter_with_labels n q` >>
  gvs[simplify_cfg_iter_with_labels_def, scfg_trace_result_def] >>
  metis_tac[scfg_function_trace_trans]
QED

Theorem scfg_function_trace_simplify_cfg:
  scfg_static f /\ EVERY (\i. i.inst_opcode <> PHI) (fn_insts f) ==>
  scfg_function_trace f (simplify_cfg_fn f)
Proof
  strip_tac >>
  `EVERY no_phis f.fn_blocks` by
    (fs[EVERY_MEM, no_phis_def, fn_insts_def] >>
     metis_tac[fn_insts_blocks_MEM]) >>
  metis_tac[scfg_function_trace_iter, simplify_cfg_fn_def,
            simplify_cfg_fn_with_labels_def]
QED

Definition scfg_optional_restrict_pair_def:
  scfg_optional_restrict_pair f g <=> g = f \/ g = remove_unreachable_blocks f
End

Definition scfg_optional_restrict_pos_def:
  scfg_optional_restrict_pos f i s g j t <=>
    scfg_optional_restrict_pair f g /\ i = j /\ s = t
End

Definition scfg_optional_restrict_context_def:
  scfg_optional_restrict_context C C' <=>
    C'.ctx_entry = C.ctx_entry /\ EVERY wf_function C.ctx_functions /\
    EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)) C.ctx_functions /\
    (!nm g. lookup_function nm C'.ctx_functions = SOME g ==>
      ?f. lookup_function nm C.ctx_functions = SOME f /\ scfg_optional_restrict_pair f g)
End

Theorem scfg_optional_restrict_active:
  scfg_optional_restrict_pair f g /\ active_inst g i s ==> active_inst f i s
Proof
  simp[scfg_optional_restrict_pair_def] >> metis_tac[scfg_restriction_active_back]
QED

Theorem scfg_optional_restrict_enters:
  scfg_optional_restrict_pair f g /\ ALL_DISTINCT (fn_labels f) /\
  enters_block g s t ==> enters_block f s t
Proof
  simp[scfg_optional_restrict_pair_def] >> metis_tac[scfg_restriction_enters_back]
QED

Theorem scfg_optional_restrict_entry:
  scfg_optional_restrict_pair f g /\ wf_function f ==>
  fn_entry_label g = fn_entry_label f
Proof
  simp[scfg_optional_restrict_pair_def] >>
  metis_tac[remove_unreachable_blocks_entry, wf_function_def]
QED

Theorem scfg_optional_restrict_setup:
  scfg_optional_restrict_pair f g /\ wf_function f ==>
  setup_callee g args s = setup_callee f args s
Proof
  simp[scfg_optional_restrict_pair_def] >> metis_tac[scfg_restrict_setup]
QED

Theorem scfg_optional_restrict_ghosts:
  scfg_optional_restrict_pair f g /\
  EVERY (\i. i.inst_opcode <> PHI) (fn_insts f) ==>
  entry_prov f s G = G /\ entry_taint_vars f s tn = tn /\
  entry_prov g s G = G /\ entry_taint_vars g s tn = tn
Proof
  simp[scfg_optional_restrict_pair_def] >> metis_tac[scfg_restrict_entry_ghosts]
QED

Theorem scfg_optional_restrict_lookup:
  scfg_optional_restrict_context C C' /\ lookup_function nm C'.ctx_functions = SOME g ==>
  ?f. lookup_function nm C.ctx_functions = SOME f /\ scfg_optional_restrict_pair f g /\
      wf_function f /\ EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)
Proof
  simp[scfg_optional_restrict_context_def, EVERY_MEM] >>
  metis_tac[lookup_function_MEM]
QED

Definition scfg_optional_restrict_witness_def:
  scfg_optional_restrict_witness vs C stk PG G tn g i s <=>
    ?fs f nm. lookup_function nm C.ctx_functions = SOME f /\
      scfg_optional_restrict_pair f g /\ frame_reachable vs C fs PG G tn f i s /\
      scfg_saved_stack scfg_optional_restrict_pos fs stk
End

Theorem scfg_optional_restrict_witness_entry:
  scfg_optional_restrict_context C C' /\ C'.ctx_entry = SOME name /\
  lookup_function name C'.ctx_functions = SOME g /\ fn_entry_label g = SOME lbl /\
  enters_block g
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s /\
  active_inst g i s ==>
  scfg_optional_restrict_witness vs C [] [] FEMPTY entry_taint g i s
Proof
  strip_tac >> drule_all scfg_optional_restrict_lookup >> strip_tac >>
  `ALL_DISTINCT (fn_labels f)` by metis_tac[wf_function_def] >>
  `fn_entry_label f = SOME lbl` by metis_tac[scfg_optional_restrict_entry] >>
  `enters_block f
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s` by
    metis_tac[scfg_optional_restrict_enters] >>
  `active_inst f i s` by metis_tac[scfg_optional_restrict_active] >>
  simp[scfg_optional_restrict_witness_def] >> qexistsl_tac [`[]`, `f`, `name`] >>
  simp[] >> irule frame_reachable_entry >>
  fs[scfg_optional_restrict_context_def] >> metis_tac[]
QED

Theorem scfg_optional_restrict_witness_next:
  scfg_optional_restrict_witness vs C stk PG G tn g inst s /\ active_inst g inst s /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst k C' inst s = OK v /\
  active_inst g j (v with vs_inst_idx := SUC s.vs_inst_idx) ==>
  scfg_optional_restrict_witness vs C stk PG (step_prov PG G inst v)
    (step_taint inst s v tn) g j (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  simp[scfg_optional_restrict_witness_def] >> rpt strip_tac >>
  `step_inst k C inst s = OK v` by gvs[step_inst_non_invoke] >>
  qexistsl_tac [`fs`, `f`, `nm`] >> simp[] >>
  irule frame_reachable_next >> metis_tac[scfg_optional_restrict_active]
QED

Theorem scfg_optional_restrict_witness_block:
  scfg_optional_restrict_context C C' /\
  scfg_optional_restrict_witness vs C stk PG G tn g inst s /\ active_inst g inst s /\
  is_terminator inst.inst_opcode /\ step_inst k C' inst s = OK v /\
  ~v.vs_halted /\ enters_block g v t /\ active_inst g j t ==>
  scfg_optional_restrict_witness vs C stk PG (entry_prov g v G)
    (entry_taint_vars g v tn) g j t
Proof
  simp[scfg_optional_restrict_witness_def] >> rpt strip_tac >>
  `wf_function f /\ EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)` by
    (fs[scfg_optional_restrict_context_def, EVERY_MEM] >> metis_tac[lookup_function_MEM]) >>
  `ALL_DISTINCT (fn_labels f)` by metis_tac[wf_function_def] >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  `step_inst k C inst s = OK v` by gvs[step_inst_non_invoke] >>
  drule_all scfg_optional_restrict_ghosts >> strip_tac >>
  qexistsl_tac [`fs`, `f`, `nm`] >> simp[] >>
  `frame_reachable vs C fs PG (entry_prov f v G)
    (entry_taint_vars f v tn) f j t` by
    (irule frame_reachable_block >>
     metis_tac[scfg_optional_restrict_active, scfg_optional_restrict_enters]) >>
  metis_tac[]
QED

Theorem scfg_optional_restrict_witness_call:
  scfg_optional_restrict_context C C' /\
  scfg_optional_restrict_witness vs C stk PG G tn caller inst s /\
  active_inst caller inst s /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm, ops) /\
  lookup_function nm C'.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME ct /\
  enters_block callee ct t /\ active_inst callee i t ==>
  scfg_optional_restrict_witness vs C
    (<|cf_fn := caller; cf_inst := inst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee i t
Proof
  strip_tac >> drule_all scfg_optional_restrict_lookup >> strip_tac >>
  qpat_x_assum `scfg_optional_restrict_witness _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[scfg_optional_restrict_witness_def] >> strip_tac >>
  rename1 `frame_reachable vs C fs PG G tn caller0 inst s` >>
  `setup_callee f args s = SOME ct` by metis_tac[scfg_optional_restrict_setup] >>
  `ALL_DISTINCT (fn_labels f)` by metis_tac[wf_function_def] >>
  `active_inst caller0 inst s /\ enters_block f ct t /\ active_inst f i t` by
    metis_tac[scfg_optional_restrict_active, scfg_optional_restrict_enters] >>
  qexistsl_tac [`<|cf_fn := caller0; cf_inst := inst; cf_state := s;
     cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: fs`, `f`, `nm`] >>
  simp[scfg_saved_stack_def, scfg_saved_call_def, scfg_saved_frame_def,
       scfg_optional_restrict_pos_def, scfg_data_agree_refl] >>
  conj_tac >- (irule frame_reachable_call >> metis_tac[]) >>
  fs[scfg_saved_stack_def]
QED

Theorem scfg_optional_restrict_witness_ret:
  scfg_optional_restrict_context C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  scfg_optional_restrict_witness vs C (g::stk) PG G tn callee ri s /\
  active_inst callee ri s /\ step_inst k C' ri s = IntRet ret v /\
  bind_outputs g.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state g.cf_state v)) = SOME t /\
  active_inst g.cf_fn j (t with vs_inst_idx := SUC g.cf_state.vs_inst_idx) ==>
  scfg_optional_restrict_witness vs C stk g.cf_params
    (DRESTRICT g.cf_prov (COMPL (set g.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT g.cf_tvar (COMPL (set g.cf_inst.inst_outputs)))
    g.cf_fn j (t with vs_inst_idx := SUC g.cf_state.vs_inst_idx)
Proof
  simp[scfg_optional_restrict_witness_def] >> rpt strip_tac >>
  fs[scfg_saved_stack_cons, scfg_saved_call_def, scfg_saved_frame_def,
     scfg_optional_restrict_pos_def] >> gvs[] >>
  `ri.inst_opcode <> INVOKE` by metis_tac[step_inst_intret_not_invoke] >>
  `step_inst k C ri s = IntRet ret v` by gvs[step_inst_non_invoke] >>
  `scfg_rooted C (f'::rest) f ri s` by
    (irule scfg_frame_reachable_rooted >>
     fs[scfg_optional_restrict_context_def, EVERY_MEM] >>
     metis_tac[lookup_function_MEM]) >>
  `?name. lookup_function name C.ctx_functions = SOME f'.cf_fn` by
    (fs[scfg_rooted_def] >> drule scfg_root_history_cons >> strip_tac >>
     metis_tac[scfg_root_history_lookup]) >>
  `frame_reachable vs C rest f'.cf_params
    (DRESTRICT f'.cf_prov (COMPL (set f'.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f'.cf_tvar (COMPL (set f'.cf_inst.inst_outputs)))
    f'.cf_fn j (t with vs_inst_idx := SUC f'.cf_state.vs_inst_idx)` by
    (irule frame_reachable_ret >> metis_tac[scfg_optional_restrict_active]) >>
  qexistsl_tac [`rest`, `f'.cf_fn`, `name`] >> gvs[]
QED

Theorem scfg_optional_restrict_frame_witness:
  !vs C' stk PG G tn g i s.
  frame_reachable vs C' stk PG G tn g i s ==>
  !C. scfg_optional_restrict_context C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted ==>
  scfg_optional_restrict_witness vs C stk PG G tn g i s
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >> rpt strip_tac
  >- (irule scfg_optional_restrict_witness_entry >> metis_tac[])
  >- (irule scfg_optional_restrict_witness_next >> metis_tac[])
  >- (irule scfg_optional_restrict_witness_block >> metis_tac[])
  >- (irule scfg_optional_restrict_witness_call >> metis_tac[])
  >> irule scfg_optional_restrict_witness_ret >> metis_tac[]
QED

Theorem scfg_optional_restrict_stack_states:
  !fs gs. scfg_saved_stack scfg_optional_restrict_pos fs gs ==>
  LIST_REL (\f g. f.cf_state = g.cf_state) fs gs
Proof
  Induct_on `fs` >> Cases_on `gs` >>
  simp[scfg_saved_stack_def, scfg_saved_call_def, scfg_saved_frame_def,
       scfg_optional_restrict_pos_def] >> metis_tac[]
QED

Theorem scfg_optional_restrict_frame_back:
  scfg_optional_restrict_context C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  frame_reachable vs C' stk PG G tn g i s ==>
  ?fs f nm. lookup_function nm C.ctx_functions = SOME f /\
    scfg_optional_restrict_pair f g /\ frame_reachable vs C fs PG G tn f i s /\
    scfg_saved_stack scfg_optional_restrict_pos fs stk /\
    LIST_REL (\f g. f.cf_state = g.cf_state) fs stk
Proof
  strip_tac >> drule_all scfg_optional_restrict_frame_witness >>
  simp[scfg_optional_restrict_witness_def] >>
  metis_tac[scfg_optional_restrict_stack_states]
QED

Theorem scfg_optional_restrict_context_refl:
  EVERY wf_function C.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)) C.ctx_functions ==>
  scfg_optional_restrict_context C C
Proof
  simp[scfg_optional_restrict_context_def, scfg_optional_restrict_pair_def] >>
  metis_tac[]
QED

Theorem scfg_optional_restrict_pair_name:
  scfg_optional_restrict_pair f g ==> g.fn_name = f.fn_name
Proof
  simp[scfg_optional_restrict_pair_def] >> strip_tac >> simp[] >>
  Cases_on `fn_entry_label f` >> simp[remove_unreachable_blocks_def]
QED

Theorem scfg_lookup_function_occurrence:
  !pre nm g. h.fn_name = f.fn_name /\ R f h /\
  (!a. MEM a (pre ++ post) ==> R a a) /\
  lookup_function nm (pre ++ h::post) = SOME g ==>
  ?a. lookup_function nm (pre ++ f::post) = SOME a /\ R a g
Proof
  Induct_on `pre`
  >- (rpt strip_tac >> fs[lookup_function_def, FIND_thm] >>
      Cases_on `f.fn_name = nm` >> gvs[] >>
      metis_tac[lookup_function_MEM, lookup_function_def]) >>
  rpt strip_tac >> fs[lookup_function_def, FIND_thm] >>
  Cases_on `h'.fn_name = nm` >> gvs[] >>
  metis_tac[lookup_function_def]
QED

Theorem scfg_optional_restrict_lookup_occurrence:
  !pre nm g.
  scfg_optional_restrict_pair f h /\
  lookup_function nm (pre ++ h::post) = SOME g ==>
  ?a. lookup_function nm (pre ++ f::post) = SOME a /\ scfg_optional_restrict_pair a g
Proof
  rpt strip_tac >> irule scfg_lookup_function_occurrence >>
  conj_tac >- simp[scfg_optional_restrict_pair_def] >>
  qexists_tac `h` >> simp[] >> metis_tac[scfg_optional_restrict_pair_name]
QED

Theorem scfg_optional_restrict_context_occurrence:
  C.ctx_functions = pre ++ f::post /\ C'.ctx_functions = pre ++ h::post /\
  C'.ctx_entry = C.ctx_entry /\ scfg_optional_restrict_pair f h /\
  EVERY wf_function C.ctx_functions /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> PHI) (fn_insts fn)) C.ctx_functions ==>
  scfg_optional_restrict_context C C'
Proof
  simp[scfg_optional_restrict_context_def] >> rpt strip_tac >>
  qspecl_then [`pre`, `nm`, `g`] mp_tac scfg_optional_restrict_lookup_occurrence >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem scfg_function_edge_name:
  scfg_function_edge f g ==> g.fn_name = f.fn_name
Proof
  simp[scfg_function_edge_def] >> strip_tac
  >- (Cases_on `fn_entry_label f` >> simp[remove_unreachable_blocks_def])
  >- simp[scfg_chain_def] >>
  metis_tac[scfg_bypass_name]
QED

Theorem scfg_function_edge_preserves:
  scfg_function_edge f g ==> wf_function g /\ EVERY no_phis g.fn_blocks
Proof
  simp[scfg_function_edge_def] >> strip_tac
  >- metis_tac[remove_unreachable_blocks_wf, remove_unreachable_blocks_no_phi]
  >- metis_tac[scfg_function_trace_chain, scfg_chain_wf] >>
  conj_tac
  >- metis_tac[scfg_bypass_normalized, scfg_normalized_static, scfg_static_wf] >>
  fs[scfg_bypass_hyp_def] >>
  `no_phis a` by metis_tac[lookup_block_member_label, EVERY_MEM] >>
  drule_all do_merge_jump_no_phi >> simp[]
QED

Definition scfg_context_edge_def:
  scfg_context_edge C C' <=> C'.ctx_entry = C.ctx_entry /\
    EVERY wf_function C.ctx_functions /\ EVERY (\f. EVERY no_phis f.fn_blocks) C.ctx_functions /\
    ?pre f g post. C.ctx_functions = pre ++ f::post /\
      C'.ctx_functions = pre ++ g::post /\ scfg_function_edge f g
End

Definition scfg_context_trace_def:
  scfg_context_trace C C' <=> RTC scfg_context_edge C C'
End

Theorem scfg_context_edge_preserves:
  scfg_context_edge C C' ==>
  EVERY wf_function C'.ctx_functions /\
  EVERY (\f. EVERY no_phis f.fn_blocks) C'.ctx_functions
Proof
  simp[scfg_context_edge_def] >> rpt strip_tac >>
  gvs[EVERY_APPEND, scfg_function_edge_preserves] >>
  metis_tac[scfg_function_edge_preserves]
QED

Theorem scfg_no_phi_insts_iff:
  EVERY no_phis f.fn_blocks <=> EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)
Proof
  simp[EVERY_MEM, no_phis_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]
QED

Theorem scfg_context_edge_interfaces:
  scfg_context_edge C C' ==>
  scfg_merge_context C C' \/ scfg_bypass_context C C' \/
  scfg_optional_restrict_context C C'
Proof
  simp[scfg_context_edge_def] >> rpt strip_tac >>
  `!nm f. lookup_function nm C.ctx_functions = SOME f ==>
    wf_function f /\ EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)` by
    (rpt strip_tac >> drule lookup_function_MEM >> strip_tac >>
     gvs[scfg_no_phi_insts_iff, EVERY_MEM] >> metis_tac[]) >>
  `g.fn_name = f.fn_name` by metis_tac[scfg_function_edge_name] >>
  fs[scfg_function_edge_def]
  >- (disj2_tac >> disj2_tac >>
      irule scfg_optional_restrict_context_occurrence >>
      simp[GSYM scfg_no_phi_insts_iff] >>
      qexistsl_tac [`f`, `g`, `post`, `pre`] >>
      simp[scfg_optional_restrict_pair_def])
  >- suspend "merge"
  >> suspend "bypass"
QED

Resume scfg_context_edge_interfaces[merge]:
  disj1_tac >> pure_rewrite_tac[scfg_merge_context_def] >>
  conj_tac >- simp[] >> conj_tac >- metis_tac[] >> rpt strip_tac >>
  qpat_x_assum `lookup_function nm C'.ctx_functions = SOME _` mp_tac >>
  pure_asm_rewrite_tac [] >> strip_tac >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  irule scfg_lookup_function_occurrence >>
  conj_tac >- simp[scfg_merge_pair_def] >>
  qexists_tac `g` >> simp[scfg_merge_pair_def] >> metis_tac[]
QED

Resume scfg_context_edge_interfaces[bypass]:
  disj2_tac >> disj1_tac >> simp[scfg_bypass_context_def] >> rpt strip_tac >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  irule scfg_lookup_function_occurrence >>
  conj_tac
  >- (simp[scfg_bypass_pair_def, GSYM scfg_no_phi_insts_iff] >>
      fs[EVERY_MEM] >> metis_tac[]) >>
  qexists_tac `g` >> simp[scfg_bypass_pair_def] >>
  metis_tac[scfg_no_phi_insts_iff]
QED
Finalise scfg_context_edge_interfaces

Theorem scfg_context_trace_refl[simp]:
  scfg_context_trace C C
Proof
  simp[scfg_context_trace_def]
QED

Theorem scfg_context_trace_trans:
  scfg_context_trace C B /\ scfg_context_trace B A ==>
  scfg_context_trace C A
Proof
  simp[scfg_context_trace_def] >> metis_tac[RTC_TRANS]
QED

Theorem scfg_function_trace_occurrence:
  !f g. scfg_function_trace f g ==>
  !C pre post. EVERY wf_function (pre ++ post) /\
    EVERY (\h. EVERY no_phis h.fn_blocks) (pre ++ post) ==>
    scfg_context_trace (C with ctx_functions := pre ++ f::post)
      (C with ctx_functions := pre ++ g::post)
Proof
  pure_rewrite_tac[scfg_function_trace_def] >>
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac
  >- simp[] >>
  `scfg_context_edge (C with ctx_functions := pre ++ f::post)
    (C with ctx_functions := pre ++ f'::post)` by
    (simp[scfg_context_edge_def] >>
     conj_tac >- fs[scfg_function_edge_def, EVERY_APPEND] >>
     conj_tac >- fs[scfg_function_edge_def, EVERY_APPEND] >>
     qexistsl_tac [`pre`, `f`, `f'`, `post`] >> simp[]) >>
  `scfg_context_trace (C with ctx_functions := pre ++ f'::post)
    (C with ctx_functions := pre ++ g::post)` by
    (first_x_assum irule >> simp[]) >>
  metis_tac[scfg_context_trace_def, RTC_SINGLE, RTC_TRANS]
QED

Theorem scfg_function_trace_preserves:
  !f g. scfg_function_trace f g ==>
  wf_function f /\ EVERY no_phis f.fn_blocks ==>
  wf_function g /\ EVERY no_phis g.fn_blocks
Proof
  pure_rewrite_tac[scfg_function_trace_def] >>
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac >>
  metis_tac[scfg_function_edge_preserves]
QED

Theorem scfg_context_trace_list:
  !xs ys. LIST_REL scfg_function_trace xs ys ==>
  !C pre. EVERY wf_function (pre ++ xs) /\
    EVERY (\h. EVERY no_phis h.fn_blocks) (pre ++ xs) ==>
    scfg_context_trace (C with ctx_functions := pre ++ xs)
      (C with ctx_functions := pre ++ ys)
Proof
  ho_match_mp_tac LIST_REL_ind >> rpt strip_tac
  >- simp[] >>
  rename1 `scfg_function_trace f g` >>
  `wf_function g /\ EVERY no_phis g.fn_blocks` by
    (irule scfg_function_trace_preserves >> qexists_tac `f` >> fs[]) >>
  `scfg_context_trace (C with ctx_functions := pre ++ f::xs)
    (C with ctx_functions := pre ++ g::xs)` by
    (irule scfg_function_trace_occurrence >> fs[EVERY_APPEND]) >>
  `scfg_context_trace (C with ctx_functions := pre ++ g::xs)
    (C with ctx_functions := pre ++ g::ys)` by
    (first_x_assum (qspecl_then [`C`, `pre ++ [g]`] mp_tac) >>
     fs[EVERY_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  metis_tac[scfg_context_trace_trans]
QED

Theorem scfg_context_trace_simplify_cfg:
  EVERY scfg_static C.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)) C.ctx_functions ==>
  scfg_context_trace C
    (C with ctx_functions := MAP simplify_cfg_fn C.ctx_functions)
Proof
  strip_tac >>
  `LIST_REL scfg_function_trace C.ctx_functions
    (MAP simplify_cfg_fn C.ctx_functions)` by
    (simp[LIST_REL_MAP2, LIST_REL_EL_EQN] >> rpt strip_tac >>
     irule scfg_function_trace_simplify_cfg >>
     fs[EVERY_MEM] >> metis_tac[EL_MEM]) >>
  drule scfg_context_trace_list >>
  disch_then (qspecl_then [`C`, `[]`] mp_tac) >>
  simp[] >> impl_tac
  >- (fs[EVERY_MEM, GSYM scfg_no_phi_insts_iff] >>
      metis_tac[scfg_static_wf]) >>
  simp[combinTheory.UPDATE_EQ]
QED

Definition scfg_position_edge_def:
  scfg_position_edge (f,i,s) (g,j,t) <=>
    scfg_merge_pos f i s g j t \/ scfg_bypass_pos f i s g j t \/
    scfg_optional_restrict_pos f i s g j t
End

Definition scfg_position_trace_def:
  scfg_position_trace f i s g j t <=> RTC scfg_position_edge (f,i,s) (g,j,t)
End

Theorem scfg_position_trace_refl[simp]:
  scfg_position_trace f i s f i s
Proof
  simp[scfg_position_trace_def]
QED

Theorem scfg_position_trace_trans:
  scfg_position_trace f i s g j t /\ scfg_position_trace g j t h k u ==>
  scfg_position_trace f i s h k u
Proof
  simp[scfg_position_trace_def] >> metis_tac[RTC_TRANS]
QED

Theorem scfg_saved_stack_mono:
  !rel rel'. (!f i s g j t. rel f i s g j t ==> rel' f i s g j t) ==>
  !fs gs. scfg_saved_stack rel fs gs ==> scfg_saved_stack rel' fs gs
Proof
  rpt gen_tac >> strip_tac >> simp[scfg_saved_stack_def] >>
  ho_match_mp_tac LIST_REL_ind >>
  simp[scfg_saved_call_def, scfg_saved_frame_def] >> metis_tac[]
QED

Theorem scfg_saved_stack_trace_refl[simp]:
  scfg_saved_stack scfg_position_trace fs fs
Proof
  simp[scfg_saved_stack_def] >> Induct_on `fs` >>
  simp[scfg_saved_call_def, scfg_saved_frame_def, scfg_data_agree_def]
QED

Theorem scfg_saved_stack_trace_trans:
  !fs gs. scfg_saved_stack scfg_position_trace fs gs ==>
  !hs. scfg_saved_stack scfg_position_trace gs hs ==>
  scfg_saved_stack scfg_position_trace fs hs
Proof
  simp[scfg_saved_stack_def] >> ho_match_mp_tac LIST_REL_ind >>
  rpt strip_tac >>
  Cases_on `hs` >> gvs[scfg_saved_call_def, scfg_saved_frame_def] >>
  metis_tac[scfg_position_trace_trans, scfg_data_agree_trans]
QED

Theorem scfg_position_trace_edge:
  scfg_merge_pos f i s g j t \/ scfg_bypass_pos f i s g j t \/
  scfg_optional_restrict_pos f i s g j t ==>
  scfg_position_trace f i s g j t
Proof
  simp[scfg_position_trace_def] >> strip_tac >>
  irule RTC_SINGLE >> simp[scfg_position_edge_def]
QED

Theorem scfg_context_edge_frame_back:
  scfg_context_edge C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  frame_reachable vs C' stk PG G tn g j t ==>
  ?fs f i s. frame_reachable vs C fs PG G tn f i s /\
    scfg_saved_stack scfg_position_trace fs stk /\
    scfg_position_trace f i s g j t /\ scfg_data_agree s t
Proof
  strip_tac >> drule scfg_context_edge_interfaces >> strip_tac
  >- suspend "merge"
  >- suspend "bypass"
  >> suspend "restrict"
QED

Resume scfg_context_edge_frame_back[merge]:
  drule_all scfg_merge_frame_back >> strip_tac >>
  qexistsl_tac [`fs`, `f`, `j`, `s`] >> simp[] >>
  conj_tac
  >- (irule scfg_saved_stack_mono >> goal_assum (drule_at Any) >>
      metis_tac[scfg_position_trace_edge]) >>
  metis_tac[scfg_position_trace_edge]
QED

Resume scfg_context_edge_frame_back[bypass]:
  `!nm f. lookup_function nm C.ctx_functions = SOME f ==> wf_function f` by
    (fs[scfg_context_edge_def] >> rpt strip_tac >>
     drule lookup_function_MEM >> strip_tac >> gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all scfg_bypass_context_reachable >>
  simp[scfg_bypass_witness_def] >> strip_tac >>
  qexistsl_tac [`fs`, `f`, `i`, `s`] >> simp[] >> rpt conj_tac
  >- (irule scfg_saved_stack_mono >> goal_assum (drule_at Any) >>
      metis_tac[scfg_position_trace_edge])
  >- metis_tac[scfg_position_trace_edge] >>
  metis_tac[scfg_bypass_pos_data]
QED

Resume scfg_context_edge_frame_back[restrict]:
  drule_all scfg_optional_restrict_frame_back >> strip_tac >>
  qexistsl_tac [`fs`, `f`, `j`, `t`] >> simp[scfg_data_agree_def] >>
  conj_tac
  >- (irule scfg_saved_stack_mono >> goal_assum (drule_at Any) >>
      metis_tac[scfg_position_trace_edge]) >>
  irule scfg_position_trace_edge >> disj2_tac >> disj2_tac >>
  simp[scfg_optional_restrict_pos_def]
QED
Finalise scfg_context_edge_frame_back

Theorem scfg_frame_reachable_functions:
  !vs C stk PG G tn f i s. frame_reachable vs C stk PG G tn f i s ==>
    MEM f C.ctx_functions /\ EVERY (\cf. MEM cf.cf_fn C.ctx_functions) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> simp[] >> rpt strip_tac >>
  metis_tac[lookup_function_MEM]
QED

Theorem scfg_frame_reachable_wf:
  frame_reachable vs C stk PG G tn f i s /\
  EVERY wf_function C.ctx_functions /\
  EVERY (\h. EVERY no_phis h.fn_blocks) C.ctx_functions ==>
  wf_function f /\ EVERY no_phis f.fn_blocks
Proof
  strip_tac >> drule scfg_frame_reachable_functions >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Definition scfg_live_position_edge_def:
  scfg_live_position_edge (f,i,s) (g,j,t) <=>
    scfg_position_edge (f,i,s) (g,j,t) /\ wf_function f /\
    EVERY no_phis f.fn_blocks /\ active_inst f i s /\ active_inst g j t
End

Definition scfg_live_position_trace_def:
  scfg_live_position_trace f i s g j t <=>
    RTC scfg_live_position_edge (f,i,s) (g,j,t)
End

Theorem scfg_live_position_trace_refl[simp]:
  scfg_live_position_trace f i s f i s
Proof
  simp[scfg_live_position_trace_def]
QED

Theorem scfg_live_position_trace_trans:
  scfg_live_position_trace f i s g j t /\ scfg_live_position_trace g j t h k u ==>
  scfg_live_position_trace f i s h k u
Proof
  simp[scfg_live_position_trace_def] >> metis_tac[RTC_TRANS]
QED

Theorem scfg_live_position_trace_projection:
  scfg_live_position_trace f i s g j t ==> scfg_position_trace f i s g j t
Proof
  simp[scfg_live_position_trace_def, scfg_position_trace_def] >> strip_tac >>
  irule RTC_MONOTONE >> goal_assum (drule_at Any) >>
  simp[pairTheory.FORALL_PROD, scfg_live_position_edge_def]
QED

Theorem scfg_live_position_edge_taint:
  scfg_live_position_edge (f,i,s) (g,j,t) /\ taint_ok f tn i s ==>
  taint_ok g tn j t
Proof
  simp[scfg_live_position_edge_def, scfg_position_edge_def] >> strip_tac
  >- metis_tac[scfg_merge_pos_taint_ok, scfg_no_phi_insts_iff]
  >- metis_tac[scfg_bypass_pos_taint_ok] >>
  fs[scfg_optional_restrict_pos_def, scfg_optional_restrict_pair_def] >> gvs[] >>
  irule scfg_restrict_pos_taint_ok >>
  simp[scfg_restrict_pos_def] >> metis_tac[]
QED

Theorem scfg_live_position_trace_taint_tuple:
  !p q. RTC scfg_live_position_edge p q ==>
  !tn. taint_ok (FST p) tn (FST (SND p)) (SND (SND p)) ==>
    taint_ok (FST q) tn (FST (SND q)) (SND (SND q))
Proof
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac >>
  PairCases_on `p` >> PairCases_on `p'` >>
  fs[] >> metis_tac[scfg_live_position_edge_taint]
QED

Theorem scfg_live_position_trace_taint:
  scfg_live_position_trace f i s g j t /\ taint_ok f tn i s ==>
  taint_ok g tn j t
Proof
  simp[scfg_live_position_trace_def] >>
  metis_tac[scfg_live_position_trace_taint_tuple, pairTheory.FST, pairTheory.SND]
QED

Theorem scfg_reachable_position_live:
  frame_reachable vs C fs PG G tn f i s /\
  frame_reachable vs C' gs PG G tn g j t /\
  EVERY wf_function C.ctx_functions /\
  EVERY (\h. EVERY no_phis h.fn_blocks) C.ctx_functions /\
  scfg_position_edge (f,i,s) (g,j,t) ==>
  scfg_live_position_trace f i s g j t
Proof
  strip_tac >> simp[scfg_live_position_trace_def] >> irule RTC_SINGLE >>
  simp[scfg_live_position_edge_def] >>
  metis_tac[scfg_frame_reachable_wf, scfg_frame_reachable_active]
QED

Theorem scfg_context_edge_live_frame_back:
  scfg_context_edge C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  frame_reachable vs C' stk PG G tn g j t ==>
  ?fs f i s. frame_reachable vs C fs PG G tn f i s /\
    scfg_saved_stack scfg_position_trace fs stk /\
    scfg_live_position_trace f i s g j t /\ scfg_data_agree s t
Proof
  strip_tac >>
  `EVERY wf_function C.ctx_functions /\
   EVERY (\h. EVERY no_phis h.fn_blocks) C.ctx_functions` by
    fs[scfg_context_edge_def] >>
  drule scfg_context_edge_interfaces >> strip_tac
  >- suspend "merge"
  >- suspend "bypass"
  >> suspend "restrict"
QED

Resume scfg_context_edge_live_frame_back[merge]:
  drule_all scfg_merge_frame_back >> strip_tac >>
  qexistsl_tac [`fs`, `f`, `j`, `s`] >> simp[] >>
  conj_tac
  >- (irule scfg_saved_stack_mono >> goal_assum (drule_at Any) >>
      metis_tac[scfg_position_trace_edge]) >>
  irule scfg_reachable_position_live >> simp[scfg_position_edge_def] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

Resume scfg_context_edge_live_frame_back[bypass]:
  `!nm f. lookup_function nm C.ctx_functions = SOME f ==> wf_function f` by
    (rpt strip_tac >> drule lookup_function_MEM >> strip_tac >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all scfg_bypass_context_reachable >>
  simp[scfg_bypass_witness_def] >> strip_tac >>
  qexistsl_tac [`fs`, `f`, `i`, `s`] >> simp[] >> rpt conj_tac
  >- (irule scfg_saved_stack_mono >> goal_assum (drule_at Any) >>
      metis_tac[scfg_position_trace_edge])
  >- (irule scfg_reachable_position_live >> simp[scfg_position_edge_def] >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]) >>
  metis_tac[scfg_bypass_pos_data]
QED

Resume scfg_context_edge_live_frame_back[restrict]:
  drule_all scfg_optional_restrict_frame_back >> strip_tac >>
  qexistsl_tac [`fs`, `f`, `j`, `t`] >> simp[scfg_data_agree_def] >>
  conj_tac
  >- (irule scfg_saved_stack_mono >> goal_assum (drule_at Any) >>
      metis_tac[scfg_position_trace_edge]) >>
  irule scfg_reachable_position_live >>
  simp[scfg_position_edge_def, scfg_optional_restrict_pos_def] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED
Finalise scfg_context_edge_live_frame_back

Theorem scfg_context_trace_live_frame_back:
  !C C'. scfg_context_trace C C' ==>
  !vs stk PG G tn g j t. vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  frame_reachable vs C' stk PG G tn g j t ==>
  ?fs f i s. frame_reachable vs C fs PG G tn f i s /\
    scfg_saved_stack scfg_position_trace fs stk /\
    scfg_live_position_trace f i s g j t /\ scfg_data_agree s t
Proof
  pure_rewrite_tac[scfg_context_trace_def] >>
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac
  >- (qexistsl_tac [`stk`, `g`, `j`, `t`] >>
      simp[scfg_data_agree_def]) >>
  first_x_assum drule_all >> strip_tac >>
  drule_all scfg_context_edge_live_frame_back >> strip_tac >>
  rename1 `frame_reachable vs C fs0 PG G tn f0 i0 s0` >>
  qexistsl_tac [`fs0`, `f0`, `i0`, `s0`] >> simp[] >>
  conj_tac >- metis_tac[scfg_saved_stack_trace_trans] >>
  conj_tac >- metis_tac[scfg_live_position_trace_trans] >>
  metis_tac[scfg_data_agree_trans]
QED

Theorem scfg_context_trace_frame_back:
  !C C'. scfg_context_trace C C' ==>
  !vs stk PG G tn g j t. vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  frame_reachable vs C' stk PG G tn g j t ==>
  ?fs f i s. frame_reachable vs C fs PG G tn f i s /\
    scfg_saved_stack scfg_position_trace fs stk /\
    scfg_position_trace f i s g j t /\ scfg_data_agree s t
Proof
  rpt strip_tac >> drule_all scfg_context_trace_live_frame_back >>
  metis_tac[scfg_live_position_trace_projection]
QED

Theorem scfg_live_position_edge_revert:
  scfg_live_position_edge (f,i,s) (g,j,t) ==>
  (in_revert_forward f s ==> in_revert_forward g t) /\
  (about_to_revert f i s ==> about_to_revert g j t)
Proof
  simp[scfg_live_position_edge_def, scfg_position_edge_def] >> strip_tac
  >- metis_tac[scfg_merge_pos_revert_forward, scfg_merge_pos_about_to_revert,
               scfg_no_phi_insts_iff]
  >- metis_tac[scfg_bypass_pos_revert_forward, scfg_bypass_pos_about_to_revert] >>
  fs[scfg_optional_restrict_pos_def, scfg_optional_restrict_pair_def] >> gvs[] >>
  `scfg_restrict_pos f i s (remove_unreachable_blocks f) i s` by
    simp[scfg_restrict_pos_def] >>
  metis_tac[scfg_restrict_pos_observations]
QED

Theorem scfg_live_position_trace_revert_tuple:
  !p q. RTC scfg_live_position_edge p q ==>
  (in_revert_forward (FST p) (SND (SND p)) ==>
    in_revert_forward (FST q) (SND (SND q))) /\
  (about_to_revert (FST p) (FST (SND p)) (SND (SND p)) ==>
    about_to_revert (FST q) (FST (SND q)) (SND (SND q)))
Proof
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac >>
  PairCases_on `p` >> PairCases_on `p'` >>
  fs[] >> metis_tac[scfg_live_position_edge_revert]
QED

Theorem scfg_live_position_trace_revert:
  scfg_live_position_trace f i s g j t ==>
  (in_revert_forward f s ==> in_revert_forward g t) /\
  (about_to_revert f i s ==> about_to_revert g j t)
Proof
  simp[scfg_live_position_trace_def] >> strip_tac >>
  qspecl_then [`(f,i,s)`, `(g,j,t)`] mp_tac
    scfg_live_position_trace_revert_tuple >> simp[]
QED

Theorem scfg_request_step_ordinary:
  step_inst k C i s = OK t /\
  LENGTH s.vs_requests < LENGTH t.vs_requests ==>
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI
Proof
  strip_tac >> reverse conj_tac
  >- (strip_tac >>
      gvs[step_inst_non_invoke, step_inst_base_def]) >>
  strip_tac >>
  `i.inst_opcode <> INVOKE` by
    (strip_tac >> gvs[is_terminator_def]) >>
  `step_inst_base i s = OK t` by gvs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst _ _ _ _ = _` kall_tac >>
  Cases_on `i.inst_opcode` >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  qpat_assum `i.inst_opcode = _` (fn eq =>
    PURE_ONCE_REWRITE_TAC
      [tryfind (fn th => MATCH_MP th eq)
         (CONJUNCTS step_inst_base_opcode_eqs)]) >>
  simp[AllCaseEqs(), jump_to_def] >> rpt strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem scfg_position_edge_ordinary:
  scfg_position_edge (f,i,s) (g,j,t) /\
  ~is_terminator j.inst_opcode /\ j.inst_opcode <> PHI ==> i = j
Proof
  simp[scfg_position_edge_def] >> strip_tac
  >- fs[scfg_merge_pos_def]
  >- (fs[scfg_bypass_pos_def] >>
      metis_tac[scfg_bypass_image_ordinary_inv]) >>
  fs[scfg_optional_restrict_pos_def]
QED

Theorem scfg_position_trace_ordinary_tuple:
  !p q. RTC scfg_position_edge p q ==>
  ~is_terminator (FST (SND q)).inst_opcode /\
  (FST (SND q)).inst_opcode <> PHI ==>
  FST (SND p) = FST (SND q)
Proof
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac
  >- simp[] >>
  PairCases_on `p` >> PairCases_on `p'` >> PairCases_on `q` >>
  fs[] >> metis_tac[scfg_position_edge_ordinary]
QED

Theorem scfg_position_trace_ordinary:
  scfg_position_trace f i s g j t /\
  ~is_terminator j.inst_opcode /\ j.inst_opcode <> PHI ==> i = j
Proof
  simp[scfg_position_trace_def] >>
  metis_tac[scfg_position_trace_ordinary_tuple, pairTheory.FST, pairTheory.SND]
QED

Theorem scfg_live_position_request_back:
  scfg_live_position_trace f i s g j t /\ scfg_data_agree s t /\
  j.inst_opcode <> INVOKE /\ step_inst k C' j t = OK t' /\
  LENGTH t.vs_requests < LENGTH t'.vs_requests ==>
  ?s'. i.inst_opcode <> INVOKE /\ step_inst k C i s = OK s' /\
    LENGTH s.vs_requests < LENGTH s'.vs_requests /\ scfg_data_agree s' t'
Proof
  strip_tac >>
  `i = j` by
    (drule_all scfg_request_step_ordinary >> strip_tac >>
     metis_tac[scfg_position_trace_ordinary, scfg_live_position_trace_projection]) >>
  gvs[] >> drule_all scfg_data_agree_ok_back >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  qexists_tac `u` >> fs[scfg_data_agree_def, execution_frame_def]
QED

Theorem scfg_bypass_pos_nonbranch:
  scfg_bypass_pos f i s g j t /\ active_inst f i s /\
  j.inst_opcode <> JMP /\ j.inst_opcode <> JNZ /\ j.inst_opcode <> PHI ==>
  i = j
Proof
  strip_tac >> drule scfg_bypass_pos_cases >> strip_tac >>
  `i.inst_opcode <> PHI` by
    (fs[EVERY_MEM, active_inst_def] >>
     metis_tac[unitLabelMapIdentityTheory.fn_insts_MEM, EL_MEM]) >>
  reverse (Cases_on `s.vs_current_bb = a.bb_label /\ is_terminator i.inst_opcode`)
  >- (Cases_on `is_terminator i.inst_opcode`
      >- (fs[] >> gvs[scfg_bypass_image_def, update_phi_bypass_def]) >>
      gvs[scfg_bypass_image_ordinary]) >>
  `i.inst_opcode = JNZ` by metis_tac[scfg_bypass_active_source_terminator] >>
  metis_tac[scfg_bypass_image_opcode]
QED

Theorem scfg_live_position_edge_nonbranch:
  scfg_live_position_edge (f,i,s) (g,j,t) /\
  j.inst_opcode <> JMP /\ j.inst_opcode <> JNZ /\ j.inst_opcode <> PHI ==>
  i = j
Proof
  simp[scfg_live_position_edge_def, scfg_position_edge_def] >> strip_tac
  >- fs[scfg_merge_pos_def]
  >- metis_tac[scfg_bypass_pos_nonbranch] >>
  fs[scfg_optional_restrict_pos_def]
QED

Theorem scfg_live_position_trace_nonbranch_tuple:
  !p q. RTC scfg_live_position_edge p q ==>
  (FST (SND q)).inst_opcode <> JMP /\
  (FST (SND q)).inst_opcode <> JNZ /\
  (FST (SND q)).inst_opcode <> PHI ==>
  FST (SND p) = FST (SND q)
Proof
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac
  >- simp[] >>
  PairCases_on `p` >> PairCases_on `p'` >> PairCases_on `q` >>
  fs[] >> metis_tac[scfg_live_position_edge_nonbranch]
QED

Theorem scfg_live_position_trace_nonbranch:
  scfg_live_position_trace f i s g j t /\
  j.inst_opcode <> JMP /\ j.inst_opcode <> JNZ /\ j.inst_opcode <> PHI ==>
  i = j
Proof
  simp[scfg_live_position_trace_def] >>
  metis_tac[scfg_live_position_trace_nonbranch_tuple, pairTheory.FST, pairTheory.SND]
QED

Theorem scfg_halt_step_nonbranch:
  step_inst k C i s = Halt t ==>
  i.inst_opcode <> JMP /\ i.inst_opcode <> JNZ /\ i.inst_opcode <> PHI
Proof
  strip_tac >> rpt conj_tac >> strip_tac >>
  gvs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  qpat_assum `i.inst_opcode = _` (fn eq =>
    PURE_ONCE_REWRITE_TAC
      [tryfind (fn th => MATCH_MP th eq)
         (CONJUNCTS step_inst_base_opcode_eqs)]) >>
  simp[AllCaseEqs()]
QED

Theorem scfg_data_agree_halt_back:
  scfg_data_agree s t /\ i.inst_opcode <> INVOKE /\
  step_inst k C' i t = Halt v ==>
  ?u. step_inst k C i s = Halt u /\ scfg_data_agree u v
Proof
  strip_tac >>
  `scfg_payload t s` by
    metis_tac[scfg_data_agree_sym, scfg_data_agree_payload] >>
  drule scfg_payload_step >>
  disch_then (qspecl_then [`k`, `i`, `C'`] mp_tac) >> simp[] >>
  Cases_on `step_inst k C' i s` >> simp[scfg_result_def] >>
  strip_tac >> gvs[step_inst_non_invoke, scfg_data_agree_payload] >>
  metis_tac[scfg_payload_sym, scfg_data_agree_payload]
QED

Theorem scfg_live_position_halt_back:
  scfg_live_position_trace f i s g j t /\ scfg_data_agree s t /\
  j.inst_opcode <> INVOKE /\ step_inst k C' j t = Halt t' ==>
  ?s'. i = j /\ step_inst k C i s = Halt s' /\ scfg_data_agree s' t'
Proof
  strip_tac >>
  `i = j` by
    (drule scfg_halt_step_nonbranch >>
     metis_tac[scfg_live_position_trace_nonbranch]) >>
  gvs[] >> metis_tac[scfg_data_agree_halt_back]
QED

Theorem scfg_data_agree_ret_taint:
  scfg_data_agree s t ==> ret_taint tn i s = ret_taint tn i t
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    metis_tac[scfg_data_agree_eval_operand] >>
  simp[ret_taint_def]
QED

Theorem scfg_context_trace_final_taint_back:
  scfg_context_trace C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  final_taint vs C' t_h tn R ==>
  ?s_h. final_taint vs C s_h tn R /\ scfg_data_agree s_h t_h
Proof
  simp[final_taint_def] >> strip_tac >>
  drule_all scfg_context_trace_live_frame_back >> strip_tac >>
  drule_all scfg_live_position_halt_back >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  gvs[] >>
  rename1 `frame_reachable vs C fs PG G T0 f i src` >>
  rename1 `step_inst fuel C i src = Halt out` >>
  qexists_tac `out` >> simp[] >>
  qexistsl_tac [`fs`, `PG`, `G`, `T0`, `f`, `i`, `src`, `fuel`] >>
  simp[] >>
  metis_tac[scfg_frame_reachable_active, scfg_data_agree_step_taint,
            scfg_data_agree_ret_taint]
QED

Theorem scfg_function_edge_entry:
  scfg_function_edge f g ==> fn_entry_label g = fn_entry_label f
Proof
  simp[scfg_function_edge_def] >> strip_tac >>
  metis_tac[remove_unreachable_blocks_entry, scfg_chain_entry_eq,
            scfg_bypass_entry_eq]
QED

Theorem scfg_function_trace_entry:
  !f g. scfg_function_trace f g ==> fn_entry_label g = fn_entry_label f
Proof
  pure_rewrite_tac[scfg_function_trace_def] >>
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac >>
  metis_tac[scfg_function_edge_entry]
QED

Theorem scfg_function_trace_entry_state:
  scfg_function_trace f g /\ fn_entry_state f s0 ==> fn_entry_state g s0
Proof
  strip_tac >> drule scfg_function_trace_entry >> simp[fn_entry_state_def] >>
  metis_tac[fn_entry_state_def]
QED

Theorem scfg_restriction_dload_payload:
  wf_function f /\ frame_reach C (remove_unreachable_blocks f) s0 j t ==>
  ?s. frame_reach C f s0 j s /\ scfg_payload s t
Proof
  strip_tac >> qexists_tac `t` >> simp[scfg_payload_refl] >>
  metis_tac[scfg_restriction_frame_reach_back, wf_function_def]
QED

Theorem scfg_chain_dload_payload:
  scfg_chain_hyp f a b /\ fn_entry_state f s0 /\
  frame_reach C (scfg_chain f a b) s0 j t /\
  (j.inst_opcode = DLOAD \/ j.inst_opcode = DLOADBYTES) ==>
  ?s. frame_reach C f s0 j s /\ scfg_payload s t
Proof
  strip_tac >>
  `wf_function (scfg_chain f a b)` by metis_tac[scfg_chain_wf] >>
  drule_all scfg_frame_reach_decompose >>
  disch_then (qx_choosel_then [`s`, `bb`, `v`, `e`] strip_assume_tac) >>
  `scfg_chain_exit a b s0 s0` by metis_tac[scfg_chain_initial_exit] >>
  `~s0.vs_halted` by fs[fn_entry_state_def] >>
  `?u. scfg_bprefix C f s0 u /\ ~u.vs_halted /\ scfg_chain_exit a b u s` by
    (irule scfg_chain_bprefix_backward >>
     goal_assum (drule_at Any) >> simp[scfg_bprefix_rules] >>
     conj_tac >- (qexists_tac `s0` >> simp[scfg_bprefix_rules]) >>
     qexists_tac `s0` >> simp[]) >>
  `j.inst_opcode <> PHI` by simp[] >>
  qpat_x_assum `e = _` SUBST_ALL_TAC >>
  drule_all scfg_chain_rooted_observation >> metis_tac[]
QED

Theorem scfg_bypass_dload_image:
  j = scfg_bypass_image A B target l i /\
  (j.inst_opcode = DLOAD \/ j.inst_opcode = DLOADBYTES) ==> i = j
Proof
  strip_tac >> gvs[] >> irule EQ_SYM >>
  match_mp_tac scfg_bypass_image_ordinary_inv >>
  simp[Excl "scfg_bypass_image_classes", is_terminator_def]
QED

Theorem scfg_bypass_dload_payload:
  scfg_bypass_hyp f a b g /\ fn_entry_state f s0 /\
  frame_reach C g s0 j t /\
  (j.inst_opcode = DLOAD \/ j.inst_opcode = DLOADBYTES) ==>
  ?s. frame_reach C f s0 j s /\ scfg_payload s t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `scfg_bypass_aligned a b s0 s0` by
    (`s0.vs_current_bb <> b.bb_label` by
       metis_tac[scfg_bypass_not_entry_label, fn_entry_state_def] >>
     `s0.vs_prev_bb = NONE` by fs[fn_entry_state_def] >>
     simp[scfg_bypass_aligned_def] >>
     qpat_x_assum `s0.vs_prev_bb = NONE` (fn th => rewrite_tac[GSYM th]) >>
     simp[]) >>
  `ctx_bisim C C` by simp[ctx_bisim_refl] >>
  drule_all scfg_bypass_rooted_observe >> strip_tac >>
  `i = j` by metis_tac[scfg_bypass_dload_image] >>
  qexists_tac `u` >> conj_tac >- metis_tac[] >>
  qpat_x_assum `scfg_bypass_aligned a b u t` mp_tac >>
  pure_rewrite_tac[scfg_bypass_aligned_def] >> strip_tac >>
  qpat_x_assum `t = _` SUBST1_TAC >> pure_rewrite_tac[scfg_payload_ctrl]
QED

Theorem scfg_function_edge_dload_payload:
  scfg_function_edge f g /\ fn_entry_state f s0 /\
  frame_reach C g s0 j t /\
  (j.inst_opcode = DLOAD \/ j.inst_opcode = DLOADBYTES) ==>
  ?s. frame_reach C f s0 j s /\ scfg_payload s t
Proof
  simp[scfg_function_edge_def] >>
  metis_tac[scfg_restriction_dload_payload, scfg_chain_dload_payload,
            scfg_bypass_dload_payload]
QED

Theorem scfg_function_trace_dload_payload:
  !f g. scfg_function_trace f g ==>
  !C s0 j t. fn_entry_state f s0 /\ frame_reach C g s0 j t /\
  (j.inst_opcode = DLOAD \/ j.inst_opcode = DLOADBYTES) ==>
  ?s. frame_reach C f s0 j s /\ scfg_payload s t
Proof
  pure_rewrite_tac[scfg_function_trace_def] >>
  ho_match_mp_tac RTC_INDUCT >> conj_tac
  >- (rpt gen_tac >> strip_tac >> qexists_tac `t` >>
      simp[scfg_payload_refl]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `fn_entry_state f' s0` by
    metis_tac[scfg_function_edge_entry, fn_entry_state_def] >>
  first_x_assum drule_all >> strip_tac >>
  drule_all scfg_function_edge_dload_payload >>
  metis_tac[scfg_payload_trans]
QED

Theorem scfg_frame_origin_dload_payload:
  ctx_bisim C C' /\
  (!nm f g. lookup_function nm C.ctx_functions = SOME f /\
             lookup_function nm C'.ctx_functions = SOME g ==>
             scfg_function_trace f g) /\
  frame_origin vs C C' g j t /\
  (j.inst_opcode = DLOAD \/ j.inst_opcode = DLOADBYTES) ==>
  ?f s. raw_reachable vs C f j s /\ scfg_payload s t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `frame_origin _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[frame_origin_def] >> strip_tac >>
  `scfg_function_trace fn g` by metis_tac[] >>
  `frame_reach C g s0 j t` by metis_tac[frame_reach_ctx_bisim] >>
  drule_all scfg_function_trace_dload_payload >> strip_tac >>
  metis_tac[frame_reach_raw_reachable]
QED

Theorem scfg_raw_dload_payload:
  ctx_bisim C C' /\
  (!nm f g. lookup_function nm C.ctx_functions = SOME f /\
             lookup_function nm C'.ctx_functions = SOME g ==>
             scfg_function_trace f g) /\
  LIST_REL (\f g. g.fn_name = f.fn_name /\
                    fn_entry_label g = fn_entry_label f /\
                    frame_sim vs.vs_labels C C' f g)
    C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  raw_reachable vs C' g j t /\
  (j.inst_opcode = DLOAD \/ j.inst_opcode = DLOADBYTES) ==>
  ?f s. raw_reachable vs C f j s /\ scfg_payload s t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `frame_origin vs C C' g j t` by metis_tac[frame_sim_raw_origins] >>
  irule scfg_frame_origin_dload_payload >> metis_tac[]
QED

Theorem scfg_access_ok_transport:
  scfg_data_agree s t /\
  (in_revert_forward f s ==> in_revert_forward g t) /\
  access_ok lo G f i s ==> access_ok lo G g i t
Proof
  strip_tac >>
  `source_memory_read_ranges i s = source_memory_read_ranges i t` by
    metis_tac[scfg_data_agree_read_ranges] >>
  `source_memory_write_ranges i s = source_memory_write_ranges i t` by
    metis_tac[scfg_data_agree_write_ranges] >>
  fs[access_ok_def] >> metis_tac[scfg_data_agree_eval_operand]
QED

Theorem scfg_branch_access_ok:
  i.inst_opcode = JMP \/ i.inst_opcode = JNZ \/ i.inst_opcode = PHI ==>
  access_ok lo G f i s
Proof
  strip_tac >>
  simp[access_ok_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def]
QED

Theorem scfg_live_position_access_ok:
  scfg_live_position_trace f i s g j t /\ scfg_data_agree s t /\
  access_ok lo G f i s ==> access_ok lo G g j t
Proof
  strip_tac >>
  Cases_on `j.inst_opcode = JMP \/ j.inst_opcode = JNZ \/ j.inst_opcode = PHI`
  >- metis_tac[scfg_branch_access_ok] >>
  `i = j` by metis_tac[scfg_live_position_trace_nonbranch] >>
  irule scfg_access_ok_transport >>
  metis_tac[scfg_live_position_trace_revert]
QED

Theorem scfg_data_agree_allocas:
  scfg_data_agree s t ==>
  (allocas_from lo s <=> allocas_from lo t) /\
  (allocas_below_fmp s <=> allocas_below_fmp t)
Proof
  simp[scfg_data_agree_def, execution_frame_def,
       venom_state_component_equality, allocas_from_def,
       allocas_below_fmp_def]
QED

Theorem scfg_context_trace_frame_rows:
  scfg_context_trace C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  ptr_discipline lo C vs /\ ~ctx_has_dalloca C' /\
  frame_reachable vs C' stk PG G tn g j t ==>
  access_ok lo G g j t /\ taint_ok g tn j t /\ allocas_from lo t /\
  (ctx_has_dalloca C' ==> allocas_below_fmp t)
Proof
  strip_tac >> drule_all scfg_context_trace_live_frame_back >> strip_tac >>
  `access_ok lo G f i s /\ taint_ok f tn i s /\ allocas_from lo s` by
    metis_tac[ptr_discipline_def] >>
  metis_tac[scfg_live_position_access_ok, scfg_live_position_trace_taint,
            scfg_data_agree_allocas]
QED

Theorem scfg_simplify_cfg_no_dalloca:
  ~ctx_has_dalloca C ==>
  ~ctx_has_dalloca (C with ctx_functions := MAP simplify_cfg_fn C.ctx_functions)
Proof
  simp[ctx_has_dalloca_def, GSYM EVERY_NOT_EXISTS, EVERY_MAP] >>
  strip_tac >> irule EVERY_MONOTONIC >>
  goal_assum (drule_at Any) >> rpt strip_tac >>
  fs[combinTheory.o_DEF, GSYM EVERY_NOT_EXISTS] >>
  simp[simplify_cfg_fn_def] >>
  ho_match_mp_tac simplify_cfg_fn_with_labels_opcodes >> simp[]
QED

Theorem scfg_simplify_cfg_frame_rows:
  EVERY scfg_static C.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)) C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\ ptr_discipline lo C vs /\
  ~ctx_has_dalloca C /\
  frame_reachable vs (C with ctx_functions := MAP simplify_cfg_fn C.ctx_functions)
    stk PG G tn g j t ==>
  access_ok lo G g j t /\ taint_ok g tn j t /\ allocas_from lo t /\
  (ctx_has_dalloca (C with ctx_functions := MAP simplify_cfg_fn C.ctx_functions) ==>
   allocas_below_fmp t)
Proof
  strip_tac >> irule scfg_context_trace_frame_rows >>
  metis_tac[scfg_context_trace_simplify_cfg, scfg_simplify_cfg_no_dalloca]
QED

Theorem scfg_context_trace_taint_within:
  scfg_context_trace C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  taint_within D C vs ==> taint_within D C' vs
Proof
  strip_tac >> simp[taint_within_def] >> conj_tac
  >- (rpt strip_tac >>
      drule_all scfg_context_trace_live_frame_back >> strip_tac >>
      drule_all scfg_live_position_request_back >>
      disch_then (qspec_then `C` strip_assume_tac) >>
      rename1 `frame_reachable vs C fs PG G tn f i src` >>
      `active_inst f i src` by metis_tac[scfg_frame_reachable_active] >>
      fs[taint_within_def] >>
      first_x_assum drule_all >>
      fs[scfg_data_agree_def, execution_frame_def,
         venom_state_component_equality] >>
      metis_tac[]) >>
  rpt strip_tac >> drule_all scfg_context_trace_final_taint_back >> strip_tac >>
  fs[taint_within_def] >>
  qpat_x_assum `!s_h tn R. _` drule >>
  fs[scfg_data_agree_def, execution_frame_def]
QED

Theorem scfg_payload_dload_offset_ok:
  scfg_payload s t /\ dload_offset_ok C f i s ==>
  dload_offset_ok C' g i t
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    metis_tac[scfg_payload_operand] >>
  `s.vs_code = t.vs_code /\ s.vs_data_section = t.vs_data_section` by
    (qpat_x_assum `scfg_payload s t` mp_tac >>
     simp[scfg_payload_def, scfg_ctrl_def] >>
     disch_then SUBST1_TAC >> simp[]) >>
  fs[dload_offset_ok_def] >> metis_tac[]
QED

Theorem scfg_trace_mem_inv_dload_offset:
  ctx_bisim C C' /\
  (!nm f g. lookup_function nm C.ctx_functions = SOME f /\
             lookup_function nm C'.ctx_functions = SOME g ==>
             scfg_function_trace f g) /\
  LIST_REL (\f g. g.fn_name = f.fn_name /\
                    fn_entry_label g = fn_entry_label f /\
                    frame_sim vs.vs_labels C C' f g)
    C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  mem_inv dload_offset_ok C vs ==>
  mem_inv dload_offset_ok C' vs
Proof
  strip_tac >> fs[mem_inv_raw_reachable] >> conj_tac
  >- (drule list_rel_lookup_function >> simp[] >>
      disch_then (qspec_then `name` mp_tac) >>
      simp[optionTheory.OPTREL_def] >> metis_tac[]) >>
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = DLOAD \/ inst.inst_opcode = DLOADBYTES`
  >- (drule_all scfg_raw_dload_payload >> strip_tac >>
      metis_tac[scfg_payload_dload_offset_ok]) >>
  fs[dload_offset_ok_def]
QED
