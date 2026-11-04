Theory simplifyCfgAvailability
Ancestors
  simplifyCfgFragments simplifyCfgSimTools o1PassLift contextCodegenRel venomInstProofs venomExecProps venomExecProofs venomExecSemantics venomInst venomWf venomState finite_map list

Theorem scfg_step_outputs_defined:
  inst_wf i /\ step_inst k C i s = OK t /\ MEM v i.inst_outputs ==>
  IS_SOME (lookup_var v t)
Proof
  rpt strip_tac >>
  Cases_on `is_terminator i.inst_opcode`
  >- metis_tac[terminator_no_outputs, MEM] >>
  `i.inst_opcode <> PHI` by metis_tac[step_inst_ok_imp_not_phi] >>
  drule_all step_inst_fdom >>
  simp[lookup_var_def, FLOOKUP_DEF] >> metis_tac[]
QED

(* Existing eval_phis_vars_grow supplies PHI definedness monotonicity. *)

Theorem scfg_phi_prefix_length:
  !ps. EVERY (\i. i.inst_opcode = PHI) ps ==>
    phi_prefix_length ps = LENGTH ps
Proof
  Induct >> simp[phi_prefix_length_def]
QED

Theorem scfg_eval_phis_outputs_defined:
  EVERY (\i. i.inst_opcode = PHI) ps /\ eval_phis s ps = OK t /\
  MEM i ps /\ MEM v i.inst_outputs ==> IS_SOME (lookup_var v t)
Proof
  rpt strip_tac >>
  `MEM i (TAKE (phi_prefix_length ps) ps)` by
    simp[scfg_phi_prefix_length] >>
  drule_all eval_phis_outputs_in_fdom_mem >>
  simp[lookup_var_def, FLOOKUP_DEF]
QED

(* A concrete executed path: completed blocks and the current prefix have
   defined all of their outputs. Repeated labels are intentionally allowed. *)
Definition scfg_path_defined_def:
  scfg_path_defined fn path bb n s <=>
    path <> [] /\ is_fn_path fn path /\
    (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\
    LAST path = bb.bb_label /\
    (!k b i v. k < LENGTH path - 1 /\
       lookup_block (EL k path) fn.fn_blocks = SOME b /\
       MEM i b.bb_instructions /\ MEM v i.inst_outputs ==>
       IS_SOME (lookup_var v s)) /\
    (!k v. k < n /\ k < LENGTH bb.bb_instructions /\
       MEM v (EL k bb.bb_instructions).inst_outputs ==>
       IS_SOME (lookup_var v s))
End

Theorem scfg_path_defined_mono:
  scfg_path_defined fn path bb n s /\
  (!v. IS_SOME (lookup_var v s) ==> IS_SOME (lookup_var v t)) ==>
  scfg_path_defined fn path bb n t
Proof
  rw[scfg_path_defined_def] >> metis_tac[]
QED

Theorem scfg_path_defined_entry:
  fn_entry_state fn s0 /\
  lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s0 bb.bb_instructions = OK t ==>
  scfg_path_defined fn [bb.bb_label] bb
    (phi_prefix_length bb.bb_instructions)
    (t with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  rpt strip_tac >>
  drule lookup_block_label >> strip_tac >>
  simp[scfg_path_defined_def, is_fn_path_def] >>
  conj_tac >- gvs[fn_entry_state_def] >>
  rpt strip_tac >>
  drule_all eval_phis_outputs_in_fdom_idx >>
  simp[lookup_var_def, FLOOKUP_DEF]
QED

Theorem scfg_path_defined_step:
  scfg_path_defined fn path bb n s /\ inst_wf i /\
  n < LENGTH bb.bb_instructions /\ EL n bb.bb_instructions = i /\
  step_inst fuel C i s = OK t ==>
  scfg_path_defined fn path bb (SUC n) t
Proof
  rpt strip_tac >>
  `!v. IS_SOME (lookup_var v s) ==> IS_SOME (lookup_var v t)` by
    metis_tac[step_inst_lookup_mono, step_inst_ok_imp_not_phi] >>
  `scfg_path_defined fn path bb n t` by
    metis_tac[scfg_path_defined_mono] >>
  qpat_x_assum `scfg_path_defined fn path bb n s` kall_tac >>
  gvs[scfg_path_defined_def] >>
  conj_tac >- metis_tac[] >> rpt strip_tac >>
  Cases_on `k < n` >- metis_tac[] >>
  `k = n` by decide_tac >> gvs[] >>
  metis_tac[scfg_step_outputs_defined]
QED

Theorem scfg_path_defined_extend:
  scfg_path_defined fn path bb (LENGTH bb.bb_instructions) s /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  fn_cfg_edge fn bb.bb_label next.bb_label ==>
  scfg_path_defined fn (path ++ [next.bb_label]) next 0 s
Proof
  rw[scfg_path_defined_def] >- metis_tac[is_fn_path_snoc]
  >- (Cases_on `path` >> gvs[]) >>
  Cases_on `k < LENGTH path - 1`
  >- (gvs[EL_APPEND_EQN] >> metis_tac[]) >>
  `k = LENGTH path - 1` by decide_tac >>
  `LENGTH path - 1 = PRE (LENGTH path)` by decide_tac >>
  gvs[EL_APPEND_EQN, LAST_EL] >> metis_tac[MEM_EL]
QED

Theorem scfg_path_defined_phis:
  scfg_path_defined fn path bb 0 s /\
  eval_phis s bb.bb_instructions = OK t ==>
  scfg_path_defined fn path bb (phi_prefix_length bb.bb_instructions)
    (t with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  rpt strip_tac >>
  `scfg_path_defined fn path bb 0 t` by
    (irule scfg_path_defined_mono >> qexists_tac `s` >> simp[] >>
     drule eval_phis_vars_grow >>
     simp[lookup_var_def, FLOOKUP_DEF, COND_RAND, pred_setTheory.SUBSET_DEF]) >>
  qpat_x_assum `scfg_path_defined fn path bb 0 s` kall_tac >>
  gvs[scfg_path_defined_def, lookup_var_def] >>
  conj_tac >- metis_tac[] >> rpt strip_tac >>
  drule_all eval_phis_outputs_in_fdom_idx >>
  simp[FLOOKUP_DEF]
QED

Theorem scfg_path_defined_append:
  scfg_path_defined fn path bb (LENGTH bb.bb_instructions) s /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  fn_cfg_edge fn bb.bb_label next.bb_label /\
  eval_phis s next.bb_instructions = OK t ==>
  scfg_path_defined fn (path ++ [next.bb_label]) next
    (phi_prefix_length next.bb_instructions)
    (t with vs_inst_idx := phi_prefix_length next.bb_instructions)
Proof
  rpt strip_tac >>
  irule scfg_path_defined_phis >>
  metis_tac[scfg_path_defined_extend]
QED

Theorem scfg_frame_path_start:
  fn_entry_state fn s0 /\ enters_block fn s0 s ==>
  ?bb path. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    scfg_path_defined fn path bb s.vs_inst_idx s
Proof
  rw[enters_block_def] >>
  `s_phi.vs_current_bb = s0.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  qexistsl_tac [`bb`, `[bb.bb_label]`] >> simp[] >>
  irule scfg_path_defined_entry >> metis_tac[]
QED

Theorem scfg_frame_path_next:
  wf_function fn /\ fn_inst_wf fn /\ active_inst fn i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  scfg_path_defined fn path bb s.vs_inst_idx s /\
  ~is_terminator i.inst_opcode /\ step_inst fuel C i s = OK t ==>
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  scfg_path_defined fn path bb (SUC s.vs_inst_idx)
    (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `inst_wf i` by metis_tac[active_inst_wf] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   EL s.vs_inst_idx bb.bb_instructions = i` by
    (gvs[active_inst_def] >> metis_tac[same_label_same_block]) >>
  `scfg_path_defined fn path bb (SUC s.vs_inst_idx) t` by
    metis_tac[scfg_path_defined_step] >>
  gvs[scfg_path_defined_def, lookup_var_def] >> metis_tac[]
QED

Theorem scfg_path_defined_end:
  scfg_path_defined fn path bb n s /\ bb_well_formed bb /\
  n < LENGTH bb.bb_instructions /\ EL n bb.bb_instructions = i /\
  inst_wf i /\ is_terminator i.inst_opcode /\
  step_inst fuel C i s = OK t ==>
  scfg_path_defined fn path bb (LENGTH bb.bb_instructions) t
Proof
  rpt strip_tac >>
  `n = PRE (LENGTH bb.bb_instructions)` by
    metis_tac[bb_well_formed_def] >>
  `SUC n = LENGTH bb.bb_instructions` by
    (fs[bb_well_formed_def] >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  metis_tac[scfg_path_defined_step]
QED

Theorem scfg_frame_path_block:
  wf_function fn /\ fn_inst_wf fn /\ active_inst fn i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  scfg_path_defined fn path bb s.vs_inst_idx s /\
  is_terminator i.inst_opcode /\ step_inst fuel C i s = OK t /\
  ~t.vs_halted /\ enters_block fn t u ==>
  ?next. lookup_block u.vs_current_bb fn.fn_blocks = SOME next /\
    scfg_path_defined fn (path ++ [next.bb_label]) next u.vs_inst_idx u
Proof
  rpt strip_tac >>
  `inst_wf i` by metis_tac[active_inst_wf] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   EL s.vs_inst_idx bb.bb_instructions = i` by
    (gvs[active_inst_def] >> metis_tac[same_label_same_block]) >>
  `bb_well_formed bb` by metis_tac[wf_function_bb_well_formed] >>
  `scfg_path_defined fn path bb (LENGTH bb.bb_instructions) t` by
    metis_tac[scfg_path_defined_end] >>
  `LAST bb.bb_instructions = i` by
    (gvs[bb_well_formed_def, LAST_EL] >> metis_tac[]) >>
  `i.inst_opcode <> INVOKE` by (Cases_on `i.inst_opcode` >> gvs[is_terminator_def]) >>
  `MEM t.vs_current_bb (get_successors i)` by
    metis_tac[step_inst_base_term_succs, step_inst_non_invoke] >>
  `MEM t.vs_current_bb (bb_succs bb)` by
    (Cases_on `bb.bb_instructions` >> gvs[bb_succs_def, MEM_nub, MEM_REVERSE]) >>
  gvs[enters_block_def] >> rename1 `eval_phis t next.bb_instructions = OK u_phi` >>
  `u_phi.vs_current_bb = t.vs_current_bb /\ next.bb_label = t.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb, lookup_block_label] >>
  qexists_tac `next` >> conj_tac >- simp[] >>
  irule scfg_path_defined_append >>
  qexistsl_tac [`bb`, `t`] >> simp[] >>
  simp[fn_cfg_edge_def] >> metis_tac[]
QED

Theorem scfg_frame_path_defined:
  !C fn s0 i s. frame_reach C fn s0 i s ==>
    wf_function fn /\ fn_inst_wf fn /\ fn_entry_state fn s0 ==>
    ?bb path. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      scfg_path_defined fn path bb s.vs_inst_idx s
Proof
  ho_match_mp_tac frame_reach_strongind >> rpt conj_tac
  >- (rpt strip_tac >> metis_tac[scfg_frame_path_start])
  >- (rpt strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      drule frame_reach_active >> strip_tac >>
      drule_all scfg_frame_path_next >> simp[] >> metis_tac[frame_reach_active]) >>
  rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule frame_reach_active >> strip_tac >>
  drule_all scfg_frame_path_block >> metis_tac[frame_reach_active]
QED

Theorem scfg_frame_path_endpoint:
  wf_function fn /\ fn_inst_wf fn /\ fn_entry_state fn s0 /\
  frame_reach C fn s0 i s /\ is_terminator i.inst_opcode /\
  step_inst fuel C i s = OK t ==>
  ?bb path. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    scfg_path_defined fn path bb (LENGTH bb.bb_instructions) t
Proof
  rpt strip_tac >>
  drule_all scfg_frame_path_defined >> strip_tac >>
  `active_inst fn i s` by metis_tac[frame_reach_active] >>
  `inst_wf i` by metis_tac[active_inst_wf] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   EL s.vs_inst_idx bb.bb_instructions = i` by
    (gvs[active_inst_def] >> metis_tac[same_label_same_block]) >>
  metis_tac[scfg_path_defined_end, wf_function_bb_well_formed]
QED

Theorem scfg_exec_path_endpoint:
  !n fuel C bb s t fn path.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx ==>
    bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
    scfg_path_defined fn path bb s.vs_inst_idx s /\
    exec_block fuel C bb s = OK t ==>
    scfg_path_defined fn path bb (LENGTH bb.bb_instructions) t
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  qpat_x_assum `exec_block fuel C bb s = OK t` mp_tac >>
  simp[Once exec_block_def, get_instruction_def] >>
  Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions` >> simp[] >>
  Cases_on `step_inst fuel C (EL s.vs_inst_idx bb.bb_instructions) s` >> simp[] >>
  rename1 `step_inst fuel C (EL s.vs_inst_idx bb.bb_instructions) s = OK u` >>
  `inst_wf (EL s.vs_inst_idx bb.bb_instructions)` by
    metis_tac[EVERY_EL] >>
  Cases_on `is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode`
  >- (Cases_on `u.vs_halted` >> simp[] >> strip_tac >> gvs[] >>
      metis_tac[scfg_path_defined_end]) >>
  simp[] >> strip_tac >>
  `scfg_path_defined fn path bb (SUC s.vs_inst_idx) u` by
    metis_tac[scfg_path_defined_step] >>
  `scfg_path_defined fn path bb (SUC s.vs_inst_idx)
     (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule scfg_path_defined_mono >> qexists_tac `u` >>
     simp[lookup_var_def]) >>
  first_x_assum irule >> simp[] >>
  qexistsl_tac [`C`, `fuel`,
    `u with vs_inst_idx := SUC s.vs_inst_idx`] >> simp[]
QED

Theorem scfg_run_block_path_endpoint:
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  scfg_path_defined fn path bb 0 s /\ run_block fuel C bb s = OK t ==>
  scfg_path_defined fn path bb (LENGTH bb.bb_instructions) t
Proof
  rpt strip_tac >>
  qpat_x_assum `run_block fuel C bb s = OK t` mp_tac >>
  rewrite_tac[run_block_def] >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >> simp[] >> strip_tac >>
  rename1 `eval_phis _ _ = OK u` >>
  drule_all scfg_path_defined_phis >> strip_tac >>
  irule scfg_exec_path_endpoint >> simp[] >>
  qexistsl_tac [`C`, `fuel`,
    `u with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >> simp[]
QED

Theorem scfg_run_block_path_next:
  wf_function fn /\ fn_inst_wf fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  scfg_path_defined fn path bb 0 s /\ run_block fuel C bb s = OK t ==>
  scfg_path_defined fn path bb (LENGTH bb.bb_instructions) t /\
  fn_cfg_edge fn bb.bb_label t.vs_current_bb /\
  ?next. lookup_block t.vs_current_bb fn.fn_blocks = SOME next /\
    scfg_path_defined fn (path ++ [next.bb_label]) next 0 t
Proof
  rpt strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions` by
    metis_tac[wf_function_bb_well_formed, fn_inst_wf_every_bb] >>
  `scfg_path_defined fn path bb (LENGTH bb.bb_instructions) t` by
    metis_tac[scfg_run_block_path_endpoint] >>
  `MEM t.vs_current_bb (bb_succs bb)` by
    (irule venomExecPropsTheory.run_block_current_bb_in_succs >>
     conj_tac
     >- (gvs[bb_well_formed_def] >> rpt strip_tac >>
         `i < LENGTH bb.bb_instructions` by decide_tac >>
         first_x_assum drule_all >> decide_tac) >>
     metis_tac[bb_well_formed_def]) >>
  `fn_cfg_edge fn bb.bb_label t.vs_current_bb` by
    (simp[fn_cfg_edge_def] >> metis_tac[]) >>
  simp[] >>
  `MEM t.vs_current_bb (fn_labels fn)` by
    metis_tac[wf_function_def, fn_succs_closed_def] >>
  gvs[fn_labels_def, MEM_MAP] >>
  rename1 `MEM next fn.fn_blocks` >>
  `lookup_block t.vs_current_bb fn.fn_blocks = SOME next` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     gvs[wf_function_def, fn_labels_def]) >>
  qexists_tac `next` >> conj_tac >- metis_tac[] >>
  irule scfg_path_defined_extend >> metis_tac[]
QED

Theorem scfg_bprefix_path_defined:
  !C fn s t. scfg_bprefix C fn s t ==>
  wf_function fn /\ fn_inst_wf fn ==>
  !bb path. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    scfg_path_defined fn path bb 0 s ==>
    ?last route. lookup_block t.vs_current_bb fn.fn_blocks = SOME last /\
      scfg_path_defined fn route last 0 t
Proof
  ho_match_mp_tac scfg_bprefix_ind >> rpt strip_tac
  >- metis_tac[] >>
  gvs[] >> drule_all scfg_run_block_path_next >> strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

Theorem scfg_bprefix_entry_path:
  wf_function fn /\ fn_inst_wf fn /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s ==>
  ?bb path. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    scfg_path_defined fn path bb 0 s
Proof
  rpt strip_tac >>
  `?bb. lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_entry_state_def, fn_entry_label_def, entry_block_def,
         lookup_block_def, FIND_thm]) >>
  `scfg_path_defined fn [bb.bb_label] bb 0 s0` by
    (drule lookup_block_label >>
     simp[scfg_path_defined_def, is_fn_path_def] >>
     gvs[fn_entry_state_def]) >>
  drule_all scfg_bprefix_path_defined >> metis_tac[]
QED

Theorem scfg_bprefix_path_endpoint:
  wf_function fn /\ fn_inst_wf fn /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block fuel C bb s = OK t ==>
  ?path. scfg_path_defined fn path bb (LENGTH bb.bb_instructions) t /\
    fn_cfg_edge fn bb.bb_label t.vs_current_bb
Proof
  rpt strip_tac >>
  drule_all scfg_bprefix_entry_path >> strip_tac >> gvs[] >>
  drule_all scfg_run_block_path_next >> metis_tac[]
QED

Theorem scfg_bprefix_incoming:
  wf_function fn /\ fn_inst_wf fn /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  s = s0 \/
  ?pb path. MEM pb fn.fn_blocks /\
    fn_cfg_edge fn pb.bb_label bb.bb_label /\
    s.vs_prev_bb = SOME pb.bb_label /\
    scfg_path_defined fn path pb (LENGTH pb.bb_instructions) s
Proof
  rpt strip_tac >> drule scfg_bprefix_last >> strip_tac
  >- simp[] >>
  disj2_tac >>
  `MEM pb fn.fn_blocks /\ pb.bb_label = u.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `bb_well_formed pb /\ EVERY inst_wf pb.bb_instructions` by
    metis_tac[wf_function_bb_well_formed, fn_inst_wf_every_bb] >>
  `s.vs_prev_bb = SOME u.vs_current_bb` by
    (irule venomExecPropsTheory.run_block_ok_prev_bb_exact >>
     qexistsl_tac [`pb`, `C`, `k`] >> simp[] >> conj_tac
     >- (gvs[bb_well_formed_def] >> rpt strip_tac >>
         `i < LENGTH pb.bb_instructions` by decide_tac >>
         first_x_assum drule_all >> decide_tac) >>
     metis_tac[bb_well_formed_def]) >>
  drule_all scfg_bprefix_path_endpoint >> strip_tac >>
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
  qexistsl_tac [`pb`, `path`] >> gvs[]
QED

Theorem scfg_bprefix_incoming_nonentry:
  wf_function fn /\ fn_inst_wf fn /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\ s <> s0 ==>
  ?pb path. MEM pb fn.fn_blocks /\
    fn_cfg_edge fn pb.bb_label bb.bb_label /\
    s.vs_prev_bb = SOME pb.bb_label /\
    scfg_path_defined fn path pb (LENGTH pb.bb_instructions) s
Proof
  metis_tac[scfg_bprefix_incoming]
QED

Theorem scfg_path_use_defined:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  scfg_path_defined fn path bb n s /\
  n < LENGTH bb.bb_instructions /\ EL n bb.bb_instructions = i /\
  def_on_all_paths fn bb (SOME i) v ==>
  IS_SOME (lookup_var v s)
Proof
  rpt strip_tac >>
  qpat_x_assum `def_on_all_paths _ _ _ _` mp_tac >>
  simp[def_on_all_paths_def] >>
  disch_then (qspec_then `path` mp_tac) >>
  impl_tac >- gvs[scfg_path_defined_def] >>
  strip_tac
  >- (`lookup_block def_bb.bb_label fn.fn_blocks = SOME def_bb` by
        (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
      gvs[scfg_path_defined_def] >> metis_tac[]) >>
  `j = n` by metis_tac[inst_ids_el_eq, wf_function_def] >>
  gvs[scfg_path_defined_def] >> metis_tac[arithmeticTheory.LESS_TRANS]
QED

Theorem scfg_frame_operand_defined:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_entry_state fn s0 /\ frame_reach C fn s0 i s /\
  i.inst_opcode <> PHI /\ MEM (Var v) i.inst_operands ==>
  IS_SOME (lookup_var v s)
Proof
  rpt strip_tac >>
  drule_all scfg_frame_path_defined >> strip_tac >>
  `active_inst fn i s` by metis_tac[frame_reach_active] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   EL s.vs_inst_idx bb.bb_instructions = i` by
    (gvs[active_inst_def] >> metis_tac[same_label_same_block]) >>
  `def_on_all_paths fn bb (SOME i) v` by
    (fs[fn_defs_reach_uses_def] >> metis_tac[MEM_EL]) >>
  irule scfg_path_use_defined >> metis_tac[]
QED

Theorem scfg_path_endpoint_defined:
  wf_function fn /\ scfg_path_defined fn path bb (LENGTH bb.bb_instructions) s /\
  def_on_all_paths fn bb NONE v ==>
  IS_SOME (lookup_var v s)
Proof
  rpt strip_tac >>
  qpat_x_assum `def_on_all_paths _ _ _ _` mp_tac >>
  simp[def_on_all_paths_def] >>
  disch_then (qspec_then `path` mp_tac) >>
  impl_tac >- gvs[scfg_path_defined_def] >>
  strip_tac
  >- (`lookup_block def_bb.bb_label fn.fn_blocks = SOME def_bb` by
        (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
      gvs[scfg_path_defined_def] >> metis_tac[]) >>
  gvs[scfg_path_defined_def] >> metis_tac[]
QED

Theorem scfg_phi_edge_defined:
  wf_function fn /\ fn_defs_reach_uses fn /\
  scfg_path_defined fn path pred_bb (LENGTH pred_bb.bb_instructions) s /\
  MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
  MEM pred_bb fn.fn_blocks /\ fn_cfg_edge fn pred_bb.bb_label bb.bb_label /\
  MEM (pred_bb.bb_label,v) (phi_pairs i.inst_operands) ==>
  IS_SOME (lookup_var v s)
Proof
  rpt strip_tac >>
  `def_on_all_paths fn pred_bb NONE v` by
    (fs[fn_defs_reach_uses_def] >> metis_tac[]) >>
  irule scfg_path_endpoint_defined >> metis_tac[]
QED
