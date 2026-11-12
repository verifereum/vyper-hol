(*
 * The facts every step of FmpLowering's stage simulation starts from: what
 * row 3 says of the active function and instruction, and how the stage
 * relation relates an instruction's operands, and what the relation's
 * lowering witness is pinned to.
 *
 * TOP-LEVEL:
 *   fmp_stage_frame_facts - row 3's facts at a frame_reachable point
 *   fmp_stage_prov_support - only syntactic pointers carry provenance
 *   fmp_stage_operand     - an operand's source and target values
 *   fmp_stage_witness_pin - the relation's lowering witness agrees with C's
 *                           entry, and its runner is no source output
 *)
Theory fmpStageOpBase
Ancestors
  fmpStageRel ptrStaticDiscipline ptrDiscipline o1PassContract
  fmpStepBridge fmpLowerDefs fmpWfDefs livenessProofs cfgHelpers pred_set
  contextCodegenRel venomExecSemantics venomInst list
  fmpStageOpBaseRoot fmpStageOpBaseActual o1LowerDloadGhost finite_map

Theorem frame_reachable_fn_mem[local]:
  !vs ctx stk PG G tn fn inst s.
    frame_reachable vs ctx stk PG G tn fn inst s ==>
    MEM fn ctx.ctx_functions /\ EVERY (\f. MEM f.cf_fn ctx.ctx_functions) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rw[] >>
  metis_tac[venomInstTheory.lookup_function_MEM]
QED

(* Why: o1_inv 3 and o1_ctx_shape hold of every function, and
   o1_static_inv's access_ok/taint_ok of every frame_reachable point, at
   the eom fmp_stage_ctx names. *)
Theorem fmp_stage_frame_facts:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s ==>
  MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) /\
  o1_fn_shape C fn /\ ssa_form fn /\ make_ssa_input_ok fn /\
  fn.fn_fmp_signature = NONE /\ pre_fmp_ops fn /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn) /\
  access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
  ?P. EVERY (fn_static_ptr_ok P) C.ctx_functions
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[frame_reachable_fn_mem] >>
  `MEM inst (fn_insts fn)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  gvs[fmp_stage_ctx_def, o1_inv_def, o1_static_inv_def, o1_ctx_shape_def,
      o1_pre_def, fmp_free_ctx_def, o1_fn_row_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem static_invoke_prov_positions[local]:
  ptr_use_static_ok P (fn_pv P fn) inst /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\ FDOM G SUBSET fn_pv P fn ==>
  !k site. k < LENGTH (MAP (op_prov G) ops) /\
    EL k (MAP (op_prov G) ops) = SOME site ==> k IN P nm
Proof
  simp[ptr_use_static_ok_def] >> rpt strip_tac >> gvs[] >>
  gvs[EL_MAP] >>
  Cases_on `EL k ops` >> gvs[op_prov_def] >>
  `s IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem frame_reachable_static_prov_support[local]:
  !vs C stk PG G tn fn inst s.
  frame_reachable vs C stk PG G tn fn inst s ==>
  !P. EVERY (fn_static_ptr_ok P) C.ctx_functions ==>
  MEM fn C.ctx_functions /\ FDOM G SUBSET fn_pv P fn /\
  (!k site. k < LENGTH PG /\ EL k PG = SOME site ==> k IN P fn.fn_name) /\
  EVERY (\f. MEM f.cf_fn C.ctx_functions /\
    FDOM f.cf_prov SUBSET fn_pv P f.cf_fn /\
    (!k site. k < LENGTH f.cf_params /\ EL k f.cf_params = SOME site ==>
      k IN P f.cf_fn.fn_name)) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[venomInstTheory.lookup_function_MEM])
  >- (rpt strip_tac >>
      first_x_assum (qspec_then `P` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
      irule step_prov_support >> simp[] >>
      gvs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
      metis_tac[MEM_EL])
  >- (rpt strip_tac >>
      first_x_assum (qspec_then `P` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
      metis_tac[entry_prov_support])
  >- (rpt strip_tac >>
      first_x_assum (qspec_then `P` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
      imp_res_tac venomInstTheory.lookup_function_MEM >> gvs[] >>
      `MEM inst (fn_insts fn)` by
        (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
         metis_tac[MEM_EL]) >>
      `ptr_use_static_ok P (fn_pv P fn) inst` by
        (gvs[EVERY_MEM, fn_static_ptr_ok_def] >> metis_tac[]) >>
      `fn'.fn_name = nm` by
        (fs[lookup_function_def] >> drule venomExecProofsTheory.FIND_P >> simp[]) >>
      drule static_invoke_prov_positions >> simp[] >>
      disch_then (qspecl_then [`G`, `k`, `site`] mp_tac) >> simp[]) >>
  rpt strip_tac >>
  first_x_assum (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  gvs[FDOM_DRESTRICT, SUBSET_DEF]
QED

(* Why: as frame_reachable_prov_support (o1LowerDloadGhost) for
   fn_ptr_ok: only syntactic pointers carry provenance, and a callee's
   pointer parameters are at positions its pointer roots name.  The static
   discipline keeps the INVOKE clause and affine_pointer_ops that proof
   uses. *)
Theorem fmp_stage_prov_support:
  !vs C stk PG G tn fn inst s.
  frame_reachable vs C stk PG G tn fn inst s ==>
  !P. EVERY (fn_static_ptr_ok P) C.ctx_functions ==>
  FDOM G SUBSET fn_pv P fn /\
  (!k site. k < LENGTH PG /\ EL k PG = SOME site ==> k IN P fn.fn_name) /\
  EVERY (\f. FDOM f.cf_prov SUBSET fn_pv P f.cf_fn /\
    (!k site. k < LENGTH f.cf_params /\ EL k f.cf_params = SOME site ==>
      k IN P f.cf_fn.fn_name)) stk
Proof
  rpt strip_tac >>
  drule frame_reachable_static_prov_support >>
  disch_then (qspec_then `P` mp_tac) >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem stage_operand_live[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ active_inst fn inst s /\
  MEM (Var v) inst.inst_operands ==>
  MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
Proof
  strip_tac >>
  `fn_reachable fn s.vs_current_bb` by
    (gvs[make_ssa_input_ok_def, cfgWfTheory.all_reachable_def, active_inst_def] >>
     metis_tac[]) >>
  `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[venomWfPropsTheory.fn_reachable_in_cfg_dfs_pre] >>
  gvs[active_inst_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     gvs[venomWfTheory.wf_function_def, fn_labels_def]) >>
  drule live_vars_at_uses >> simp[] >>
  disch_then irule >> goal_assum (drule_at Any) >>
  simp[operand_var_in_inst_uses]
QED

(* Why: an operand of a non-PHI instruction is used there, so it is live
   at the point (live_vars_at_uses, once the block is known to be in the
   CFG's DFS order, as every frame_reachable block is), and fmp_env_rel
   relates live variables other than the return pc's.  Literals and
   labels evaluate alike on both sides. *)
Theorem fmp_stage_operand:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  inst.inst_opcode <> PHI /\ MEM op inst.inst_operands /\
  (!v. op = Var v ==> ~retpc_var fn v) /\
  eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\
      fmp_value_rel sm (op_prov G op) (op_taint tn op) x y
Proof
  strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `fmp_env_rel sm fn
     (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
     G tn.t_var s t /\ s.vs_labels = t.vs_labels` by
    (gvs[fmp_stage_rel_def, fmp_frame_rel_def] >> metis_tac[]) >>
  Cases_on `op` >>
  gvs[venomStateTheory.eval_operand_def, op_prov_def, op_taint_def,
      fmp_value_rel_def, o1LowerDloadRelocationKernelTheory.ld_value_agree_def,
      word_agree_except_def]
  >- (gvs[venomStateTheory.lookup_var_def] >>
      `MEM s' (live_vars_at (liveness_analyze fn)
                 s.vs_current_bb s.vs_inst_idx)` by
        metis_tac[stage_operand_live, o1_fn_shape_def] >>
      qpat_x_assum `fmp_env_rel _ _ _ _ _ _ _` mp_tac >>
      simp[fmp_env_rel_def] >>
      disch_then (qspec_then `s'` mp_tac) >> simp[op_taint_def] >>
      strip_tac >> qexists `y` >>
      gvs[fmp_value_rel_def,
          o1LowerDloadRelocationKernelTheory.ld_value_agree_def,
          word_agree_except_def])
QED

(* Why: fmp_frame_rel lets its lowering witness (infos, ctx, runner) be
   any that produce fn' from fn.  When the witness has a root, fn' is
   pinned to the actual lowering (ctx_pass_stage, whose observed context
   has C's entry): INITIAL_FMP and FMP_PARAM appear only as the root, the
   former only in the entry's lowering, and the root writes the runner,
   which is fresh for fn. *)
Theorem fmp_stage_witness_pin:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\ MEM fn C.ctx_functions /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
  (fn_is_context_entry ctx fn <=> C.ctx_entry = SOME fn.fn_name) /\
  !i. MEM i (fn_insts fn) ==> ~MEM runner i.inst_outputs
Proof
  strip_tac >>
  drule_all fmp_stage_actual_witness >> strip_tac >>
  imp_res_tac fmp_stage_lowered_root_fingerprint >>
  Cases_on `fmp_stage_root infos0 ctx0 fn` >> gvs[] >>
  Cases_on `fn_is_context_entry ctx fn` >>
  Cases_on `fn_is_context_entry ctx0 fn` >> gvs[]
QED
