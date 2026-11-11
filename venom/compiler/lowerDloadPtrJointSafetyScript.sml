Theory lowerDloadPtrJointSafety
Ancestors lowerDloadPtrJointReachable lowerDloadPtrTerminalClosure
  lowerDloadPtrRel lowerDloadPtrAggregate ptrDiscipline list
  venomExecSemantics venomState venomMemProps venomInst finite_map
  lowerDloadPtrPhase lowerDloadPtrPhaseNext lowerDloadDefs
  lowerDloadPtrExpansionSafety lowerDloadPtrExpansionTransport lowerDloadPtrDloadOrigins
  lowerDloadPtrBackward lowerDloadPtrSupplyOrigins o1PassContract
  unitShapeDefs venomWf contextRawReachable o1PassLift irSupply
  lowerDloadPtrRawReachable lowerDloadPtrStatic instIdxIndep contextCodegenRel
  lowerDloadPtrBytesTransport codegenRel o1ContractLowerDload venomFnScheduleRunner
  venomExecProps memSafeRun lowerDloadPtrCall lowerDloadPtrBlockEntry
  unitTransformDefs pred_set lowerDloadPtrSourceInv lowerDloadPtrCopiedSafety
  venomFnScheduleRunnerProps

Theorem dload_terminal_mode_allocas_from:
  dload_terminal_mode lo P vs C ds H un g j t ==> allocas_from lo t
Proof
  simp[dload_terminal_mode_def] >> rpt strip_tac >>
  qpat_x_assum `dload_table_stack _ _ _` mp_tac >>
  simp[dload_table_stack_def] >> strip_tac >>
  irule dload_live_layout_allocas_from >>
  qexistsl_tac [`fs`, `0`, `s.vs_alloca_next`, `t.vs_alloca_next`] >>
  simp[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem dload_boundary_allocas_from:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds ==>
  allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  strip_tac >>
  drule dload_boundary_layout >> strip_tac >>
  drule dload_boundary_tables >>
  simp[dload_table_stack_def] >> strip_tac >>
  conj_tac
  >- (irule dload_live_layout_allocas_from >>
      qexistsl_tac [`fs`, `0`, `s.vs_alloca_next`, `t.vs_alloca_next`] >>
      simp[] >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  fs[dload_live_layout_def]
QED

Theorem dload_exec_alloca_lower_bound:
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  exec_alloca i s z = OK t ==> allocas_from lo t
Proof
  simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[allocas_from_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem dload_step_allocas_lower_bound:
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~is_terminator i.inst_opcode /\ ~is_ext_call_op i.inst_opcode /\
  i.inst_opcode <> INVOKE /\ step_inst fuel C i s = OK t ==>
  allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  strip_tac >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (irule step_inst_alloca_next_mono >> metis_tac[]) >>
  conj_tac >- (
    Cases_on `i.inst_opcode = ALLOCA`
    >- (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
        simp[step_inst_non_invoke, step_inst_base_def] >>
        simp[AllCaseEqs()] >> strip_tac >>
        drule_all dload_exec_alloca_lower_bound >> simp[]) >>
    `t.vs_allocas = s.vs_allocas` by
      (`~is_alloca_op i.inst_opcode` by
         (Cases_on `i.inst_opcode` >> gvs[is_alloca_op_def]) >>
       drule_all step_inst_non_alloca_preserves_allocas >> simp[]) >>
    fs[allocas_from_def] >> metis_tac[]) >> decide_tac
QED

Theorem dload_prefix_allocas_lower_bound:
  !n t H un.
    allocas_from lo t0 /\ lo <= t0.vs_alloca_next /\
    (!k. k < n ==> ~is_terminator (EL k xs).inst_opcode /\
      ~is_ext_call_op (EL k xs).inst_opcode /\
      (EL k xs).inst_opcode <> INVOKE) /\
    dload_prefix_match fuel C PH xs n t0 H0 un0 t H un ==>
    allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  Induct_on `n`
  >- simp[dload_prefix_match_def] >>
  rpt gen_tac >> strip_tac >>
  drule dload_prefix_successor >> strip_tac >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `~is_terminator (EL n xs).inst_opcode /\
   ~is_ext_call_op (EL n xs).inst_opcode /\
   (EL n xs).inst_opcode <> INVOKE` by
    (first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
  drule_all dload_step_allocas_lower_bound >>
  gvs[allocas_from_def] >> metis_tac[]
QED

Theorem dload_supply_prefix_allocas_from:
  dload_boundary_core lo fs V Ws PG PH G H0 tn un0 s t0 cs ds /\
  lower_dload_inst_supply supply i = (xs,next) /\
  dload_prefix_match fuel Ct PH xs n t0 H0 un0 t H un /\
  n < LENGTH xs ==> allocas_from lo t
Proof
  strip_tac >> drule dload_boundary_allocas_from >> strip_tac >>
  `!k. k < n ==> ~is_terminator (EL k xs).inst_opcode /\
    ~is_ext_call_op (EL k xs).inst_opcode /\
    (EL k xs).inst_opcode <> INVOKE` by
    (rpt strip_tac >>
     `SUC k < LENGTH xs` by decide_tac >>
     drule_all dload_supply_interior_shape >> strip_tac >>
     gvs[] >> gvs[is_terminator_def, is_ext_call_op_def]) >>
  drule_all dload_prefix_allocas_lower_bound >> simp[]
QED

Theorem dload_boundary_cached_scratch_bounds[local]:
  dload_boundary_core lo (r::rs) V Ws PG PH G H0 tn un0 s t0 cs ds /\
  id IN r.dr_scratch /\ FLOOKUP t0.vs_allocas id = SOME (bb,sz) ==>
  sz = 32 /\ bb + 32 < dimword (:256)
Proof
  strip_tac >>
  drule dload_boundary_layout >> strip_tac >>
  drule dload_boundary_tables >>
  simp[dload_table_stack_def] >> strip_tac >>
  `r.dr_target = t0.vs_allocas` by
    (qpat_x_assum `!k. k < SUC (LENGTH rs) ==> _`
      (qspec_then `0` mp_tac) >> simp[]) >>
  `sz = 32 /\ lo <= bb /\ bb+32 <= t0.vs_alloca_next /\ bb < dimword (:256)` by
    (irule dload_scratch_site_bounds >>
     qexistsl_tac [`id`,`r::rs`,`0`,`s.vs_alloca_next`] >> simp[]) >>
  fs[dload_live_layout_def]
QED

Theorem dload_normal_later_dload_safety:
  o1_ctx_shape C /\ o1_run_state_ok vs /\ o1_src_inv D C vs /\
  callee_first names C.ctx_functions /\ ptr_discipline lo C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  frame_reachable vs C cs PG G tn f i s /\
  frame_reachable vs C' ds PH H un g j t /\
  dload_boundary_core lo fs
    (set (fn_ir_vars f) DIFF {v | retpc_var f v})
    (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
    PG PH G H0 tn un0 s t0 cs ds /\
  dload_control_match q f g s t0 i emitted 0 /\
  dload_prefix_match pfuel C' PH emitted n t0 H0 un0 t H un /\
  FDOM G SUBSET fn_pv P f /\
  LENGTH fs = SUC (LENGTH cs) /\ LENGTH cs = LENGTH ds /\
  (!k. k < LENGTH fs ==>
    (EL k fs).dr_scratch =
      FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
      {id | ?ci. MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))) /\
                 ci.inst_id = id}) /\
  ir_supply_covers_fn q f /\
  (?q'. lower_dload_function_supply q f = (g,q')) /\
  (!k. k < LENGTH cs ==>
    ?qc qc'. lower_dload_function_supply qc (EL k cs).cf_fn =
      ((EL k ds).cf_fn,qc')) /\
  i.inst_opcode = DLOAD /\ 2 <= n /\ n < 4 ==>
  access_ok lo H g (EL n emitted) t /\ taint_ok g un (EL n emitted) t
Proof
  strip_tac >>
  Cases_on `fs` >- gvs[] >> rename1 `LENGTH (r::rs) = _` >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match q f g s t0 i emitted 0` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
       fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `MEM f C.ctx_functions` by
    (qpat_assum `frame_reachable vs C cs PG G tn f i s`
       (mp_then Any mp_tac frame_reachable_raw_certificate) >>
     simp[] >> strip_tac >> simp[]) >>
  `o1_fn_shape C f /\ fn_ptr_ok P f` by
    fs[o1_ctx_shape_def, EVERY_MEM] >>
  `?off out. i.inst_operands = [off] /\ i.inst_outputs = [out]` by
    suspend "shape" >>
  `!v. off = Var v ==> v IN set (fn_ir_vars f) /\ ~retpc_var f v` by
    suspend "operand" >>
  drule_all dload_control_supply_origins >> strip_tac >>
  `off <> Var av` by metis_tac[] >>
  `op_taint un0 off = {}` by suspend "clean" >>
  `?x. eval_operand off t0 = SOME x` by suspend "defined" >>
  `(FLOOKUP t0.vs_allocas (EL 0 emitted).inst_id = NONE ==>
    t0.vs_alloca_next + 32 < dimword (:256))` by suspend "reserve" >>
  `!bb sz. FLOOKUP t0.vs_allocas (EL 0 emitted).inst_id = SOME (bb,sz) ==>
    sz = 32 /\ bb + 32 < dimword (:256)` by suspend "cached" >>
  irule dload_supply_prefix_safety >> simp[] >>
  goal_assum (drule_at (Pat `dload_prefix_match`)) >>
  goal_assum (drule_at (Pat `lower_dload_inst_supply`)) >>
  qexistsl_tac [`off`,`out`,`x`] >>
  rpt conj_tac >> first_assum (MATCH_ACCEPT_TAC o SIMP_RULE (srw_ss()) [])
QED

Resume dload_normal_later_dload_safety[shape]:
  rpt strip_tac >>
  `fn_inst_wf f` by fs[o1_fn_shape_def] >>
  `inst_wf i` by
    (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  gvs[inst_wf_def] >>
  Cases_on `i.inst_operands` >> gvs[] >>
  Cases_on `i.inst_outputs` >> gvs[]
QED

Resume dload_normal_later_dload_safety[operand]:
  rpt strip_tac
  >- (irule fn_ir_vars_operand >> qexists `i` >> simp[]) >>
  `MEM (Var v) i.inst_operands` by simp[] >>
  `opaque_use_ok f` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
  drule_all opaque_use_ok_retpc_use >>
  gvs[retpc_use_ok_def, MEM]
QED

Resume dload_normal_later_dload_safety[cached]:
  rpt strip_tac >>
  `(EL 0 emitted).inst_id IN r.dr_scratch` by
    (qpat_x_assum `!k. k < LENGTH (r::rs) ==> _` (qspec_then `0` mp_tac) >>
     simp[] >> strip_tac >> simp[] >>
     fs[FLOOKUP_DEF]) >>
  drule_all dload_boundary_cached_scratch_bounds >> simp[]
QED

Resume dload_normal_later_dload_safety[clean]:
  rpt strip_tac >>
  `taint_ok f tn i s` by
    (qpat_x_assum `ptr_discipline lo C vs` mp_tac >>
     simp[ptr_discipline_def] >> strip_tac >>
     first_x_assum (drule_at (Pat `frame_reachable`)) >> simp[]) >>
  drule_all dload_offset_clean >> strip_tac >>
  drule dload_boundary_vars >> strip_tac >>
  Cases_on `off` >> gvs[op_taint_def] >>
  fs[dload_vars_match_def] >> metis_tac[]
QED

Resume dload_normal_later_dload_safety[reserve]:
  rpt strip_tac >>
  `vs.vs_allocas = FEMPTY` by
    fs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `dload_headroom_ok C f i s` by suspend "headroom" >>
  `dload_table_stack (r::rs) (s::MAP (\c. c.cf_state) cs)
    (t0::MAP (\d. d.cf_state) ds)` by
    (drule dload_boundary_tables >> simp[]) >>
  irule dload_positive_prefix_fresh_reserve >>
  qpat_assum `frame_reachable vs C cs PG G tn f i s`
    (irule_at (Pat `frame_reachable`)) >>
  qpat_assum `frame_reachable vs C' ds PH H un g j t`
    (irule_at (Pat `frame_reachable`)) >>
  qpat_assum `dload_prefix_match pfuel C' PH emitted n t0 H0 un0 t H un`
    (irule_at (Pat `dload_prefix_match`)) >>
  qpat_assum `lower_dload_inst_supply supply i = (emitted,after)`
    (irule_at (Pat `lower_dload_inst_supply`)) >>
  qpat_assum `dload_table_stack (r::rs) _ _`
    (irule_at (Pat `dload_table_stack`)) >>
  qpat_assum `callee_first names C.ctx_functions`
    (irule_at (Pat `callee_first`)) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> simp[EXTENSION] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `k`
  >- (simp[] >> metis_tac[]) >>
  fs[EL_MAP] >> metis_tac[]
QED

Resume dload_normal_later_dload_safety[headroom]:
  rpt strip_tac >>
  qpat_assum `frame_reachable vs C cs PG G tn f i s`
    (mp_then Any mp_tac o1_src_frame_dload_headroom_ok) >>
  disch_then (qspec_then `D` mp_tac) >> simp[]
QED

Resume dload_normal_later_dload_safety[defined]:
  rpt strip_tac >>
  drule_all dload_supply_expansion >> strip_tac >> gvs[] >>
  `n = SUC (SUC 0) \/ n = SUC (SUC (SUC 0))` by decide_tac >>
  qpat_x_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_asm_rewrite_tac [dload_prefix_match_def, EL, HD, TL, LENGTH] >>
  rpt strip_tac >> gvs[] >>
  irule dload_replay_offset_defined >>
  goal_assum (drule_at (Pat `step_inst`)) >>
  goal_assum (drule_at (Pat `step_inst`)) >> simp[] >> metis_tac[]
QED

Finalise dload_normal_later_dload_safety

Theorem dload_normal_dloadbytes_safety:
  o1_ctx_shape C /\ ptr_discipline lo C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  frame_reachable vs C cs PG G tn f i s /\
  dload_boundary_core lo fs
    (set (fn_ir_vars f) DIFF {v | retpc_var f v})
    (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
    PG PH G H0 tn un0 s t0 cs ds /\
  dload_control_match q f g s t0 i emitted 0 /\
  dload_prefix_match pfuel C' PH emitted n t0 H0 un0 t H un /\
  FDOM G SUBSET fn_pv P f /\ ir_supply_covers_fn q f /\
  i.inst_opcode = DLOADBYTES /\ n < LENGTH emitted ==>
  access_ok lo H g (EL n emitted) t /\ taint_ok g un (EL n emitted) t
Proof
  strip_tac >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
          fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `MEM f C.ctx_functions` by
    (qpat_assum `frame_reachable vs C cs PG G tn f i s`
      (mp_then Any mp_tac frame_reachable_raw_certificate) >>
     simp[] >> strip_tac >> simp[]) >>
  `o1_fn_shape C f /\ fn_ptr_ok P f` by fs[o1_ctx_shape_def, EVERY_MEM] >>
  `?dst off sz. i.inst_operands = [dst;off;sz] /\ i.inst_outputs = []` by
    suspend "shape" >>
  `!v. MEM (Var v) i.inst_operands ==>
    v IN set (fn_ir_vars f) DIFF {v | retpc_var f v}` by suspend "operands" >>
  `?supply after cv supply1.
    lower_dload_inst_supply supply i = (emitted,after) /\
    fresh_ir_var supply = (cv,supply1) /\ cv NOTIN set (fn_ir_vars f)` by
    suspend "supply" >>
  `access_ok lo G f i s /\ taint_ok f tn i s` by
    (qpat_x_assum `ptr_discipline lo C vs` mp_tac >>
     simp[ptr_discipline_def] >> strip_tac >>
     first_x_assum (drule_at (Pat `frame_reachable`)) >> simp[]) >>
  `~in_revert_forward f s` by suspend "forward" >>
  suspend "phases"
QED

Resume dload_normal_dloadbytes_safety[shape]:
  rpt strip_tac >>
  `fn_inst_wf f` by fs[o1_fn_shape_def] >>
  `inst_wf i` by
    (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  gvs[inst_wf_def] >>
  Cases_on `i.inst_operands` >> gvs[] >> rename1 `SUC (LENGTH rest) = 3` >>
  Cases_on `rest` >> gvs[] >> rename1 `SUC (SUC (LENGTH tail)) = 3` >>
  Cases_on `tail` >> gvs[] >>
  rename1 `SUC (SUC (SUC (LENGTH last))) = 3` >>
  Cases_on `last` >> gvs[]
QED

Resume dload_normal_dloadbytes_safety[operands]:
  rpt strip_tac >> simp[] >> conj_tac
  >- (irule fn_ir_vars_operand >> qexists `i` >> simp[]) >>
  `opaque_use_ok f` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
  strip_tac >> drule_all opaque_use_ok_retpc_use >>
  gvs[retpc_use_ok_def, MEM]
QED

Resume dload_normal_dloadbytes_safety[supply]:
  rpt strip_tac >>
  qpat_x_assum `dload_control_match q f g s t0 i emitted 0` mp_tac >>
  pure_rewrite_tac[dload_control_match_def] >> strip_tac >>
  Cases_on `fresh_ir_var is` >> rename1 `fresh_ir_var is = (cv1,supply2)` >>
  qexistsl [`is`,`after`,`cv1`,`supply2`] >> simp[] >>
  Cases_on `lower_dload_blocks_supply q (TAKE bi f.fn_blocks)` >>
  drule lower_dload_blocks_supply_reserved_operand >> strip_tac >>
  drule lower_dload_insts_supply_reserved_operand >> strip_tac >>
  drule fresh_ir_var_contract >> strip_tac >>
  fs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >> metis_tac[]
QED

Resume dload_normal_dloadbytes_safety[forward]:
  rpt strip_tac >>
  `active_inst f i s` by fs[dload_control_match_def] >>
  `ALL_DISTINCT (fn_labels f)` by
    fs[o1_fn_shape_def, fn_shape_ok_def, wf_function_def] >>
  qpat_x_assum `active_inst f i s` mp_tac >>
  pure_rewrite_tac[active_inst_def] >> strip_tac >>
  `lookup_block s.vs_current_bb f.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> fs[fn_labels_def]) >>
  `get_instruction bb s.vs_inst_idx = SOME i` by simp[get_instruction_def] >>
  gvs[in_revert_forward_def] >>
  drule_all revert_forward_at_opcode >> simp[]
QED

Resume dload_normal_dloadbytes_safety[phases]:
  `dload_vars_match fs (set (fn_ir_vars f) DIFF {v | retpc_var f v})
    G H0 tn un0 s t0` by metis_tac[dload_boundary_vars] >>
  `s.vs_labels = t0.vs_labels` by
    (drule dload_boundary_environment >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `op_taint un0 off = {}` by
    (drule_all dloadbytes_scalar_clean >> strip_tac >>
     Cases_on `off` >> gvs[op_taint_def] >>
     fs[dload_vars_match_def] >> metis_tac[]) >>
  Cases_on `n = 0`
  >- (gvs[] >> irule (SIMP_RULE (srw_ss()) [] dloadbytes_supply_zero_safety) >>
      goal_assum (drule_at (Pat `dload_prefix_match`)) >>
      goal_assum (drule_at (Pat `lower_dload_inst_supply`)) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `lower_dload_inst_supply _ _ = _` mp_tac >>
  simp[lower_dload_inst_supply_def] >>
  Cases_on `fresh_inst_id supply1` >> simp[] >>
  rename1 `fresh_inst_id supply1 = (aid,supply2)` >>
  Cases_on `fresh_inst_id supply2` >> simp[] >>
  strip_tac >> gvs[] >>
  `n = SUC 0` by decide_tac >> gvs[] >>
  qpat_x_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  `1 = SUC 0` by simp[] >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  simp[dload_prefix_match_def] >> disch_then strip_assume_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `step_inst pfuel C' a t0` >>
  qmatch_goalsub_abbrev_tac `access_ok lo _ g c _` >>
  `step_inst_base a t0 = OK v` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_non_invoke, Abbr `a`]) >>
  `dload_boundary_core lo fs
    (set (fn_ir_vars f) DIFF {v | retpc_var f v})
    (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
    PG PH G (step_prov PH H0 a v) tn (step_taint a t0 v un0) s v cs ds` by
    (irule dload_boundary_core_add_temporary >> simp[Abbr `a`] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `access_ok lo H1 g c t1` >>
  qmatch_goalsub_abbrev_tac `taint_ok g un1 c t1` >>
  `dload_boundary_core lo fs
    (set (fn_ir_vars f) DIFF {v | retpc_var f v})
    (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
    PG PH G H1 tn un1 s t1 cs ds` by
    (qpat_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ s v _ _`
      (mp_then Any mp_tac dload_boundary_core_index_update) >>
     disch_then (qspecl_then [`SUC t0.vs_inst_idx`,`s.vs_inst_idx`] mp_tac) >>
     simp[Abbr `H1`, Abbr `un1`, Abbr `t1`]) >>
  `op_taint un1 (Var cv) = {}` by suspend "temporary_clean" >>
  `eval_operand off s <> NONE` by suspend "offset_defined" >>
  drule dload_boundary_vars >> strip_tac >>
  drule dload_boundary_layout >> strip_tac >>
  `s.vs_labels = t1.vs_labels` by
    (qpat_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ s t1 _ _`
      (mp_then Any mp_tac dload_boundary_environment) >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  irule dloadbytes_codecopy_safety >>
  simp[Abbr `c`] >>
  goal_assum (drule_at (Pat `dload_vars_match`)) >>
  goal_assum (drule_at (Pat `dload_live_layout`)) >>
  qexistsl [`P`,`f`,`i`,`off`] >>
  simp[] >> metis_tac[]
QED

Resume dload_normal_dloadbytes_safety[temporary_clean]:
  simp[Abbr `un1`, Abbr `a`, op_taint_def, step_taint_def,
       out_taint_def, mem_taint_def, imm_taint_def, adopt_reset_def,
       set_var_taint_def, FLOOKUP_UPDATE] >>
  Cases_on `eval_operand off t0` >> simp[]
QED

Resume dload_normal_dloadbytes_safety[offset_defined]:
  `eval_operand off t0 <> NONE` by
    (qpat_x_assum `step_inst_base a t0 = OK v` mp_tac >>
     simp[Abbr `a`, step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
     metis_tac[optionTheory.NOT_SOME_NONE]) >>
  `!v. off = Var v ==> v IN set (fn_ir_vars f) DIFF {v | retpc_var f v}` by
    (gvs[] >> metis_tac[]) >>
  drule_at (Pat `dload_vars_match`) dload_matched_operand_defined >>
  simp[] >> metis_tac[]
QED

Finalise dload_normal_dloadbytes_safety

(* The unchanged normal replay witness exported by JointReachable. *)
val normal = ``\ds PH H un g j t.
  ?cs PG G tn f i s q emitted n pfuel t0 H0 un0 fs.
    frame_reachable vs C cs PG G tn f i s /\
    dload_boundary_core lo fs
      (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
      PG PH G H0 tn un0 s t0 cs ds /\
    dload_control_match q f g s t0 i emitted 0 /\
    dload_prefix_match pfuel C' PH emitted n t0 H0 un0 t H un /\
    dload_control_match q f g s t i emitted n /\ j = EL n emitted /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v s = NONE <=> lookup_var v t0 = NONE)) /\
    FDOM G SUBSET fn_pv P f /\
    (!k b sz. k < LENGTH PG /\ EL k PG = SOME (b,sz) ==> k IN P f.fn_name) /\
    (!c. MEM c cs ==> FDOM c.cf_prov SUBSET fn_pv P c.cf_fn) /\
    (!c k b sz. MEM c cs /\ k < LENGTH c.cf_params /\
      EL k c.cf_params = SOME (b,sz) ==> k IN P c.cf_fn.fn_name) /\
    LENGTH fs = SUC (LENGTH cs) /\ LENGTH cs = LENGTH ds /\
    (!k. k < LENGTH fs ==>
      (EL k fs).dr_scratch =
        FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
        {id | ?ci. MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))) /\
                   ci.inst_id = id}) /\
    ir_supply_covers_fn q f /\
    (?q'. lower_dload_function_supply q f = (g,q')) /\
    (!k. k < LENGTH cs ==>
      let c = EL k cs; d = EL k ds in
      dload_live_layout lo c.cf_state.vs_alloca_next d.cf_state.vs_alloca_next
        (DROP (SUC k) fs) /\
      dload_equal_environment c.cf_state d.cf_state /\
      c.cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
      c.cf_inst = d.cf_inst /\
      (!a. a IN set (fn_ir_vars c.cf_fn) ==>
        (lookup_var a c.cf_state = NONE <=> lookup_var a d.cf_state = NONE)) /\
      (?qc. ir_supply_covers_fn qc c.cf_fn /\
        (?qc'. lower_dload_function_supply qc c.cf_fn = (d.cf_fn,qc')) /\
        dload_control_match qc c.cf_fn d.cf_fn c.cf_state d.cf_state
          c.cf_inst [c.cf_inst] 0))``;

Theorem dload_normal_safety:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  o1_ctx_shape C /\ EVERY fn_shape_ok C'.ctx_functions /\ o1_run_state_ok vs /\
  o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
  ptr_discipline lo C vs /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  frame_reachable vs C' ds PH H un g j t /\
  (^normal) ds PH H un g j t ==>
  access_ok lo H g j t /\ taint_ok g un j t /\ allocas_from lo t /\
  (ctx_has_dalloca C' ==> allocas_below_fmp t)
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >> gvs[] >>
  `(ctx_has_dalloca C' ==> allocas_below_fmp t)` by
    (metis_tac[lower_dload_src_inv_below_fmp]) >>
  qpat_assum `dload_control_match q f g s t i emitted n`
    (mp_then Any strip_assume_tac dload_control_match_expansion) >>
  `allocas_from lo t` by suspend "allocations" >>
  `access_ok lo H g (EL n emitted) t /\ taint_ok g un (EL n emitted) t`
    suffices_by metis_tac[] >>
  Cases_on `i.inst_opcode = DLOAD` >- suspend "dload" >>
  Cases_on `i.inst_opcode = DLOADBYTES` >- suspend "bytes" >>
  suspend "copied"
QED

Resume dload_normal_safety[allocations]:
  irule dload_supply_prefix_allocas_from >>
  goal_assum (drule_at (Pat `dload_boundary_core`)) >>
  goal_assum (drule_at (Pat `dload_prefix_match`)) >> metis_tac[]
QED

Resume dload_normal_safety[bytes]:
  irule dload_normal_dloadbytes_safety >> simp[] >>
  goal_assum (drule_at (Pat `dload_boundary_core`)) >>
  goal_assum (drule_at (Pat `dload_prefix_match`)) >> metis_tac[]
QED

Resume dload_normal_safety[copied]:
  `n = 0` by metis_tac[dload_control_match_phase] >>
  `emitted = [i]` by
    (qpat_x_assum `lower_dload_inst_supply _ _ = _` mp_tac >>
     simp[lower_dload_inst_supply_def]) >>
  gvs[dload_prefix_zero] >>
  irule dload_normal_copied_safety >> simp[] >>
  goal_assum (drule_at (Pat `dload_boundary_core`)) >> metis_tac[]
QED

Resume dload_normal_safety[dload]:
  Cases_on `2 <= n`
  >- (`n < 4` by
        (`n <> 0` by decide_tac >>
         qpat_assum `dload_control_match q f g s t i emitted n`
           (mp_then Any mp_tac dload_control_match_phase) >> simp[]) >>
      irule dload_normal_later_dload_safety >> simp[] >>
      goal_assum (drule_at (Pat `dload_boundary_core`)) >>
      goal_assum (drule_at (Pat `dload_prefix_match`)) >>
      simp[] >> metis_tac[]) >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match q f g s t0 i emitted 0` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
       fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `MEM f C.ctx_functions` by
    (qpat_assum `frame_reachable vs C cs PG G tn f i s`
       (mp_then Any mp_tac frame_reachable_raw_certificate) >>
     simp[] >> strip_tac >> simp[]) >>
  `o1_fn_shape C f` by fs[o1_ctx_shape_def, EVERY_MEM] >>
  `?off out. i.inst_operands = [off] /\ i.inst_outputs = [out]` by
    suspend "early_shape" >>
  `!v. off = Var v ==> v IN set (fn_ir_vars f) /\ ~retpc_var f v` by
    suspend "early_operand" >>
  drule_all dload_control_supply_origins >> strip_tac >>
  `off <> Var av` by metis_tac[] >>
  `op_taint un0 off = {}` by suspend "early_clean" >>
  irule dload_supply_early_safety >>
  conj_tac >- decide_tac >>
  goal_assum (drule_at (Pat `dload_prefix_match`)) >>
  goal_assum (drule_at (Pat `lower_dload_inst_supply`)) >>
  qexistsl [`av`,`off`,`out`] >> simp[]
QED

Resume dload_normal_safety[early_shape]:
  `fn_inst_wf f` by fs[o1_fn_shape_def] >>
  `inst_wf i` by
    (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  gvs[inst_wf_def] >>
  Cases_on `i.inst_operands` >> gvs[] >>
  Cases_on `i.inst_outputs` >> gvs[]
QED

Resume dload_normal_safety[early_operand]:
  rpt strip_tac
  >- (irule fn_ir_vars_operand >> qexists `i` >> simp[]) >>
  `MEM (Var v) i.inst_operands` by simp[] >>
  `opaque_use_ok f` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
  drule_all opaque_use_ok_retpc_use >> gvs[retpc_use_ok_def, MEM]
QED

Resume dload_normal_safety[early_clean]:
  `fn_ptr_ok P f` by fs[EVERY_MEM] >>
  `taint_ok f tn i s` by
    (qpat_x_assum `ptr_discipline lo C vs` mp_tac >>
     simp[ptr_discipline_def] >> strip_tac >>
     first_x_assum (drule_at (Pat `frame_reachable`)) >> simp[]) >>
  drule_all dload_offset_clean >> strip_tac >>
  drule dload_boundary_vars >> strip_tac >>
  Cases_on `off` >> gvs[op_taint_def] >>
  fs[dload_vars_match_def] >> metis_tac[]
QED

Finalise dload_normal_safety

Theorem lower_dload_stage_fn_shape:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  o1_ctx_shape C ==> EVERY fn_shape_ok C'.ctx_functions
Proof
  simp[ctx_pass_stage_def, o1_ctx_shape_def, EVERY_MEM,
       LIST_REL_EL_EQN, MEM_EL] >> rpt strip_tac >>
  first_x_assum (qspec_then `n` mp_tac) >> impl_tac >- fs[] >> strip_tac >>
  `o1_fn_shape C (EL n C.ctx_functions)` by metis_tac[] >>
  gvs[fn_pass_step_def, AllCaseEqs()] >>
  `MEM (EL n C.ctx_functions) observed.cu_context.ctx_functions` by
    metis_tac[lookup_unique_function_member] >>
  `ir_supply_covers_fn s (EL n C.ctx_functions)` by
    metis_tac[lower_dload_covers_member] >>
  irule lower_dload_function_supply_fn_shape >>
  goal_assum (drule_at (Pat `lower_dload_function_supply`)) >>
  fs[o1_fn_shape_def]
QED

Theorem lower_dload_stage_dynamic_safety:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  frame_reachable vs C' ds PH H un g j t ==>
  access_ok lo H g j t /\ taint_ok g un j t /\ allocas_from lo t /\
  (ctx_has_dalloca C' ==> allocas_below_fmp t)
Proof
  strip_tac >>
  `EVERY fn_shape_ok C'.ctx_functions` by metis_tac[lower_dload_stage_fn_shape] >>
  drule_all dload_joint_reachable >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  disch_then (DISJ_CASES_THEN assume_tac)
  >- (rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
      drule_all (SIMP_RULE (srw_ss()) [] dload_normal_safety) >> simp[]) >>
  metis_tac[dload_terminal_mode_safety, dload_terminal_mode_allocas_from,
            lower_dload_src_inv_below_fmp]
QED
