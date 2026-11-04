Theory loadElimInstWf
Ancestors
  loadElimActions loadElimDefs passSharedDefs passSharedProps venomWf
  venomInst cfgTransform list rich_list string
  removeUnusedSsaProofs cfgNormProof

Definition le_supported_config_def:
  le_supported_config cfg <=>
    MEM cfg [memory_config; transient_config; storage_config;
             dload_config; calldataload_config]
End

Definition le_load_opcodes_def:
  le_load_opcodes = [MLOAD; TLOAD; SLOAD; DLOAD; CALLDATALOAD]
End

Definition le_reserved_names_def:
  le_reserved_names ops fn <=>
    !inst v. MEM inst (fn_insts fn) /\ MEM inst.inst_opcode ops /\
      MEM v (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) ==>
      v <> fresh_phi_var inst.inst_id
End

Theorem le_load_elim_inst_cases:
  !ctx actions ll inst.
    load_elim_inst ctx actions ll inst = inst \/
    (?v. load_elim_inst ctx actions ll inst = mk_assign_inst inst v) \/
    load_elim_inst ctx actions ll inst = mk_nop_inst inst
Proof
  rpt gen_tac >> simp[load_elim_inst_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >> metis_tac[]
QED

Theorem le_load_elim_inst_id:
  !ctx actions ll inst.
    (load_elim_inst ctx actions ll inst).inst_id = inst.inst_id
Proof
  rpt gen_tac >>
  qspecl_then [`ctx`, `actions`, `ll`, `inst`]
    strip_assume_tac le_load_elim_inst_cases >>
  simp[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem le_load_elim_inst_outputs:
  !ctx actions ll inst.
    (load_elim_inst ctx actions ll inst).inst_outputs = inst.inst_outputs \/
    (load_elim_inst ctx actions ll inst).inst_outputs = []
Proof
  rpt gen_tac >>
  qspecl_then [`ctx`, `actions`, `ll`, `inst`]
    strip_assume_tac le_load_elim_inst_cases >>
  simp[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem le_supported_config_exclusions:
  !cfg. le_supported_config cfg ==>
    ~is_terminator cfg.lc_load /\ cfg.lc_load <> PHI /\
    (!st. cfg.lc_store = SOME st ==> ~is_terminator st /\ st <> PHI)
Proof
  simp[le_supported_config_def, memory_config_def, transient_config_def,
       storage_config_def, dload_config_def, calldataload_config_def] >>
  rpt strip_tac >> gvs[is_terminator_def]
QED

Theorem le_load_elim_inst_unchanged:
  !ctx actions ll inst.
    inst.inst_opcode <> ctx.lctx_config.lc_load /\
    (!st. ctx.lctx_config.lc_store = SOME st ==> inst.inst_opcode <> st) ==>
    load_elim_inst ctx actions ll inst = inst
Proof
  rpt strip_tac >> simp[load_elim_inst_def] >>
  Cases_on `ctx.lctx_config.lc_store` >> simp[] >> metis_tac[]
QED

Theorem le_load_elim_inst_phi_unchanged:
  !ctx actions ll inst.
    le_supported_config ctx.lctx_config /\ inst.inst_opcode = PHI ==>
    load_elim_inst ctx actions ll inst = inst
Proof
  rpt strip_tac >> drule le_supported_config_exclusions >> strip_tac >>
  irule le_load_elim_inst_unchanged >> simp[] >> metis_tac[]
QED

Theorem le_load_elim_inst_terminator_unchanged:
  !ctx actions ll inst.
    le_supported_config ctx.lctx_config /\ is_terminator inst.inst_opcode ==>
    load_elim_inst ctx actions ll inst = inst
Proof
  rpt strip_tac >> drule le_supported_config_exclusions >> strip_tac >>
  irule le_load_elim_inst_unchanged >> metis_tac[]
QED

Theorem le_load_elim_inst_phi:
  !ctx actions ll inst.
    le_supported_config ctx.lctx_config ==>
    ((load_elim_inst ctx actions ll inst).inst_opcode = PHI <=>
     inst.inst_opcode = PHI)
Proof
  rpt strip_tac >> eq_tac
  >- (qspecl_then [`ctx`, `actions`, `ll`, `inst`]
        strip_assume_tac le_load_elim_inst_cases >>
      simp[mk_assign_inst_def, mk_nop_inst_def])
  >> strip_tac >> drule_all le_load_elim_inst_phi_unchanged >> simp[]
QED

Theorem le_load_elim_inst_terminator:
  !ctx actions ll inst.
    le_supported_config ctx.lctx_config ==>
    (is_terminator (load_elim_inst ctx actions ll inst).inst_opcode <=>
     is_terminator inst.inst_opcode)
Proof
  rpt strip_tac >> eq_tac
  >- (qspecl_then [`ctx`, `actions`, `ll`, `inst`]
        strip_assume_tac le_load_elim_inst_cases >>
      simp[mk_assign_inst_def, mk_nop_inst_def, is_terminator_def])
  >> strip_tac >> drule_all le_load_elim_inst_terminator_unchanged >> simp[]
QED

Theorem le_load_elim_inst_future_load:
  !ctx actions ll inst.
    MEM (load_elim_inst ctx actions ll inst).inst_opcode le_load_opcodes ==>
    (load_elim_inst ctx actions ll inst).inst_opcode = inst.inst_opcode
Proof
  rpt gen_tac >>
  qspecl_then [`ctx`, `actions`, `ll`, `inst`]
    strip_assume_tac le_load_elim_inst_cases >>
  simp[mk_assign_inst_def, mk_nop_inst_def, le_load_opcodes_def]
QED

Theorem le_initial_reserved_names:
  !fn ops.
    EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) ==>
    le_reserved_names ops fn
Proof
  pure_rewrite_tac[le_reserved_names_def, EVERY_MEM] >> rpt strip_tac >>
  `MEM v (fn_all_vars fn)` by
    (gvs[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     irule inst_output_in_fn_all_vars >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >>
  metis_tac[le_fresh_phi_var_prefix]
QED

Theorem le_reserved_names_probe:
  !p q. p <> q ==>
    le_reserved_names [MLOAD]
      (mk_raw_function "probe"
        [<|bb_label := "entry"; bb_instructions :=
           [<|inst_id := p; inst_opcode := PHI;
              inst_operands := []; inst_outputs := [fresh_phi_var p]|>;
            <|inst_id := q; inst_opcode := MLOAD;
              inst_operands := []; inst_outputs := []|>]|>])
Proof
  simp[le_reserved_names_def, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, le_fresh_phi_var_inj] >>
  rpt strip_tac >> gvs[]
QED

Theorem le_distinct_opcode_ids:
  !fn i j.
    fn_inst_ids_distinct fn /\ MEM i (fn_insts fn) /\
    MEM j (fn_insts fn) /\ i.inst_opcode <> j.inst_opcode ==>
    i.inst_id <> j.inst_id
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    gvs[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_flat,
        MAP_FLAT, listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  drule mem2varProofsTheory.ALL_DISTINCT_MAP_IMP >>
  disch_then (qspecl_then [`i`, `j`] mp_tac) >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem le_future_load_action_name_apart:
  !m ctx cfg result fn pa inst.
    fn_inst_ids_distinct fn /\
    MEM pa (collect_phi_actions m ctx cfg result fn) /\
    MEM inst (fn_insts fn) /\
    inst.inst_opcode <> ctx.lctx_config.lc_load ==>
    pa.pa_phi_out <> fresh_phi_var inst.inst_id
Proof
  rpt strip_tac >> drule le_collect_phi_action_inst >>
  rpt strip_tac >> gvs[le_fresh_phi_var_inj] >>
  `inst.inst_opcode <> inst'.inst_opcode` by simp[] >>
  drule_all le_distinct_opcode_ids >> simp[]
QED
