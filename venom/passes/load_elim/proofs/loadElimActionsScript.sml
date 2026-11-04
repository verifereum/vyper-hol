Theory loadElimActions
Ancestors
  loadElimDefs loadElimStructure venomWf venomInst cfgTransform list rich_list
  string ASCIInumbers arithmetic combin indexedLists removeUnusedSsaProofs mem2varProofs

Theorem le_fresh_phi_id_bound:
  !m i. m < fresh_phi_id m i
Proof
  simp[fresh_phi_id_def]
QED

Theorem le_fresh_phi_id_inj:
  !m i j. (fresh_phi_id m i = fresh_phi_id m j) <=> (i = j)
Proof
  simp[fresh_phi_id_def]
QED

Theorem le_fresh_phi_var_inj:
  !i j. (fresh_phi_var i = fresh_phi_var j) <=> (i = j)
Proof
  simp[fresh_phi_var_def, toString_11]
QED

Theorem le_fresh_phi_var_prefix:
  !i. isPREFIX "$le_phi_" (fresh_phi_var i)
Proof
  simp[fresh_phi_var_def]
QED

Theorem le_foldl_max_initial:
  !xs z. z <= FOLDL MAX z xs
Proof
  Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then `MAX z h` mp_tac) >> simp[MAX_DEF] >>
  rpt strip_tac >> decide_tac
QED

Theorem le_foldl_max_bound:
  !xs z x. MEM x xs ==> x <= FOLDL MAX z xs
Proof
  Induct >> simp[] >> rpt strip_tac
  >- (mp_tac (Q.SPECL [`xs`, `MAX z x`] le_foldl_max_initial) >>
      simp[MAX_DEF] >> rpt strip_tac >> decide_tac)
  >> first_x_assum irule >> simp[]
QED

Theorem le_fn_max_inst_id_bound:
  !fn i. MEM i (fn_insts fn) ==> i.inst_id <= fn_max_inst_id fn
Proof
  rpt strip_tac >> simp[fn_max_inst_id_def] >>
  irule le_foldl_max_bound >> simp[MEM_MAP] >>
  qexists `i` >> gvs[fn_insts_def, fn_insts_blocks_flat]
QED

Theorem le_compute_phi_action_fields:
  !m cfg result key lbl inst pa.
    compute_phi_action m cfg result key lbl inst = SOME pa ==>
    pa.pa_load_id = inst.inst_id /\
    pa.pa_phi_id = fresh_phi_id m inst.inst_id /\
    pa.pa_phi_out = fresh_phi_var inst.inst_id
Proof
  rpt gen_tac >> simp[compute_phi_action_def] >>
  strip_tac >> gvs[]
QED

(* A collector can keep or discard each source, but cannot replicate it. *)
Theorem le_zero_one_mapi_mem:
  !xs f key out y.
    (!n x a. MEM a (f n x) ==> out a = key x) /\
    MEM y (FLAT (MAPi f xs)) ==>
    MEM (out y) (MAP key xs)
Proof
  rpt strip_tac >> gvs[MEM_FLAT, MEM_MAPi] >>
  res_tac >> gvs[MEM_MAP] >> metis_tac[MEM_EL]
QED

Theorem le_zero_one_mapi_distinct:
  !xs f key out.
    ALL_DISTINCT (MAP key xs) /\
    (!n x. LENGTH (f n x) <= 1) /\
    (!n x a. MEM a (f n x) ==> out a = key x) ==>
    ALL_DISTINCT (MAP out (FLAT (MAPi f xs)))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `ALL_DISTINCT (MAP out (FLAT (MAPi (f o SUC) xs)))` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  Cases_on `f 0 h` >- simp[] >>
  rename1 `f 0 h = a::rest` >>
  `rest = []` by
    (qpat_x_assum `!n x. LENGTH _ <= 1`
       (qspecl_then [`0`, `h`] mp_tac) >>
     Cases_on `rest` >> simp[]) >>
  gvs[] >>
  `out a = key h` by metis_tac[MEM] >>
  simp[] >> strip_tac >>
  gvs[MEM_MAP] >>
  `MEM (out y) (MAP key xs)` by
    (irule le_zero_one_mapi_mem >>
     qexists `f o SUC` >> simp[] >> metis_tac[]) >>
  gvs[MEM_MAP] >> metis_tac[]
QED

(* Name the zero-or-one emission boundary of the collection traversal. *)
Definition le_action_emit_def:
  le_action_emit m ctx cfg result lbl = \idx inst.
    if inst.inst_opcode = ctx.lctx_config.lc_load then
      (case (inst.inst_operands, inst.inst_outputs) of
         ([addr], [_]) =>
           (case FLOOKUP (unwrap_load_lattice (df_at NONE result lbl idx))
                   (load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
                     (normalize_operand ctx.lctx_dfg []) inst) of
              SOME vs =>
                if LENGTH vs > 1 then
                  (case compute_phi_action m cfg result
                     (load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
                       (normalize_operand ctx.lctx_dfg []) inst) lbl inst of
                     SOME pa => [pa] | NONE => [])
                else []
            | NONE => [])
       | _ => [])
    else []
End

Theorem le_collect_phi_actions_eq:
  !m ctx cfg result fn.
    collect_phi_actions m ctx cfg result fn =
    FLAT (MAP (\bb. FLAT (MAPi
      (le_action_emit m ctx cfg result bb.bb_label) bb.bb_instructions))
      fn.fn_blocks)
Proof
  simp[collect_phi_actions_def, le_action_emit_def]
QED

Theorem le_action_emit_cases:
  !m ctx cfg result lbl idx inst.
    le_action_emit m ctx cfg result lbl idx inst = [] \/
    ?pa. le_action_emit m ctx cfg result lbl idx inst = [pa] /\
         inst.inst_opcode = ctx.lctx_config.lc_load /\
         compute_phi_action m cfg result
           (load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
             (normalize_operand ctx.lctx_dfg []) inst) lbl inst = SOME pa
Proof
  rpt gen_tac >> simp[le_action_emit_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) 
QED

Theorem le_action_emit_length:
  !m ctx cfg result lbl idx inst.
    LENGTH (le_action_emit m ctx cfg result lbl idx inst) <= 1
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`m`, `ctx`, `cfg`, `result`, `lbl`, `idx`, `inst`]
    le_action_emit_cases) >> strip_tac >> simp[]
QED

Theorem le_action_emit_fields:
  !m ctx cfg result lbl idx inst pa.
    MEM pa (le_action_emit m ctx cfg result lbl idx inst) ==>
    inst.inst_opcode = ctx.lctx_config.lc_load /\
    pa.pa_load_id = inst.inst_id /\
    pa.pa_phi_id = fresh_phi_id m inst.inst_id /\
    pa.pa_phi_out = fresh_phi_var inst.inst_id
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`m`, `ctx`, `cfg`, `result`, `lbl`, `idx`, `inst`]
    le_action_emit_cases) >> strip_tac >> simp[] >> strip_tac >>
  gvs[] >> drule le_compute_phi_action_fields >> simp[]
QED

Theorem le_collect_phi_action_source:
  !m ctx cfg result fn pa.
    MEM pa (collect_phi_actions m ctx cfg result fn) ==>
    ?bb idx inst.
      MEM bb fn.fn_blocks /\ idx < LENGTH bb.bb_instructions /\
      inst = EL idx bb.bb_instructions /\
      inst.inst_opcode = ctx.lctx_config.lc_load /\
      pa.pa_load_id = inst.inst_id /\
      pa.pa_phi_id = fresh_phi_id m inst.inst_id /\
      pa.pa_phi_out = fresh_phi_var inst.inst_id
Proof
  rpt gen_tac >> simp[le_collect_phi_actions_eq, MEM_FLAT, MEM_MAP,
                       MEM_MAPi] >>
  rpt strip_tac >> gvs[MEM_FLAT, MEM_MAPi] >>
  drule le_action_emit_fields >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem le_nested_zero_one_distinct:
  !bs src emit key out.
    ALL_DISTINCT (FLAT (MAP (\b. MAP key (src b)) bs)) /\
    (!b n x. LENGTH (emit b n x) <= 1) /\
    (!b n x a. MEM a (emit b n x) ==> out a = key x) ==>
    ALL_DISTINCT (FLAT (MAP
      (\b. MAP out (FLAT (MAPi (emit b) (src b)))) bs))
Proof
  Induct >> simp[ALL_DISTINCT_APPEND] >> rpt strip_tac
  >- (irule le_zero_one_mapi_distinct >> simp[] >> metis_tac[])
  >- (first_x_assum irule >> simp[] >> metis_tac[])
  >> gvs[MEM_FLAT, MEM_MAP, MEM_MAPi] >>
  metis_tac[MEM_MAP, MEM_EL]
QED

Theorem le_collect_phi_actions_distinct:
  !m ctx cfg result fn.
    fn_inst_ids_distinct fn ==>
    ALL_DISTINCT (MAP (\pa. pa.pa_load_id)
      (collect_phi_actions m ctx cfg result fn))
Proof
  rpt strip_tac >>
  pure_rewrite_tac[le_collect_phi_actions_eq, MAP_FLAT, MAP_MAP_o, o_DEF] >>
  BETA_TAC >>
  ho_match_mp_tac le_nested_zero_one_distinct >>
  qexists `\i. i.inst_id` >>
  simp[le_action_emit_length] >> conj_tac
  >- gvs[fn_inst_ids_distinct_def, fn_insts_def,
         fn_insts_blocks_flat, MAP_FLAT, MAP_MAP_o, o_DEF]
  >> rpt strip_tac >> drule le_action_emit_fields >> simp[]
QED

Theorem le_collect_phi_action_fields:
  !m ctx cfg result fn pa.
    MEM pa (collect_phi_actions m ctx cfg result fn) ==>
    pa.pa_phi_id = fresh_phi_id m pa.pa_load_id /\
    pa.pa_phi_out = fresh_phi_var pa.pa_load_id
Proof
  rpt strip_tac >> drule le_collect_phi_action_source >>
  rpt strip_tac >> gvs[]
QED

Theorem le_collect_phi_ids:
  !m ctx cfg result fn.
    MAP (\pa. pa.pa_phi_id) (collect_phi_actions m ctx cfg result fn) =
    MAP (fresh_phi_id m)
      (MAP (\pa. pa.pa_load_id) (collect_phi_actions m ctx cfg result fn))
Proof
  rpt gen_tac >> simp[MAP_MAP_o, o_DEF] >>
  irule MAP_CONG >> simp[] >> rpt strip_tac >>
  drule le_collect_phi_action_fields >> simp[]
QED

Theorem le_collect_phi_outputs:
  !m ctx cfg result fn.
    MAP (\pa. pa.pa_phi_out) (collect_phi_actions m ctx cfg result fn) =
    MAP fresh_phi_var
      (MAP (\pa. pa.pa_load_id) (collect_phi_actions m ctx cfg result fn))
Proof
  rpt gen_tac >> simp[MAP_MAP_o, o_DEF] >>
  irule MAP_CONG >> simp[] >> rpt strip_tac >>
  drule le_collect_phi_action_fields >> simp[]
QED

Theorem le_collect_phi_ids_distinct:
  !m ctx cfg result fn.
    fn_inst_ids_distinct fn ==>
    ALL_DISTINCT (MAP (\pa. pa.pa_phi_id)
      (collect_phi_actions m ctx cfg result fn))
Proof
  rpt strip_tac >> pure_rewrite_tac[le_collect_phi_ids] >>
  irule ALL_DISTINCT_MAP_INJ >> simp[le_fresh_phi_id_inj] >>
  irule le_collect_phi_actions_distinct >> simp[]
QED

Theorem le_collect_phi_outputs_distinct:
  !m ctx cfg result fn.
    fn_inst_ids_distinct fn ==>
    ALL_DISTINCT (MAP (\pa. pa.pa_phi_out)
      (collect_phi_actions m ctx cfg result fn))
Proof
  rpt strip_tac >> pure_rewrite_tac[le_collect_phi_outputs] >>
  irule ALL_DISTINCT_MAP_INJ >> simp[le_fresh_phi_var_inj] >>
  irule le_collect_phi_actions_distinct >> simp[]
QED

Theorem le_distinct_buckets:
  !labels actions tag value.
    ALL_DISTINCT labels /\ ALL_DISTINCT (MAP value actions) ==>
    ALL_DISTINCT (FLAT (MAP (\lbl.
      MAP value (FILTER (\a. tag a = lbl) actions)) labels))
Proof
  Induct >> simp[ALL_DISTINCT_APPEND] >> rpt strip_tac
  >- (qpat_x_assum `ALL_DISTINCT (MAP value actions)` mp_tac >>
      Induct_on `actions` >> simp[] >> rpt strip_tac >>
      Cases_on `tag h' = h` >> simp[] >>
      gvs[MEM_MAP, MEM_FILTER] >> metis_tac[])
  >> gvs[MEM_MAP, MEM_FILTER, MEM_FLAT, ALL_DISTINCT_MAP] >>
  drule ALL_DISTINCT_MAP_IMP >>
  disch_then (qspecl_then [`y`, `y'`] mp_tac) >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem le_phis_for_block_source:
  !actions lbl i.
    MEM i (phis_for_block actions lbl) ==>
    ?pa. MEM pa actions /\ pa.pa_join_lbl = lbl /\
         i.inst_id = pa.pa_phi_id /\
         i.inst_opcode = PHI /\
         i.inst_outputs = [pa.pa_phi_out]
Proof
  simp[phis_for_block_def, MEM_MAP, MEM_FILTER] >>
  rpt strip_tac >> goal_assum (drule_at Any) >> simp[]
QED

Theorem le_phis_for_blocks_ids_distinct:
  !bs actions.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bs) /\
    ALL_DISTINCT (MAP (\pa. pa.pa_phi_id) actions) ==>
    ALL_DISTINCT (FLAT (MAP (\bb.
      MAP (\i. i.inst_id) (phis_for_block actions bb.bb_label)) bs))
Proof
  rpt strip_tac >>
  qspecl_then [`MAP (\bb. bb.bb_label) bs`, `actions`,
              `\pa. pa.pa_join_lbl`, `\pa. pa.pa_phi_id`]
    mp_tac le_distinct_buckets >>
  simp[phis_for_block_def, MAP_MAP_o, o_DEF]
QED

Theorem le_phis_for_blocks_outputs_distinct:
  !bs actions.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bs) /\
    ALL_DISTINCT (MAP (\pa. pa.pa_phi_out) actions) ==>
    ALL_DISTINCT (FLAT (MAP (\bb.
      FLAT (MAP (\i. i.inst_outputs) (phis_for_block actions bb.bb_label))) bs))
Proof
  rpt strip_tac >>
  `!xs:phi_action list.
     FLAT (MAP (\pa. [pa.pa_phi_out]) xs) = MAP (\pa. pa.pa_phi_out) xs`
    by (Induct >> simp[]) >>
  qspecl_then [`MAP (\bb. bb.bb_label) bs`, `actions`,
              `\pa. pa.pa_join_lbl`, `\pa. pa.pa_phi_out`]
    mp_tac le_distinct_buckets >>
  simp[phis_for_block_def, MAP_MAP_o, o_DEF]
QED

Theorem le_collect_phi_action_inst:
  !m ctx cfg result fn pa.
    MEM pa (collect_phi_actions m ctx cfg result fn) ==>
    ?inst. MEM inst (fn_insts fn) /\
      inst.inst_opcode = ctx.lctx_config.lc_load /\
      pa.pa_load_id = inst.inst_id /\
      pa.pa_phi_id = fresh_phi_id m inst.inst_id /\
      pa.pa_phi_out = fresh_phi_var inst.inst_id
Proof
  rpt strip_tac >> drule le_collect_phi_action_source >>
  rpt strip_tac >>
  gvs[] >> qexists `EL idx bb.bb_instructions` >>
  simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
  qexists `bb.bb_instructions` >> simp[] >>
  conj_tac >- (qexists `bb` >> simp[]) >>
  metis_tac[MEM_EL]
QED

Theorem le_inserted_phi_fresh_id:
  !ctx cfg result fn lbl inst.
    MEM inst (phis_for_block
      (collect_phi_actions (fn_max_inst_id fn) ctx cfg result fn) lbl) ==>
    fn_max_inst_id fn < inst.inst_id
Proof
  rpt strip_tac >> drule le_phis_for_block_source >> rpt strip_tac >>
  drule le_collect_phi_action_fields >> rpt strip_tac >>
  gvs[le_fresh_phi_id_bound]
QED
