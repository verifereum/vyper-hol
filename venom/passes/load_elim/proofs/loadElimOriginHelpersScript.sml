Theory loadElimOriginHelpers
Ancestors
  loadElimDefs list rich_list finite_map indexedLists

Theorem phi_action_lookup_member:
  phi_action_lookup actions id = SOME out ==>
  ?pa. MEM pa actions /\ pa.pa_load_id = id /\ pa.pa_phi_out = out
Proof
  simp[phi_action_lookup_def] >>
  Cases_on `FILTER (\pa. pa.pa_load_id = id) actions` >> simp[] >>
  strip_tac >>
  `MEM h (FILTER (\pa. pa.pa_load_id = id) actions)` by simp[] >>
  gvs[MEM_FILTER] >> metis_tac[]
QED

Theorem phis_for_block_member:
  MEM inst (phis_for_block actions lbl) ==>
  ?pa. MEM pa actions /\ pa.pa_join_lbl = lbl /\
    inst = <| inst_id := pa.pa_phi_id; inst_opcode := PHI;
              inst_operands := pa.pa_phi_ops; inst_outputs := [pa.pa_phi_out] |>
Proof
  simp[phis_for_block_def, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem compute_phi_action_origin:
  compute_phi_action max_id cfg result key lbl inst = SOME pa ==>
  pa.pa_load_id = inst.inst_id /\ pa.pa_load_lbl = lbl /\
  pa.pa_phi_out = fresh_phi_var inst.inst_id /\
  pa.pa_phi_id = fresh_phi_id max_id inst.inst_id
Proof
  simp[compute_phi_action_def] >> strip_tac >> gvs[]
QED

Theorem collect_phi_actions_member:
  MEM pa (collect_phi_actions max_id ctx cfg result fn) ==>
  ?bb idx inst addr out vs.
    MEM bb fn.fn_blocks /\ idx < LENGTH bb.bb_instructions /\
    EL idx bb.bb_instructions = inst /\
    inst.inst_opcode = ctx.lctx_config.lc_load /\
    inst.inst_operands = [addr] /\ inst.inst_outputs = [out] /\
    FLOOKUP (unwrap_load_lattice (df_at NONE result bb.bb_label idx))
      (load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
        (normalize_operand ctx.lctx_dfg []) inst) = SOME vs /\
    LENGTH vs > 1 /\
    compute_phi_action max_id cfg result
      (load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
        (normalize_operand ctx.lctx_dfg []) inst) bb.bb_label inst = SOME pa
Proof
  simp[collect_phi_actions_def, MEM_FLAT, MEM_MAP, MEM_MAPi] >>
  rpt strip_tac >>
  gvs[MEM_FLAT, MEM_MAPi, AllCaseEqs()] >> metis_tac[]
QED

Theorem load_elim_inst_invoke[simp]:
  inst.inst_opcode = INVOKE ==> load_elim_inst ctx actions ll inst = inst
Proof
  simp[load_elim_inst_def]
QED

Theorem load_elim_inst_unchanged:
  inst.inst_opcode <> ctx.lctx_config.lc_load /\
  (!st. ctx.lctx_config.lc_store = SOME st ==> inst.inst_opcode <> st) ==>
  load_elim_inst ctx actions ll inst = inst
Proof
  strip_tac >> simp[load_elim_inst_def] >>
  Cases_on `ctx.lctx_config.lc_store` >> simp[]
QED

Theorem load_elim_inst_changed:
  load_elim_inst ctx actions ll inst = transformed /\ transformed <> inst ==>
  inst.inst_opcode <> INVOKE /\
  ((?addr out v.
      inst.inst_opcode = ctx.lctx_config.lc_load /\
      inst.inst_operands = [addr] /\ inst.inst_outputs = [out] /\
      FLOOKUP (unwrap_load_lattice ll)
        (load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
          (normalize_operand ctx.lctx_dfg []) inst) = SOME [v] /\
      transformed = mk_assign_inst inst v) \/
   (?addr out vs phi_out.
      inst.inst_opcode = ctx.lctx_config.lc_load /\
      inst.inst_operands = [addr] /\ inst.inst_outputs = [out] /\
      FLOOKUP (unwrap_load_lattice ll)
        (load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
          (normalize_operand ctx.lctx_dfg []) inst) = SOME vs /\
      LENGTH vs > 1 /\ phi_action_lookup actions inst.inst_id = SOME phi_out /\
      transformed = mk_assign_inst inst (Var phi_out)) \/
   (?st addr value vs.
      ctx.lctx_config.lc_store = SOME st /\
      inst.inst_opcode <> ctx.lctx_config.lc_load /\ inst.inst_opcode = st /\
      inst.inst_operands = [addr; value] /\
      FLOOKUP (unwrap_load_lattice ll)
        (load_get_write_key ctx.lctx_bp ctx.lctx_addr_space
          (normalize_operand ctx.lctx_dfg []) inst) = SOME vs /\
      vs <> [] /\
      EVERY (\v. case (v,value) of
        (Var _,Var _) => normalize_operand ctx.lctx_dfg [] v =
                         normalize_operand ctx.lctx_dfg [] value
        | _ => v = value) vs /\
      transformed = mk_nop_inst inst))
Proof
  Cases_on `inst.inst_opcode = INVOKE` >- simp[load_elim_inst_def] >>
  Cases_on `inst.inst_opcode = ctx.lctx_config.lc_load` >>
  simp[load_elim_inst_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()]
QED
