(* Canonical readonly analysis builders and copy-forwarding structure. *)

Theory readonlyMemoryArgsProps
Ancestors
  readonlyMemoryArgsDefs invokeCopyFwdCommonDefs internalReturnCopyFwdDefs
  readonlyInvokeCopyFwdDefs copyFwdEquiv callLayoutDefs basePtrDefs
  venomEffects memLocDefs o1PassContract o1PassLift ptrDiscipline
  unitShapeDefs dretDesugarDefs unitTransformDefs passSimulationDefs venomWf
  venomInst venomInstProps venomExecSemantics venomExecProps venomState
  stateEquiv stateEquivProps passSharedDefs passSharedProps passResidualFrame
  stateFrame venomRetProps vfmTypes While list rich_list finite_map pred_set
  arithmetic pair option relation words

(* ==========================================================================
   1. Canonical Function Metadata and Readonly Analysis Builders
   ========================================================================== *)

Definition icf_fn_meta_of_fn_def:
  icf_fn_meta_of_fn (fn : ir_function) : invoke_fn_meta =
    <| ifm_invoke_param_count := LENGTH (fn_user_param_insts fn);
       ifm_has_memory_return_buffer :=
         (fn.fn_call_abi.ica_has_memory_return_buffer = SOME T) |>
End

Definition icf_fn_meta_of_def:
  icf_fn_meta_of (ctx : venom_context) : (string, invoke_fn_meta) fmap =
    FOLDL (\fm fn. fm |+ (fn.fn_name, icf_fn_meta_of_fn fn))
      FEMPTY ctx.ctx_functions
End

Definition readonly_mem_analyze_def:
  readonly_mem_analyze (ctx : venom_context) : (string, bool list) fmap =
    rma_analyze (icf_fn_meta_of ctx) ctx
End

(* ==========================================================================
   2. Structural Compatibility of Copy-Forwarded Instructions
   ========================================================================== *)

Definition icf_inst_compat_def:
  icf_inst_compat (i1 : instruction) (i2 : instruction) : bool <=>
    i2.inst_id = i1.inst_id /\
    (is_terminator i2.inst_opcode <=> is_terminator i1.inst_opcode) /\
    ((i2.inst_opcode = PHI) <=> (i1.inst_opcode = PHI)) /\
    ((i2.inst_opcode = i1.inst_opcode /\
      i2.inst_outputs = i1.inst_outputs /\
      LENGTH i2.inst_operands = LENGTH i1.inst_operands) \/
     (i1.inst_opcode = MCOPY /\ i2 = mk_nop_inst i1))
End

Definition icf_inst_cfg_compat_def:
  icf_inst_cfg_compat (i1 : instruction) (i2 : instruction) : bool <=>
    icf_inst_compat i1 i2 /\
    (is_terminator i1.inst_opcode ==>
     i2.inst_opcode = i1.inst_opcode /\
     MAP get_label i2.inst_operands = MAP get_label i1.inst_operands)
End

Theorem mk_nop_inst_eq_by_id:
  !i1 i2.
    i2.inst_id = i1.inst_id /\
    i2.inst_opcode = NOP /\
    i2.inst_operands = [] /\
    i2.inst_outputs = [] ==>
    i2 = mk_nop_inst i1
Proof
  rw[mk_nop_inst_def, venomInstTheory.instruction_component_equality]
QED

Theorem icf_inst_compat_refl[simp]:
  !i. icf_inst_compat i i
Proof
  simp[icf_inst_compat_def]
QED

Theorem icf_inst_compat_mk_nop:
  !i. i.inst_opcode = MCOPY ==> icf_inst_compat i (mk_nop_inst i)
Proof
  rw[icf_inst_compat_def, mk_nop_inst_def, is_terminator_def]
QED

Theorem icf_inst_compat_trans:
  !i1 i2 i3.
    icf_inst_compat i1 i2 /\ icf_inst_compat i2 i3 ==>
    icf_inst_compat i1 i3
Proof
  rw[icf_inst_compat_def] >>
  gvs[mk_nop_inst_def, venomInstTheory.instruction_component_equality]
QED

Theorem icf_inst_cfg_compat_refl[simp]:
  !i. icf_inst_cfg_compat i i
Proof
  simp[icf_inst_cfg_compat_def]
QED

Theorem icf_inst_cfg_compat_mk_nop:
  !i. i.inst_opcode = MCOPY ==> icf_inst_cfg_compat i (mk_nop_inst i)
Proof
  rw[icf_inst_cfg_compat_def, icf_inst_compat_mk_nop] >>
  `~is_terminator MCOPY` by EVAL_TAC >> fs[]
QED

Theorem icf_inst_cfg_compat_trans:
  !i1 i2 i3.
    icf_inst_cfg_compat i1 i2 /\ icf_inst_cfg_compat i2 i3 ==>
    icf_inst_cfg_compat i1 i3
Proof
  rw[icf_inst_cfg_compat_def] >> metis_tac[icf_inst_compat_trans]
QED

Theorem LIST_REL_icf_inst_compat_refl[simp]:
  !insts. LIST_REL icf_inst_compat insts insts
Proof
  Induct >> simp[]
QED

Theorem LIST_REL_icf_inst_compat_trans:
  !l1 l2 l3.
    LIST_REL icf_inst_compat l1 l2 /\
    LIST_REL icf_inst_compat l2 l3 ==>
    LIST_REL icf_inst_compat l1 l3
Proof
  metis_tac[LIST_REL_trans, icf_inst_compat_trans]
QED

Theorem LIST_REL_icf_inst_cfg_compat_refl[simp]:
  !insts. LIST_REL icf_inst_cfg_compat insts insts
Proof
  Induct >> simp[]
QED

Theorem LIST_REL_icf_inst_cfg_compat_trans:
  !l1 l2 l3.
    LIST_REL icf_inst_cfg_compat l1 l2 /\
    LIST_REL icf_inst_cfg_compat l2 l3 ==>
    LIST_REL icf_inst_cfg_compat l1 l3
Proof
  metis_tac[LIST_REL_trans, icf_inst_cfg_compat_trans]
QED

Theorem LIST_REL_icf_inst_cfg_imp_compat:
  !l1 l2.
    LIST_REL icf_inst_cfg_compat l1 l2 ==>
    LIST_REL icf_inst_compat l1 l2
Proof
  Induct_on `LIST_REL` >> rw[icf_inst_cfg_compat_def]
QED

Theorem LIST_REL_icf_inst_compat_ids:
  !l1 l2.
    LIST_REL icf_inst_compat l1 l2 ==>
    MAP (\i. i.inst_id) l2 = MAP (\i. i.inst_id) l1
Proof
  Induct_on `LIST_REL` >> rw[icf_inst_compat_def]
QED

Theorem icf_inst_cfg_compat_get_successors:
  !i1 i2.
    icf_inst_cfg_compat i1 i2 ==>
    get_successors i2 = get_successors i1
Proof
  rw[icf_inst_cfg_compat_def, icf_inst_compat_def, get_successors_def]
QED

Theorem LIST_REL_icf_inst_cfg_compat_LAST:
  !l1 l2.
    l1 <> [] /\ LIST_REL icf_inst_cfg_compat l1 l2 ==>
    l2 <> [] /\ icf_inst_cfg_compat (LAST l1) (LAST l2)
Proof
  Induct_on `LIST_REL` >> rw[] >>
  Cases_on `l1` >> gvs[]
QED

Theorem LIST_REL_icf_inst_cfg_compat_bb_wf_succs:
  !bb1 bb2.
    bb2.bb_label = bb1.bb_label /\
    LIST_REL icf_inst_cfg_compat bb1.bb_instructions bb2.bb_instructions ==>
    (bb_well_formed bb2 <=> bb_well_formed bb1) /\
    bb_succs bb2 = bb_succs bb1 /\
    MAP (\i. i.inst_id) bb2.bb_instructions =
      MAP (\i. i.inst_id) bb1.bb_instructions
Proof
  rpt strip_tac
  >- (`LENGTH bb2.bb_instructions = LENGTH bb1.bb_instructions` by
        metis_tac[LIST_REL_LENGTH] >>
      `!k. k < LENGTH bb1.bb_instructions ==>
           icf_inst_compat (EL k bb1.bb_instructions)
                           (EL k bb2.bb_instructions)` by
        (rpt strip_tac >>
         drule LIST_REL_icf_inst_cfg_imp_compat >>
         disch_then (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
         simp[]) >>
      Cases_on `bb1.bb_instructions = []`
      >- (`bb2.bb_instructions = []` by
            (Cases_on `bb2.bb_instructions` >> gvs[]) >>
          simp[bb_well_formed_def]) >>
      drule_all LIST_REL_icf_inst_cfg_compat_LAST >> strip_tac >>
      `is_terminator (LAST bb2.bb_instructions).inst_opcode <=>
       is_terminator (LAST bb1.bb_instructions).inst_opcode` by
        fs[icf_inst_cfg_compat_def, icf_inst_compat_def] >>
      `!k. k < LENGTH bb1.bb_instructions ==>
           (is_terminator (EL k bb2.bb_instructions).inst_opcode <=>
            is_terminator (EL k bb1.bb_instructions).inst_opcode)` by
        (gen_tac >> strip_tac >> res_tac >>
         fs[icf_inst_compat_def]) >>
      `!k. k < LENGTH bb1.bb_instructions ==>
           ((EL k bb2.bb_instructions).inst_opcode = PHI <=>
            (EL k bb1.bb_instructions).inst_opcode = PHI)` by
        (gen_tac >> strip_tac >> res_tac >>
         fs[icf_inst_compat_def]) >>
      simp[bb_well_formed_def] >> eq_tac >> rpt strip_tac >> gvs[] >>
      metis_tac[])
  >- (Cases_on `bb1.bb_instructions = []`
      >- (`bb2.bb_instructions = []` by
            (Cases_on `bb2.bb_instructions` >> gvs[]) >>
          simp[bb_succs_def]) >>
      drule_all LIST_REL_icf_inst_cfg_compat_LAST >> strip_tac >>
      drule icf_inst_cfg_compat_get_successors >> strip_tac >>
      Cases_on `bb1.bb_instructions` >> Cases_on `bb2.bb_instructions` >>
      gvs[bb_succs_def])
  >- (drule LIST_REL_icf_inst_cfg_imp_compat >>
      metis_tac[LIST_REL_icf_inst_compat_ids])
QED

(* ==========================================================================
   4. Block and Function Copy-Forwarding Compatibility and Soundness
   ========================================================================== *)

Definition icf_auth_ok_def:
  icf_auth_ok (fn_meta : (string, invoke_fn_meta) fmap)
              (ctx_fns : ir_function list)
              (rma : (string, bool list) fmap) : bool <=>
    (?inst. icf_invoke_has_ret_buf fn_meta ctx_fns inst) \/
    (?inst pos. inst.inst_opcode = INVOKE /\ icf_is_readonly_op rma inst pos)
End

Theorem ricf_try_forward_sites[local]:
  !ctx bb copy_idx src_var_opt rewrite_sites.
    ricf_try_forward ctx bb copy_idx = SOME (src_var_opt, rewrite_sites) ==>
    copy_idx < LENGTH bb.bb_instructions /\
    (EL copy_idx bb.bb_instructions).inst_opcode = MCOPY /\
    (!ri pos.
       MEM (ri, pos) rewrite_sites ==>
       ~(THE (findi (\el. el.inst_id = ri.inst_id) bb.bb_instructions) < copy_idx))
Proof
  simp[ricf_try_forward_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `EVERY ($~ o (\idx. idx < copy_idx)) _`
    (mp_tac o REWRITE_RULE [EVERY_MAP, EVERY_MEM]) >>
  disch_then drule >> simp[]
QED

Theorem ricf_try_forward_prefix_and_copy:
  !ctx bb copy_idx src_var_opt rewrite_sites src_op.
    ricf_try_forward ctx bb copy_idx = SOME (src_var_opt, rewrite_sites) ==>
    copy_idx < LENGTH bb.bb_instructions /\
    LENGTH (ricf_apply_forward bb.bb_instructions copy_idx src_op rewrite_sites) =
      LENGTH bb.bb_instructions /\
    (EL copy_idx bb.bb_instructions).inst_opcode = MCOPY /\
    EL copy_idx
      (ricf_apply_forward bb.bb_instructions copy_idx src_op rewrite_sites) =
      mk_nop_inst (EL copy_idx bb.bb_instructions) /\
    (!i. i < copy_idx ==>
         EL i (ricf_apply_forward bb.bb_instructions copy_idx src_op rewrite_sites) =
           EL i bb.bb_instructions)
Proof
  rpt gen_tac >> strip_tac >>
  drule ricf_try_forward_sites >> strip_tac >>
  simp[ricf_apply_forward_def, indexedListsTheory.EL_MAPi] >>
  rpt strip_tac >>
  `FILTER (\(ri,pos). ri.inst_id = (EL i bb.bb_instructions).inst_id)
     rewrite_sites = []` by
    (simp[listTheory.FILTER_EQ_NIL, EVERY_MEM, pairTheory.FORALL_PROD] >>
     rpt strip_tac >>
     `i < LENGTH bb.bb_instructions` by decide_tac >>
     drule_then (qspec_then `\el. el.inst_id = p_1.inst_id` mp_tac) findi_EL_le >>
     first_x_assum drule >> rpt strip_tac >> gvs[] >> decide_tac) >>
  simp[]
QED

Theorem phi_prefix_eval_phis_agree_before:
  !l1 l2 k s.
    k < LENGTH l1 /\
    LENGTH l2 = LENGTH l1 /\
    (EL k l1).inst_opcode <> PHI /\
    (EL k l2).inst_opcode <> PHI /\
    (!i. i < k ==> EL i l2 = EL i l1) ==>
    phi_prefix_length l2 = phi_prefix_length l1 /\
    phi_prefix_length l1 <= k /\
    eval_phis s l2 = eval_phis s l1
Proof
  Induct_on `l1` >> Cases_on `l2` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `k` >> gvs[]
  >- simp[phi_prefix_length_def, eval_phis_def]
  >- (`h' = h` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      `!i. i < n ==> EL i t = EL i l1` by
        (rpt strip_tac >>
         first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]) >>
      gvs[] >>
      Cases_on `h.inst_opcode = PHI` >>
      simp[phi_prefix_length_def, eval_phis_def] >>
      first_x_assum (qspecl_then [`t`, `n`, `s`] mp_tac) >>
      simp[])
QED

(* ==========================================================================
   5. Evaluation Helpers for Concrete Copy-Forwarding Witnesses
   ========================================================================== *)

Theorem icf_collect_aliases_no_assign:
  !dfg root.
    EVERY (\inst. inst.inst_opcode <> ASSIGN) (dfg_get_uses dfg root) ==>
    icf_collect_aliases dfg root = {root}
Proof
  rw[icf_collect_aliases_def] >>
  `icf_aliases_step dfg {root} = (F, {root})` by
    (simp[icf_aliases_step_def] >>
     `BIGUNION (IMAGE (\inst. if inst.inst_opcode = ASSIGN then
                      case inst.inst_outputs of [out] => {out} | _ => {}
                    else {}) (set (dfg_get_uses dfg root))) DIFF {root} = {}` by
       (fs[EXTENSION, EVERY_MEM, PULL_EXISTS] >> rw[] >>
        metis_tac[]) >>
     `!U r:string. U DIFF {r} = {} ==> {r} UNION U = {r}` by
       (pure_rewrite_tac[EXTENSION, IN_DIFF, NOT_IN_EMPTY, IN_UNION, IN_SING] >>
        metis_tac[]) >>
     simp[] >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >> simp[] >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >> simp[]
QED

Theorem icf_alias_use_positions_sing[simp]:
  !dfg root.
    icf_alias_use_positions dfg {root} =
    MAP (\(inst, pos). (root, inst, pos)) (icf_use_positions dfg root)
Proof
  simp[icf_alias_use_positions_def, SET_TO_LIST_SING]
QED

Theorem bp_get_read_location_mcopy_size[simp]:
  !bp id dst src sz outs.
    (bp_get_read_location bp
       <| inst_id := id; inst_opcode := MCOPY;
          inst_operands := [Var dst; Var src; Lit sz];
          inst_outputs := outs |>
       AddrSp_Memory).ml_size = SOME (w2n sz)
Proof
  rw[bp_get_read_location_def, is_raw_fmp_opcode_def, read_effects_def,
     mem_read_ops_def, bp_segment_from_ops_def] >>
  Cases_on `bp_ptr_from_op bp (Var src)` >> simp[] >>
  Cases_on `x` >> simp[]
QED

Theorem icf_has_src_clobber_adjacent[simp]:
  !aliases bp insts copy_idx invoke_idx src_loc.
    invoke_idx <= copy_idx + 1 ==>
    icf_has_src_clobber aliases bp insts copy_idx [invoke_idx] src_loc = F
Proof
  rw[icf_has_src_clobber_def] >>
  `invoke_idx - (copy_idx + 1) = 0` by decide_tac >>
  simp[rich_listTheory.COUNT_LIST_def]
QED

Theorem fn_dominates_entry_refl:
  !fn entry.
    fn_entry_label fn = SOME entry ==>
    fn_dominates fn entry entry
Proof
  rw[fn_dominates_def, fn_reachable_def, relationTheory.RTC_REFL] >>
  Cases_on `path` >> gvs[]
QED

Theorem single_block_wf_ssa:
  !fn bb.
    fn.fn_blocks = [bb] /\
    ssa_form fn /\
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions /\
    EVERY (\j.
      EVERY (\op.
        case op of
          Var v => EXISTS (\i. MEM v (EL i bb.bb_instructions).inst_outputs)
                          (COUNT_LIST j)
        | _ => T)
        (EL j bb.bb_instructions).inst_operands)
      (COUNT_LIST (LENGTH bb.bb_instructions)) ==>
    wf_ssa fn
Proof
  rpt gen_tac >> strip_tac >>
  simp[wf_ssa_def, def_dominates_uses_def] >>
  rpt strip_tac >> gvs[] >>
  `?j. j < LENGTH bb.bb_instructions /\ EL j bb.bb_instructions = inst` by
    metis_tac[MEM_EL] >>
  `inst.inst_opcode <> PHI` by (fs[EVERY_MEM] >> res_tac) >>
  simp[def_available_at_def] >> rpt strip_tac >>
  qpat_x_assum `EVERY (\j. _) _`
    (mp_tac o REWRITE_RULE [EVERY_MEM, rich_listTheory.MEM_COUNT_LIST]) >>
  disch_then (qspec_then `j` mp_tac) >> simp[EVERY_MEM] >>
  disch_then (qspec_then `Var v` mp_tac) >>
  simp[EXISTS_MEM, rich_listTheory.MEM_COUNT_LIST] >>
  strip_tac >>
  qexists_tac `EL i bb.bb_instructions` >>
  rpt conj_tac
  >- (irule EL_MEM >> decide_tac)
  >- simp[]
  >- (irule fn_dominates_entry_refl >>
      simp[fn_entry_label_def, entry_block_def])
  >- (qexistsl_tac [`i`, `j`] >> simp[])
QED

Theorem copy_phi_var_no_assign_phi:
  !origin fn x.
    EVERY (\i. i.inst_opcode <> ASSIGN /\ i.inst_opcode <> PHI) (fn_insts fn) ==>
    (copy_phi_var origin fn x <=>
     EXISTS (\inst. inst.inst_opcode = origin /\ MEM x inst.inst_outputs)
       (fn_insts fn))
Proof
  rpt gen_tac >> strip_tac >> eq_tac
  >- (`!origin g x.
         copy_phi_var origin g x ==>
         g = fn ==>
         EXISTS (\inst. inst.inst_opcode = origin /\ MEM x inst.inst_outputs)
           (fn_insts fn)` suffices_by metis_tac[] >>
      Induct_on `copy_phi_var` >> rw[EXISTS_MEM]
      >- metis_tac[]
      >- (fs[EVERY_MEM] >> res_tac)
      >- (fs[EVERY_MEM] >> res_tac))
  >- (rw[EXISTS_MEM] >> metis_tac[copy_phi_var_rules])
QED

Theorem single_block_o1_fn_shape:
  !ctx fn bb.
    fn.fn_blocks = [bb] /\
    wf_function fn /\
    fn_inst_wf fn /\
    ssa_form fn /\
    fn_entry_label fn = SOME fn.fn_name /\
    ~reserved_label bb.bb_label /\
    EVERY inst_shape_ok (fn_insts fn) /\
    first_block_no_preds fn /\
    first_block_no_phi fn /\
    EVERY (\i. i.inst_opcode <> ASSIGN /\ i.inst_opcode <> PHI /\
               i.inst_opcode <> DRET /\ i.inst_opcode <> DALLOCA)
      (fn_insts fn) /\
    EVERY (\inst.
      EVERY (\op.
        case op of
          Var x =>
            (if EXISTS (\ri. ri.inst_opcode = RETPC_PARAM /\
                             MEM x ri.inst_outputs) (fn_insts fn)
             then MEM inst.inst_opcode [RET; RETFMP; DRET] /\
                  inst.inst_operands <> [] /\
                  LAST inst.inst_operands = Var x /\
                  ~MEM (Var x) (FRONT inst.inst_operands)
             else T)
        | _ => T)
        inst.inst_operands)
      (fn_insts fn) /\
    EVERY (\inst.
      MEM inst.inst_opcode [RET; RETFMP; DRET] ==>
      inst.inst_operands <> [] /\
      case LAST inst.inst_operands of
        Var x => EXISTS (\ri. ri.inst_opcode = RETPC_PARAM /\
                              MEM x ri.inst_outputs) (fn_insts fn)
      | _ => F)
      (fn_insts fn) /\
    EVERY (\inst.
      EVERY (\x.
        EXISTS (\ri. ri.inst_opcode = RETPC_PARAM /\ MEM x ri.inst_outputs)
          (fn_insts fn) ==>
        inst.inst_opcode = RETPC_PARAM)
        inst.inst_outputs)
      (fn_insts fn) /\
    EVERY (\i.
      EVERY (\j.
        EVERY (\x. MEM x j.inst_outputs ==> i = j) i.inst_outputs)
        (fn_insts fn))
      (fn_insts fn) /\
    EVERY (\inst.
      inst.inst_opcode = INVOKE ==>
      case inst.inst_operands of
        Label lbl :: _ => MEM lbl (ctx_fn_names ctx)
      | _ => F)
      (fn_insts fn) /\
    EVERY (\inst.
      inst.inst_opcode <> INVOKE ==>
      EVERY (\op.
        case op of
          Label l => MEM l (fn_labels fn) \/ reserved_label l
        | _ => T)
        inst.inst_operands)
      (fn_insts fn) /\
    (ctx.ctx_entry = SOME fn.fn_name ==>
       entry_fn_no_return fn /\ entry_fn_no_params fn) /\
    (ctx.ctx_entry <> SOME fn.fn_name ==>
       EVERY (\inst. ~MEM inst.inst_opcode [STOP; RETURN]) (fn_insts fn)) ==>
    o1_fn_shape ctx fn
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> ASSIGN /\ i.inst_opcode <> PHI) (fn_insts fn)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions` by
    (fs[fn_insts_def, fn_insts_blocks_def, EVERY_MEM] >> metis_tac[]) >>
  `reachable_fn fn = fn` by metis_tac[reachable_fn_single_block] >>
  `!x. retpc_var fn x <=>
       EXISTS (\ri. ri.inst_opcode = RETPC_PARAM /\ MEM x ri.inst_outputs)
         (fn_insts fn)` by
    (gen_tac >> simp[retpc_var_def] >>
     irule copy_phi_var_no_assign_phi >> simp[]) >>
  simp[o1_fn_shape_def, fn_shape_ok_def] >>
  rpt conj_tac
  >- (rw[opaque_use_ok_def, retpc_use_ok_def] >>
      qpat_x_assum `EVERY (\inst. EVERY (\op. case op of _ => _) inst.inst_operands) _`
        (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
      disch_then drule >> simp[EVERY_MEM] >>
      disch_then (qspec_then `Var x` mp_tac) >> simp[] >>
      strip_tac >> disj2_tac >> disj2_tac >> simp[] >>
      qexists_tac `FRONT inst.inst_operands` >>
      simp[Once (GSYM SNOC_LAST_FRONT), SNOC_APPEND])
  >- (simp[retpc_shape_ok_def] >> rpt conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `EVERY (\inst. MEM inst.inst_opcode _ ==> _) _`
            (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
          disch_then drule >> simp[] >> strip_tac >>
          Cases_on `LAST inst.inst_operands` >> gvs[] >>
          qexistsl_tac [`FRONT inst.inst_operands`, `s`] >>
          simp[Once (GSYM SNOC_LAST_FRONT), SNOC_APPEND])
      >- (rpt strip_tac >> fs[EVERY_MEM] >> res_tac)
      >- (rpt strip_tac >>
          qpat_x_assum `EVERY (\inst. EVERY (\x. _ ==> inst.inst_opcode = RETPC_PARAM) _) _`
            (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
          disch_then drule >> simp[EVERY_MEM] >>
          disch_then drule >> simp[])
      >- (rpt strip_tac >>
          qpat_x_assum `EVERY (\i. EVERY (\j. EVERY (\x. MEM x j.inst_outputs ==> i = j) _) _) _`
            (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
          metis_tac[]))
  >- (rw[fn_invoke_ok_def] >>
      qpat_x_assum `EVERY (\inst. inst.inst_opcode = INVOKE ==> _) _`
        (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
      disch_then drule >> simp[] >>
      Cases_on `inst.inst_operands` >> simp[] >>
      Cases_on `h` >> simp[])
  >- (rw[fn_label_refs_ok_def] >>
      qpat_x_assum `EVERY (\inst. inst.inst_opcode <> INVOKE ==> _) _`
        (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
      disch_then drule >> simp[EVERY_MEM] >>
      disch_then (qspec_then `Label l` mp_tac) >> simp[])
  >- (rw[no_dret_def] >> fs[EVERY_MEM] >> res_tac)
  >- (rpt strip_tac >> fs[EVERY_MEM] >> res_tac)
QED

Theorem mk_nop_inst_opcode[simp]:
  !inst. (mk_nop_inst inst).inst_opcode = NOP
Proof
  simp[mk_nop_inst_def]
QED

Theorem mk_inst_acc[simp]:
  (mk_inst id op ops outs).inst_id = id /\
  (mk_inst id op ops outs).inst_opcode = op /\
  (mk_inst id op ops outs).inst_operands = ops /\
  (mk_inst id op ops outs).inst_outputs = outs /\
  ((mk_inst id op ops outs) with inst_operands := ops') = mk_inst id op ops' outs
Proof
  simp[mk_inst_def]
QED

Theorem mcopy_fields[simp]:
  (mcopy d sc sz s).vs_vars = s.vs_vars /\
  (mcopy d sc sz s).vs_call_ctx = s.vs_call_ctx /\
  (mcopy d sc sz s).vs_accounts = s.vs_accounts /\
  (mcopy d sc sz s).vs_halted = s.vs_halted /\
  (mcopy d sc sz s).vs_returndata = s.vs_returndata /\
  (mcopy d sc sz s).vs_logs = s.vs_logs /\
  (mcopy d sc sz s).vs_transient = s.vs_transient /\
  (mcopy d sc sz s).vs_outcomes = s.vs_outcomes /\
  (mcopy d sc sz s).vs_requests = s.vs_requests /\
  (mcopy d sc sz s).vs_pending_deletions = s.vs_pending_deletions /\
  (mcopy d sc sz s).vs_immutables = s.vs_immutables
Proof
  simp[mcopy_def, write_memory_with_expansion_def, LET_THM]
QED

Theorem mload_with_vars_idx[simp]:
  mload a (s with vs_inst_idx := i) = mload a s /\
  mload a (s with <| vs_vars := v; vs_inst_idx := i |>) = mload a s
Proof
  simp[mload_def]
QED

Theorem w2n_32w_bytes32[simp]:
  w2n (32w : bytes32) = 32
Proof
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def]
QED
