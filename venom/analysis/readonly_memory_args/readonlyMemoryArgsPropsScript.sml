(*
 * Readonly Memory Args Analysis — Properties and Copy-Forwarding Contract
 *
 * Canonical metadata/analysis builders (icf_fn_meta_of_fn, icf_fn_meta_of,
 * readonly_mem_analyze), memory agreement outside a forwarded destination
 * region (mem_agrees_except, copy_fwd_state_rel), structural compatibility
 * of copy-forwarded blocks and functions (icf_inst_compat, icf_inst_cfg_compat,
 * icf_block_compat, icf_fn_compat), and the interprocedural soundness
 * contract (rma_sound) lifting function-level copy forwarding to ctx_sim.
 *)

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
   2. Memory Agreement Outside Destination and Copy-Forwarding State Relation
   ========================================================================== *)

Definition mem_agrees_except_def:
  mem_agrees_except (dst_addr : num) (sz : num)
                    (s1 : venom_state) (s2 : venom_state) : bool <=>
    !a. (a < dst_addr \/ dst_addr + sz <= a) ==>
        mem_byte_at s1.vs_memory a = mem_byte_at s2.vs_memory a
End

Theorem mem_agrees_except_refl[simp]:
  !dst_addr sz s. mem_agrees_except dst_addr sz s s
Proof
  rw[mem_agrees_except_def]
QED

Theorem mem_agrees_except_sym:
  !dst_addr sz s1 s2.
    mem_agrees_except dst_addr sz s1 s2 ==>
    mem_agrees_except dst_addr sz s2 s1
Proof
  rw[mem_agrees_except_def] >> metis_tac[]
QED

Theorem mcopy_establishes_mem_agrees_except:
  !s dst_addr src_addr sz.
    mem_agrees_except dst_addr sz (mcopy dst_addr src_addr sz s) s
Proof
  rw[mem_agrees_except_def, mcopy_def, LET_THM] >>
  irule wmwe_byte_at_outside >> simp[mcopy_data_length]
QED

Definition copy_fwd_state_rel_def:
  copy_fwd_state_rel (dst_addr : num) (src_addr : num) (sz : num)
                     (s1 : venom_state) (s2 : venom_state) : bool <=>
    icf_equiv s1 s2 /\
    cross_mem_region_equiv s1.vs_memory dst_addr s2.vs_memory src_addr sz /\
    mem_agrees_except dst_addr sz s1 s2
End

Theorem mcopy_establishes_copy_fwd_state_rel:
  !s dst_addr src_addr sz.
    copy_fwd_state_rel dst_addr src_addr sz (mcopy dst_addr src_addr sz s) s
Proof
  ntac 4 gen_tac >>
  simp[copy_fwd_state_rel_def, mcopy_establishes_mem_agrees_except] >>
  conj_tac
  >- simp[icf_equiv_def, lookup_var_def, mcopy_def,
          write_memory_with_expansion_def, LET_THM]
  >- (rw[cross_mem_region_equiv_def] >>
      mp_tac (Q.SPECL [`s`, `dst_addr`, `src_addr`, `sz`]
              mcopy_establishes_equiv) >>
      simp[LET_THM])
QED

Theorem copy_fwd_state_rel_observable_equiv:
  !dst src sz s1 s2.
    copy_fwd_state_rel dst src sz s1 s2 ==>
    observable_equiv s1 s2
Proof
  rw[copy_fwd_state_rel_def] >> metis_tac[icf_equiv_observable_equiv]
QED

Theorem copy_fwd_state_rel_icf_equiv:
  !dst src sz s1 s2.
    copy_fwd_state_rel dst src sz s1 s2 ==>
    icf_equiv s1 s2
Proof
  rw[copy_fwd_state_rel_def]
QED

Theorem copy_fwd_state_rel_with_inst_idx:
  !dst src sz s1 s2 idx.
    copy_fwd_state_rel dst src sz s1 s2 ==>
    copy_fwd_state_rel dst src sz
      (s1 with vs_inst_idx := idx)
      (s2 with vs_inst_idx := idx)
Proof
  rw[copy_fwd_state_rel_def, icf_equiv_def, lookup_var_def,
     mem_agrees_except_def, cross_mem_region_equiv_def]
QED

Theorem adopt_return_fmp_preserves_copy_fwd_state_rel:
  !dst_addr src_addr sz ret s1 s2.
    copy_fwd_state_rel dst_addr src_addr sz s1 s2 ==>
    copy_fwd_state_rel dst_addr src_addr sz
      (adopt_return_fmp ret s1) (adopt_return_fmp ret s2)
Proof
  rw[adopt_return_fmp_def] >> Cases_on `ret.iret_adopt_fmp` >>
  rw[copy_fwd_state_rel_def, icf_equiv_def, lookup_var_def,
     mem_agrees_except_def, Excl "pass_residual_mask_equality"] >>
  fs[copy_fwd_state_rel_def, icf_equiv_def, lookup_var_def,
     mem_agrees_except_def]
QED

Theorem update_var_preserves_copy_fwd_state_rel:
  !dst_addr src_addr sz v val s1 s2.
    copy_fwd_state_rel dst_addr src_addr sz s1 s2 ==>
    copy_fwd_state_rel dst_addr src_addr sz
      (update_var v val s1) (update_var v val s2)
Proof
  rw[copy_fwd_state_rel_def, icf_equiv_def, update_var_def,
     lookup_var_def, FLOOKUP_UPDATE, mem_agrees_except_def,
     Excl "pass_residual_mask_equality"]
QED

Theorem foldl_update_var_preserves_copy_fwd_state_rel[local]:
  !pairs dst_addr src_addr sz s1 s2.
    copy_fwd_state_rel dst_addr src_addr sz s1 s2 ==>
    copy_fwd_state_rel dst_addr src_addr sz
      (FOLDL (\s' (out,val). update_var out val s') s1 pairs)
      (FOLDL (\s' (out,val). update_var out val s') s2 pairs)
Proof
  Induct_on `pairs` >> simp[] >>
  Cases >> simp[] >> rpt strip_tac >>
  first_x_assum irule >>
  irule update_var_preserves_copy_fwd_state_rel >> simp[]
QED

Theorem bind_outputs_preserves_copy_fwd_state_rel:
  !outs vals dst_addr src_addr sz s1 s2.
    copy_fwd_state_rel dst_addr src_addr sz s1 s2 ==>
    case (bind_outputs outs vals s1, bind_outputs outs vals s2) of
      (SOME s1', SOME s2') => copy_fwd_state_rel dst_addr src_addr sz s1' s2'
    | (NONE, NONE) => T
    | _ => F
Proof
  rw[bind_outputs_def] >>
  irule foldl_update_var_preserves_copy_fwd_state_rel >> simp[]
QED

Definition region_disjoint_def:
  region_disjoint (a1 : num) (sz1 : num) (a2 : num) (sz2 : num) : bool <=>
    a1 + sz1 <= a2 \/ a2 + sz2 <= a1
End

Theorem mload_copy_fwd_state_rel_cross:
  !dst_addr src_addr sz s1 s2.
    32 <= sz /\
    copy_fwd_state_rel dst_addr src_addr sz s1 s2 ==>
    mload dst_addr s1 = mload src_addr s2
Proof
  rw[copy_fwd_state_rel_def] >>
  irule mload_cross_equiv >>
  irule cross_mem_region_equiv_sub >>
  qexists_tac `sz` >> simp[]
QED

Theorem mload_copy_fwd_state_rel_disjoint:
  !dst_addr src_addr sz addr s1 s2.
    32 <= sz /\
    region_disjoint addr sz dst_addr sz /\
    copy_fwd_state_rel dst_addr src_addr sz s1 s2 ==>
    mload addr s1 = mload addr s2
Proof
  rw[copy_fwd_state_rel_def, mem_agrees_except_def, region_disjoint_def] >>
  irule mload_cross_equiv >>
  rw[cross_mem_region_equiv_def] >>
  first_x_assum irule >> decide_tac
QED

Theorem mload_mcopy_same:
  !s dst_addr src_addr sz.
    32 <= sz ==>
    mload dst_addr (mcopy dst_addr src_addr sz s) = mload src_addr s
Proof
  rpt strip_tac >>
  irule mload_cross_equiv >>
  rw[cross_mem_region_equiv_def] >>
  mp_tac (Q.SPECL [`s`, `dst_addr`, `src_addr`, `sz`] mcopy_establishes_equiv) >>
  simp[LET_THM]
QED

Theorem step_inst_alloca_ok:
  !fuel ctx id sz out s s'.
    step_inst fuel ctx (mk_inst id ALLOCA [Lit sz] [out]) s = OK s' ==>
    (?v. lookup_var out s' = SOME v) /\
    (!u. u <> out ==> lookup_var u s' = lookup_var u s)
Proof
  rw[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def,
     eval_operands_def, eval_operand_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >>
  TRY (PairCases_on `x`) >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem step_inst_preserves_eval_operand:
  !fuel ctx inst op s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    (!v. op = Var v ==> ~MEM v inst.inst_outputs) ==>
    eval_operand op s' = eval_operand op s
Proof
  ntac 3 gen_tac >> Cases >> rw[eval_operand_def]
  >- metis_tac[venomInstPropsTheory.step_preserves_non_output_vars]
  >- (drule venomExecPropsTheory.step_inst_preserves_labels_always >> simp[])
QED

Theorem wmwe_preserves_copy_fwd_state_rel_disjoint:
  !dst_addr src_addr sz addr bytes s1 s2.
    region_disjoint addr (LENGTH bytes) dst_addr sz /\
    region_disjoint addr (LENGTH bytes) src_addr sz /\
    copy_fwd_state_rel dst_addr src_addr sz s1 s2 ==>
    copy_fwd_state_rel dst_addr src_addr sz
      (write_memory_with_expansion addr bytes s1)
      (write_memory_with_expansion addr bytes s2)
Proof
  rpt gen_tac >>
  simp[copy_fwd_state_rel_def, mem_agrees_except_def,
       cross_mem_region_equiv_def] >>
  strip_tac >>
  conj_tac
  >- fs[icf_equiv_def, lookup_var_def, write_memory_with_expansion_def,
        Excl "pass_residual_mask_equality"] >>
  conj_tac
  >- (rpt strip_tac >>
      `mem_byte_at (write_memory_with_expansion addr bytes s1).vs_memory
         (dst_addr + i) =
       mem_byte_at s1.vs_memory (dst_addr + i)` by
        (irule wmwe_byte_at_outside >> fs[region_disjoint_def]) >>
      `mem_byte_at (write_memory_with_expansion addr bytes s2).vs_memory
         (i + src_addr) =
       mem_byte_at s2.vs_memory (i + src_addr)` by
        (irule wmwe_byte_at_outside >> fs[region_disjoint_def]) >>
      simp[]) >>
  gen_tac >> disch_tac >>
  Cases_on `addr <= a /\ a < addr + LENGTH bytes`
  >- (`a = addr + (a - addr) /\ a - addr < LENGTH bytes` by decide_tac >>
      qpat_x_assum `a = _` SUBST1_TAC >>
      simp[wmwe_byte_at_written])
  >- (`mem_byte_at (write_memory_with_expansion addr bytes s1).vs_memory a =
       mem_byte_at s1.vs_memory a` by
        (irule wmwe_byte_at_outside >> decide_tac) >>
      `mem_byte_at (write_memory_with_expansion addr bytes s2).vs_memory a =
       mem_byte_at s2.vs_memory a` by
        (irule wmwe_byte_at_outside >> decide_tac) >>
      simp[] >> first_x_assum irule >> simp[])
QED

Theorem mstore_preserves_copy_fwd_state_rel_disjoint:
  !dst_addr src_addr sz addr (val : bytes32) s1 s2.
    32 <= sz /\
    region_disjoint addr sz dst_addr sz /\
    region_disjoint addr sz src_addr sz /\
    copy_fwd_state_rel dst_addr src_addr sz s1 s2 ==>
    copy_fwd_state_rel dst_addr src_addr sz
      (mstore addr val s1) (mstore addr val s2)
Proof
  rpt strip_tac >>
  `mstore addr val s1 =
   write_memory_with_expansion addr (word_to_bytes val T) s1 /\
   mstore addr val s2 =
   write_memory_with_expansion addr (word_to_bytes val T) s2` by
    simp[mstore_def, write_memory_with_expansion_def] >>
  `LENGTH (word_to_bytes val T) <= 32` by
    (simp[byteTheory.LENGTH_word_to_bytes] >>
     CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]) >>
  simp[] >>
  irule wmwe_preserves_copy_fwd_state_rel_disjoint >>
  gvs[region_disjoint_def]
QED

(* ==========================================================================
   3. Structural Compatibility for Copy Forwarding
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

Definition icf_mcopy_noped_def:
  icf_mcopy_noped (bb0 : basic_block) (bb : basic_block) : bool <=>
    bb.bb_label = bb0.bb_label /\
    LIST_REL icf_inst_compat bb0.bb_instructions bb.bb_instructions /\
    (bb = bb0 \/
     ?i. i < LENGTH bb0.bb_instructions /\
         (EL i bb0.bb_instructions).inst_opcode = MCOPY /\
         (EL i bb.bb_instructions).inst_opcode = NOP)
End

Theorem icf_mcopy_noped_refl[simp]:
  !bb. icf_mcopy_noped bb bb
Proof
  simp[icf_mcopy_noped_def]
QED

Theorem LIST_REL_icf_mcopy_noped_refl[simp]:
  !bbs. LIST_REL icf_mcopy_noped bbs bbs
Proof
  Induct >> simp[]
QED

Theorem LIST_REL_icf_inst_compat_EL[local]:
  !l1 l2 i.
    LIST_REL icf_inst_compat l1 l2 /\ i < LENGTH l1 ==>
    LENGTH l2 = LENGTH l1 /\ icf_inst_compat (EL i l1) (EL i l2)
Proof
  rw[LIST_REL_EL_EQN]
QED

Theorem icf_mcopy_noped_trans:
  !bb0 bb1 bb2.
    icf_mcopy_noped bb0 bb1 /\ icf_mcopy_noped bb1 bb2 ==>
    icf_mcopy_noped bb0 bb2
Proof
  rw[icf_mcopy_noped_def] >> gvs[]
  >- metis_tac[LIST_REL_icf_inst_compat_trans]
  >- (disj2_tac >> qexists_tac `i` >> simp[])
  >- metis_tac[LIST_REL_icf_inst_compat_trans]
  >- (disj2_tac >> qexists_tac `i` >>
      `LENGTH bb1.bb_instructions = LENGTH bb0.bb_instructions /\
       icf_inst_compat (EL i bb0.bb_instructions) (EL i bb1.bb_instructions)` by
        metis_tac[LIST_REL_icf_inst_compat_EL] >>
      `icf_inst_compat (EL i bb1.bb_instructions) (EL i bb2.bb_instructions)` by
        metis_tac[LIST_REL_icf_inst_compat_EL] >>
      gvs[icf_inst_compat_def, mk_nop_inst_def])
QED

Theorem icf_mcopy_noped_step:
  !bb0 bb1 bb2 i.
    icf_mcopy_noped bb0 bb1 /\
    bb2.bb_label = bb1.bb_label /\
    LIST_REL icf_inst_compat bb1.bb_instructions bb2.bb_instructions /\
    i < LENGTH bb1.bb_instructions /\
    (EL i bb1.bb_instructions).inst_opcode = MCOPY /\
    (EL i bb2.bb_instructions).inst_opcode = NOP ==>
    icf_mcopy_noped bb0 bb2
Proof
  rpt strip_tac >>
  irule icf_mcopy_noped_trans >>
  qexists_tac `bb1` >> simp[] >>
  simp[icf_mcopy_noped_def] >> disj2_tac >>
  qexists_tac `i` >> simp[]
QED

Theorem icf_mcopy_noped_no_mcopy:
  !bb0 bb1.
    EVERY (\inst. inst.inst_opcode <> MCOPY) bb0.bb_instructions /\
    icf_mcopy_noped bb0 bb1 ==>
    bb1 = bb0
Proof
  rw[icf_mcopy_noped_def] >>
  fs[EVERY_MEM] >>
  `MEM (EL i bb0.bb_instructions) bb0.bb_instructions` by
    (irule EL_MEM >> simp[]) >>
  res_tac >> gvs[]
QED

Theorem icf_mcopy_noped_unique_mcopy:
  !bb0 bb1 k m.
    k < LENGTH bb0.bb_instructions /\
    (!j. j < LENGTH bb0.bb_instructions /\ j <> k ==>
         (EL j bb0.bb_instructions).inst_opcode <> MCOPY) /\
    icf_mcopy_noped bb0 bb1 /\
    m < LENGTH bb1.bb_instructions /\
    (EL m bb1.bb_instructions).inst_opcode = MCOPY ==>
    bb1 = bb0 /\ m = k
Proof
  rw[icf_mcopy_noped_def]
  >- (spose_not_then assume_tac >> res_tac)
  >> (`LENGTH bb1.bb_instructions = LENGTH bb0.bb_instructions` by
        metis_tac[LIST_REL_LENGTH] >>
      `i = k` by (spose_not_then assume_tac >> res_tac) >>
      `m < LENGTH bb0.bb_instructions` by decide_tac >>
      `icf_inst_compat (EL m bb0.bb_instructions) (EL m bb1.bb_instructions)` by
        metis_tac[LIST_REL_icf_inst_compat_EL] >>
      `(EL m bb0.bb_instructions).inst_opcode = MCOPY` by
        gvs[icf_inst_compat_def, mk_nop_inst_def] >>
      `m = k` by (spose_not_then assume_tac >> res_tac) >>
      gvs[])
QED

Theorem LIST_REL_icf_inst_compat_preserves_bb_wf:
  !bb1 bb2.
    bb2.bb_label = bb1.bb_label /\
    LIST_REL icf_inst_compat bb1.bb_instructions bb2.bb_instructions /\
    bb_well_formed bb1 ==>
    bb_well_formed bb2
Proof
  rpt strip_tac >>
  `bb2 = (bb1 with bb_instructions := bb2.bb_instructions)` by
    simp[venomInstTheory.basic_block_component_equality] >>
  `bb1 = (bb1 with bb_instructions := bb1.bb_instructions)` by
    simp[venomInstTheory.basic_block_component_equality] >>
  qpat_x_assum `bb2 = _` SUBST1_TAC >>
  qpat_x_assum `bb1 = _` SUBST1_TAC >>
  irule (GEN_ALL bb_well_formed_transfer) >>
  qexists_tac `bb1.bb_instructions` >> simp[] >>
  `LENGTH bb2.bb_instructions = LENGTH bb1.bb_instructions` by
    metis_tac[LIST_REL_LENGTH] >>
  simp[] >> rpt strip_tac >>
  `icf_inst_compat (EL i bb1.bb_instructions) (EL i bb2.bb_instructions)` by
    metis_tac[LIST_REL_icf_inst_compat_EL] >>
  fs[icf_inst_compat_def]
QED

Theorem icf_mcopy_noped_preserves_bb_wf:
  !bb1 bb2.
    icf_mcopy_noped bb1 bb2 /\ bb_well_formed bb1 ==>
    bb_well_formed bb2
Proof
  metis_tac[icf_mcopy_noped_def, LIST_REL_icf_inst_compat_preserves_bb_wf]
QED


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

Definition icf_fwd_step_def:
  icf_fwd_step (fn_meta : (string, invoke_fn_meta) fmap)
               (ctx_fns : ir_function list)
               (rma : (string, bool list) fmap)
               (fn : ir_function)
               (bb1 : basic_block) (copy_idx : num) (bb2 : basic_block) : bool <=>
    wf_ssa fn /\
    ((ircf_no_dst_write_alias fn /\
      ?new_insts.
        ircf_try_forward
          (icf_build_ctx fn_meta ctx_fns rma fn)
          bb1 copy_idx = SOME new_insts /\
        bb2 = (bb1 with bb_instructions := new_insts)) \/
     (ricf_full_alloca_copies fn /\
      ricf_no_derived_mutable_sibling fn /\
      ?cur_bbs b src_var_opt rewrite_sites.
        LIST_REL icf_mcopy_noped fn.fn_blocks cur_bbs /\
        MEM b cur_bbs /\
        icf_mcopy_noped b bb1 /\
        ricf_try_forward
          ((icf_build_ctx fn_meta ctx_fns rma fn) with
             icf_dfg := dfg_build_function (fn with fn_blocks := cur_bbs))
          bb1 copy_idx = SOME (src_var_opt, rewrite_sites) /\
        let src_op =
          case src_var_opt of
            SOME sv => Var sv
          | NONE => EL 1 (EL copy_idx bb1.bb_instructions).inst_operands in
        bb2 = (bb1 with bb_instructions :=
                 ricf_apply_forward bb1.bb_instructions copy_idx
                   src_op rewrite_sites)))
End

Theorem icf_fwd_step_structural:
  !fn_meta ctx_fns rma fn bb1 copy_idx bb2.
    icf_fwd_step fn_meta ctx_fns rma fn bb1 copy_idx bb2 ==>
    copy_idx < LENGTH bb1.bb_instructions /\
    LENGTH bb2.bb_instructions = LENGTH bb1.bb_instructions /\
    bb2.bb_label = bb1.bb_label /\
    (EL copy_idx bb1.bb_instructions).inst_opcode = MCOPY /\
    EL copy_idx bb2.bb_instructions =
      mk_nop_inst (EL copy_idx bb1.bb_instructions) /\
    (!i. i < copy_idx ==>
         EL i bb2.bb_instructions = EL i bb1.bb_instructions) /\
    LIST_REL icf_inst_compat bb1.bb_instructions bb2.bb_instructions
Proof
  simp[icf_fwd_step_def, LET_THM] >> rpt gen_tac >> strip_tac
  >- (drule ircf_try_forward_prefix_and_copy >> strip_tac >> simp[] >>
      gvs[ircf_try_forward_def, AllCaseEqs()] >>
      rw[LIST_REL_EL_EQN, indexedListsTheory.EL_MAPi] >>
      rw[icf_inst_compat_def, mk_nop_inst_def, is_terminator_def])
  >- (drule ricf_try_forward_prefix_and_copy >> strip_tac >> simp[] >>
      rw[ricf_apply_forward_def, LIST_REL_EL_EQN,
         indexedListsTheory.EL_MAPi] >>
      rw[icf_inst_compat_def, mk_nop_inst_def, is_terminator_def])
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

Theorem icf_fwd_step_phis:
  !fn_meta ctx_fns rma fn bb1 copy_idx bb2 s.
    icf_fwd_step fn_meta ctx_fns rma fn bb1 copy_idx bb2 ==>
    phi_prefix_length bb2.bb_instructions =
      phi_prefix_length bb1.bb_instructions /\
    phi_prefix_length bb1.bb_instructions <= copy_idx /\
    eval_phis s bb2.bb_instructions = eval_phis s bb1.bb_instructions
Proof
  rpt strip_tac >>
  drule icf_fwd_step_structural >> strip_tac >>
  mp_tac (Q.SPECL [`bb1.bb_instructions`, `bb2.bb_instructions`,
                   `copy_idx`, `s`] phi_prefix_eval_phis_agree_before) >>
  simp[mk_nop_inst_def]
QED

Definition icf_bounded_fwd_step_def:
  icf_bounded_fwd_step (fn_meta : (string, invoke_fn_meta) fmap)
                       (ctx_fns : ir_function list)
                       (rma : (string, bool list) fmap)
                       (fn : ir_function) (bb0 : basic_block)
                       (bb1 : basic_block) (bb2 : basic_block) : bool <=>
    icf_mcopy_noped bb0 bb1 /\
    ?copy_idx. icf_fwd_step fn_meta ctx_fns rma fn bb1 copy_idx bb2
End

Definition icf_block_compat_def:
  icf_block_compat (fn_meta : (string, invoke_fn_meta) fmap)
                   (ctx_fns : ir_function list)
                   (rma : (string, bool list) fmap)
                   (fn : ir_function)
                   (bb1 : basic_block) (bb2 : basic_block) : bool <=>
    icf_mcopy_noped bb1 bb2 /\
    (bb2 = bb1 \/
     (icf_auth_ok fn_meta ctx_fns rma /\
      RTC (icf_bounded_fwd_step fn_meta ctx_fns rma fn bb1) bb1 bb2))
End

Theorem icf_block_compat_refl[simp]:
  !fn_meta ctx_fns rma fn bb. icf_block_compat fn_meta ctx_fns rma fn bb bb
Proof
  simp[icf_block_compat_def]
QED

Theorem icf_block_compat_label:
  !fn_meta ctx_fns rma fn bb1 bb2.
    icf_block_compat fn_meta ctx_fns rma fn bb1 bb2 ==>
    bb2.bb_label = bb1.bb_label
Proof
  rw[icf_block_compat_def, icf_mcopy_noped_def]
QED

Theorem icf_block_compat_step:
  !fn_meta ctx_fns rma fn bb0 bb1 copy_idx bb2.
    icf_block_compat fn_meta ctx_fns rma fn bb0 bb1 /\
    icf_auth_ok fn_meta ctx_fns rma /\
    icf_mcopy_noped bb1 bb2 /\
    icf_fwd_step fn_meta ctx_fns rma fn bb1 copy_idx bb2 ==>
    icf_block_compat fn_meta ctx_fns rma fn bb0 bb2
Proof
  rw[icf_block_compat_def] >> gvs[]
  >- (disj2_tac >> irule relationTheory.RTC_SINGLE >>
      simp[icf_bounded_fwd_step_def] >> metis_tac[])
  >- metis_tac[icf_mcopy_noped_trans]
  >- (disj2_tac >>
      `icf_bounded_fwd_step fn_meta ctx_fns rma fn bb0 bb1 bb2` by
        (simp[icf_bounded_fwd_step_def] >> metis_tac[]) >>
      metis_tac[relationTheory.RTC_RULES_RIGHT1])
QED

Definition icf_fn_compat_def:
  icf_fn_compat (fn_meta : (string, invoke_fn_meta) fmap)
                (ctx_fns : ir_function list)
                (rma : (string, bool list) fmap)
                (fn1 : ir_function) (fn2 : ir_function) : bool <=>
    fn2 = fn1 \/
    (?bbs.
       LIST_REL (icf_block_compat fn_meta ctx_fns rma fn1) fn1.fn_blocks bbs /\
       (fn2 = (fn1 with fn_blocks := bbs) \/
        fn2 = clear_nops_function (fn1 with fn_blocks := bbs)))
End

Theorem icf_fn_compat_refl[simp]:
  !fn_meta ctx_fns rma fn. icf_fn_compat fn_meta ctx_fns rma fn fn
Proof
  simp[icf_fn_compat_def]
QED

Theorem icf_fn_compat_fn_name:
  !fn_meta ctx_fns rma fn1 fn2.
    icf_fn_compat fn_meta ctx_fns rma fn1 fn2 ==>
    fn2.fn_name = fn1.fn_name
Proof
  rw[icf_fn_compat_def, clear_nops_function_def] >> gvs[]
QED

Theorem LIST_REL_same_label_entry_label[local]:
  !R fn1 fn2.
    LIST_REL R fn1.fn_blocks fn2.fn_blocks /\
    (!b1 b2. R b1 b2 ==> b2.bb_label = b1.bb_label) ==>
    fn_entry_label fn2 = fn_entry_label fn1
Proof
  rpt strip_tac >>
  simp[fn_entry_label_def, entry_block_def] >>
  Cases_on `fn1.fn_blocks` >> Cases_on `fn2.fn_blocks` >> gvs[] >>
  res_tac >> simp[]
QED

Theorem clear_nops_function_entry_label[local,simp]:
  !fn. fn_entry_label (clear_nops_function fn) = fn_entry_label fn
Proof
  gen_tac >> simp[fn_entry_label_def, entry_block_def, clear_nops_function_def] >>
  Cases_on `fn.fn_blocks` >> simp[clear_nops_block_def]
QED

Theorem icf_fn_compat_entry_label:
  !fn_meta ctx_fns rma fn1 fn2.
    icf_fn_compat fn_meta ctx_fns rma fn1 fn2 ==>
    fn_entry_label fn2 = fn_entry_label fn1
Proof
  rw[icf_fn_compat_def] >> simp[] >>
  irule LIST_REL_same_label_entry_label >>
  qexists_tac `icf_block_compat fn_meta ctx_fns rma fn1` >>
  simp[] >> metis_tac[icf_block_compat_label]
QED

Definition icf_exec_result_rel_def:
  icf_exec_result_rel (OK s1) (OK s2) = (s2 = s1) /\
  icf_exec_result_rel (IntRet ret1 s1) (IntRet ret2 s2) =
    (ret2 = ret1 /\ execution_frame s2 = execution_frame s1) /\
  icf_exec_result_rel (Halt s1) (Halt s2) = observable_equiv s1 s2 /\
  icf_exec_result_rel (Abort a1 s1) (Abort a2 s2) =
    (a2 = a1 /\ revert_equiv s1 s2) /\
  icf_exec_result_rel (Error e1) (Error e2) = T /\
  icf_exec_result_rel _ _ = F
End

Theorem revert_equiv_refl[local,simp]:
  !s. revert_equiv s s
Proof
  simp[revert_equiv_def]
QED

Theorem icf_exec_result_rel_refl[simp]:
  !r. icf_exec_result_rel r r
Proof
  Cases >> simp[icf_exec_result_rel_def, stateEquivPropsTheory.observable_equiv_refl]
QED

Theorem icf_exec_result_rel_trans:
  !r1 r2 r3.
    icf_exec_result_rel r1 r2 /\ icf_exec_result_rel r2 r3 ==>
    icf_exec_result_rel r1 r3
Proof
  Cases >> Cases >> Cases >>
  rw[icf_exec_result_rel_def, observable_equiv_def, revert_equiv_def]
QED

Theorem result_equiv_empty_icf_exec_result_rel:
  !r1 r2.
    result_equiv {} r1 r2 ==>
    icf_exec_result_rel r1 r2
Proof
  Cases >> Cases >>
  rw[result_equiv_def, icf_exec_result_rel_def, execution_equiv_def,
     observable_equiv_def, revert_equiv_def] >>
  metis_tac[stateEquivPropsTheory.state_equiv_empty_eq]
QED

Theorem exec_block_same_inst:
  !fuel ctx bb1 bb2 s.
    get_instruction bb2 s.vs_inst_idx = get_instruction bb1 s.vs_inst_idx /\
    (!inst s'.
       get_instruction bb1 s.vs_inst_idx = SOME inst /\
       ~is_terminator inst.inst_opcode /\
       step_inst fuel ctx inst s = OK s' ==>
       icf_exec_result_rel
         (exec_block fuel ctx bb1 (s' with vs_inst_idx := SUC s.vs_inst_idx))
         (exec_block fuel ctx bb2 (s' with vs_inst_idx := SUC s.vs_inst_idx))) ==>
    icf_exec_result_rel (exec_block fuel ctx bb1 s) (exec_block fuel ctx bb2 s)
Proof
  rpt strip_tac >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[] >>
  Cases_on `get_instruction bb1 s.vs_inst_idx` >> simp[] >>
  Cases_on `step_inst fuel ctx x s` >> simp[] >>
  Cases_on `is_terminator x.inst_opcode` >> simp[]
QED

Inductive prefix_steps:
[~refl:]
  (!fuel ctx bb copy_idx s.
     s.vs_inst_idx = copy_idx ==>
     prefix_steps fuel ctx bb copy_idx s s)
[~step:]
  (!fuel ctx bb copy_idx s inst s' s_end.
     s.vs_inst_idx < copy_idx /\
     get_instruction bb s.vs_inst_idx = SOME inst /\
     ~is_terminator inst.inst_opcode /\
     step_inst fuel ctx inst s = OK s' /\
     prefix_steps fuel ctx bb copy_idx
       (s' with vs_inst_idx := SUC s.vs_inst_idx) s_end ==>
     prefix_steps fuel ctx bb copy_idx s s_end)
End

Theorem prefix_steps_end_idx:
  !fuel ctx bb copy_idx s s_end.
    prefix_steps fuel ctx bb copy_idx s s_end ==>
    s_end.vs_inst_idx = copy_idx
Proof
  Induct_on `prefix_steps` >> rw[]
QED

Theorem prefix_steps_inv_at[local]:
  !fuel ctx bb copy_idx s s_end.
    prefix_steps fuel ctx bb copy_idx s s_end ==>
    s.vs_inst_idx = copy_idx ==>
    s_end = s
Proof
  Induct_on `prefix_steps` >> rw[]
QED

Theorem prefix_steps_inv_lt[local]:
  !fuel ctx bb copy_idx s s_end.
    prefix_steps fuel ctx bb copy_idx s s_end ==>
    s.vs_inst_idx < copy_idx ==>
    ?inst s'.
      get_instruction bb s.vs_inst_idx = SOME inst /\
      ~is_terminator inst.inst_opcode /\
      step_inst fuel ctx inst s = OK s' /\
      prefix_steps fuel ctx bb copy_idx
        (s' with vs_inst_idx := SUC s.vs_inst_idx) s_end
Proof
  Induct_on `prefix_steps` >> rw[] >> metis_tac[]
QED

Theorem prefix_steps_3_from_0:
  !fuel ctx bb s0 s_end i0 i1 i2.
    s0.vs_inst_idx = 0 /\
    get_instruction bb 0 = SOME i0 /\
    get_instruction bb 1 = SOME i1 /\
    get_instruction bb 2 = SOME i2 /\
    prefix_steps fuel ctx bb 3 s0 s_end ==>
    ?s1 s2 s3.
      step_inst fuel ctx i0 s0 = OK s1 /\
      step_inst fuel ctx i1 (s1 with vs_inst_idx := 1) = OK s2 /\
      step_inst fuel ctx i2 (s2 with vs_inst_idx := 2) = OK s3 /\
      s_end = (s3 with vs_inst_idx := 3)
Proof
  rpt strip_tac >>
  drule prefix_steps_inv_lt >> simp[] >> strip_tac >> gvs[] >>
  drule prefix_steps_inv_lt >> simp[] >> strip_tac >> gvs[] >>
  drule prefix_steps_inv_lt >> simp[] >> strip_tac >> gvs[] >>
  drule prefix_steps_inv_at >> simp[]
QED

Theorem exec_block_prefix_to_copy_measure[local]:
  !m fuel ctx bb1 bb2 copy_idx s.
    m = copy_idx - s.vs_inst_idx /\
    s.vs_inst_idx <= copy_idx /\
    copy_idx <= LENGTH bb1.bb_instructions /\
    copy_idx <= LENGTH bb2.bb_instructions /\
    (!i. i < copy_idx ==>
         EL i bb2.bb_instructions = EL i bb1.bb_instructions) /\
    (!s_copy.
       prefix_steps fuel ctx bb1 copy_idx s s_copy ==>
       icf_exec_result_rel
         (exec_block fuel ctx bb1 s_copy)
         (exec_block fuel ctx bb2 s_copy)) ==>
    icf_exec_result_rel (exec_block fuel ctx bb1 s) (exec_block fuel ctx bb2 s)
Proof
  completeInduct_on `m` >> rpt gen_tac >> strip_tac >>
  Cases_on `s.vs_inst_idx = copy_idx`
  >- (first_x_assum irule >> irule prefix_steps_refl >> simp[]) >>
  `s.vs_inst_idx < copy_idx` by decide_tac >>
  `get_instruction bb2 s.vs_inst_idx = get_instruction bb1 s.vs_inst_idx` by
    (simp[get_instruction_def] >> first_assum irule >> decide_tac) >>
  irule exec_block_same_inst >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!m'. m' < m ==> _`
    (qspec_then `copy_idx - SUC s.vs_inst_idx` mp_tac) >>
  impl_tac >- decide_tac >>
  disch_then (qspecl_then [`fuel`, `ctx`, `bb1`, `bb2`, `copy_idx`,
                           `s' with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[] >> impl_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      irule prefix_steps_step >> simp[] >>
      qexistsl_tac [`inst`, `s'`] >> simp[]) >>
  simp[]
QED

Theorem exec_block_prefix_to_copy:
  !fuel ctx bb1 bb2 copy_idx s.
    s.vs_inst_idx <= copy_idx /\
    copy_idx <= LENGTH bb1.bb_instructions /\
    copy_idx <= LENGTH bb2.bb_instructions /\
    (!i. i < copy_idx ==>
         EL i bb2.bb_instructions = EL i bb1.bb_instructions) /\
    (!s_copy.
       prefix_steps fuel ctx bb1 copy_idx s s_copy ==>
       icf_exec_result_rel
         (exec_block fuel ctx bb1 s_copy)
         (exec_block fuel ctx bb2 s_copy)) ==>
    icf_exec_result_rel (exec_block fuel ctx bb1 s) (exec_block fuel ctx bb2 s)
Proof
  metis_tac[exec_block_prefix_to_copy_measure]
QED

Definition rma_arg_pair_ok_def:
  rma_arg_pair_ok (rma : (string, bool list) fmap) (fn_name : string)
                  (dst_addr : num) (src_addr : num) (sz : num)
                  (k : num) (v1 : bytes32) (v2 : bytes32) : bool <=>
    if rma_is_readonly rma fn_name k then
      (v2 = v1 /\ region_disjoint (w2n v1) sz dst_addr sz) \/
      (w2n v1 = dst_addr /\ w2n v2 = src_addr)
    else
      v2 = v1 /\
      region_disjoint (w2n v1) sz dst_addr sz /\
      region_disjoint (w2n v1) sz src_addr sz
End

Definition rma_args_ok_def:
  rma_args_ok (rma : (string, bool list) fmap) (fn_name : string)
              (dst_addr : num) (src_addr : num) (sz : num)
              (args1 : bytes32 list) (args2 : bytes32 list) : bool <=>
    LENGTH args2 = LENGTH args1 /\
    (!k. k < LENGTH args1 ==>
         rma_arg_pair_ok rma fn_name dst_addr src_addr sz
           k (EL k args1) (EL k args2))
End

Definition callee_return_rel_def:
  callee_return_rel dst_addr src_addr sz s1 s2
    (IntRet ret1 rs1) (IntRet ret2 rs2) =
    (ret2 = ret1 /\
     copy_fwd_state_rel dst_addr src_addr sz
       (merge_callee_state s1 rs1) (merge_callee_state s2 rs2)) /\
  callee_return_rel dst_addr src_addr sz s1 s2
    (Halt hs1) (Halt hs2) = observable_equiv hs1 hs2 /\
  callee_return_rel dst_addr src_addr sz s1 s2
    (Abort a1 as1) (Abort a2 as2) = (a2 = a1 /\ revert_equiv as1 as2) /\
  callee_return_rel dst_addr src_addr sz s1 s2
    (Error e1) (Error e2) = T /\
  callee_return_rel dst_addr src_addr sz s1 s2
    (OK os1) (OK os2) = T /\
  callee_return_rel dst_addr src_addr sz s1 s2 _ _ = F
End

Definition copy_fwd_step_result_rel_def:
  copy_fwd_step_result_rel dst_addr src_addr sz (OK s1) (OK s2) =
    copy_fwd_state_rel dst_addr src_addr sz s1 s2 /\
  copy_fwd_step_result_rel dst_addr src_addr sz (IntRet ret1 s1) (IntRet ret2 s2) =
    (ret2 = ret1 /\ execution_frame s2 = execution_frame s1) /\
  copy_fwd_step_result_rel dst_addr src_addr sz (Halt s1) (Halt s2) =
    observable_equiv s1 s2 /\
  copy_fwd_step_result_rel dst_addr src_addr sz (Abort a1 s1) (Abort a2 s2) =
    (a2 = a1 /\ revert_equiv s1 s2) /\
  copy_fwd_step_result_rel dst_addr src_addr sz (Error e1) (Error e2) = T /\
  copy_fwd_step_result_rel _ _ _ _ _ = F
End

Definition icf_invoke_step_rel_def:
  icf_invoke_step_rel (ctx : venom_context) (rma : (string, bool list) fmap)
                      (dst_addr : num) (src_addr : num) (sz : num)
                      (i1 : instruction) (i2 : instruction)
                      (s1 : venom_state) (s2 : venom_state) : bool <=>
    i2.inst_outputs = i1.inst_outputs /\
    case decode_invoke i1 of
      NONE => decode_invoke i2 = NONE
    | SOME (fn_name, arg_ops1) =>
        ?arg_ops2.
          decode_invoke i2 = SOME (fn_name, arg_ops2) /\
          (!callee_fn.
             lookup_function fn_name ctx.ctx_functions = SOME callee_fn ==>
             has_ret_instruction callee_fn) /\
          case eval_operands arg_ops1 s1 of
            NONE => eval_operands arg_ops2 s2 = NONE
          | SOME args1 =>
              ?args2.
                eval_operands arg_ops2 s2 = SOME args2 /\
                rma_args_ok rma fn_name dst_addr src_addr sz args1 args2
End

Definition icf_suffix_inst_rel_def:
  icf_suffix_inst_rel (ctx : venom_context) (rma : (string, bool list) fmap)
                      (dst_addr : num) (src_addr : num) (sz : num)
                      (i1 : instruction) (i2 : instruction)
                      (s1 : venom_state) (s2 : venom_state) : bool <=>
    if is_terminator i1.inst_opcode then
      icf_exec_result_rel (step_inst_base i1 s1) (step_inst_base i2 s2)
    else if i1.inst_opcode = INVOKE then
      i2.inst_opcode = INVOKE /\
      icf_invoke_step_rel ctx rma dst_addr src_addr sz i1 i2 s1 s2
    else
      i2.inst_opcode <> INVOKE /\
      copy_fwd_step_result_rel dst_addr src_addr sz
        (step_inst_base i1 s1) (step_inst_base i2 s2)
End

Definition rma_sound_def:
  rma_sound (ctx : venom_context)
            (rma : (string, bool list) fmap) : bool <=>
    (!callee_fn dst_addr src_addr sz s1 s2 args1 args2 cs1 cs2 fuel.
       MEM callee_fn ctx.ctx_functions /\
       has_ret_instruction callee_fn /\
       32 <= sz /\
       copy_fwd_state_rel dst_addr src_addr sz s1 s2 /\
       rma_args_ok rma callee_fn.fn_name dst_addr src_addr sz args1 args2 /\
       setup_callee callee_fn args1 s1 = SOME cs1 /\
       setup_callee callee_fn args2 s2 = SOME cs2 ==>
       callee_return_rel dst_addr src_addr sz s1 s2
         (run_blocks fuel ctx callee_fn cs1)
         (run_blocks fuel ctx callee_fn cs2)) /\
    (!fn bb0 bb1 copy_idx bb2 fuel s s_phi s_copy.
       MEM fn ctx.ctx_functions /\
       MEM bb0 fn.fn_blocks /\
       icf_mcopy_noped bb0 bb1 /\
       icf_fwd_step (icf_fn_meta_of ctx) ctx.ctx_functions rma
         fn bb1 copy_idx bb2 /\
       eval_phis s bb1.bb_instructions = OK s_phi /\
       prefix_steps fuel ctx bb1 copy_idx
         (s_phi with vs_inst_idx := phi_prefix_length bb1.bb_instructions)
         s_copy ==>
       ?dst_op src_op sz_w v_dst v_src.
         (EL copy_idx bb1.bb_instructions).inst_operands =
           [dst_op; src_op; Lit sz_w] /\
         eval_operand dst_op s_copy = SOME v_dst /\
         eval_operand src_op s_copy = SOME v_src /\
         32 <= w2n sz_w /\
         (!j v.
            SUC copy_idx <= j /\ j < LENGTH bb1.bb_instructions /\
            (dst_op = Var v \/ src_op = Var v) ==>
            ~MEM v (EL j bb1.bb_instructions).inst_outputs) /\
         (!j t1 t2.
            SUC copy_idx <= j /\ j < LENGTH bb1.bb_instructions /\
            t1.vs_inst_idx = j /\ t2.vs_inst_idx = j /\
            eval_operand dst_op t1 = SOME v_dst /\
            eval_operand src_op t2 = SOME v_src /\
            copy_fwd_state_rel (w2n v_dst) (w2n v_src) (w2n sz_w) t1 t2 ==>
            icf_suffix_inst_rel ctx rma (w2n v_dst) (w2n v_src) (w2n sz_w)
              (EL j bb1.bb_instructions) (EL j bb2.bb_instructions) t1 t2))
End

Theorem lookup_function_MEM_name[local]:
  !fns name fn.
    lookup_function name fns = SOME fn ==>
    MEM fn fns /\ fn.fn_name = name
Proof
  Induct >> simp[lookup_function_def, FIND_thm] >>
  rw[] >> gvs[lookup_function_def] >> res_tac >> simp[]
QED

Theorem setup_callee_same_some[local]:
  !fn args1 s1 args2 s2 cs1.
    setup_callee fn args1 s1 = SOME cs1 ==>
    ?cs2. setup_callee fn args2 s2 = SOME cs2
Proof
  rw[setup_callee_def] >> Cases_on `fn_entry_label fn` >> gvs[]
QED

Theorem is_terminator_not_invoke[local]:
  !opc. is_terminator opc ==> opc <> INVOKE
Proof
  Cases >> EVAL_TAC
QED

Theorem step_inst_invoke_under_copy_fwd_state_rel:
  !fuel ctx rma dst_addr src_addr sz i1 i2 s1 s2.
    rma_sound ctx rma /\
    32 <= sz /\
    copy_fwd_state_rel dst_addr src_addr sz s1 s2 /\
    i1.inst_opcode = INVOKE /\
    i2.inst_opcode = INVOKE /\
    icf_invoke_step_rel ctx rma dst_addr src_addr sz i1 i2 s1 s2 ==>
    copy_fwd_step_result_rel dst_addr src_addr sz
      (step_inst fuel ctx i1 s1) (step_inst fuel ctx i2 s2)
Proof
  rpt strip_tac >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [step_inst_def])) >>
  simp[] >>
  qpat_x_assum `icf_invoke_step_rel _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [icf_invoke_step_rel_def]) >>
  Cases_on `decode_invoke i1` >> simp[copy_fwd_step_result_rel_def] >>
  PairCases_on `x` >> simp[] >> strip_tac >> simp[] >>
  Cases_on `lookup_function x0 ctx.ctx_functions` >>
  simp[copy_fwd_step_result_rel_def] >>
  `MEM x ctx.ctx_functions /\ x.fn_name = x0` by
    metis_tac[lookup_function_MEM_name] >>
  `has_ret_instruction x` by
    (qpat_x_assum `!callee_fn. SOME x = SOME callee_fn ==> _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  Cases_on `eval_operands x1 s1` >> gvs[copy_fwd_step_result_rel_def] >>
  Cases_on `setup_callee x x' s1`
  >- (`setup_callee x args2 s2 = NONE` by
        (Cases_on `setup_callee x args2 s2` >> simp[] >>
         drule_then (qspecl_then [`x'`, `s1`] mp_tac) setup_callee_same_some >>
         simp[]) >>
      simp[copy_fwd_step_result_rel_def]) >>
  drule_then (qspecl_then [`args2`, `s2`] strip_assume_tac)
    setup_callee_same_some >>
  simp[] >>
  qpat_x_assum `rma_sound ctx rma`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [rma_sound_def]) >>
  disch_then (qspecl_then [`x`, `dst_addr`, `src_addr`, `sz`, `s1`, `s2`,
                           `x'`, `args2`, `x''`, `cs2`, `fuel`] mp_tac) >>
  simp[] >>
  Cases_on `run_blocks fuel ctx x x''` >>
  Cases_on `run_blocks fuel ctx x cs2` >>
  simp[callee_return_rel_def, copy_fwd_step_result_rel_def] >>
  strip_tac >> gvs[] >>
  drule_then (qspec_then `i` assume_tac)
    adopt_return_fmp_preserves_copy_fwd_state_rel >>
  drule_then (qspecl_then [`i1.inst_outputs`, `i.iret_values`] mp_tac)
    bind_outputs_preserves_copy_fwd_state_rel >>
  Cases_on `bind_outputs i1.inst_outputs i.iret_values
              (adopt_return_fmp i (merge_callee_state s1 v))` >>
  Cases_on `bind_outputs i1.inst_outputs i.iret_values
              (adopt_return_fmp i (merge_callee_state s2 v'))` >>
  simp[copy_fwd_step_result_rel_def]
QED

Theorem eval_operand_with_inst_idx[local,simp]:
  !op s idx. eval_operand op (s with vs_inst_idx := idx) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem exec_block_suffix_measure[local]:
  !m fuel ctx rma dst_op src_op v_dst v_src sz bb1 bb2 idx s1 s2.
    m = LENGTH bb1.bb_instructions - idx /\
    rma_sound ctx rma /\
    LENGTH bb2.bb_instructions = LENGTH bb1.bb_instructions /\
    LIST_REL icf_inst_compat bb1.bb_instructions bb2.bb_instructions /\
    32 <= sz /\
    s1.vs_inst_idx = idx /\
    s2.vs_inst_idx = idx /\
    eval_operand dst_op s1 = SOME v_dst /\
    eval_operand src_op s2 = SOME v_src /\
    copy_fwd_state_rel (w2n v_dst) (w2n v_src) sz s1 s2 /\
    (!j v.
       idx <= j /\ j < LENGTH bb1.bb_instructions /\
       (dst_op = Var v \/ src_op = Var v) ==>
       ~MEM v (EL j bb1.bb_instructions).inst_outputs) /\
    (!j t1 t2.
       idx <= j /\ j < LENGTH bb1.bb_instructions /\
       t1.vs_inst_idx = j /\ t2.vs_inst_idx = j /\
       eval_operand dst_op t1 = SOME v_dst /\
       eval_operand src_op t2 = SOME v_src /\
       copy_fwd_state_rel (w2n v_dst) (w2n v_src) sz t1 t2 ==>
       icf_suffix_inst_rel ctx rma (w2n v_dst) (w2n v_src) sz
         (EL j bb1.bb_instructions) (EL j bb2.bb_instructions) t1 t2) ==>
    icf_exec_result_rel (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb2 s2)
Proof
  completeInduct_on `m` >> rpt gen_tac >> strip_tac >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  Cases_on `idx < LENGTH bb1.bb_instructions`
  >- (`get_instruction bb1 s1.vs_inst_idx = SOME (EL idx bb1.bb_instructions) /\
       get_instruction bb2 s2.vs_inst_idx = SOME (EL idx bb2.bb_instructions)` by
        simp[get_instruction_def] >>
      simp[] >>
      `icf_inst_compat (EL idx bb1.bb_instructions)
                       (EL idx bb2.bb_instructions)` by
        metis_tac[LIST_REL_icf_inst_compat_EL] >>
      `is_terminator (EL idx bb2.bb_instructions).inst_opcode <=>
       is_terminator (EL idx bb1.bb_instructions).inst_opcode` by
        fs[icf_inst_compat_def] >>
      `icf_suffix_inst_rel ctx rma (w2n v_dst) (w2n v_src) sz
         (EL idx bb1.bb_instructions) (EL idx bb2.bb_instructions) s1 s2` by
        (first_assum irule >> simp[]) >>
      Cases_on `is_terminator (EL idx bb1.bb_instructions).inst_opcode` >>
      qpat_x_assum `icf_suffix_inst_rel _ _ _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [icf_suffix_inst_rel_def]) >>
      simp[] >> strip_tac
      >- (`(EL idx bb1.bb_instructions).inst_opcode <> INVOKE /\
           (EL idx bb2.bb_instructions).inst_opcode <> INVOKE` by
            metis_tac[is_terminator_not_invoke] >>
          simp[step_inst_non_invoke] >>
          Cases_on `step_inst_base (EL idx bb1.bb_instructions) s1` >>
          Cases_on `step_inst_base (EL idx bb2.bb_instructions) s2` >>
          gvs[icf_exec_result_rel_def]) >>
      `copy_fwd_step_result_rel (w2n v_dst) (w2n v_src) sz
         (step_inst fuel ctx (EL idx bb1.bb_instructions) s1)
         (step_inst fuel ctx (EL idx bb2.bb_instructions) s2)` by
        (Cases_on `(EL idx bb1.bb_instructions).inst_opcode = INVOKE` >> fs[]
         >- (irule step_inst_invoke_under_copy_fwd_state_rel >>
             simp[] >> qexists_tac `rma` >> simp[])
         >- simp[step_inst_non_invoke]) >>
      Cases_on `step_inst fuel ctx (EL idx bb1.bb_instructions) s1` >>
      Cases_on `step_inst fuel ctx (EL idx bb2.bb_instructions) s2` >>
      fs[copy_fwd_step_result_rel_def, icf_exec_result_rel_def] >>
      `!v'. MEM v' (EL idx bb2.bb_instructions).inst_outputs ==>
            MEM v' (EL idx bb1.bb_instructions).inst_outputs` by
        (gvs[icf_inst_compat_def, mk_nop_inst_def]) >>
      `eval_operand dst_op v = SOME v_dst` by
        (qpat_x_assum `!m'. _` kall_tac >>
         metis_tac[step_inst_preserves_eval_operand, LESS_EQ_REFL]) >>
      `eval_operand src_op v' = SOME v_src` by
        (qpat_assum `step_inst fuel ctx (EL idx bb2.bb_instructions) s2 = OK v'`
           (mp_then Any (qspec_then `src_op` mp_tac)
             step_inst_preserves_eval_operand) >>
         simp[] >> impl_tac
         >- (rpt strip_tac >> first_x_assum drule >>
             metis_tac[LESS_EQ_REFL]) >> simp[]) >>
      qpat_x_assum `!m'. m' < _ ==> _`
        (qspec_then `LENGTH bb1.bb_instructions - SUC idx` mp_tac) >>
      impl_tac >- decide_tac >>
      disch_then (qspecl_then [`fuel`, `ctx`, `rma`, `dst_op`, `src_op`,
                               `v_dst`, `v_src`, `sz`, `bb1`, `bb2`,
                               `v with vs_inst_idx := SUC idx`,
                               `v' with vs_inst_idx := SUC idx`] mp_tac) >>
      simp[] >> impl_tac
      >- (rpt conj_tac
          >- (irule copy_fwd_state_rel_with_inst_idx >> simp[])
          >- (rpt strip_tac >>
              qpat_x_assum `!j v. _` (qspecl_then [`j`, `v''`] mp_tac) >>
              simp[] >> decide_tac)) >>
      simp[])
  >- (`get_instruction bb1 s1.vs_inst_idx = NONE /\
       get_instruction bb2 s2.vs_inst_idx = NONE` by
        simp[get_instruction_def] >>
      simp[icf_exec_result_rel_def])
QED

Theorem exec_block_suffix_under_copy_fwd_state_rel:
  !fuel ctx rma dst_op src_op v_dst v_src sz bb1 bb2 idx s1 s2.
    rma_sound ctx rma /\
    LENGTH bb2.bb_instructions = LENGTH bb1.bb_instructions /\
    LIST_REL icf_inst_compat bb1.bb_instructions bb2.bb_instructions /\
    32 <= sz /\
    s1.vs_inst_idx = idx /\
    s2.vs_inst_idx = idx /\
    eval_operand dst_op s1 = SOME v_dst /\
    eval_operand src_op s2 = SOME v_src /\
    copy_fwd_state_rel (w2n v_dst) (w2n v_src) sz s1 s2 /\
    (!j v.
       idx <= j /\ j < LENGTH bb1.bb_instructions /\
       (dst_op = Var v \/ src_op = Var v) ==>
       ~MEM v (EL j bb1.bb_instructions).inst_outputs) /\
    (!j t1 t2.
       idx <= j /\ j < LENGTH bb1.bb_instructions /\
       t1.vs_inst_idx = j /\ t2.vs_inst_idx = j /\
       eval_operand dst_op t1 = SOME v_dst /\
       eval_operand src_op t2 = SOME v_src /\
       copy_fwd_state_rel (w2n v_dst) (w2n v_src) sz t1 t2 ==>
       icf_suffix_inst_rel ctx rma (w2n v_dst) (w2n v_src) sz
         (EL j bb1.bb_instructions) (EL j bb2.bb_instructions) t1 t2) ==>
    icf_exec_result_rel (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb2 s2)
Proof
  metis_tac[exec_block_suffix_measure]
QED

Theorem step_inst_mcopy_ok[local]:
  !fuel ctx inst dst_op src_op sz_w s v_dst v_src.
    inst.inst_opcode = MCOPY /\
    inst.inst_operands = [dst_op; src_op; Lit sz_w] /\
    eval_operand dst_op s = SOME v_dst /\
    eval_operand src_op s = SOME v_src ==>
    step_inst fuel ctx inst s =
      OK (mcopy (w2n v_dst) (w2n v_src) (w2n sz_w) s) /\
    ~is_terminator inst.inst_opcode
Proof
  rw[step_inst_non_invoke, step_inst_base_opcode_eqs, is_terminator_def,
     eval_operands_def, eval_operand_def]
QED

Theorem eval_operand_mcopy[local,simp]:
  !op d sc sz s.
    eval_operand op (mcopy d sc sz s) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def, mcopy_def,
                write_memory_with_expansion_def, LET_THM]
QED

Theorem icf_fwd_step_run_block:
  !ctx rma fn bb0 bb1 copy_idx bb2 fuel s.
    rma_sound ctx rma /\
    MEM fn ctx.ctx_functions /\
    MEM bb0 fn.fn_blocks /\
    icf_mcopy_noped bb0 bb1 /\
    icf_fwd_step (icf_fn_meta_of ctx) ctx.ctx_functions rma
      fn bb1 copy_idx bb2 ==>
    icf_exec_result_rel (run_block fuel ctx bb1 s) (run_block fuel ctx bb2 s)
Proof
  rpt strip_tac >>
  drule icf_fwd_step_structural >> strip_tac >>
  drule_then (qspec_then `s` strip_assume_tac) icf_fwd_step_phis >>
  simp[run_block_def] >>
  Cases_on `eval_phis s bb1.bb_instructions` >> simp[icf_exec_result_rel_def] >>
  irule exec_block_prefix_to_copy >>
  qexists_tac `copy_idx` >> simp[] >>
  rpt strip_tac >>
  drule prefix_steps_end_idx >> strip_tac >>
  qpat_assum `rma_sound ctx rma`
    (mp_tac o CONJUNCT2 o REWRITE_RULE [rma_sound_def]) >>
  disch_then (qspecl_then [`fn`, `bb0`, `bb1`, `copy_idx`, `bb2`,
                           `fuel`, `s`, `v`, `s_copy`] mp_tac) >>
  simp[] >> strip_tac >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  `get_instruction bb1 s_copy.vs_inst_idx =
   SOME (EL copy_idx bb1.bb_instructions) /\
   get_instruction bb2 s_copy.vs_inst_idx =
   SOME (mk_nop_inst (EL copy_idx bb1.bb_instructions))` by
    simp[get_instruction_def] >>
  simp[mk_nop_inst_correct] >>
  `step_inst fuel ctx (EL copy_idx bb1.bb_instructions) s_copy =
   OK (mcopy (w2n v_dst) (w2n v_src) (w2n sz_w) s_copy) /\
   ~is_terminator (EL copy_idx bb1.bb_instructions).inst_opcode` by
    (irule step_inst_mcopy_ok >> simp[]) >>
  `~is_terminator (mk_nop_inst (EL copy_idx bb1.bb_instructions)).inst_opcode` by
    simp[mk_nop_inst_def, is_terminator_def] >>
  simp[is_terminator_def] >>
  irule exec_block_suffix_under_copy_fwd_state_rel >>
  simp[] >>
  qexistsl_tac [`dst_op`, `rma`, `src_op`,
                `w2n sz_w`, `v_dst`, `v_src`] >>
  simp[] >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  irule copy_fwd_state_rel_with_inst_idx >>
  simp[mcopy_establishes_copy_fwd_state_rel]
QED

Theorem step_inst_base_mload_cross_copy_fwd_state_rel:
  !id dst_var src_var out_var dst_addr src_addr sz s1 s2 v_dst v_src.
    32 <= sz /\
    copy_fwd_state_rel dst_addr src_addr sz s1 s2 /\
    lookup_var dst_var s1 = SOME v_dst /\
    lookup_var src_var s2 = SOME v_src /\
    w2n v_dst = dst_addr /\
    w2n v_src = src_addr ==>
    copy_fwd_step_result_rel dst_addr src_addr sz
      (step_inst_base (mk_inst id MLOAD [Var dst_var] [out_var]) s1)
      (step_inst_base (mk_inst id MLOAD [Var src_var] [out_var]) s2)
Proof
  rpt strip_tac >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
       eval_operands_def, eval_operand_def,
       copy_fwd_step_result_rel_def] >>
  `mload (w2n v_dst) s1 = mload (w2n v_src) s2` by
    (gvs[] >> irule mload_copy_fwd_state_rel_cross >>
     qexists_tac `sz` >> simp[]) >>
  gvs[update_var_preserves_copy_fwd_state_rel]
QED

Theorem step_inst_base_sstore_copy_fwd_state_rel:
  !id slot_op val_op dst_addr src_addr sz s1 s2.
    copy_fwd_state_rel dst_addr src_addr sz s1 s2 ==>
    copy_fwd_step_result_rel dst_addr src_addr sz
      (step_inst_base (mk_inst id SSTORE [slot_op; val_op] []) s1)
      (step_inst_base (mk_inst id SSTORE [slot_op; val_op] []) s2)
Proof
  rpt strip_tac >>
  `(!v. lookup_var v s2 = lookup_var v s1) /\
   s2.vs_labels = s1.vs_labels /\
   s2.vs_call_ctx = s1.vs_call_ctx /\
   s2.vs_accounts = s1.vs_accounts /\
   s2.vs_halted = s1.vs_halted /\
   s2.vs_returndata = s1.vs_returndata /\
   s2.vs_logs = s1.vs_logs /\
   s2.vs_transient = s1.vs_transient /\
   s2.vs_outcomes = s1.vs_outcomes /\
   s2.vs_requests = s1.vs_requests /\
   s2.vs_pending_deletions = s1.vs_pending_deletions /\
   s2.vs_immutables = s1.vs_immutables` by
    fs[copy_fwd_state_rel_def, icf_equiv_def] >>
  `eval_operands [slot_op; val_op] s2 = eval_operands [slot_op; val_op] s1` by
    (Cases_on `slot_op` >> Cases_on `val_op` >>
     simp[eval_operands_def, eval_operand_def]) >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def] >>
  `eval_operand slot_op s2 = eval_operand slot_op s1 /\
   eval_operand val_op s2 = eval_operand val_op s1` by
    (Cases_on `slot_op` >> Cases_on `val_op` >> simp[eval_operand_def]) >>
  Cases_on `eval_operand slot_op s1` >>
  gvs[copy_fwd_step_result_rel_def] >>
  Cases_on `eval_operand val_op s1` >>
  gvs[copy_fwd_step_result_rel_def] >>
  Cases_on `s1.vs_call_ctx.cc_static` >>
  simp[copy_fwd_step_result_rel_def, revert_equiv_def] >>
  rw[copy_fwd_state_rel_def, icf_equiv_def, lookup_var_def, sstore_def,
     mem_agrees_except_def, Excl "pass_residual_mask_equality"] >>
  gvs[copy_fwd_state_rel_def, icf_equiv_def, lookup_var_def,
      mem_agrees_except_def, eval_operands_def, copy_fwd_step_result_rel_def,
      halt_state_def, set_returndata_def, revert_equiv_def]
QED

Theorem step_inst_base_stop_copy_fwd_state_rel:
  !id dst_addr src_addr sz s1 s2.
    copy_fwd_state_rel dst_addr src_addr sz s1 s2 ==>
    icf_exec_result_rel
      (step_inst_base (mk_inst id STOP [] []) s1)
      (step_inst_base (mk_inst id STOP [] []) s2)
Proof
  rw[step_inst_base_opcode_eqs, mk_inst_def, icf_exec_result_rel_def,
     halt_state_def, set_returndata_def, observable_equiv_def,
     copy_fwd_state_rel_def, icf_equiv_def]
QED

Theorem icf_rtc_fwd_step_run_block[local]:
  !ctx rma fn bb0 bb1 bb2.
    RTC (icf_bounded_fwd_step (icf_fn_meta_of ctx) ctx.ctx_functions rma fn bb0)
      bb1 bb2 ==>
    rma_sound ctx rma /\
    MEM fn ctx.ctx_functions /\
    MEM bb0 fn.fn_blocks ==>
    !fuel s.
      icf_exec_result_rel (run_block fuel ctx bb1 s) (run_block fuel ctx bb2 s)
Proof
  ntac 4 gen_tac >>
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT >> rw[] >>
  first_x_assum drule_all >> strip_tac >>
  gvs[icf_bounded_fwd_step_def] >>
  `icf_exec_result_rel (run_block fuel ctx bb1 s) (run_block fuel ctx bb1' s)` by
    metis_tac[icf_fwd_step_run_block] >>
  metis_tac[icf_exec_result_rel_trans]
QED

Theorem icf_block_compat_run_block:
  !fn_meta ctx rma fn bb1 bb2 fuel s.
    rma_sound ctx rma /\
    fn_meta = icf_fn_meta_of ctx /\
    rma = readonly_mem_analyze ctx /\
    MEM fn ctx.ctx_functions /\
    MEM bb1 fn.fn_blocks /\
    icf_block_compat fn_meta ctx.ctx_functions rma fn bb1 bb2 ==>
    icf_exec_result_rel (run_block fuel ctx bb1 s) (run_block fuel ctx bb2 s)
Proof
  rw[icf_block_compat_def] >> simp[] >>
  metis_tac[icf_rtc_fwd_step_run_block]
QED

Theorem LIST_REL_lookup_block_mem[local]:
  !R bbs1 bbs2 lbl.
    (!b1 b2. R b1 b2 ==> b2.bb_label = b1.bb_label) /\
    LIST_REL R bbs1 bbs2 ==>
    case lookup_block lbl bbs1 of
      NONE => lookup_block lbl bbs2 = NONE
    | SOME b1 =>
        ?b2. lookup_block lbl bbs2 = SOME b2 /\ MEM b1 bbs1 /\ R b1 b2
Proof
  gen_tac >> Induct_on `LIST_REL` >> rw[lookup_block_def, FIND_thm] >>
  `h2.bb_label = h1.bb_label` by res_tac >>
  rw[] >>
  first_x_assum (qspec_then `lbl` mp_tac) >>
  simp[lookup_block_def] >>
  Cases_on `FIND (\b. b.bb_label = lbl) bbs1` >> simp[] >>
  strip_tac >> simp[]
QED

Theorem icf_fn_compat_lookup_block_sim:
  !fn_meta ctx rma fn1 fn2 lbl.
    rma_sound ctx rma /\
    fn_meta = icf_fn_meta_of ctx /\
    rma = readonly_mem_analyze ctx /\
    MEM fn1 ctx.ctx_functions /\
    wf_function fn1 /\
    icf_fn_compat fn_meta ctx.ctx_functions rma fn1 fn2 ==>
    case lookup_block lbl fn1.fn_blocks of
      NONE => lookup_block lbl fn2.fn_blocks = NONE
    | SOME bb1 =>
        ?bb2. lookup_block lbl fn2.fn_blocks = SOME bb2 /\
              (!fuel s.
                 icf_exec_result_rel
                   (run_block fuel ctx bb1 s)
                   (run_block fuel ctx bb2 s))
Proof
  rpt strip_tac >>
  qpat_x_assum `icf_fn_compat _ _ _ _ _` mp_tac >>
  simp[icf_fn_compat_def] >> strip_tac
  >- (gvs[] >> Cases_on `lookup_block lbl fn1.fn_blocks` >> simp[])
  >- (mp_tac (Q.SPECL [`icf_block_compat (icf_fn_meta_of ctx) ctx.ctx_functions
                         (readonly_mem_analyze ctx) fn1`,
                       `fn1.fn_blocks`, `bbs`, `lbl`]
              LIST_REL_lookup_block_mem) >>
      impl_tac >- (simp[] >> metis_tac[icf_block_compat_label]) >>
      Cases_on `lookup_block lbl fn1.fn_blocks` >> simp[] >>
      strip_tac >> gvs[] >>
      rpt strip_tac >>
      metis_tac[icf_block_compat_run_block])
  >- (qabbrev_tac `R = \b1 b3.
        ?b2. icf_block_compat (icf_fn_meta_of ctx) ctx.ctx_functions
               (readonly_mem_analyze ctx) fn1 b1 b2 /\
             b3 = clear_nops_block b2` >>
      `LIST_REL R fn1.fn_blocks (MAP clear_nops_block bbs)` by
        (qpat_x_assum `LIST_REL _ _ _`
           (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
         rw[Abbr `R`, LIST_REL_EL_EQN, EL_MAP] >> metis_tac[]) >>
      mp_tac (Q.SPECL [`R`, `fn1.fn_blocks`, `MAP clear_nops_block bbs`, `lbl`]
              LIST_REL_lookup_block_mem) >>
      impl_tac
      >- (simp[Abbr `R`, clear_nops_block_def] >>
          rpt strip_tac >> gvs[] >>
          drule icf_block_compat_label >> simp[]) >>
      simp[clear_nops_function_def, Abbr `R`] >>
      Cases_on `lookup_block lbl fn1.fn_blocks` >> simp[] >>
      strip_tac >> gvs[] >>
      rpt strip_tac >>
      `icf_exec_result_rel (run_block fuel ctx x s) (run_block fuel ctx b2' s)` by
        metis_tac[icf_block_compat_run_block] >>
      `bb_well_formed x` by (fs[wf_function_def, EVERY_MEM] >> res_tac) >>
      `icf_mcopy_noped x b2'` by fs[icf_block_compat_def] >>
      `bb_well_formed b2'` by metis_tac[icf_mcopy_noped_preserves_bb_wf] >>
      `result_equiv {} (run_block fuel ctx b2' s)
         (run_block fuel ctx (clear_nops_block b2') s)` by
        metis_tac[clear_nops_run_block_equiv] >>
      `icf_exec_result_rel (run_block fuel ctx b2' s)
         (run_block fuel ctx (clear_nops_block b2') s)` by
        metis_tac[result_equiv_empty_icf_exec_result_rel] >>
      metis_tac[icf_exec_result_rel_trans])
QED

Theorem run_blocks_0[local,simp]:
  !ctx fn s. run_blocks 0 ctx fn s = Error "out of fuel"
Proof
  simp[Once run_blocks_def]
QED

Theorem icf_fn_compat_run_blocks_same_ctx:
  !fuel fn_meta ctx rma fn1 fn2 s.
    rma_sound ctx rma /\
    fn_meta = icf_fn_meta_of ctx /\
    rma = readonly_mem_analyze ctx /\
    MEM fn1 ctx.ctx_functions /\
    wf_function fn1 /\
    icf_fn_compat fn_meta ctx.ctx_functions rma fn1 fn2 ==>
    icf_exec_result_rel (run_blocks fuel ctx fn1 s) (run_blocks fuel ctx fn2 s)
Proof
  Induct_on `fuel` >- simp[] >>
  rpt strip_tac >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [run_blocks_unfold])) >>
  mp_tac (Q.SPECL [`fn_meta`, `ctx`, `rma`, `fn1`, `fn2`, `s.vs_current_bb`]
          icf_fn_compat_lookup_block_sim) >>
  simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn1.fn_blocks` >>
  simp[icf_exec_result_rel_def] >>
  strip_tac >> simp[] >>
  first_x_assum (qspecl_then [`fuel`, `s`] mp_tac) >>
  Cases_on `run_block fuel ctx x s` >>
  Cases_on `run_block fuel ctx bb2 s` >>
  simp[icf_exec_result_rel_def] >>
  strip_tac >> gvs[] >>
  Cases_on `v.vs_halted` >>
  simp[icf_exec_result_rel_def, stateEquivPropsTheory.observable_equiv_refl] >>
  metis_tac[]
QED

Definition icf_bounded_call_agree_def:
  icf_bounded_call_agree (n : num) (A : venom_context) (B : venom_context) : bool <=>
    !name.
      case lookup_function name A.ctx_functions of
        NONE => lookup_function name B.ctx_functions = NONE
      | SOME f1 =>
          ?f2. lookup_function name B.ctx_functions = SOME f2 /\
               fn_entry_label f2 = fn_entry_label f1 /\
               (!k s. k < n ==>
                  icf_exec_result_rel (run_blocks k A f1 s) (run_blocks k B f2 s))
End

Theorem icf_bounded_call_agree_mono:
  !n m A B.
    icf_bounded_call_agree n A B /\ m <= n ==>
    icf_bounded_call_agree m A B
Proof
  rw[icf_bounded_call_agree_def] >>
  first_x_assum (qspec_then `name` mp_tac) >>
  Cases_on `lookup_function name A.ctx_functions` >> simp[] >>
  strip_tac >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem icf_step_inst_ctx_change:
  !n A B k inst s.
    icf_bounded_call_agree n A B /\ k < n ==>
    icf_exec_result_rel (step_inst k A inst s) (step_inst k B inst s)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [step_inst_def])) >>
      simp[] >>
      Cases_on `decode_invoke inst` >> simp[icf_exec_result_rel_def] >>
      PairCases_on `x` >> simp[] >>
      qpat_x_assum `icf_bounded_call_agree _ _ _`
        (mp_tac o REWRITE_RULE [icf_bounded_call_agree_def]) >>
      disch_then (qspec_then `x0` mp_tac) >>
      Cases_on `lookup_function x0 A.ctx_functions` >>
      simp[icf_exec_result_rel_def] >>
      strip_tac >> simp[] >>
      Cases_on `eval_operands x1 s` >> simp[icf_exec_result_rel_def] >>
      `setup_callee f2 x' s = setup_callee x x' s` by
        metis_tac[o1PassLiftTheory.setup_callee_entry_label] >>
      simp[] >>
      Cases_on `setup_callee x x' s` >> simp[icf_exec_result_rel_def] >>
      first_x_assum (qspecl_then [`k`, `x''`] mp_tac) >> simp[] >>
      Cases_on `run_blocks k A x x''` >>
      Cases_on `run_blocks k B f2 x''` >>
      simp[icf_exec_result_rel_def] >>
      strip_tac >> gvs[] >>
      `merge_callee_state s v' = merge_callee_state s v` by
        simp[merge_callee_state_def, venom_state_component_equality] >>
      simp[]) >>
  simp[step_inst_non_invoke]
QED

Theorem icf_exec_block_ctx_change_measure[local]:
  !m n A B k bb s.
    m = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    icf_bounded_call_agree n A B /\ k < n ==>
    icf_exec_result_rel (exec_block k A bb s) (exec_block k B bb s)
Proof
  completeInduct_on `m` >> rpt gen_tac >> strip_tac >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  Cases_on `get_instruction bb s.vs_inst_idx` >>
  simp[icf_exec_result_rel_def] >>
  `icf_exec_result_rel (step_inst k A x s) (step_inst k B x s)` by
    metis_tac[icf_step_inst_ctx_change] >>
  Cases_on `step_inst k A x s` >>
  Cases_on `step_inst k B x s` >>
  gvs[icf_exec_result_rel_def] >>
  Cases_on `is_terminator x.inst_opcode` >> simp[icf_exec_result_rel_def] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  first_x_assum
    (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  impl_tac >- decide_tac >>
  disch_then (qspecl_then [`n`, `A`, `B`, `k`, `bb`,
                           `v with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[]
QED

Theorem icf_exec_block_ctx_change:
  !n A B k bb s.
    icf_bounded_call_agree n A B /\ k < n ==>
    icf_exec_result_rel (exec_block k A bb s) (exec_block k B bb s)
Proof
  metis_tac[icf_exec_block_ctx_change_measure]
QED

Theorem icf_run_block_ctx_change:
  !n A B k bb s.
    icf_bounded_call_agree n A B /\ k < n ==>
    icf_exec_result_rel (run_block k A bb s) (run_block k B bb s)
Proof
  rpt strip_tac >>
  simp[run_block_def] >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[icf_exec_result_rel_def] >>
  irule icf_exec_block_ctx_change >>
  qexists_tac `n` >> simp[]
QED

Theorem icf_run_blocks_ctx_change:
  !n A B f s.
    icf_bounded_call_agree n A B ==>
    icf_exec_result_rel (run_blocks n A f s) (run_blocks n B f s)
Proof
  Induct_on `n` >- simp[] >>
  rpt strip_tac >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [run_blocks_unfold])) >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks` >>
  simp[icf_exec_result_rel_def] >>
  `n < SUC n` by decide_tac >>
  `icf_exec_result_rel (run_block n A x s) (run_block n B x s)` by
    metis_tac[icf_run_block_ctx_change] >>
  Cases_on `run_block n A x s` >>
  Cases_on `run_block n B x s` >>
  gvs[icf_exec_result_rel_def] >>
  Cases_on `v.vs_halted` >>
  simp[icf_exec_result_rel_def, stateEquivPropsTheory.observable_equiv_refl] >>
  first_x_assum irule >>
  irule icf_bounded_call_agree_mono >>
  qexists_tac `SUC n` >> simp[]
QED

Theorem LIST_REL_same_name_lookup:
  !R fns1 fns2 name.
    (!f1 f2. R f1 f2 ==> f2.fn_name = f1.fn_name) /\
    LIST_REL R fns1 fns2 ==>
    (case lookup_function name fns1 of
       NONE => lookup_function name fns2 = NONE
     | SOME f1 => ?f2. lookup_function name fns2 = SOME f2 /\ R f1 f2)
Proof
  gen_tac >> Induct_on `LIST_REL` >> rw[lookup_function_def, FIND_thm] >>
  `h2.fn_name = h1.fn_name` by res_tac >>
  rw[] >> first_x_assum (qspec_then `name` mp_tac) >> simp[lookup_function_def]
QED

Theorem icf_fn_compat_bounded_call_agree:
  !fn_meta C C' rma n.
    rma_sound C rma /\
    fn_meta = icf_fn_meta_of C /\
    rma = readonly_mem_analyze C /\
    (?P. EVERY (\fn. fn_ptr_ok P fn) C.ctx_functions) /\
    EVERY wf_function C.ctx_functions /\
    LIST_REL (icf_fn_compat fn_meta C.ctx_functions rma)
      C.ctx_functions C'.ctx_functions ==>
    icf_bounded_call_agree n C C'
Proof
  ntac 4 gen_tac >> strip_tac >>
  Induct_on `n` >> rw[icf_bounded_call_agree_def]
  >- (mp_tac (Q.SPECL [`icf_fn_compat (icf_fn_meta_of C) C.ctx_functions
                         (readonly_mem_analyze C)`,
                       `C.ctx_functions`, `C'.ctx_functions`, `name`]
              LIST_REL_same_name_lookup) >>
       impl_tac >- metis_tac[icf_fn_compat_fn_name] >>
       Cases_on `lookup_function name C.ctx_functions` >> simp[] >>
       strip_tac >> simp[] >> metis_tac[icf_fn_compat_entry_label])
  >- (mp_tac (Q.SPECL [`icf_fn_compat (icf_fn_meta_of C) C.ctx_functions
                         (readonly_mem_analyze C)`,
                       `C.ctx_functions`, `C'.ctx_functions`, `name`]
              LIST_REL_same_name_lookup) >>
      impl_tac >- metis_tac[icf_fn_compat_fn_name] >>
      Cases_on `lookup_function name C.ctx_functions` >> simp[] >>
      strip_tac >> simp[] >>
      conj_tac >- metis_tac[icf_fn_compat_entry_label] >>
      rpt strip_tac >>
      `MEM x C.ctx_functions` by metis_tac[lookup_function_MEM_name] >>
      `wf_function x /\ fn_ptr_ok P x` by (fs[EVERY_MEM] >> res_tac) >>
      `icf_exec_result_rel (run_blocks k C x s) (run_blocks k C f2 s)` by
        metis_tac[icf_fn_compat_run_blocks_same_ctx] >>
      `icf_bounded_call_agree n C C'` by
        (simp[icf_bounded_call_agree_def] >> metis_tac[]) >>
      `icf_bounded_call_agree k C C'` by
        (irule icf_bounded_call_agree_mono >>
         qexists_tac `n` >> simp[]) >>
      `icf_exec_result_rel (run_blocks k C f2 s) (run_blocks k C' f2 s)` by
        metis_tac[icf_run_blocks_ctx_change] >>
      metis_tac[icf_exec_result_rel_trans])
QED

Theorem icf_ctx_sim_from_fn_compat:
  !D lo fn_meta C C' rma vs.
    o1_ctx_shape C /\
    ptr_discipline lo C vs /\
    fn_meta = icf_fn_meta_of C /\
    rma = readonly_mem_analyze C /\
    rma_sound C rma /\
    C'.ctx_entry = C.ctx_entry /\
    LIST_REL (icf_fn_compat fn_meta C.ctx_functions rma)
      C.ctx_functions C'.ctx_functions ==>
    ctx_sim D C C' vs vs
Proof
  rpt strip_tac >>
  `EVERY wf_function C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >>
     metis_tac[]) >>
  `?P. EVERY (\fn. fn_ptr_ok P fn) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >>
     qexists_tac `P` >> metis_tac[]) >>
  irule ctx_transform_correct_ctx_sim >>
  rw[ctx_transform_correct_def] >>
  qexists_tac `fuel` >>
  `(!name fn. C.ctx_entry = SOME name /\
              lookup_function name C.ctx_functions = SOME fn ==>
              EVERY (\inst. ~MEM inst.inst_opcode [RET; RETFMP; DRET])
                (fn_insts fn))` by
    (rpt strip_tac >>
     `MEM fn C.ctx_functions /\ fn.fn_name = name` by
       metis_tac[lookup_function_MEM_name] >>
     fs[o1_ctx_shape_def, o1_fn_shape_def, entry_fn_no_return_def,
        EVERY_MEM] >>
     metis_tac[]) >>
  `!v t. run_context fuel C vs <> IntRet v t` by
    metis_tac[venomRetPropsTheory.run_context_not_int_ret] >>
  `!t. run_context fuel C vs <> OK t` by
    metis_tac[venomRetPropsTheory.run_context_not_ok] >>
  qpat_x_assum `terminates _` mp_tac >>
  simp[run_context_def] >>
  Cases_on `C.ctx_entry` >- simp[terminates_def] >>
  `icf_bounded_call_agree (SUC fuel) C C'` by
    metis_tac[icf_fn_compat_bounded_call_agree] >>
  qpat_x_assum `icf_bounded_call_agree _ _ _`
    (mp_tac o REWRITE_RULE [icf_bounded_call_agree_def]) >>
  disch_then (qspec_then `x` mp_tac) >>
  Cases_on `lookup_function x C.ctx_functions` >- simp[terminates_def] >>
  simp[run_function_def] >> strip_tac >>
  Cases_on `fn_entry_label x'` >- simp[terminates_def] >>
  simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`fuel`,
    `vs with <|vs_prev_bb := NONE; vs_current_bb := x''; vs_inst_idx := 0|>`] mp_tac) >>
  simp[] >>
  qpat_x_assum `!v t. run_context fuel C vs <> IntRet v t` mp_tac >>
  qpat_x_assum `!t. run_context fuel C vs <> OK t` mp_tac >>
  simp[run_context_def, run_function_def] >>
  Cases_on `run_blocks fuel C x'
              (vs with <|vs_prev_bb := NONE; vs_current_bb := x''; vs_inst_idx := 0|>)` >>
  Cases_on `run_blocks fuel C' f2
              (vs with <|vs_prev_bb := NONE; vs_current_bb := x''; vs_inst_idx := 0|>)` >>
  gvs[terminates_def, icf_exec_result_rel_def, unit_result_rel_def]
QED

(* ==========================================================================
   5. Evaluation Helpers for Concrete Copy-Forwarding Witnesses
   ========================================================================== *)

Theorem FOLDL_block_pass_SND:
  !f bbs c0 acc0.
    SND (FOLDL (\(changed, acc) bb.
      let (bb_changed, new_bb) = f bb in
      (changed \/ bb_changed, acc ++ [new_bb])) (c0, acc0) bbs) =
    acc0 ++ MAP (\bb. SND (f bb)) bbs
Proof
  gen_tac >> Induct_on `bbs` >> fs[] >> rpt gen_tac >>
  Cases_on `f h` >> fs[]
QED

Theorem unique_mcopy_7_at_3:
  !i0 i1 i2 i3 i4 i5 i6.
    i0.inst_opcode <> MCOPY /\
    i1.inst_opcode <> MCOPY /\
    i2.inst_opcode <> MCOPY /\
    i3.inst_opcode = MCOPY /\
    i4.inst_opcode <> MCOPY /\
    i5.inst_opcode <> MCOPY /\
    i6.inst_opcode <> MCOPY ==>
    3 < LENGTH [i0; i1; i2; i3; i4; i5; i6] /\
    (EL 3 [i0; i1; i2; i3; i4; i5; i6]).inst_opcode = MCOPY /\
    (!j. j < LENGTH [i0; i1; i2; i3; i4; i5; i6] /\ j <> 3 ==>
         (EL j [i0; i1; i2; i3; i4; i5; i6]).inst_opcode <> MCOPY)
Proof
  rpt strip_tac >> simp[] >>
  `j = 0 \/ j = 1 \/ j = 2 \/ j = 4 \/ j = 5 \/ j = 6` by gvs[] >>
  gvs[]
QED

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
    call_checks_ok fn /\
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

Theorem icf_fwd_step_has_mcopy:
  !fn_meta ctx_fns rma fn bb1 copy_idx bb2.
    icf_fwd_step fn_meta ctx_fns rma fn bb1 copy_idx bb2 ==>
    ~EVERY (\i. i.inst_opcode <> MCOPY) bb1.bb_instructions
Proof
  rpt strip_tac >>
  drule icf_fwd_step_structural >> strip_tac >>
  fs[EVERY_MEM] >>
  first_x_assum (qspec_then `EL copy_idx bb1.bb_instructions` mp_tac) >>
  simp[EL_MEM]
QED

Theorem icf_mcopy_noped_mcopy_back:
  !b1 b2 i.
    icf_mcopy_noped b1 b2 /\
    i < LENGTH b2.bb_instructions /\
    (EL i b2.bb_instructions).inst_opcode = MCOPY ==>
    i < LENGTH b1.bb_instructions /\
    (EL i b1.bb_instructions).inst_opcode = MCOPY
Proof
  rw[icf_mcopy_noped_def, LIST_REL_EL_EQN] >>
  first_x_assum (qspec_then `i` mp_tac) >>
  simp[icf_inst_compat_def, mk_nop_inst_def] >> rw[] >> gvs[]
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
