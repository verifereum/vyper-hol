(*
 * Internal Return Copy Forwarding — what a transformed block is
 *
 * ircf_transform_block folds ircf_try_forward over a block's MCOPYs,
 * always consulting the DFG of the original function while the block
 * changes under it.  This theory states its result without the fold:
 * the forwarded copies are the source MCOPYs that became NOPs, each
 * meets the use-shape conditions on the original function, ASSIGNs are
 * untouched, and every other instruction has each destination alias of
 * a forwarded copy replaced by that copy's source root.
 *
 * TOP-LEVEL:
 *   ircf_alias              — v reachable from x by ASSIGN chains
 *   ircf_fwd_ok             — the conditions one forwarded copy meets
 *   ircf_block_plan         — the transformed block, described
 *   ircf_transform_block_plan — ircf_transform_block meets it
 *)

Theory internalReturnCopyFwdPlan
Ancestors
  internalReturnCopyFwdDefs invokeCopyFwdCommonDefs dfgDefs passSharedDefs
  venomWf venomInst list pred_set dfgAnalysisProps While venomWfProps
  o1LowerDloadClosure

(* v is x, or the output of an ASSIGN of an alias of x *)
Inductive ircf_alias:
[~refl:]
  (!fn x. ircf_alias fn x x)
[~assign:]
  (!fn x v inst out.
     ircf_alias fn x v /\ MEM inst (fn_insts fn) /\
     inst.inst_opcode = ASSIGN /\ MEM (Var v) inst.inst_operands /\
     inst.inst_outputs = [out] ==>
     ircf_alias fn x out)
End

Theorem ircf_alias_output_bound:
  !fn x v. ircf_alias fn x v ==>
    v = x \/ MEM v (FLAT (MAP (\inst. inst.inst_outputs) (fn_insts fn)))
Proof
  ho_match_mp_tac ircf_alias_ind >> rpt strip_tac >> simp[] >>
  disj2_tac >> simp[MEM_FLAT, MEM_MAP] >> metis_tac[MEM]
QED

Theorem ircf_alias_finite:
  !fn x. FINITE {v | ircf_alias fn x v}
Proof
  rpt gen_tac >> irule SUBSET_FINITE_I >>
  qexists_tac `x INSERT set (FLAT (MAP (\inst. inst.inst_outputs) (fn_insts fn)))` >>
  simp[SUBSET_DEF] >> metis_tac[ircf_alias_output_bound]
QED

Theorem ircf_alias_step_closed:
  !fn x a. a SUBSET {v | ircf_alias fn x v} ==>
    SND (icf_aliases_step (dfg_build_function fn) a) SUBSET
      {v | ircf_alias fn x v}
Proof
  simp[SUBSET_DEF, icf_aliases_step_mem] >> rpt strip_tac >>
  gvs[] >> drule dfg_build_function_uses_sound >>
  strip_tac >> irule ircf_alias_assign >>
  qexistsl_tac [`inst`, `v`] >>
  gvs[dfg_operand_vars_eq, MEM_operand_vars_eq_Var]
QED

Theorem ircf_collect_aliases_fixpoint:
  !fn x. ?res.
    OWHILE (\(changed, _). changed)
      (\(_, a). icf_aliases_step (dfg_build_function fn) a) (T,{x}) = SOME (F,res) /\
    x IN res /\ res SUBSET {v | ircf_alias fn x v} /\
    icf_aliases_step (dfg_build_function fn) res = (F,res)
Proof
  rpt gen_tac >>
  qspecl_then [`CARD ({v | ircf_alias fn x v} DIFF {x})`,
              `{v | ircf_alias fn x v}`, `dfg_build_function fn`, `{x}`]
    mp_tac icf_aliases_owhile_fixpoint >>
  simp[ircf_alias_finite, ircf_alias_refl, ircf_alias_step_closed] >>
  metis_tac[SUBSET_DEF, IN_SING]
QED

Theorem ircf_alias_least_closed:
  !fn x v. ircf_alias fn x v ==>
    !a. x IN a /\ SND (icf_aliases_step (dfg_build_function fn) a) = a ==>
        v IN a
Proof
  ho_match_mp_tac ircf_alias_ind >> rpt strip_tac >> gvs[] >>
  `MEM inst (dfg_get_uses (dfg_build_function fn) v)` by
    (irule dfg_build_function_uses_complete >>
     simp[dfg_operand_vars_eq, MEM_operand_vars_eq_Var]) >>
  metis_tac[icf_aliases_step_mem]
QED

Theorem icf_collect_aliases_ircf_alias:
  !fn x. icf_collect_aliases (dfg_build_function fn) x =
         {v | ircf_alias fn x v}
Proof
  rpt gen_tac >> qspecl_then [`fn`, `x`] strip_assume_tac
    ircf_collect_aliases_fixpoint >>
  simp[icf_collect_aliases_def] >>
  simp[EXTENSION] >> gen_tac >> eq_tac
  >- (gvs[SUBSET_DEF] >> metis_tac[]) >>
  strip_tac >> drule ircf_alias_least_closed >>
  disch_then (qspec_then `res` mp_tac) >> simp[]
QED

Theorem ircf_alias_use_positions_mem:
  !fn x v inst pos.
    MEM (v,inst,pos)
      (icf_alias_use_positions (dfg_build_function fn)
        (icf_collect_aliases (dfg_build_function fn) x)) <=>
    ircf_alias fn x v /\ MEM inst (fn_insts fn) /\
    pos < LENGTH inst.inst_operands /\ EL pos inst.inst_operands = Var v
Proof
  simp[icf_collect_aliases_ircf_alias, icf_alias_use_positions_mem,
       ircf_alias_finite, icf_use_positions_mem] >>
  rpt gen_tac >> eq_tac
  >- (rpt strip_tac >> drule dfg_build_function_uses_sound >> simp[]) >>
  rpt strip_tac >> simp[] >> irule dfg_build_function_uses_complete >>
  simp[dfg_operand_vars_eq, MEM_operand_vars_eq_Var] >>
  metis_tac[EL_MEM]
QED

Theorem ircf_alias_trans:
  !fn y z. ircf_alias fn y z ==> !x.
    ircf_alias fn x y ==> ircf_alias fn x z
Proof
  ho_match_mp_tac ircf_alias_ind >> rpt strip_tac >>
  metis_tac[ircf_alias_assign]
QED

Theorem ircf_assign_root_alias:
  !dfg visited v fn.
    dfg = dfg_build_function fn /\ fn_inst_wf fn ==>
    ircf_alias fn (icf_assign_root dfg visited v) v
Proof
  recInduct icf_assign_root_ind >> rpt strip_tac >> gvs[] >>
  once_rewrite_tac[icf_assign_root_def] >>
  Cases_on `v IN visited` >> simp[ircf_alias_refl] >>
  Cases_on `dfg_get_def (dfg_build_function fn) v` >> simp[ircf_alias_refl] >>
  rename1 `dfg_get_def (dfg_build_function fn) v = SOME inst` >>
  Cases_on `inst.inst_opcode = ASSIGN` >> simp[ircf_alias_refl] >>
  drule dfg_build_function_correct >> strip_tac >>
  `inst_wf inst` by
    (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[]) >>
  `inst.inst_outputs = [v]` by
    (gvs[inst_wf_def] >> Cases_on `inst.inst_outputs` >> gvs[LENGTH_EQ_NUM_compute]) >>
  Cases_on `inst.inst_operands` >> simp[ircf_alias_refl] >>
  Cases_on `h` >> simp[ircf_alias_refl] >>
  Cases_on `t` >> simp[ircf_alias_refl] >>
  irule ircf_alias_assign >> qexistsl_tac [`inst`, `s`] >>
  simp[] >> first_x_assum irule >> simp[]
QED

Definition ircf_alloca_of_def:
  ircf_alloca_of fn x sz <=>
    ?ai. MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
         ai.inst_outputs = [x] /\ ai.inst_operands = [Lit sz]
End

Theorem ircf_alloca_alias_root:
  !fn a b sz. ssa_form fn /\ ircf_alloca_of fn b sz /\
    ircf_alias fn a b ==> a = b
Proof
  rpt gen_tac >> simp[ircf_alloca_of_def] >> strip_tac >>
  qpat_x_assum `ircf_alias _ _ _` mp_tac >>
  once_rewrite_tac[ircf_alias_cases] >> strip_tac >> gvs[] >>
  `inst = ai` by
    (irule ssa_outputs_same_inst >>
     gvs[fn_insts_def] >> metis_tac[MEM]) >> gvs[]
QED

Theorem ircf_alias_assign_inv:
  !fn b sz inst out v.
    ssa_form fn /\ ircf_alloca_of fn b sz /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode = ASSIGN /\
    inst.inst_outputs = [out] /\ inst.inst_operands = [Var v] /\
    ircf_alias fn b out ==> ircf_alias fn b v
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ircf_alias _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [ircf_alias_cases])
  >- (gvs[ircf_alloca_of_def] >>
      `inst = ai` by
        (irule ssa_outputs_same_inst >>
         gvs[fn_insts_def] >> metis_tac[MEM]) >> gvs[]) >>
  `inst' = inst` by
    (irule ssa_outputs_same_inst >>
     gvs[fn_insts_def] >> metis_tac[MEM]) >> gvs[]
QED

Theorem ircf_alloca_aliases_separate:
  !fn a v. ircf_alias fn a v ==>
    !b sa sb. ssa_form fn /\ fn_inst_wf fn /\
      ircf_alloca_of fn a sa /\ ircf_alloca_of fn b sb /\
      ircf_alias fn b v ==> a = b
Proof
  ho_match_mp_tac ircf_alias_ind >> conj_tac
  >- (rpt strip_tac >> metis_tac[ircf_alloca_alias_root]) >>
  rpt strip_tac >>
  `inst_wf inst` by
    (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[]) >>
  `inst.inst_operands = [Var v]` by
    (gvs[inst_wf_def] >> Cases_on `inst.inst_operands` >> gvs[LENGTH_EQ_NUM_compute]) >>
  `ircf_alias fn b v` by
    (irule ircf_alias_assign_inv >> metis_tac[]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem ircf_alloca_of_dfg:
  !fn root inst sz.
    fn_inst_wf fn /\ dfg_get_def (dfg_build_function fn) root = SOME inst /\
    icf_is_alloca inst /\ icf_matches_alloca_size inst sz ==>
    ircf_alloca_of fn root sz
Proof
  rpt gen_tac >> simp[icf_is_alloca_def, icf_matches_alloca_size_def] >> strip_tac >>
  drule dfg_build_function_correct >> strip_tac >>
  `inst_wf inst` by
    (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[]) >>
  `inst.inst_outputs = [root]` by
    (gvs[inst_wf_def] >> Cases_on `inst.inst_outputs` >> gvs[LENGTH_EQ_NUM_compute]) >>
  simp[ircf_alloca_of_def] >> qexists_tac `inst` >> simp[] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[]
QED

(* The destination root, source root and size of a forwardable copy, as
   ircf_try_forward computes them. *)
Definition ircf_copy_roots_def:
  ircf_copy_roots fn (inst:instruction) =
    case inst.inst_operands of
      [Var dv; Var sv; Lit sz] =>
        SOME (icf_assign_root (dfg_build_function fn) {} dv,
              icf_assign_root (dfg_build_function fn) {} sv, sz)
    | _ => NONE
End

(* The copies forwarded from bb to bb2 *)
Definition ircf_fwds_def:
  ircf_fwds (bb:basic_block) (bb2:basic_block) =
    {k | k < LENGTH bb.bb_instructions /\
         (EL k bb.bb_instructions).inst_opcode = MCOPY /\
         (EL k bb2.bb_instructions).inst_opcode = NOP}
End

(* Copy k of bb, MCOPY d <- s of sz bytes, meets the use shape:
   both roots are ALLOCAs of sz bytes; the source's aliases are used only
   by ASSIGNs, this copy, and INVOKEs earlier in bb; the destination's
   aliases, apart from ASSIGNs and this copy, only later in bb, by
   non-PHIs, as memory addresses. *)
Definition ircf_fwd_ok_def:
  ircf_fwd_ok fn bb k d s sz <=>
    k < LENGTH bb.bb_instructions /\
    (EL k bb.bb_instructions).inst_opcode = MCOPY /\
    (?dv sv.
       (EL k bb.bb_instructions).inst_operands = [Var dv; Var sv; Lit sz] /\
       ircf_alias fn d dv /\ ircf_alias fn s sv) /\
    d <> s /\ ircf_alloca_of fn d sz /\ ircf_alloca_of fn s sz /\
    (!inst v.
       MEM inst (fn_insts fn) /\ ircf_alias fn s v /\
       MEM (Var v) inst.inst_operands ==>
       inst.inst_opcode = ASSIGN \/
       inst.inst_id = (EL k bb.bb_instructions).inst_id \/
       (inst.inst_opcode = INVOKE /\
        ?i. i < k /\ EL i bb.bb_instructions = inst)) /\
    (!inst v.
       MEM inst (fn_insts fn) /\ ircf_alias fn d v /\
       MEM (Var v) inst.inst_operands /\ inst.inst_opcode <> ASSIGN /\
       inst.inst_id <> (EL k bb.bb_instructions).inst_id ==>
       inst.inst_opcode <> PHI /\
       (?i. k < i /\ i < LENGTH bb.bb_instructions /\
            EL i bb.bb_instructions = inst) /\
       (!pos v'.
          pos < LENGTH inst.inst_operands /\
          EL pos inst.inst_operands = Var v' /\ ircf_alias fn d v' ==>
          is_mem_addr_position inst.inst_opcode pos))
End

(* v redirected to the source root of the forwarded copy whose
   destination it aliases, if any *)
Definition ircf_redirect_def:
  ircf_redirect fn bb bb2 v =
    if ?k d s sz. k IN ircf_fwds bb bb2 /\
                  ircf_copy_roots fn (EL k bb.bb_instructions) =
                    SOME (d,s,sz) /\
                  ircf_alias fn d v
    then @s. ?k d sz. k IN ircf_fwds bb bb2 /\
                      ircf_copy_roots fn (EL k bb.bb_instructions) =
                        SOME (d,s,sz) /\
                      ircf_alias fn d v
    else v
End

Definition ircf_redirect_op_def:
  ircf_redirect_op fn bb bb2 op =
    case op of Var v => Var (ircf_redirect fn bb bb2 v) | _ => op
End

Definition ircf_block_plan_def:
  ircf_block_plan fn bb bb2 <=>
    bb2.bb_label = bb.bb_label /\
    LENGTH bb2.bb_instructions = LENGTH bb.bb_instructions /\
    (!k. k IN ircf_fwds bb bb2 ==>
         ?d s sz.
           ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,s,sz) /\
           ircf_fwd_ok fn bb k d s sz) /\
    (!i. i < LENGTH bb.bb_instructions ==>
         EL i bb2.bb_instructions =
           if i IN ircf_fwds bb bb2 then mk_nop_inst (EL i bb.bb_instructions)
           else if (EL i bb.bb_instructions).inst_opcode = ASSIGN
           then EL i bb.bb_instructions
           else (EL i bb.bb_instructions) with inst_operands :=
                  MAP (ircf_redirect_op fn bb bb2)
                    (EL i bb.bb_instructions).inst_operands)
End

Theorem ircf_findi_original_inst:
  !fn bb cur inst j.
    wf_function fn /\ MEM bb fn.fn_blocks /\ MEM inst (fn_insts fn) /\
    MAP (\i. i.inst_id) cur.bb_instructions =
      MAP (\i. i.inst_id) bb.bb_instructions /\
    findi (\i. i.inst_id = inst.inst_id) cur.bb_instructions = SOME j ==>
    j < LENGTH bb.bb_instructions /\ EL j bb.bb_instructions = inst
Proof
  rpt strip_tac >>
  drule findi_inst_ids >> disch_then (qspec_then `inst.inst_id` assume_tac) >>
  `findi (\i. i.inst_id = inst.inst_id) bb.bb_instructions = SOME j` by metis_tac[] >>
  drule_all findi_some_index >> strip_tac >> simp[] >>
  irule fn_inst_ids_distinct_inj >> conj_tac >- gvs[] >> qexists_tac `fn` >>
  gvs[wf_function_def] >>
  simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
  metis_tac[EL_MEM]
QED

Theorem ircf_ret_buf_original_uses:
  !fn bb cur ctx s cid k.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    ctx.icf_dfg = dfg_build_function fn /\
    MAP (\i. i.inst_id) cur.bb_instructions =
      MAP (\i. i.inst_id) bb.bb_instructions /\
    ircf_is_ret_buf_source ctx cur.bb_instructions s cid k ==>
    !inst v. MEM inst (fn_insts fn) /\ ircf_alias fn s v /\
      MEM (Var v) inst.inst_operands ==>
      inst.inst_opcode = ASSIGN \/ inst.inst_id = cid \/
      (inst.inst_opcode = INVOKE /\
       ?i. i < k /\ EL i bb.bb_instructions = inst)
Proof
  rpt gen_tac >> strip_tac >>
  drule ircf_is_ret_buf_source_uses >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `MEM (Var v) _` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  `MEM (v,inst,n) (icf_alias_use_positions ctx.icf_dfg
      (icf_collect_aliases ctx.icf_dfg s))` by
    simp[ircf_alias_use_positions_mem] >>
  first_x_assum (qspecl_then [`v`, `inst`, `n`] mp_tac) >>
  simp[] >> strip_tac >> gvs[icf_is_assign_output_use_def] >>
  drule_all ircf_findi_original_inst >> strip_tac >>
  simp[] >> metis_tac[]
QED

Theorem ircf_forward_original_dst_position:
  !fn bb cur ctx k new_insts dst src sz inst v pos.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    ctx.icf_dfg = dfg_build_function fn /\
    MAP (\i. i.inst_id) cur.bb_instructions =
      MAP (\i. i.inst_id) bb.bb_instructions /\
    ircf_try_forward ctx cur k = SOME new_insts /\
    (EL k cur.bb_instructions).inst_operands = [Var dst; Var src; Lit sz] /\
    MEM inst (fn_insts fn) /\
    ircf_alias fn (icf_assign_root ctx.icf_dfg {} dst) v /\
    pos < LENGTH inst.inst_operands /\ EL pos inst.inst_operands = Var v /\
    inst.inst_opcode <> ASSIGN /\
    inst.inst_id <> (EL k cur.bb_instructions).inst_id ==>
    inst.inst_opcode <> PHI /\ is_mem_addr_position inst.inst_opcode pos /\
    ?i. k < i /\ i < LENGTH bb.bb_instructions /\ EL i bb.bb_instructions = inst
Proof
  rpt gen_tac >> strip_tac >>
  drule ircf_try_forward_checks >> strip_tac >> gvs[] >>
  `MEM (v,inst,pos) (icf_alias_use_positions ctx.icf_dfg
     (icf_collect_aliases ctx.icf_dfg (icf_assign_root ctx.icf_dfg {} dst)))` by
    simp[ircf_alias_use_positions_mem] >>
  first_x_assum (qspecl_then [`v`, `inst`, `pos`] mp_tac) >>
  simp[icf_is_assign_output_use_def] >> strip_tac >> gvs[] >>
  drule_all ircf_findi_original_inst >> strip_tac >> metis_tac[]
QED

Theorem ircf_try_forward_original_ok:
  !fn bb cur ctx k new_insts.
    wf_function fn /\ fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
    ctx.icf_dfg = dfg_build_function fn /\
    MAP (\i. i.inst_id) cur.bb_instructions =
      MAP (\i. i.inst_id) bb.bb_instructions /\
    k < LENGTH bb.bb_instructions /\
    EL k cur.bb_instructions = EL k bb.bb_instructions /\
    ircf_try_forward ctx cur k = SOME new_insts ==>
    ?d s sz. ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,s,sz) /\
             ircf_fwd_ok fn bb k d s sz
Proof
  rpt gen_tac >> strip_tac >>
  drule ircf_try_forward_checks >> strip_tac >>
  drule ircf_try_forward_prefix_and_copy >> strip_tac >>
  qexistsl_tac [`icf_assign_root ctx.icf_dfg {} dst`,
               `icf_assign_root ctx.icf_dfg {} src`, `sz`] >>
  gvs[] >> simp[ircf_copy_roots_def, ircf_fwd_ok_def] >>
  conj_tac >- metis_tac[ircf_assign_root_alias] >>
  conj_tac >- metis_tac[ircf_alloca_of_dfg] >>
  conj_tac >- metis_tac[ircf_alloca_of_dfg] >>
  conj_tac >- (match_mp_tac ircf_ret_buf_original_uses >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `MEM (Var v) _` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  metis_tac[ircf_forward_original_dst_position]
QED

Theorem ircf_block_plan_fwd_ok:
  !fn bb cur k d s sz.
    ircf_block_plan fn bb cur /\ k IN ircf_fwds bb cur /\
    ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,s,sz) ==>
    ircf_fwd_ok fn bb k d s sz
Proof
  rpt gen_tac >> simp[ircf_block_plan_def] >> strip_tac >>
  qpat_x_assum `!k. k IN _ ==> _` (qspec_then `k` mp_tac) >>
  simp[] >> rpt strip_tac >> gvs[]
QED

Theorem ircf_block_plan_inst_ids:
  !fn bb cur. ircf_block_plan fn bb cur ==>
    MAP (\i. i.inst_id) cur.bb_instructions =
    MAP (\i. i.inst_id) bb.bb_instructions
Proof
  rpt gen_tac >> simp[ircf_block_plan_def] >> strip_tac >>
  irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
  first_x_assum (qspec_then `x` mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  Cases_on `x IN ircf_fwds bb cur` >> simp[mk_nop_inst_def] >>
  Cases_on `(EL x bb.bb_instructions).inst_opcode = ASSIGN` >> simp[]
QED

Theorem ircf_copy_roots_no_write_use:
  !fn bb copy d s sz bb2 inst v.
    ircf_no_dst_write_alias fn /\ MEM bb fn.fn_blocks /\
    MEM copy bb.bb_instructions /\ copy.inst_opcode = MCOPY /\
    ircf_copy_roots fn copy = SOME (d,s,sz) /\
    MEM bb2 fn.fn_blocks /\ MEM inst bb2.bb_instructions /\
    inst.inst_id <> copy.inst_id /\ ircf_alias fn d v /\
    MEM (Var v) inst.inst_operands ==>
    mem_write_ops inst = NONE /\ inst.inst_opcode <> INVOKE
Proof
  rpt gen_tac >>
  simp[ircf_copy_roots_def, ircf_no_dst_write_alias_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum (qspec_then `bb` mp_tac) >>
  simp[icf_collect_aliases_ircf_alias] >> metis_tac[]
QED

Theorem ircf_copy_roots_mcopy_no_alias:
  !fn bb copy d s sz bb2 inst dst src len v.
    ircf_no_dst_write_alias fn /\ MEM bb fn.fn_blocks /\
    MEM copy bb.bb_instructions /\ copy.inst_opcode = MCOPY /\
    ircf_copy_roots fn copy = SOME (d,s,sz) /\
    MEM bb2 fn.fn_blocks /\ MEM inst bb2.bb_instructions /\
    inst.inst_id <> copy.inst_id /\ inst.inst_opcode = MCOPY /\
    inst.inst_operands = [dst;src;len] /\ MEM (Var v) inst.inst_operands ==>
    ~ircf_alias fn d v
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  drule_all ircf_copy_roots_no_write_use >>
  simp[memLocDefsTheory.mem_write_ops_def]
QED

Theorem ircf_forward_roots_separate:
  !fn bb copy d s sz bb2 k d2 s2 sz2.
    ircf_no_dst_write_alias fn /\ MEM bb fn.fn_blocks /\
    MEM copy bb.bb_instructions /\ copy.inst_opcode = MCOPY /\
    ircf_copy_roots fn copy = SOME (d,s,sz) /\
    MEM bb2 fn.fn_blocks /\ ircf_fwd_ok fn bb2 k d2 s2 sz2 /\
    (EL k bb2.bb_instructions).inst_id <> copy.inst_id ==>
    d <> d2 /\ d <> s2
Proof
  rpt gen_tac >> simp[ircf_fwd_ok_def] >> strip_tac >>
  `~ircf_alias fn d dv /\ ~ircf_alias fn d sv` by
    (conj_tac >> metis_tac[ircf_copy_roots_mcopy_no_alias, EL_MEM, MEM]) >>
  metis_tac[]
QED

Theorem ircf_forward_alias_source_unique:
  !fn bb k j d s sz d2 s2 sz2 v.
    wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
    ircf_no_dst_write_alias fn /\ MEM bb fn.fn_blocks /\
    ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,s,sz) /\
    ircf_copy_roots fn (EL j bb.bb_instructions) = SOME (d2,s2,sz2) /\
    ircf_fwd_ok fn bb k d s sz /\ ircf_fwd_ok fn bb j d2 s2 sz2 /\
    ircf_alias fn d v /\ ircf_alias fn d2 v ==> s = s2
Proof
  rpt gen_tac >> strip_tac >>
  `d = d2` by
    (irule ircf_alloca_aliases_separate >>
     gvs[ircf_fwd_ok_def] >> metis_tac[]) >>
  `k < LENGTH bb.bb_instructions /\ j < LENGTH bb.bb_instructions /\
   (EL k bb.bb_instructions).inst_opcode = MCOPY` by
    gvs[ircf_fwd_ok_def] >>
  `(EL j bb.bb_instructions).inst_id = (EL k bb.bb_instructions).inst_id` by
    (spose_not_then assume_tac >>
     `MEM (EL k bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
     drule_all ircf_forward_roots_separate >> simp[]) >>
  `EL j bb.bb_instructions = EL k bb.bb_instructions` by
    (irule fn_inst_ids_distinct_inj >> conj_tac >- simp[] >> qexists_tac `fn` >>
     gvs[wf_function_def] >>
     simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM]) >>
  gvs[]
QED

Theorem ircf_forward_source_not_dest_alias:
  !fn bb k j d s sz d2 s2 sz2.
    wf_function fn /\ ssa_form fn /\ ircf_no_dst_write_alias fn /\
    MEM bb fn.fn_blocks /\
    ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,s,sz) /\
    ircf_copy_roots fn (EL j bb.bb_instructions) = SOME (d2,s2,sz2) /\
    ircf_fwd_ok fn bb k d s sz /\ ircf_fwd_ok fn bb j d2 s2 sz2 ==>
    ~ircf_alias fn d s2
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  `d = s2` by
    (irule ircf_alloca_alias_root >> gvs[ircf_fwd_ok_def] >> metis_tac[]) >>
  `k < LENGTH bb.bb_instructions /\ j < LENGTH bb.bb_instructions /\
   (EL k bb.bb_instructions).inst_opcode = MCOPY` by gvs[ircf_fwd_ok_def] >>
  Cases_on `(EL j bb.bb_instructions).inst_id = (EL k bb.bb_instructions).inst_id`
  >- (`EL j bb.bb_instructions = EL k bb.bb_instructions` by
        (irule fn_inst_ids_distinct_inj >> conj_tac >- simp[] >>
         qexists_tac `fn` >> gvs[wf_function_def] >>
         simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
         metis_tac[EL_MEM]) >> gvs[ircf_fwd_ok_def]) >>
  `MEM (EL k bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  drule_all ircf_forward_roots_separate >> simp[]
QED

Theorem ircf_redirect_unaffected:
  !fn bb cur v.
    (!k d s sz. k IN ircf_fwds bb cur /\
      ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,s,sz) ==>
      ~ircf_alias fn d v) ==>
    ircf_redirect fn bb cur v = v
Proof
  rpt strip_tac >> simp[ircf_redirect_def] >> metis_tac[]
QED

Theorem ircf_redirect_source:
  !fn bb cur k d s sz v.
    wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
    ircf_no_dst_write_alias fn /\ MEM bb fn.fn_blocks /\
    (!j d2 s2 sz2. j IN ircf_fwds bb cur /\
      ircf_copy_roots fn (EL j bb.bb_instructions) = SOME (d2,s2,sz2) ==>
      ircf_fwd_ok fn bb j d2 s2 sz2) /\
    k IN ircf_fwds bb cur /\
    ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,s,sz) /\
    ircf_alias fn d v ==> ircf_redirect fn bb cur v = s
Proof
  rpt gen_tac >> strip_tac >>
  `!j d2 s2 sz2. j IN ircf_fwds bb cur /\
    ircf_copy_roots fn (EL j bb.bb_instructions) = SOME (d2,s2,sz2) /\
    ircf_alias fn d2 v ==> s2 = s` by
    (rpt strip_tac >> metis_tac[ircf_forward_alias_source_unique]) >>
  rw[ircf_redirect_def] >- (irule SELECT_UNIQUE >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ircf_redirect_insert:
  !fn bb cur next k d s sz v.
    wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
    ircf_no_dst_write_alias fn /\ MEM bb fn.fn_blocks /\
    (!j d2 s2 sz2. j IN ircf_fwds bb cur /\
      ircf_copy_roots fn (EL j bb.bb_instructions) = SOME (d2,s2,sz2) ==>
      ircf_fwd_ok fn bb j d2 s2 sz2) /\
    ircf_fwds bb next = k INSERT ircf_fwds bb cur /\
    ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,s,sz) /\
    ircf_fwd_ok fn bb k d s sz ==>
    ircf_redirect fn bb next v =
      if ircf_alias fn d (ircf_redirect fn bb cur v) then s
      else ircf_redirect fn bb cur v
Proof
  rpt gen_tac >> strip_tac >>
  `!j d2 s2 sz2. j IN ircf_fwds bb next /\
    ircf_copy_roots fn (EL j bb.bb_instructions) = SOME (d2,s2,sz2) ==>
    ircf_fwd_ok fn bb j d2 s2 sz2` by
    (rpt gen_tac >> simp[] >> strip_tac >> gvs[] >> metis_tac[]) >>
  Cases_on `?j d2 s2 sz2. j IN ircf_fwds bb cur /\
    ircf_copy_roots fn (EL j bb.bb_instructions) = SOME (d2,s2,sz2) /\
    ircf_alias fn d2 v`
  >- (pop_assum strip_assume_tac >>
      `ircf_redirect fn bb cur v = s2` by metis_tac[ircf_redirect_source] >>
      `ircf_redirect fn bb next v = s2` by
        metis_tac[ircf_redirect_source, IN_INSERT] >>
      `~ircf_alias fn d s2` by metis_tac[ircf_forward_source_not_dest_alias] >>
      simp[]) >>
  `ircf_redirect fn bb cur v = v` by metis_tac[ircf_redirect_unaffected] >>
  Cases_on `ircf_alias fn d v`
  >- (`ircf_redirect fn bb next v = s` by
        metis_tac[ircf_redirect_source, IN_INSERT] >> simp[]) >>
  `ircf_redirect fn bb next v = v` by
    (irule ircf_redirect_unaffected >> rpt gen_tac >> simp[] >>
     strip_tac >> gvs[] >> metis_tac[]) >> simp[]
QED

Theorem ircf_block_plan_mcopy_stable:
  !fn bb cur i.
    wf_function fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
    MEM bb fn.fn_blocks /\ ircf_block_plan fn bb cur /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode = MCOPY /\
    i NOTIN ircf_fwds bb cur ==>
    EL i cur.bb_instructions = EL i bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (MAP (\inst. inst.inst_id) bb.bb_instructions)` by
    (qpat_x_assum `MEM bb _` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
     gvs[wf_function_def, fn_inst_ids_distinct_def, FLAT_APPEND,
         ALL_DISTINCT_APPEND]) >>
  `inst_wf (EL i bb.bb_instructions)` by
    (gvs[fn_inst_wf_def, fn_insts_blocks_flat, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  `?a b c. (EL i bb.bb_instructions).inst_operands = [a;b;c]` by
    (gvs[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  `!v. MEM (Var v) (EL i bb.bb_instructions).inst_operands ==>
    ircf_redirect fn bb cur v = v` by
    (rpt strip_tac >> irule ircf_redirect_unaffected >> rpt strip_tac >>
     `k < LENGTH bb.bb_instructions /\ k <> i /\
      (EL k bb.bb_instructions).inst_opcode = MCOPY` by
       (gvs[ircf_fwds_def] >> metis_tac[]) >>
     `(EL i bb.bb_instructions).inst_id <> (EL k bb.bb_instructions).inst_id` by
       (drule ALL_DISTINCT_EL_IMP >>
        disch_then (qspecl_then [`i`, `k`] mp_tac) >> simp[EL_MAP]) >>
     metis_tac[ircf_copy_roots_mcopy_no_alias, EL_MEM]) >>
  `MAP (ircf_redirect_op fn bb cur) (EL i bb.bb_instructions).inst_operands =
   (EL i bb.bb_instructions).inst_operands` by
    (irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
     Cases_on `EL x (EL i bb.bb_instructions).inst_operands` >>
     gvs[ircf_redirect_op_def] >>
     `x < LENGTH [a;b;c]` by simp[] >>
     drule EL_MEM >> simp[] >> metis_tac[]) >>
  qpat_x_assum `ircf_block_plan _ _ _` mp_tac >>
  simp[ircf_block_plan_def] >> strip_tac >>
  qpat_x_assum `!i. i < _ ==> _` (qspec_then `i` mp_tac) >>
  simp[instruction_component_equality]
QED

Theorem ircf_block_plan_mcopy_original:
  !fn bb cur k.
    wf_function fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
    MEM bb fn.fn_blocks /\ ircf_block_plan fn bb cur /\
    k < LENGTH bb.bb_instructions /\
    (EL k cur.bb_instructions).inst_opcode = MCOPY ==>
    (EL k bb.bb_instructions).inst_opcode = MCOPY /\
    k NOTIN ircf_fwds bb cur /\
    EL k cur.bb_instructions = EL k bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  `(EL k bb.bb_instructions).inst_opcode = MCOPY /\
   k NOTIN ircf_fwds bb cur` by
    (qpat_x_assum `ircf_block_plan _ _ _` mp_tac >>
     simp[ircf_block_plan_def] >> strip_tac >>
     qpat_x_assum `!i. i < _ ==> _` (qspec_then `k` mp_tac) >> simp[] >>
     Cases_on `k IN ircf_fwds bb cur` >> simp[mk_nop_inst_def] >>
     Cases_on `(EL k bb.bb_instructions).inst_opcode = ASSIGN` >>
     simp[] >> strip_tac >> gvs[]) >>
  metis_tac[ircf_block_plan_mcopy_stable]
QED

Theorem ircf_block_plan_forward_insert:
  !fn bb cur ctx k insts.
    wf_function fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
    MEM bb fn.fn_blocks /\ ircf_block_plan fn bb cur /\
    ircf_try_forward ctx cur k = SOME insts ==>
    ircf_fwds bb (cur with bb_instructions := insts) =
      k INSERT ircf_fwds bb cur
Proof
  rpt gen_tac >> strip_tac >>
  drule ircf_try_forward_prefix_and_copy >> strip_tac >>
  `LENGTH cur.bb_instructions = LENGTH bb.bb_instructions` by
    gvs[ircf_block_plan_def] >>
  `k < LENGTH bb.bb_instructions` by simp[] >>
  drule_all ircf_block_plan_mcopy_original >> strip_tac >>
  drule ircf_try_forward_inst_fields >> strip_tac >>
  simp[EXTENSION, ircf_fwds_def] >> gen_tac >>
  Cases_on `x = k` >- gvs[mk_nop_inst_def] >>
  Cases_on `x < LENGTH bb.bb_instructions` >> simp[] >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[]
QED

Theorem ircf_block_plan_refl:
  !fn bb. ircf_block_plan fn bb bb
Proof
  rpt gen_tac >>
  `ircf_fwds bb bb = {}` by
    (simp[ircf_fwds_def, EXTENSION] >> metis_tac[]) >>
  `ircf_redirect fn bb bb = I` by
    (simp[FUN_EQ_THM, ircf_redirect_def]) >>
  `ircf_redirect_op fn bb bb = I` by
    (simp[FUN_EQ_THM] >> gen_tac >> Cases_on `x` >> simp[ircf_redirect_op_def]) >>
  simp[ircf_block_plan_def] >> rpt strip_tac >>
  Cases_on `(EL i bb.bb_instructions).inst_opcode = ASSIGN` >> simp[]
QED

Theorem ircf_block_plan_step:
  !fn bb cur ctx k insts.
    wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
    ircf_no_dst_write_alias fn /\ MEM bb fn.fn_blocks /\
    ctx.icf_dfg = dfg_build_function fn /\
    ircf_block_plan fn bb cur /\
    ircf_try_forward ctx cur k = SOME insts ==>
    ircf_block_plan fn bb (cur with bb_instructions := insts)
Proof
  rpt gen_tac >> strip_tac >>
  drule ircf_try_forward_prefix_and_copy >> strip_tac >>
  `LENGTH cur.bb_instructions = LENGTH bb.bb_instructions` by
    gvs[ircf_block_plan_def] >>
  `k < LENGTH bb.bb_instructions` by simp[] >>
  drule_all ircf_block_plan_mcopy_original >> strip_tac >>
  drule ircf_block_plan_inst_ids >> strip_tac >>
  drule_all ircf_try_forward_original_ok >> strip_tac >>
  drule_all ircf_block_plan_forward_insert >> strip_tac >>
  `!j d2 s2 sz2. j IN ircf_fwds bb cur /\
    ircf_copy_roots fn (EL j bb.bb_instructions) = SOME (d2,s2,sz2) ==>
    ircf_fwd_ok fn bb j d2 s2 sz2` by
    metis_tac[ircf_block_plan_fwd_ok] >>
  simp[ircf_block_plan_def] >> conj_tac
  >- gvs[ircf_block_plan_def] >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[ircf_block_plan_def]) >>
  gen_tac >> strip_tac >>
  Cases_on `i = k` >- gvs[] >>
  suspend "pointwise"
QED

Resume ircf_block_plan_step[pointwise]:
  drule ircf_try_forward_update >> strip_tac >>
  `d = icf_assign_root ctx.icf_dfg {} dst /\
   s = icf_assign_root ctx.icf_dfg {} src` by
    gvs[ircf_copy_roots_def] >>
  `i < LENGTH cur.bb_instructions` by simp[] >>
  `EL i cur.bb_instructions =
    if i IN ircf_fwds bb cur then mk_nop_inst (EL i bb.bb_instructions)
    else if (EL i bb.bb_instructions).inst_opcode = ASSIGN
    then EL i bb.bb_instructions
    else (EL i bb.bb_instructions) with inst_operands :=
      MAP (ircf_redirect_op fn bb cur) (EL i bb.bb_instructions).inst_operands` by
    (qpat_x_assum `ircf_block_plan _ _ _` mp_tac >>
     simp[ircf_block_plan_def]) >>
  Cases_on `i IN ircf_fwds bb cur`
  >- (simp[indexedListsTheory.EL_MAPi] >> gvs[mk_nop_inst_def] >>
      Cases_on `MEM (EL i bb.bb_instructions).inst_id
        (MAP (\(v,ri,pos). ri.inst_id) uses)` >> simp[]) >>
  Cases_on `(EL i bb.bb_instructions).inst_opcode = ASSIGN`
  >- suspend "assign" >>
  suspend "ordinary"
QED

Resume ircf_block_plan_step[assign]:
  `MEM (EL i bb.bb_instructions) (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM]) >>
  `inst_wf (EL i bb.bb_instructions)` by
    (fs[fn_inst_wf_def] >> metis_tac[EL_MEM]) >>
  `~MEM (EL i bb.bb_instructions).inst_id
       (MAP (\(v,ri,pos). ri.inst_id) uses)` by
    (simp[MEM_MAP, pairTheory.EXISTS_PROD] >> rpt strip_tac >>
     fs[MEM_FILTER, pairTheory.LAMBDA_PROD, ircf_alias_use_positions_mem] >>
     rename1 `MEM ri (fn_insts fn)` >>
     `ri = EL i bb.bb_instructions` by
       (irule fn_inst_ids_distinct_inj >> metis_tac[wf_function_def]) >>
     gvs[icf_is_assign_output_use_def] >>
     gvs[inst_wf_def]) >>
  gvs[indexedListsTheory.EL_MAPi]
QED

Resume ircf_block_plan_step[ordinary]:
  `!v. ircf_redirect fn bb (cur with bb_instructions := insts) v =
     if ircf_alias fn d (ircf_redirect fn bb cur v) then s
     else ircf_redirect fn bb cur v` by
    (gen_tac >> irule ircf_redirect_insert >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `insts = MAPi update cur.bb_instructions` >>
  `EL i insts = update i (EL i cur.bb_instructions)` by
    simp[indexedListsTheory.EL_MAPi] >>
  qpat_x_assum `insts = _` kall_tac >>
  Cases_on `MEM (EL i bb.bb_instructions).inst_id
    (MAP (\(v,ri,pos). ri.inst_id) uses)`
  >- (qpat_x_assum `uses = _` kall_tac >>
      simp[indexedListsTheory.EL_MAPi, Abbr `update`,
          MAP_MAP_o, combinTheory.o_DEF] >>
      simp[instruction_component_equality] >>
      irule MAP_CONG >> simp[] >> gen_tac >> strip_tac >>
      Cases_on `x` >>
      simp[ircf_redirect_op_def, icf_collect_aliases_ircf_alias, COND_RAND]) >>
  suspend "unselected"
QED

Resume ircf_block_plan_step[unselected]:
  `ALL_DISTINCT (MAP (\inst. inst.inst_id) bb.bb_instructions)` by
    (qpat_x_assum `MEM bb _` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
     gvs[wf_function_def, fn_inst_ids_distinct_def, FLAT_APPEND,
         ALL_DISTINCT_APPEND]) >>
  `(EL i bb.bb_instructions).inst_id <> (EL k bb.bb_instructions).inst_id` by
    (drule ALL_DISTINCT_EL_IMP >>
     disch_then (qspecl_then [`i`, `k`] mp_tac) >> simp[EL_MAP]) >>
  `MEM (EL i bb.bb_instructions) (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) (EL i bb.bb_instructions).inst_operands ==>
       ~ircf_alias fn d v` by
    (rpt strip_tac >>
     qpat_x_assum `~MEM _ (MAP _ uses)` mp_tac >>
     simp[MEM_MAP, pairTheory.EXISTS_PROD] >>
     qexistsl_tac [`v`, `EL i bb.bb_instructions`] >>
     qpat_x_assum `MEM (Var v) _` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
     qexists_tac `n` >>
     simp[MEM_FILTER, ircf_alias_use_positions_mem, icf_is_assign_output_use_def] >>
     gvs[]) >>
  suspend "noalias"
QED

Resume ircf_block_plan_step[noalias]:
  `!v. MEM (Var v) (EL i bb.bb_instructions).inst_operands ==>
       ~ircf_alias fn d (ircf_redirect fn bb cur v)` by
    (gen_tac >> strip_tac >>
     Cases_on `?j d2 s2 sz2. j IN ircf_fwds bb cur /\
       ircf_copy_roots fn (EL j bb.bb_instructions) = SOME (d2,s2,sz2) /\
       ircf_alias fn d2 v`
     >- (pop_assum strip_assume_tac >>
         `ircf_fwd_ok fn bb j d2 s2 sz2` by metis_tac[] >>
         `ircf_redirect fn bb cur v = s2` by
           (irule ircf_redirect_source >> metis_tac[]) >>
         metis_tac[ircf_forward_source_not_dest_alias]) >>
     `ircf_redirect fn bb cur v = v` by
       (irule ircf_redirect_unaffected >> metis_tac[]) >>
     metis_tac[]) >>
  qpat_x_assum `uses = _` kall_tac >>
  simp[Abbr `update`, instruction_component_equality] >>
  irule MAP_CONG >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `x` >> simp[ircf_redirect_op_def] >>
  metis_tac[]
QED

Finalise ircf_block_plan_step

(* Why it holds: ircf_try_forward keeps the length and every inst_id, and
   only NOPs its copy and rewrites the instructions the original DFG lists
   as non-ASSIGN uses of the destination aliases.  A forwarded copy is
   never rewritten before it is forwarded (a destination alias used by an
   MCOPY other than its own copy writes memory, which
   ircf_no_dst_write_alias forbids; a source alias used by another copy
   fails ircf_is_ret_buf_source), so its operands and the DFG facts are
   the original ones.  icf_collect_aliases over the original DFG is
   ircf_alias (dfg_build_function_uses_sound/complete), and distinct
   roots have disjoint alias sets under SSA, so the redirect is
   well-defined. *)
Theorem ircf_transform_block_plan:
  !fn_meta ctx_fns rma fn bb.
    wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
    ircf_no_dst_write_alias fn /\ MEM bb fn.fn_blocks ==>
    ircf_block_plan fn bb
      (SND (ircf_transform_block (icf_build_ctx fn_meta ctx_fns rma fn) bb))
Proof
  rpt gen_tac >> strip_tac >>
  simp[ircf_transform_block_def] >>
  qmatch_goalsub_abbrev_tac `FOLDL fold_step _ _` >>
  `!xs acc. ircf_block_plan fn bb (SND acc) ==>
    ircf_block_plan fn bb (SND (FOLDL fold_step acc xs))` by
    (Induct >> simp[] >> rpt gen_tac >> strip_tac >>
     first_x_assum irule >> PairCases_on `acc` >> fs[] >>
     simp[Abbr `fold_step`] >>
     Cases_on `h >= LENGTH acc1.bb_instructions` >> simp[] >>
     Cases_on `(EL h acc1.bb_instructions).inst_opcode <> MCOPY` >> simp[] >>
     Cases_on `ircf_try_forward (icf_build_ctx fn_meta ctx_fns rma fn) acc1 h` >>
     simp[] >> irule ircf_block_plan_step >>
     gvs[wf_ssa_def] >>
     qexistsl_tac [`icf_build_ctx fn_meta ctx_fns rma fn`, `h`] >>
     simp[icf_build_ctx_def]) >>
  first_x_assum irule >> simp[ircf_block_plan_refl]
QED

Theorem ircf_fwd_copy_id:
  fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
  ircf_fwd_ok fn bb k d s sz /\ MEM inst (fn_insts fn) /\
  inst.inst_id = (EL k bb.bb_instructions).inst_id ==>
  inst = EL k bb.bb_instructions
Proof
  strip_tac >> irule fn_inst_ids_distinct_inj >>
  conj_tac >- simp[] >> qexists_tac `fn` >> simp[] >> rewrite_tac[fn_insts_def] >>
  irule unitShapeDefsTheory.MEM_fn_insts_blocks >>
  qexists_tac `bb` >> fs[ircf_fwd_ok_def] >> simp[EL_MEM]
QED

Theorem ircf_fwd_src_pointer_use:
  fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
  ircf_fwd_ok fn bb k d s sz /\ MEM inst (fn_insts fn) /\
  ircf_alias fn s u /\ MEM (Var u) inst.inst_operands /\
  is_pointer_preserving_op inst.inst_opcode ==>
  inst.inst_opcode = ASSIGN
Proof
  strip_tac >>
  `inst.inst_id = (EL k bb.bb_instructions).inst_id ==>
   inst = EL k bb.bb_instructions` by metis_tac[ircf_fwd_copy_id] >>
  fs[ircf_fwd_ok_def] >>
  qpat_x_assum `!i v. _ ==> i.inst_opcode = ASSIGN \/ _`
    (qspecl_then [`inst`, `u`] mp_tac) >> simp[] >>
  strip_tac >> gvs[pointerConfinedDefsTheory.is_pointer_preserving_op_def]
QED

Theorem ircf_fwd_dst_pointer_use:
  fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
  ircf_fwd_ok fn bb k d s sz /\ MEM inst (fn_insts fn) /\
  ircf_alias fn d u /\ MEM (Var u) inst.inst_operands /\
  is_pointer_preserving_op inst.inst_opcode ==>
  inst.inst_opcode = ASSIGN
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = ASSIGN` >- simp[] >>
  Cases_on `inst.inst_id = (EL k bb.bb_instructions).inst_id`
  >- (drule_all ircf_fwd_copy_id >> strip_tac >>
      gvs[ircf_fwd_ok_def, pointerConfinedDefsTheory.is_pointer_preserving_op_def]) >>
  fs[ircf_fwd_ok_def] >>
  qpat_x_assum `!i v. _ ==> i.inst_opcode <> PHI /\ _`
    (qspecl_then [`inst`, `u`] assume_tac) >> rfs[] >>
  `?pos. pos < LENGTH inst.inst_operands /\
    EL pos inst.inst_operands = Var u` by metis_tac[MEM_EL] >>
  `is_mem_addr_position inst.inst_opcode pos` by metis_tac[] >>
  Cases_on `inst.inst_opcode` >>
  gvs[pointerConfinedDefsTheory.is_pointer_preserving_op_def,
      is_mem_addr_position_def]
QED

Theorem ircf_assign_pointer_alias:
  fn_inst_wf fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\ ircf_alias fn root u /\
  MEM (Var u) inst.inst_operands /\ MEM v inst.inst_outputs ==>
  ircf_alias fn root v
Proof
  strip_tac >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, fn_insts_def,
        unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `LENGTH inst.inst_outputs = 1` by
    (qpat_x_assum `inst_wf inst` mp_tac >> simp[inst_wf_def]) >>
  `inst.inst_outputs = [v]` by
    (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  metis_tac[ircf_alias_assign]
QED

Theorem ircf_fwd_src_pointer_closure:
  fn_inst_wf fn /\ fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
  ircf_fwd_ok fn bb k d s sz ==>
  pointer_derived_vars fn {s} SUBSET {v | ircf_alias fn s v}
Proof
  strip_tac >> irule pointer_derived_vars_least >>
  simp[ircf_alias_refl] >> rpt strip_tac >>
  `inst.inst_opcode = ASSIGN` by metis_tac[ircf_fwd_src_pointer_use] >>
  metis_tac[ircf_assign_pointer_alias]
QED

Theorem ircf_fwd_dst_pointer_closure:
  fn_inst_wf fn /\ fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
  ircf_fwd_ok fn bb k d s sz ==>
  pointer_derived_vars fn {d} SUBSET {v | ircf_alias fn d v}
Proof
  strip_tac >> irule pointer_derived_vars_least >>
  simp[ircf_alias_refl] >> rpt strip_tac >>
  `inst.inst_opcode = ASSIGN` by metis_tac[ircf_fwd_dst_pointer_use] >>
  metis_tac[ircf_assign_pointer_alias]
QED

Theorem ircf_fwd_later_invoke_not_src_alias:
  fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
  ircf_fwd_ok fn bb k d s sz /\ k < i /\ i < LENGTH bb.bb_instructions /\
  inst = EL i bb.bb_instructions /\ inst.inst_opcode = INVOKE /\
  MEM (Var v) inst.inst_operands ==> ~ircf_alias fn s v
Proof
  strip_tac >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (rewrite_tac[fn_insts_def] >>
     irule unitShapeDefsTheory.MEM_fn_insts_blocks >>
     qexists_tac `bb` >> simp[EL_MEM]) >>
  `inst.inst_id <> (EL k bb.bb_instructions).inst_id` by
    (strip_tac >> drule_all ircf_fwd_copy_id >> strip_tac >>
     gvs[ircf_fwd_ok_def]) >>
  fs[ircf_fwd_ok_def] >>
  qpat_x_assum `!j v. _ ==> j.inst_opcode = ASSIGN \/ _`
    (qspecl_then [`inst`, `v`] assume_tac) >> rfs[] >>
  rename1 `EL earlier bb.bb_instructions = EL i bb.bb_instructions` >>
  `earlier < LENGTH bb.bb_instructions` by decide_tac >>
  `earlier = i` by
    (irule venomExecProofsTheory.inst_ids_el_eq >>
     qexistsl_tac [`bb`, `fn`] >> simp[]) >> decide_tac
QED

Theorem ircf_fwd_later_invoke_not_dst_alias:
  fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
  ircf_fwd_ok fn bb k d s sz /\
  ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,s,sz) /\
  ircf_no_dst_write_alias fn /\ k < i /\ i < LENGTH bb.bb_instructions /\
  inst = EL i bb.bb_instructions /\ inst.inst_opcode = INVOKE /\
  MEM (Var v) inst.inst_operands ==> ~ircf_alias fn d v
Proof
  strip_tac >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (rewrite_tac[fn_insts_def] >>
     irule unitShapeDefsTheory.MEM_fn_insts_blocks >>
     qexists_tac `bb` >> simp[EL_MEM]) >>
  `inst.inst_id <> (EL k bb.bb_instructions).inst_id` by
    (strip_tac >> drule_all ircf_fwd_copy_id >> strip_tac >>
     gvs[ircf_fwd_ok_def]) >>
  fs[ircf_fwd_ok_def] >>
  `MEM (EL k bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  `MEM inst bb.bb_instructions` by simp[EL_MEM] >>
  drule_all ircf_copy_roots_no_write_use >> simp[]
QED

Theorem ircf_block_plan_fetch_noncopy:
  ircf_block_plan fn bb bb2 /\ get_instruction bb i = SOME ii /\
  ii.inst_opcode <> MCOPY ==>
  get_instruction bb2 i = SOME
    (if ii.inst_opcode = ASSIGN then ii else
     ii with inst_operands := MAP (ircf_redirect_op fn bb bb2) ii.inst_operands)
Proof
  simp[ircf_block_plan_def, get_instruction_def] >> strip_tac >>
  `i NOTIN ircf_fwds bb bb2` by
    (strip_tac >> qpat_x_assum `!k. k IN _ ==> _` drule >>
     gvs[ircf_fwd_ok_def]) >>
  simp[]
QED

Theorem ircf_fwd_later_writer_not_dst_alias:
  fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
  ircf_fwd_ok fn bb k d sr sz /\
  ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,sr,sz) /\
  ircf_no_dst_write_alias fn /\ k < i /\ i < LENGTH bb.bb_instructions /\
  inst = EL i bb.bb_instructions /\ mem_write_ops inst = SOME ops /\
  MEM (Var v) inst.inst_operands ==> ~ircf_alias fn d v
Proof
  strip_tac >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (rewrite_tac[fn_insts_def] >>
     irule unitShapeDefsTheory.MEM_fn_insts_blocks >>
     qexists_tac `bb` >> simp[EL_MEM]) >>
  `inst.inst_id <> (EL k bb.bb_instructions).inst_id` by
    (strip_tac >> drule_all ircf_fwd_copy_id >> strip_tac >>
     `k < LENGTH bb.bb_instructions` by gvs[ircf_fwd_ok_def] >>
     `i = k` by
       (irule venomExecProofsTheory.inst_ids_el_eq >>
        qexistsl_tac [`bb`, `fn`] >> gvs[]) >> decide_tac) >>
  `MEM (EL k bb.bb_instructions) bb.bb_instructions /\
   (EL k bb.bb_instructions).inst_opcode = MCOPY` by
    (fs[ircf_fwd_ok_def] >> simp[EL_MEM]) >>
  `MEM inst bb.bb_instructions` by simp[EL_MEM] >>
  drule_all ircf_copy_roots_no_write_use >> simp[]
QED

Theorem ircf_fwd_later_writer_not_src_alias:
  fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
  ircf_fwd_ok fn bb k d sr sz /\
  k < i /\ i < LENGTH bb.bb_instructions /\
  inst = EL i bb.bb_instructions /\ mem_write_ops inst = SOME ops /\
  MEM (Var v) inst.inst_operands ==> ~ircf_alias fn sr v
Proof
  strip_tac >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (rewrite_tac[fn_insts_def] >>
     irule unitShapeDefsTheory.MEM_fn_insts_blocks >>
     qexists_tac `bb` >> simp[EL_MEM]) >>
  `inst.inst_id <> (EL k bb.bb_instructions).inst_id` by
    (strip_tac >> drule_all ircf_fwd_copy_id >> strip_tac >>
     `k < LENGTH bb.bb_instructions` by gvs[ircf_fwd_ok_def] >>
     `i = k` by
       (irule venomExecProofsTheory.inst_ids_el_eq >>
        qexistsl_tac [`bb`, `fn`] >> gvs[]) >> decide_tac) >>
  `inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> INVOKE` by
    (conj_tac >> strip_tac >> gvs[memLocDefsTheory.mem_write_ops_def]) >>
  fs[ircf_fwd_ok_def] >>
  qpat_x_assum `!j v. _ ==> j.inst_opcode = ASSIGN \/ _`
    (qspecl_then [`inst`, `v`] mp_tac) >> simp[]
QED

Theorem ircf_writer_redirect_op:
  ircf_block_plan fn bb bb2 /\ MEM bb fn.fn_blocks /\
  fn_inst_ids_distinct fn /\ ircf_no_dst_write_alias fn /\
  i < LENGTH bb.bb_instructions /\ i NOTIN ircf_fwds bb bb2 /\
  mem_write_ops (EL i bb.bb_instructions) <> NONE /\
  MEM op (EL i bb.bb_instructions).inst_operands ==>
  ircf_redirect_op fn bb bb2 op = op
Proof
  strip_tac >> Cases_on `op` >> simp[ircf_redirect_op_def] >>
  rename1 `ircf_redirect fn bb bb2 v = v` >>
  irule ircf_redirect_unaffected >> rpt gen_tac >> strip_tac >> strip_tac >>
  `ircf_fwd_ok fn bb k d s sz` by
    (drule_all ircf_block_plan_fwd_ok >> simp[]) >>
  `k < LENGTH bb.bb_instructions /\
   (EL k bb.bb_instructions).inst_opcode = MCOPY` by fs[ircf_fwd_ok_def] >>
  `(EL i bb.bb_instructions).inst_id <> (EL k bb.bb_instructions).inst_id` by
    (strip_tac >>
     `MEM (EL i bb.bb_instructions) (fn_insts fn) /\
      MEM (EL k bb.bb_instructions) (fn_insts fn)` by
       (simp[venomInstTheory.fn_insts_def] >>
        metis_tac[unitShapeDefsTheory.MEM_fn_insts_blocks, EL_MEM]) >>
     `EL i bb.bb_instructions = EL k bb.bb_instructions` by
       metis_tac[venomWfPropsTheory.fn_inst_ids_distinct_inj] >>
     `i = k` by
       (irule venomExecProofsTheory.inst_ids_el_eq >>
        qexistsl_tac [`bb`, `fn`] >> simp[]) >> metis_tac[]) >>
  `MEM (EL i bb.bb_instructions) bb.bb_instructions /\
   MEM (EL k bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  drule_all ircf_copy_roots_no_write_use >> simp[]
QED

Theorem ircf_block_plan_writer:
  ircf_block_plan fn bb bb2 /\ MEM bb fn.fn_blocks /\
  fn_inst_ids_distinct fn /\ ircf_no_dst_write_alias fn /\
  i < LENGTH bb.bb_instructions /\ i NOTIN ircf_fwds bb bb2 /\
  mem_write_ops (EL i bb.bb_instructions) <> NONE ==>
  EL i bb2.bb_instructions = EL i bb.bb_instructions
Proof
  strip_tac >>
  `MAP (ircf_redirect_op fn bb bb2) (EL i bb.bb_instructions).inst_operands =
   (EL i bb.bb_instructions).inst_operands` by
    (irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
     irule ircf_writer_redirect_op >> simp[] >>
     qexists_tac `i` >> simp[EL_MEM]) >>
  fs[ircf_block_plan_def] >> simp[]
QED

Theorem ircf_invoke_redirect_op:
  ircf_block_plan fn bb bb2 /\ MEM bb fn.fn_blocks /\
  fn_inst_ids_distinct fn /\ ircf_no_dst_write_alias fn /\
  i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = INVOKE /\
  MEM op (EL i bb.bb_instructions).inst_operands ==>
  ircf_redirect_op fn bb bb2 op = op
Proof
  strip_tac >> Cases_on `op` >> simp[ircf_redirect_op_def] >>
  rename1 `ircf_redirect fn bb bb2 v = v` >>
  irule ircf_redirect_unaffected >> rpt gen_tac >> strip_tac >> strip_tac >>
  `ircf_fwd_ok fn bb k d s sz` by
    (drule_all ircf_block_plan_fwd_ok >> simp[]) >>
  `k < LENGTH bb.bb_instructions /\
   (EL k bb.bb_instructions).inst_opcode = MCOPY` by fs[ircf_fwd_ok_def] >>
  `MEM (EL i bb.bb_instructions) (fn_insts fn) /\
   MEM (EL k bb.bb_instructions) (fn_insts fn)` by
    (simp[venomInstTheory.fn_insts_def] >>
     metis_tac[unitShapeDefsTheory.MEM_fn_insts_blocks, EL_MEM]) >>
  `(EL i bb.bb_instructions).inst_id <> (EL k bb.bb_instructions).inst_id` by
    (strip_tac >>
     `EL i bb.bb_instructions = EL k bb.bb_instructions` by
       metis_tac[venomWfPropsTheory.fn_inst_ids_distinct_inj] >> gvs[]) >>
  `MEM (EL i bb.bb_instructions) bb.bb_instructions /\
   MEM (EL k bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  drule_all ircf_copy_roots_no_write_use >> simp[]
QED

Theorem ircf_block_plan_invoke:
  ircf_block_plan fn bb bb2 /\ MEM bb fn.fn_blocks /\
  fn_inst_ids_distinct fn /\ ircf_no_dst_write_alias fn /\
  i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = INVOKE ==>
  EL i bb2.bb_instructions = EL i bb.bb_instructions
Proof
  strip_tac >>
  `i NOTIN ircf_fwds bb bb2` by
    (strip_tac >> gvs[ircf_fwds_def]) >>
  `MAP (ircf_redirect_op fn bb bb2) (EL i bb.bb_instructions).inst_operands =
   (EL i bb.bb_instructions).inst_operands` by
    (irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
     irule ircf_invoke_redirect_op >> simp[] >>
     qexists_tac `i` >> simp[EL_MEM]) >>
  fs[ircf_block_plan_def] >> simp[]
QED

Theorem ircf_unchanged_operand_not_dst_alias:
  wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
  ircf_no_dst_write_alias fn /\ MEM bb fn.fn_blocks /\
  ircf_block_plan fn bb bb2 /\ i < LENGTH bb.bb_instructions /\
  i NOTIN ircf_fwds bb bb2 /\
  (EL i bb.bb_instructions).inst_opcode <> ASSIGN /\
  EL i bb2.bb_instructions = EL i bb.bb_instructions /\
  MEM (Var v) (EL i bb.bb_instructions).inst_operands /\
  k IN ircf_fwds bb bb2 /\
  ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,sr,sz) ==>
  ~ircf_alias fn d v
Proof
  strip_tac >> strip_tac >>
  `ircf_redirect fn bb bb2 v = sr` by
    (irule ircf_redirect_source >> simp[] >>
     conj_tac >- metis_tac[ircf_block_plan_fwd_ok] >> metis_tac[]) >>
  `MAP (ircf_redirect_op fn bb bb2) (EL i bb.bb_instructions).inst_operands =
     (EL i bb.bb_instructions).inst_operands` by
    (fs[ircf_block_plan_def] >>
     first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
     simp[instruction_component_equality]) >>
  `ircf_redirect_op fn bb bb2 (Var v) = Var v` by
    (`MAP (ircf_redirect_op fn bb bb2) (EL i bb.bb_instructions).inst_operands =
      MAP I (EL i bb.bb_instructions).inst_operands` by simp[] >>
     fs[MAP_EQ_f]) >>
  `ircf_alias fn d sr` by fs[ircf_redirect_op_def] >>
  `ircf_fwd_ok fn bb k d sr sz` by
    (drule_all ircf_block_plan_fwd_ok >> simp[]) >>
  fs[ircf_fwd_ok_def] >> metis_tac[ircf_alloca_alias_root]
QED

Theorem ircf_fwd_dst_use_block:
  fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\ MEM cur fn.fn_blocks /\
  ircf_fwd_ok fn bb k d sr sz /\ i < LENGTH cur.bb_instructions /\
  inst = EL i cur.bb_instructions /\ inst.inst_opcode <> ASSIGN /\
  ircf_alias fn d v /\ MEM (Var v) inst.inst_operands ==>
  bb = cur
Proof
  strip_tac >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM]) >>
  `MEM inst bb.bb_instructions` by
    (Cases_on `inst.inst_id = (EL k bb.bb_instructions).inst_id`
     >- (drule_all ircf_fwd_copy_id >> strip_tac >> gvs[] >>
         metis_tac[ircf_fwd_ok_def, EL_MEM]) >>
     fs[ircf_fwd_ok_def] >> metis_tac[EL_MEM]) >>
  irule (all_distinct_flat_map_inj |> INST_TYPE [alpha |-> ``:num``]) >>
  qexistsl_tac [`\b. MAP (\i. i.inst_id) b.bb_instructions`,
                `fn.fn_blocks`, `inst.inst_id`] >>
  fs[fn_inst_ids_distinct_def, MEM_MAP] >> metis_tac[EL_MEM]
QED

Theorem ircf_redirect_changed_forward:
  wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
  ircf_no_dst_write_alias fn /\ MEM bb fn.fn_blocks /\
  ircf_block_plan fn bb bb2 /\ ircf_redirect fn bb bb2 v <> v ==>
  ?k d sr sz. k IN ircf_fwds bb bb2 /\
    ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,sr,sz) /\
    ircf_fwd_ok fn bb k d sr sz /\ ircf_alias fn d v /\
    ircf_redirect fn bb bb2 v = sr
Proof
  strip_tac >>
  `?k d sr sz. k IN ircf_fwds bb bb2 /\
    ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,sr,sz) /\
    ircf_alias fn d v` by metis_tac[ircf_redirect_unaffected] >>
  `ircf_fwd_ok fn bb k d sr sz` by
    (drule_all ircf_block_plan_fwd_ok >> simp[]) >>
  qexistsl_tac [`k`, `d`, `sr`, `sz`] >> simp[] >>
  irule ircf_redirect_source >> simp[] >>
  metis_tac[ircf_block_plan_fwd_ok]
QED

Theorem ircf_redirect_changed_position:
  wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
  fn_inst_ids_distinct fn /\ ircf_no_dst_write_alias fn /\
  MEM bb fn.fn_blocks /\ ircf_block_plan fn bb bb2 /\
  i < LENGTH bb.bb_instructions /\ i NOTIN ircf_fwds bb bb2 /\
  inst = EL i bb.bb_instructions /\ inst.inst_opcode <> ASSIGN /\
  pos < LENGTH inst.inst_operands /\ EL pos inst.inst_operands = Var v /\
  ircf_redirect fn bb bb2 v <> v ==>
  is_mem_addr_position inst.inst_opcode pos
Proof
  strip_tac >> drule_all ircf_redirect_changed_forward >> strip_tac >>
  `k < LENGTH bb.bb_instructions` by fs[ircf_fwd_ok_def] >>
  `MEM inst (fn_insts fn) /\ MEM (EL k bb.bb_instructions) (fn_insts fn)` by
    (gvs[venomInstTheory.fn_insts_def] >>
     metis_tac[unitShapeDefsTheory.MEM_fn_insts_blocks, EL_MEM]) >>
  `inst.inst_id <> (EL k bb.bb_instructions).inst_id` by
    (strip_tac >>
     `inst = EL k bb.bb_instructions` by
       metis_tac[venomWfPropsTheory.fn_inst_ids_distinct_inj] >>
     `i = k` by metis_tac[venomExecProofsTheory.inst_ids_el_eq] >> gvs[]) >>
  fs[ircf_fwd_ok_def] >> metis_tac[EL_MEM]
QED

Theorem ircf_block_plan_assign:
  ircf_block_plan fn bb bb2 /\ i < LENGTH bb.bb_instructions /\
  i NOTIN ircf_fwds bb bb2 /\
  (EL i bb.bb_instructions).inst_opcode = ASSIGN ==>
  EL i bb2.bb_instructions = EL i bb.bb_instructions
Proof
  simp[ircf_block_plan_def]
QED

Theorem ircf_block_plan_changed_operand:
  ircf_block_plan fn bb bb2 /\ i < LENGTH bb.bb_instructions /\
  i NOTIN ircf_fwds bb bb2 /\
  EL i bb2.bb_instructions <> EL i bb.bb_instructions ==>
  (EL i bb.bb_instructions).inst_opcode <> ASSIGN /\
  ?pos v. pos < LENGTH (EL i bb.bb_instructions).inst_operands /\
    EL pos (EL i bb.bb_instructions).inst_operands = Var v /\
    ircf_redirect fn bb bb2 v <> v
Proof
  strip_tac >>
  `(EL i bb.bb_instructions).inst_opcode <> ASSIGN` by
    metis_tac[ircf_block_plan_assign] >> simp[] >>
  `MAP (ircf_redirect_op fn bb bb2) (EL i bb.bb_instructions).inst_operands <>
   (EL i bb.bb_instructions).inst_operands` by
    (strip_tac >> gvs[ircf_block_plan_def]) >>
  `?pos. pos < LENGTH (EL i bb.bb_instructions).inst_operands /\
    ircf_redirect_op fn bb bb2 (EL pos (EL i bb.bb_instructions).inst_operands) <>
      EL pos (EL i bb.bb_instructions).inst_operands` by
    (spose_not_then assume_tac >>
     qpat_x_assum `MAP _ _ <> _` mp_tac >> simp[] >>
     irule LIST_EQ >> simp[EL_MAP]) >>
  Cases_on `EL pos (EL i bb.bb_instructions).inst_operands` >>
  fs[ircf_redirect_op_def] >> metis_tac[]
QED

Theorem ircf_block_plan_changed_opcode:
  wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
  fn_inst_ids_distinct fn /\ ircf_no_dst_write_alias fn /\
  MEM bb fn.fn_blocks /\ ircf_block_plan fn bb bb2 /\
  i < LENGTH bb.bb_instructions /\ i NOTIN ircf_fwds bb bb2 /\
  EL i bb2.bb_instructions <> EL i bb.bb_instructions ==>
  MEM (EL i bb.bb_instructions).inst_opcode
    [MLOAD; SHA3; LOG; CREATE; CREATE2; RETURN; REVERT]
Proof
  strip_tac >> drule_all ircf_block_plan_changed_operand >> strip_tac >>
  `is_mem_addr_position (EL i bb.bb_instructions).inst_opcode pos` by
    (irule ircf_redirect_changed_position >> metis_tac[]) >>
  `mem_write_ops (EL i bb.bb_instructions) = NONE` by
    metis_tac[ircf_block_plan_writer] >>
  `inst_wf (EL i bb.bb_instructions)` by
    metis_tac[venomWfTheory.fn_inst_wf_def, EL_MEM] >>
  gvs[invokeCopyFwdCommonDefsTheory.is_mem_addr_position_def,
      venomWfTheory.inst_wf_def, memLocDefsTheory.mem_write_ops_def,
      LENGTH_EQ_NUM_compute]
QED
