Theory readonlyInvokeCopyFwdReadonlyPositions
Ancestors
  readonlyInvokeCopyFwdPlan venomExecSemantics invokeCopyFwdCommonDefs readonlyInvokeCopyFwdDefs indexedLists passSharedDefs rich_list list

(* Position zero is the call label, not an argument. *)
Definition ricf_readonly_inst_edit_def:
  ricf_readonly_inst_edit rma old cur <=>
    ricf_inst_edit old cur /\
    (old.inst_opcode = INVOKE ==>
      LENGTH cur.inst_operands = LENGTH old.inst_operands /\
      icf_get_callee_name cur = icf_get_callee_name old /\
      (!p. p < LENGTH old.inst_operands ==>
        EL p cur.inst_operands = EL p old.inst_operands \/
        icf_is_readonly_op rma old p))
End

Definition ricf_readonly_block_edit_def:
  ricf_readonly_block_edit rma old cur <=>
    old.bb_label = cur.bb_label /\
    LIST_REL (ricf_readonly_inst_edit rma) old.bb_instructions cur.bb_instructions
End

Theorem ricf_readonly_inst_edit_refl[simp]:
  ricf_readonly_inst_edit rma inst inst
Proof
  simp[ricf_readonly_inst_edit_def]
QED

Theorem ricf_readonly_inst_edit_trans:
  ricf_readonly_inst_edit rma a b /\ ricf_readonly_inst_edit rma b c ==>
  ricf_readonly_inst_edit rma a c
Proof
  simp[ricf_readonly_inst_edit_def] >> strip_tac >>
  conj_tac >- metis_tac[ricf_inst_edit_trans] >>
  strip_tac >>
  `b.inst_opcode = INVOKE` by gvs[ricf_inst_edit_def] >>
  gvs[icf_is_readonly_op_def] >> metis_tac[]
QED

Theorem ricf_readonly_block_edit_refl[simp]:
  ricf_readonly_block_edit rma bb bb
Proof
  simp[ricf_readonly_block_edit_def, LIST_REL_refl]
QED

Theorem ricf_readonly_block_edit_forget:
  ricf_readonly_block_edit rma old cur ==> ricf_block_edit old cur
Proof
  simp[ricf_readonly_block_edit_def, ricf_block_edit_def, LIST_REL_EL_EQN] >>
  metis_tac[ricf_readonly_inst_edit_def]
QED

Theorem ricf_readonly_block_edit_trans:
  ricf_readonly_block_edit rma a b /\ ricf_readonly_block_edit rma b c ==>
  ricf_readonly_block_edit rma a c
Proof
  simp[ricf_readonly_block_edit_def, LIST_REL_EL_EQN] >>
  metis_tac[ricf_readonly_inst_edit_trans]
QED

Theorem ricf_event_readonly_label:
  ricf_event_ok e bb /\ i < LENGTH bb.bb_instructions /\ i <> e.rfe_index ==>
  icf_get_callee_name (EL i (ricf_event_apply e bb).bb_instructions) =
  icf_get_callee_name (EL i bb.bb_instructions)
Proof
  rpt strip_tac >>
  `~MEM ((EL i bb.bb_instructions).inst_id,0)
    (MAP (\(ri,p). (ri.inst_id,p)) e.rfe_sites)` by
    (simp[MEM_MAP, pairTheory.EXISTS_PROD] >> rpt strip_tac >>
     drule_all ricf_event_sites_readonly >>
     simp[icf_is_readonly_op_def]) >>
  drule_all ricf_event_operand_length >> strip_tac >>
  Cases_on `(EL i bb.bb_instructions).inst_operands` >>
  Cases_on `(EL i (ricf_event_apply e bb).bb_instructions).inst_operands` >>
  gvs[icf_get_callee_name_def] >>
  mp_tac (Q.INST [`j` |-> `0`] ricf_event_operand) >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem ricf_event_readonly_inst_edit:
  ricf_event_ok e bb /\ i < LENGTH bb.bb_instructions /\
  (!ri p. MEM (ri,p) e.rfe_sites /\
     ri.inst_id = (EL i bb.bb_instructions).inst_id ==>
     (EL i bb.bb_instructions).inst_opcode = INVOKE /\
     icf_get_callee_name ri = icf_get_callee_name (EL i bb.bb_instructions)) ==>
  ricf_readonly_inst_edit e.rfe_ctx.icf_rma (EL i bb.bb_instructions)
    (EL i (ricf_event_apply e bb).bb_instructions)
Proof
  rpt strip_tac >>
  `ricf_inst_edit (EL i bb.bb_instructions)
    (EL i (ricf_event_apply e bb).bb_instructions)` by
    (simp[ricf_event_apply_def, ricf_apply_forward_def, EL_MAPi] >>
     Cases_on `i = e.rfe_index`
     >- (drule ricf_event_copy_shape >> simp[ricf_event_copy_def] >>
         strip_tac >> simp[ricf_inst_edit_def, mk_nop_inst_def]) >>
     simp[] >> IF_CASES_TAC >> simp[ricf_inst_edit_def] >>
     `?ri p. MEM (ri,p) e.rfe_sites /\
        ri.inst_id = (EL i bb.bb_instructions).inst_id` by
       (gvs[NULL_EQ, FILTER_EQ_NIL, EVERY_MEM, pairTheory.FORALL_PROD] >>
        metis_tac[]) >>
     first_x_assum drule >> simp[]) >>
  simp[ricf_readonly_inst_edit_def] >> strip_tac >>
  `i <> e.rfe_index` by
    (Cases_on `i = e.rfe_index` >> gvs[] >>
     drule ricf_event_copy_shape >> simp[ricf_event_copy_def]) >>
  conj_tac >- metis_tac[ricf_event_operand_length] >>
  conj_tac >- metis_tac[ricf_event_readonly_label] >>
  rpt strip_tac >> drule_all ricf_event_operand >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  gvs[MEM_MAP, pairTheory.EXISTS_PROD] >>
  drule_all ricf_event_sites_readonly >> strip_tac >>
  first_x_assum drule >> gvs[icf_is_readonly_op_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem ricf_readonly_current_site:
  ricf_event_ok e cur /\ e.rfe_ctx.icf_dfg = dfg_build_function fn /\
  ricf_readonly_block_edit rma old cur /\ MEM old fn.fn_blocks /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  MEM (ri,p) e.rfe_sites /\ i < LENGTH cur.bb_instructions /\
  ri.inst_id = (EL i cur.bb_instructions).inst_id ==>
  (EL i cur.bb_instructions).inst_opcode = INVOKE /\
  icf_get_callee_name ri = icf_get_callee_name (EL i cur.bb_instructions)
Proof
  strip_tac >> drule_all ricf_event_sites_function >> strip_tac >>
  fs[ricf_readonly_block_edit_def, LIST_REL_EL_EQN] >>
  `ricf_readonly_inst_edit rma (EL i old.bb_instructions)
     (EL i cur.bb_instructions)` by metis_tac[] >>
  `MEM (EL i old.bb_instructions) (fn_insts fn)` by
    (simp[venomInstTheory.fn_insts_def] >>
     irule venomInstTheory.fmp_fn_insts_blocks_intro >>
     qexists_tac `old` >> simp[EL_MEM]) >>
  `ri = EL i old.bb_instructions` by
    (fs[ricf_readonly_inst_edit_def, ricf_inst_edit_def] >>
     gvs[MEM_EL] >> gvs[EL_ALL_DISTINCT_EL_EQ, EL_MAP] >> metis_tac[]) >>
  qpat_x_assum `!n. _ ==> ricf_readonly_inst_edit _ _ _` kall_tac >>
  gvs[ricf_readonly_inst_edit_def, ricf_inst_edit_def]
QED

Theorem ricf_event_readonly_block_edit:
  ricf_event_ok e cur /\ e.rfe_ctx.icf_dfg = dfg_build_function fn /\
  ricf_readonly_block_edit e.rfe_ctx.icf_rma old cur /\ MEM old fn.fn_blocks /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) ==>
  ricf_readonly_block_edit e.rfe_ctx.icf_rma cur (ricf_event_apply e cur)
Proof
  strip_tac >> simp[ricf_readonly_block_edit_def, LIST_REL_EL_EQN] >>
  conj_tac >- simp[ricf_event_apply_def, ricf_apply_forward_def] >>
  conj_tac >- metis_tac[ricf_event_prefix_and_copy] >>
  rpt strip_tac >>
  irule ricf_event_readonly_inst_edit >> simp[] >>
  metis_tac[ricf_readonly_current_site]
QED

Theorem ricf_block_trace_readonly_edit:
  !bb es last. ricf_block_trace bb es last ==>
  !fn old ctx.
    EVERY (\e. e.rfe_ctx = ctx) es /\
    ctx.icf_dfg = dfg_build_function fn /\
    ricf_readonly_block_edit ctx.icf_rma old bb /\ MEM old fn.fn_blocks /\
    ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) ==>
    ricf_readonly_block_edit ctx.icf_rma old last
Proof
  ho_match_mp_tac ricf_block_trace_ind >> rpt strip_tac >> gvs[] >>
  first_x_assum irule >> simp[] >>
  conj_tac >- metis_tac[] >>
  irule ricf_readonly_block_edit_trans >> goal_assum drule >>
  irule ricf_event_readonly_block_edit >> simp[] >> metis_tac[]
QED

Definition ricf_readonly_function_edit_def:
  ricf_readonly_function_edit rma old cur <=>
    cur = old with fn_blocks := cur.fn_blocks /\
    LIST_REL (ricf_readonly_block_edit rma) old.fn_blocks cur.fn_blocks
End

Theorem ricf_readonly_function_edit_refl[simp]:
  ricf_readonly_function_edit rma fn fn
Proof
  simp[ricf_readonly_function_edit_def, LIST_REL_refl]
QED

Theorem ricf_readonly_function_edit_forget:
  ricf_readonly_function_edit rma old cur ==> ricf_function_edit old cur
Proof
  simp[ricf_readonly_function_edit_def, ricf_function_edit_def,
       LIST_REL_EL_EQN] >> metis_tac[ricf_readonly_block_edit_forget]
QED

Theorem ricf_readonly_function_edit_trans:
  ricf_readonly_function_edit rma a b /\ ricf_readonly_function_edit rma b c ==>
  ricf_readonly_function_edit rma a c
Proof
  simp[ricf_readonly_function_edit_def] >> strip_tac >> conj_tac
  >- (qpat_x_assum `c = _` (fn th => once_rewrite_tac[th]) >>
      qpat_x_assum `b = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  fs[LIST_REL_EL_EQN] >> metis_tac[ricf_readonly_block_edit_trans]
QED

Theorem ricf_round_readonly_edit:
  ricf_round_certificate ctx fn cur /\
  ctx.icf_dfg = dfg_build_function fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) ==>
  ricf_readonly_function_edit ctx.icf_rma fn cur
Proof
  simp[ricf_round_certificate_def, ricf_readonly_function_edit_def] >>
  strip_tac >> gvs[] >> fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  first_x_assum (qspec_then `n` mp_tac) >> impl_tac >- simp[] >> strip_tac >>
  irule ricf_block_trace_readonly_edit >> conj_tac
  >- (qexists_tac `fn` >> simp[EL_MEM]) >>
  qexistsl_tac [`EL n fn.fn_blocks`,`es`] >> simp[]
QED

Theorem ricf_function_trace_readonly_edit:
  !base fn cur. ricf_function_trace base fn cur ==>
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) ==>
  ricf_readonly_function_edit base.icf_rma fn cur
Proof
  ho_match_mp_tac ricf_function_trace_ind >> simp[] >> rpt strip_tac >>
  rename1 `ricf_round_certificate (base0 with icf_dfg := _) fn mid` >>
  `ricf_readonly_function_edit base0.icf_rma fn mid` by
    (mp_tac (Q.INST [`ctx` |-> `base0 with icf_dfg := dfg_build_function fn`,
                    `cur` |-> `mid`] ricf_round_readonly_edit) >> simp[]) >>
  irule ricf_readonly_function_edit_trans >> goal_assum drule >>
  first_x_assum irule >>
  metis_tac[ricf_readonly_function_edit_forget, ricf_function_edit_ids]
QED

(* Decode-level consumer interface.  Bounds refer to arguments, excluding
   the preserved label at operand zero. *)
Theorem ricf_readonly_inst_edit_decode:
  ricf_readonly_inst_edit rma old cur /\ old.inst_opcode = INVOKE /\
  decode_invoke old = SOME (nm,args) ==>
  ?args'. decode_invoke cur = SOME (nm,args') /\
    cur.inst_id = old.inst_id /\ cur.inst_opcode = INVOKE /\
    LENGTH args' = LENGTH args /\
    (!k. k < LENGTH args ==> EL k args' = EL k args \/ rma_is_readonly rma nm k)
Proof
  simp[ricf_readonly_inst_edit_def, ricf_inst_edit_def,
       decode_invoke_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  Cases_on `cur.inst_operands` >> gvs[icf_get_callee_name_def] >>
  Cases_on `h` >> gvs[] >>
  rpt strip_tac >> first_x_assum (qspec_then `SUC k` mp_tac) >>
  simp[icf_is_readonly_op_def, icf_get_callee_name_def]
QED

Theorem ricf_readonly_block_edit_decode:
  ricf_readonly_block_edit rma old cur /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = INVOKE /\
  decode_invoke (EL i old.bb_instructions) = SOME (nm,args) ==>
  i < LENGTH cur.bb_instructions /\
  ?args'. decode_invoke (EL i cur.bb_instructions) = SOME (nm,args') /\
    (EL i cur.bb_instructions).inst_id = (EL i old.bb_instructions).inst_id /\
    (EL i cur.bb_instructions).inst_opcode = INVOKE /\
    LENGTH args' = LENGTH args /\
    (!k. k < LENGTH args ==> EL k args' = EL k args \/ rma_is_readonly rma nm k)
Proof
  simp[ricf_readonly_block_edit_def, LIST_REL_EL_EQN] >> strip_tac >>
  irule ricf_readonly_inst_edit_decode >>
  simp[] >> metis_tac[]
QED

(* Any finite prefix is itself a block trace.  The DFG belongs to the
   round-start function, not to the intermediate validation block. *)
Theorem ricf_block_trace_readonly_positions:
  ricf_block_trace bb es last /\ EVERY (\e. e.rfe_ctx = ctx) es /\
  ctx.icf_dfg = dfg_build_function fn /\ MEM bb fn.fn_blocks /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = INVOKE /\
  decode_invoke (EL i bb.bb_instructions) = SOME (nm,args) ==>
  i < LENGTH last.bb_instructions /\
  ?args'. decode_invoke (EL i last.bb_instructions) = SOME (nm,args') /\
    (EL i last.bb_instructions).inst_id = (EL i bb.bb_instructions).inst_id /\
    (EL i last.bb_instructions).inst_opcode = INVOKE /\
    LENGTH args' = LENGTH args /\
    (!k. k < LENGTH args ==> EL k args' = EL k args \/
      rma_is_readonly ctx.icf_rma nm k)
Proof
  strip_tac >> irule ricf_readonly_block_edit_decode >> simp[] >>
  irule ricf_block_trace_readonly_edit >> conj_tac
  >- (qexists_tac `fn` >> simp[]) >>
  qexistsl_tac [`bb`,`es`] >> simp[]
QED

Theorem ricf_function_trace_readonly_positions:
  !base fn last b i nm args.
  ricf_function_trace base fn last /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  b < LENGTH fn.fn_blocks /\
  i < LENGTH (EL b fn.fn_blocks).bb_instructions /\
  (EL i (EL b fn.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
  decode_invoke (EL i (EL b fn.fn_blocks).bb_instructions) = SOME (nm,args) ==>
  b < LENGTH last.fn_blocks /\ i < LENGTH (EL b last.fn_blocks).bb_instructions /\
  ?args'. decode_invoke (EL i (EL b last.fn_blocks).bb_instructions) = SOME (nm,args') /\
    (EL i (EL b last.fn_blocks).bb_instructions).inst_id =
      (EL i (EL b fn.fn_blocks).bb_instructions).inst_id /\
    (EL i (EL b last.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
    LENGTH args' = LENGTH args /\
    (!k. k < LENGTH args ==> EL k args' = EL k args \/
      rma_is_readonly base.icf_rma nm k)
Proof
  rpt gen_tac >> strip_tac >> drule_all ricf_function_trace_readonly_edit >>
  simp[ricf_readonly_function_edit_def, LIST_REL_EL_EQN] >> strip_tac >>
  irule ricf_readonly_block_edit_decode >> simp[] >> metis_tac[]
QED
