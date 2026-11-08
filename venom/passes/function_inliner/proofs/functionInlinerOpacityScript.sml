(* Static token ancestry survives replacement of RETPC_PARAM by ASSIGN 0.
   This interface intentionally does not rediscover seeds in transformed code. *)
Theory functionInlinerOpacity
Ancestors
  functionInlinerNamespace functionInlinerOrigin functionInlinerDefs unitShapeDefs
  venomExecProofs cfgTransform pred_set list rich_list string

Definition inline_opacity_ok_def:
  inline_opacity_ok fn opaque <=>
    (!i x. MEM i (fn_insts fn) /\ i.inst_opcode = RETPC_PARAM /\
      MEM x i.inst_outputs ==> x IN opaque) /\
    (!i x y. MEM i (fn_insts fn) /\ i.inst_opcode = ASSIGN /\
      i.inst_operands = [Var y] /\ MEM x i.inst_outputs /\ y IN opaque ==>
      x IN opaque) /\
    (!i x y. MEM i (fn_insts fn) /\ i.inst_opcode = PHI /\
      MEM (Var y) i.inst_operands /\ MEM x i.inst_outputs /\ y IN opaque ==>
      x IN opaque) /\
    (!i x. MEM i (fn_insts fn) /\ MEM (Var x) i.inst_operands /\
      x IN opaque ==> retpc_use_ok i x) /\
    (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs /\ x IN opaque ==>
      MEM i.inst_opcode [RETPC_PARAM; ASSIGN; PHI])
End

Theorem inline_opacity_root:
  opaque_use_ok fn /\ retpc_shape_ok fn ==>
  inline_opacity_ok fn {x | retpc_var fn x}
Proof
  simp[inline_opacity_ok_def, opaque_use_ok_def, retpc_shape_ok_def,
    retpc_var_def] >> rpt strip_tac >>
  metis_tac[copy_phi_var_rules]
QED

Theorem inliner_input_opacity:
  inliner_input_ok ctx /\ MEM fn ctx.ctx_functions ==>
  inline_opacity_ok fn {x | retpc_var fn x}
Proof
  rpt strip_tac >> irule inline_opacity_root >>
  gvs[functionInlinerContractTheory.inliner_input_ok_def, EVERY_MEM] >> metis_tac[]
QED

Theorem inline_opacity_use:
  inline_opacity_ok fn opaque /\ MEM i (fn_insts fn) /\
  MEM (Var x) i.inst_operands /\ x IN opaque ==> retpc_use_ok i x
Proof
  simp[inline_opacity_ok_def] >> metis_tac[]
QED

Theorem inline_opacity_writer:
  inline_opacity_ok fn opaque /\ MEM i (fn_insts fn) /\
  MEM x i.inst_outputs /\ x IN opaque ==>
  MEM i.inst_opcode [RETPC_PARAM; ASSIGN; PHI]
Proof
  simp[inline_opacity_ok_def] >> metis_tac[]
QED

Theorem inline_opacity_invoke_operand:
  inline_opacity_ok fn opaque /\ MEM i (fn_insts fn) /\
  i.inst_opcode = INVOKE /\ MEM (Var x) i.inst_operands ==> x NOTIN opaque
Proof
  rpt strip_tac >> drule_all inline_opacity_use >>
  simp[retpc_use_ok_def]
QED

Theorem inline_opacity_invoke_output:
  inline_opacity_ok fn opaque /\ MEM i (fn_insts fn) /\
  i.inst_opcode = INVOKE /\ MEM x i.inst_outputs ==> x NOTIN opaque
Proof
  rpt strip_tac >> drule_all inline_opacity_writer >> simp[]
QED

Theorem inline_opacity_copy:
  inline_opacity_ok fn opaque /\ MEM i (fn_insts fn) /\
  i.inst_opcode = ASSIGN /\ i.inst_operands = [Var y] /\
  MEM x i.inst_outputs /\ y IN opaque ==> x IN opaque
Proof
  simp[inline_opacity_ok_def] >> metis_tac[]
QED

Theorem inline_opacity_phi:
  inline_opacity_ok fn opaque /\ MEM i (fn_insts fn) /\
  i.inst_opcode = PHI /\ MEM (Var y) i.inst_operands /\
  MEM x i.inst_outputs /\ y IN opaque ==> x IN opaque
Proof
  simp[inline_opacity_ok_def] >> metis_tac[]
QED

Theorem inline_opacity_ordinary_operand:
  inline_opacity_ok fn opaque /\ MEM i (fn_insts fn) /\
  ~MEM i.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET] /\
  MEM (Var x) i.inst_operands ==> x NOTIN opaque
Proof
  rpt strip_tac >> drule_all inline_opacity_use >>
  gvs[retpc_use_ok_def]
QED

Theorem inline_opacity_return_front:
  inline_opacity_ok fn opaque /\ MEM i (fn_insts fn) /\
  MEM i.inst_opcode [RET; RETFMP] /\
  MEM (Var x) (TAKE (LENGTH i.inst_operands - 1) i.inst_operands) ==>
  x NOTIN opaque
Proof
  rpt strip_tac >>
  `MEM (Var x) i.inst_operands` by metis_tac[MEM_TAKE] >>
  drule_all inline_opacity_use >>
  simp[retpc_use_ok_def] >> rpt strip_tac >> gvs[TAKE_APPEND] >>
  rpt strip_tac >> gvs[TAKE_APPEND]
QED

Theorem inline_opacity_seed:
  inline_opacity_ok fn opaque /\ MEM i (fn_insts fn) /\
  i.inst_opcode = RETPC_PARAM /\ MEM x i.inst_outputs ==> x IN opaque
Proof
  simp[inline_opacity_ok_def] >> metis_tac[]
QED

(* Instruction-local form for structural transport, equivalent to the public
   function interface above. *)
Definition inline_inst_opacity_ok_def:
  inline_inst_opacity_ok opaque i <=>
    (!x. i.inst_opcode = RETPC_PARAM /\ MEM x i.inst_outputs ==> x IN opaque) /\
    (!x y. i.inst_opcode = ASSIGN /\ i.inst_operands = [Var y] /\
      MEM x i.inst_outputs /\ y IN opaque ==> x IN opaque) /\
    (!x y. i.inst_opcode = PHI /\ MEM (Var y) i.inst_operands /\
      MEM x i.inst_outputs /\ y IN opaque ==> x IN opaque) /\
    (!x. MEM (Var x) i.inst_operands /\ x IN opaque ==> retpc_use_ok i x) /\
    (!x. MEM x i.inst_outputs /\ x IN opaque ==>
      MEM i.inst_opcode [RETPC_PARAM; ASSIGN; PHI])
End

Theorem inline_opacity_every:
  inline_opacity_ok fn opaque <=>
  EVERY (inline_inst_opacity_ok opaque) (fn_insts fn)
Proof
  simp[inline_opacity_ok_def, inline_inst_opacity_ok_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem inline_inst_opacity_id:
  inline_inst_opacity_ok opaque (i with inst_id := n) <=>
  inline_inst_opacity_ok opaque i
Proof
  simp[inline_inst_opacity_ok_def, retpc_use_ok_def]
QED

Theorem inline_inst_opacity_phi_labels:
  i.inst_opcode = PHI /\ inline_inst_opacity_ok opaque i ==>
  inline_inst_opacity_ok opaque (subst_label_inst old new i)
Proof
  simp[inline_inst_opacity_ok_def, cfgTransformTheory.subst_label_inst_def,
    retpc_use_ok_def, MEM_MAP] >> rpt strip_tac >>
  rename1 `Var v = subst_label_op old new op` >>
  Cases_on `op` >> gvs[cfgTransformTheory.subst_label_op_def,
    SF boolSimps.COND_elim_ss] >> metis_tac[]
QED

Theorem inline_opacity_renumber:
  inline_opacity_ok (renumber_fn_inst_ids fn) opaque <=> inline_opacity_ok fn opaque
Proof
  simp[inline_opacity_every, EVERY_MAP] >>
  `MAP (inline_inst_opacity_ok opaque) (fn_insts (renumber_fn_inst_ids fn)) =
    MAP (inline_inst_opacity_ok opaque) (fn_insts fn)` by
    (irule renumber_fn_projection >> simp[inline_inst_opacity_id]) >>
  pop_assum (mp_tac o AP_TERM ``EVERY I``) >> simp[EVERY_MAP, SF ETA_ss]
QED

Theorem inline_opacity_fix_phis:
  inline_opacity_ok fn opaque ==>
  inline_opacity_ok (fix_inline_phis old new bb fn) opaque
Proof
  simp[inline_opacity_every, functionInlinerDefsTheory.fix_inline_phis_def,
    venomInstTheory.fn_insts_def, MEM_fn_insts_blocks_iff, EVERY_MEM, MEM_MAP] >>
  rpt strip_tac >> gvs[SF boolSimps.COND_elim_ss] >>
  gvs[MEM_MAP, SF boolSimps.COND_elim_ss] >>
  metis_tac[inline_inst_opacity_phi_labels]
QED

Theorem clone_operand_var_iff:
  clone_operand p labels op = Var x <=>
  ?v. op = Var v /\ x = STRCAT p v
Proof
  Cases_on `op` >> simp[clone_operand_def, SF boolSimps.COND_elim_ss] >>
  metis_tac[]
QED

Theorem clone_retpc_use_ok:
  retpc_use_ok i x ==> retpc_use_ok (clone_instruction p labels i) (STRCAT p x)
Proof
  simp[retpc_use_ok_def, clone_instruction_def] >> rpt strip_tac >>
  simp[clone_operand_def, MEM_MAP] >> rpt strip_tac >>
  gvs[clone_operand_var_iff]
QED

Theorem clone_inst_opacity:
  inline_inst_opacity_ok opaque i ==>
  inline_inst_opacity_ok (IMAGE (STRCAT p) opaque) (clone_instruction p labels i)
Proof
  simp[inline_inst_opacity_ok_def, clone_instruction_def,
    MEM_MAP, IN_IMAGE] >> rpt strip_tac >> gvs[]
  >- (qpat_x_assum `Var _ = clone_operand _ _ _` (mp_tac o SYM) >>
      simp[clone_operand_var_iff] >> strip_tac >> gvs[] >> metis_tac[])
  >- (qpat_x_assum `Var _ = clone_operand _ _ _` (mp_tac o SYM) >>
      simp[clone_operand_var_iff] >> strip_tac >> gvs[] >> metis_tac[])
  >- (qpat_x_assum `Var _ = clone_operand _ _ _` (mp_tac o SYM) >>
      simp[clone_operand_var_iff] >> strip_tac >> gvs[] >>
      metis_tac[clone_retpc_use_ok, clone_instruction_def])
  >> metis_tac[]
QED

Theorem inline_inst_opacity_return_front:
  inline_inst_opacity_ok opaque i /\
  MEM i.inst_opcode [RET; RETFMP] /\
  MEM (Var x) (TAKE (LENGTH i.inst_operands - 1) i.inst_operands) ==>
  x NOTIN opaque
Proof
  rpt strip_tac >>
  `MEM (Var x) i.inst_operands` by metis_tac[MEM_TAKE] >>
  gvs[inline_inst_opacity_ok_def] >>
  first_x_assum drule >> simp[retpc_use_ok_def] >>
  rpt strip_tac >> gvs[TAKE_APPEND] >>
  rpt strip_tac >> gvs[TAKE_APPEND]
QED

Theorem rewrite_inline_inst_opacity:
  inline_inst_opacity_ok opaque i /\
  (!x. MEM (Var x) args ==> x NOTIN opaque) ==>
  EVERY (inline_inst_opacity_ok opaque)
    (FST (rewrite_inline_inst args outs lab i idx))
Proof
  rpt strip_tac >> simp[rewrite_inline_inst_def] >>
  IF_CASES_TAC
  >- (IF_CASES_TAC >> simp[] >>
      gvs[inline_inst_opacity_ok_def, retpc_use_ok_def] >>
      rpt strip_tac >> metis_tac[MEM_EL]) >>
  IF_CASES_TAC
  >- (simp[EVERY_MEM, indexedListsTheory.MEM_MAPi] >> rpt strip_tac >> gvs[] >>
      simp[inline_inst_opacity_ok_def, retpc_use_ok_def] >> rpt strip_tac >>
      `MEM (Var y) (TAKE (LENGTH i.inst_operands - 1) i.inst_operands)` by
        metis_tac[MEM_EL, MEM_FILTER] >>
      metis_tac[inline_inst_opacity_return_front, MEM]) >>
  simp[]
QED

Theorem rewrite_inline_insts_opacity:
  !insts idx. EVERY (inline_inst_opacity_ok opaque) insts /\
  (!x. MEM (Var x) args ==> x NOTIN opaque) ==>
  EVERY (inline_inst_opacity_ok opaque)
    (FST (rewrite_inline_insts args outs lab insts idx))
Proof
  Induct_on `insts` >> simp[rewrite_inline_insts_def] >>
  rpt strip_tac >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  simp[EVERY_APPEND] >>
  metis_tac[rewrite_inline_inst_opacity, pairTheory.FST]
QED

Theorem rewrite_inline_blocks_opacity:
  !blocks idx. EVERY (\bb. EVERY (inline_inst_opacity_ok opaque)
      bb.bb_instructions) blocks /\
  (!x. MEM (Var x) args ==> x NOTIN opaque) ==>
  EVERY (\bb. EVERY (inline_inst_opacity_ok opaque) bb.bb_instructions)
    (FST (rewrite_inline_blocks args outs lab blocks idx))
Proof
  Induct_on `blocks` >> simp[rewrite_inline_blocks_def] >>
  rpt strip_tac >> pairarg_tac >> pairarg_tac >>
  gvs[rewrite_inline_block_def] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  metis_tac[rewrite_inline_insts_opacity, pairTheory.FST]
QED

Theorem clone_function_opacity:
  inline_opacity_ok fn opaque ==>
  inline_opacity_ok (clone_function p fn) (IMAGE (STRCAT p) opaque)
Proof
  simp[inline_opacity_every, EVERY_MEM] >> rpt strip_tac >>
  drule clone_function_inst_origin >> strip_tac >> gvs[] >>
  metis_tac[clone_inst_opacity]
QED

Theorem inline_inst_opacity_extend:
  inline_inst_opacity_ok opaque i /\
  (!x. x IN extra ==> ~MEM x i.inst_outputs /\ ~MEM (Var x) i.inst_operands) ==>
  inline_inst_opacity_ok (opaque UNION extra) i
Proof
  simp[inline_inst_opacity_ok_def, IN_UNION] >> rpt strip_tac >>
  gvs[] >> metis_tac[MEM]
QED

Theorem inline_opacity_extend:
  inline_opacity_ok fn opaque /\
  (!x. x IN extra ==> ~MEM x (cfgTransform$fn_all_vars fn)) ==>
  inline_opacity_ok fn (opaque UNION extra)
Proof
  rpt strip_tac >>
  `!v. MEM v (cfgTransform$fn_all_vars fn) ==> v NOTIN extra` by metis_tac[] >>
  `EVERY (inline_inst_vars_in (\v. v NOTIN extra)) (fn_insts fn)` by
    (rewrite_tac[GSYM inline_fn_vars_in] >> simp[]) >>
  gvs[inline_opacity_every, EVERY_MEM, inline_inst_vars_in_def] >>
  rpt strip_tac >> irule inline_inst_opacity_extend >>
  reverse conj_tac >- metis_tac[] >>
  qpat_x_assum `!e. MEM e _ ==> _ /\ _` (qspec_then `e` mp_tac) >>
  simp[] >> strip_tac >> rpt strip_tac
  >- metis_tac[] >>
  qpat_x_assum `!op. MEM op _ ==> _` (qspec_then `Var x` mp_tac) >> simp[]
QED

Theorem clone_function_opacity_union:
  inline_opacity_ok fn opaque /\
  (!x. x IN extra ==> ~isPREFIX p x) ==>
  inline_opacity_ok (clone_function p fn) (extra UNION IMAGE (STRCAT p) opaque)
Proof
  rpt strip_tac >> once_rewrite_tac[UNION_COMM] >>
  irule inline_opacity_extend >> reverse conj_tac >- metis_tac[clone_function_opacity] >>
  rpt strip_tac >>
  `!v. MEM v (cfgTransform$fn_all_vars (clone_function p fn)) ==> isPREFIX p v` by
    (simp[inline_fn_vars_in, EVERY_MEM] >> rpt strip_tac >>
     drule clone_function_inst_origin >> strip_tac >> gvs[] >>
     irule clone_inst_vars_in >> simp[]) >>
  metis_tac[]
QED

Theorem inline_opacity_blocks:
  inline_opacity_ok fn opaque <=>
  EVERY (\bb. EVERY (inline_inst_opacity_ok opaque) bb.bb_instructions) fn.fn_blocks
Proof
  simp[inline_opacity_every, EVERY_MEM, venomInstTheory.fn_insts_def,
    MEM_fn_insts_blocks_iff] >> metis_tac[]
QED

Theorem inline_call_site_opacity:
  inline_opacity_ok caller opaque /\
  inline_opacity_ok (clone_function p callee) opaque /\
  lookup_block lbl caller.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\
  (!x. MEM (Var x) (rotate_invoke_ops (EL idx bb.bb_instructions).inst_operands)
       ==> x NOTIN opaque) ==>
  inline_opacity_ok (inline_call_site p ret caller callee lbl idx) opaque
Proof
  rpt strip_tac >>
  `MEM bb caller.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `!b. MEM b caller.fn_blocks ==>
    EVERY (inline_inst_opacity_ok opaque) b.bb_instructions` by
    (qpat_x_assum `inline_opacity_ok caller _` mp_tac >>
     simp[inline_opacity_blocks, EVERY_MEM]) >>
  simp[inline_call_site_def] >> pairarg_tac >> simp[] >>
  `EVERY (\b. EVERY (inline_inst_opacity_ok opaque) b.bb_instructions)
    rewritten_blocks` by
    metis_tac[rewrite_inline_blocks_opacity, inline_opacity_blocks, pairTheory.FST] >>
  simp[inline_opacity_blocks, EVERY_MEM, replace_block_def, MEM_MAP] >>
  rpt strip_tac >> gvs[SF boolSimps.COND_elim_ss] >>
  gvs[EVERY_MEM]
  >- metis_tac[MEM_TAKE]
  >- simp[inline_inst_opacity_ok_def]
  >- metis_tac[]
  >- metis_tac[MEM_DROP_IMP] >>
  metis_tac[]
QED

Theorem rotate_invoke_nonopaque:
  (!x. MEM (Var x) ops ==> x NOTIN opaque) ==>
  !x. MEM (Var x) (rotate_invoke_ops ops) ==> x NOTIN opaque
Proof
  Cases_on `ops` >> simp[rotate_invoke_ops_def] >> metis_tac[MEM]
QED

Theorem inline_one_site_opacity:
  qualified_origin ctx n caller /\ ist.is_inline_count = n /\
  inline_opacity_ok caller caller_opaque /\
  inline_opacity_ok callee callee_opaque /\
  (!x. x IN caller_opaque ==> ~isPREFIX (inline_prefix n) x) /\
  inline_one_site caller callee ist = SOME (caller', ist') ==>
  inline_opacity_ok caller'
    (caller_opaque UNION IMAGE (STRCAT (inline_prefix n)) callee_opaque)
Proof
  rpt strip_tac >>
  `inline_opacity_ok caller
    (caller_opaque UNION IMAGE (STRCAT (inline_prefix n)) callee_opaque)` by
    (irule inline_opacity_extend >> reverse conj_tac >- simp[] >>
     simp[IN_IMAGE] >> metis_tac[qualified_origin_clone_disjoint]) >>
  `inline_opacity_ok (clone_function (inline_prefix n) callee)
    (caller_opaque UNION IMAGE (STRCAT (inline_prefix n)) callee_opaque)` by
    metis_tac[clone_function_opacity_union] >>
  `wf_function caller` by
    metis_tac[qualified_origin_erasure, inliner_fn_origin_structure] >>
  qpat_x_assum `inline_one_site _ _ _ = _` mp_tac >>
  simp[inline_one_site_def, AllCaseEqs()] >> rpt strip_tac >> gs[] >>
  `ALL_DISTINCT (fn_labels caller)` by
    gvs[venomWfTheory.wf_function_def] >>
  drule_all find_invoke_site_lookup_signature >> strip_tac >>
  `inline_opacity_ok (inline_call_site (inline_prefix n)
      (return_block_label (inline_prefix n) ist.is_label_counter)
      caller callee bb_lbl idx)
    (caller_opaque UNION IMAGE (STRCAT (inline_prefix n)) callee_opaque)` by
    (irule inline_call_site_opacity >>
     rpt conj_tac >> asm_rewrite_tac[] >> qexists_tac `bb` >>
     rpt conj_tac >> asm_rewrite_tac[] >>
     match_mp_tac rotate_invoke_nonopaque >> gen_tac >> disch_tac >>
     irule inline_opacity_invoke_operand >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `caller` >>
     simp[venomInstTheory.fn_insts_def, MEM_fn_insts_blocks_iff] >>
     reverse conj_tac >- gvs[] >>
     qexists_tac `bb` >> metis_tac[lookup_block_MEM, EL_MEM]) >>
  gvs[inline_opacity_renumber, AllCaseEqs()] >>
  CASE_TAC >> simp[inline_opacity_fix_phis]
QED

Theorem retpc_var_output_member:
  !fn x. retpc_var fn x ==> ?i. MEM i (fn_insts fn) /\ MEM x i.inst_outputs
Proof
  simp[retpc_var_def] >> rpt strip_tac >>
  drule (iffLR copy_phi_var_cases) >> metis_tac[]
QED

Theorem qualified_origin_opacity:
  !ctx n fn. qualified_origin ctx n fn ==>
    ?opaque. inline_opacity_ok fn opaque /\
      (!x. x IN opaque ==> ~isPREFIX "inl" x \/
        ?k. k < n /\ isPREFIX (inline_prefix k) x)
Proof
  ho_match_mp_tac qualified_origin_strongind >> rpt conj_tac
  >- (rpt strip_tac >> qexists_tac `{x | retpc_var fn x}` >>
      conj_tac >- metis_tac[inliner_input_opacity] >>
      simp[] >> rpt strip_tac >>
      drule retpc_var_output_member >> strip_tac >>
      gvs[functionInlinerContractTheory.inliner_input_ok_def, EVERY_MEM] >>
      metis_tac[])
  >- (rpt strip_tac >> qexists_tac `opaque` >>
      metis_tac[functionInlinerWfTheory.inline_label_bound_mono]) >>
  rpt strip_tac >>
  qexists_tac `opaque UNION IMAGE (STRCAT (inline_prefix n)) opaque'` >>
  conj_tac
  >- (irule inline_one_site_opacity >> conj_tac
      >- metis_tac[functionInlinerWfTheory.inline_label_bound_fresh] >>
      goal_assum (drule_at (Pat `inline_one_site _ _ _ = _`)) >>
      simp[] >> qexists_tac `ctx` >> simp[]) >>
  drule inline_one_site_counter >> strip_tac >>
  simp[IN_UNION, IN_IMAGE, Excl "isPREFIX", Excl "isPREFIX_def"] >> rpt strip_tac
  >- (irule functionInlinerWfTheory.inline_label_bound_mono >>
      qexists_tac `n` >> simp[]) >>
  gvs[Excl "isPREFIX", Excl "isPREFIX_def"] >>
  metis_tac[functionInlinerWfTheory.inline_label_bound_clone]
QED
