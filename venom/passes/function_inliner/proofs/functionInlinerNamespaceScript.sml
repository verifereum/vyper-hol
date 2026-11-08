(* Static variable namespaces, including both reads and writes. *)
Theory functionInlinerNamespace
Ancestors
  functionInlinerReturnBoundary functionInlinerOrigin functionInlinerContract
  functionInlinerWf functionInlinerDefs cfgTransform venomInst unitShapeDefs
  venomExecProofs indexedLists rich_list list string arithmetic

Definition inline_inst_vars_in_def:
  inline_inst_vars_in P inst <=>
    EVERY P inst.inst_outputs /\
    EVERY (\op. case op of Var v => P v | _ => T) inst.inst_operands
End

Theorem inline_fn_vars_in:
  (!v. MEM v (cfgTransform$fn_all_vars fn) ==> P v) <=>
  EVERY (inline_inst_vars_in P) (fn_insts fn)
Proof
  simp[cfgTransformTheory.fn_all_vars_def, fn_insts_def,
    MEM_fn_insts_blocks_iff, inline_inst_vars_in_def, EVERY_MEM,
    MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  eq_tac >> rpt strip_tac
  >- metis_tac[]
  >- (Cases_on `op` >> simp[] >> first_x_assum irule >>
      qexistsl [`bb`, `e`] >> simp[] >> disj2_tac >>
      goal_assum (drule_at Any) >> simp[])
  >- metis_tac[] >>
  first_x_assum (qspecl_then [`inst`, `bb`] mp_tac) >> simp[] >>
  strip_tac >> first_x_assum drule >> Cases_on `op` >> gvs[]
QED

Theorem inline_inst_vars_in_mono:
  inline_inst_vars_in P inst /\ (!v. P v ==> Q v) ==>
  inline_inst_vars_in Q inst
Proof
  simp[inline_inst_vars_in_def, EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!op. MEM op _ ==> _` drule >>
  Cases_on `op` >> simp[] >> metis_tac[]
QED

Theorem clone_inst_vars_in:
  (!v. P (STRCAT p v)) ==>
  inline_inst_vars_in P (clone_instruction p labels inst)
Proof
  simp[inline_inst_vars_in_def, clone_instruction_def, EVERY_MAP,
    EVERY_MEM, MEM_MAP] >> rpt strip_tac >- metis_tac[] >>
  Cases_on `op` >>
  simp[clone_operand_def] >> Cases_on `y` >>
  gvs[clone_operand_def, SF boolSimps.COND_elim_ss]
QED

Theorem rewrite_inline_inst_vars_in:
  !inst args outs ret pi ri P.
    inline_inst_vars_in P inst /\
    EVERY (\op. case op of Var v => P v | _ => T) args /\ EVERY P outs /\
    ((inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) ==>
      raw_return_user_arity inst = SOME (LENGTH outs)) /\
    MEM ri (FST (rewrite_inline_inst args outs ret inst pi)) ==>
    inline_inst_vars_in P ri
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_param_opcode inst.inst_opcode`
  >- (gvs[rewrite_inline_inst_def, inline_inst_vars_in_def,
          SF boolSimps.COND_elim_ss] >>
      gvs[EVERY_EL]) >>
  Cases_on `inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP`
  >- (`!x. MEM x ri.inst_outputs ==> P x` by
        metis_tac[inline_return_static_write_boundary, EVERY_MEM] >>
      gvs[rewrite_inline_inst_def, MEM_MAPi] >>
      simp[inline_inst_vars_in_def] >>
      gvs[inline_inst_vars_in_def, EVERY_MEM] >>
      qpat_x_assum `!op. MEM op inst.inst_operands ==> _` irule >>
      metis_tac[EL_MEM, MEM_FILTER, MEM_TAKE]) >>
  gvs[rewrite_inline_inst_def]
QED

Theorem rewrite_inline_insts_vars_in:
  !insts args outs ret pi ris pi' P.
    EVERY (inline_inst_vars_in P) insts /\
    EVERY (\op. case op of Var v => P v | _ => T) args /\ EVERY P outs /\
    (!inst. MEM inst insts /\
      (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) ==>
      raw_return_user_arity inst = SOME (LENGTH outs)) /\
    rewrite_inline_insts args outs ret insts pi = (ris,pi') ==>
    EVERY (inline_inst_vars_in P) ris
Proof
  Induct >> simp[rewrite_inline_insts_def] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  conj_tac
  >- (simp[EVERY_MEM] >> rpt strip_tac >>
      irule rewrite_inline_inst_vars_in >> metis_tac[pairTheory.FST]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem rewrite_inline_blocks_vars_in:
  !bbs args outs ret pi bbs' pi' P.
    EVERY (\bb. EVERY (inline_inst_vars_in P) bb.bb_instructions) bbs /\
    EVERY (\op. case op of Var v => P v | _ => T) args /\ EVERY P outs /\
    (!bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions /\
      (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) ==>
      raw_return_user_arity inst = SOME (LENGTH outs)) /\
    rewrite_inline_blocks args outs ret bbs pi = (bbs',pi') ==>
    EVERY (\bb. EVERY (inline_inst_vars_in P) bb.bb_instructions) bbs'
Proof
  Induct >> simp[rewrite_inline_blocks_def] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  conj_tac
  >- (qpat_x_assum `rewrite_inline_block _ _ _ _ _ = _` mp_tac >>
      simp[rewrite_inline_block_def] >> pairarg_tac >> simp[] >>
      strip_tac >> gvs[] >> irule rewrite_inline_insts_vars_in >>
      metis_tac[]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem rotate_invoke_vars_in:
  EVERY (\op. case op of Var v => P v | _ => T) ops ==>
  EVERY (\op. case op of Var v => P v | _ => T) (rotate_invoke_ops ops)
Proof
  Cases_on `ops` >> simp[rotate_invoke_ops_def]
QED

Theorem clone_blocks_vars_in:
  (!v. P (STRCAT p v)) ==>
  EVERY (\bb. EVERY (inline_inst_vars_in P) bb.bb_instructions)
    (clone_function p fn).fn_blocks
Proof
  simp[clone_function_def, clone_basic_block_def, EVERY_MAP] >>
  strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  irule clone_inst_vars_in >> simp[]
QED

Theorem clone_blocks_return_arity:
  (!r. MEM r (fn_insts fn) /\
    (r.inst_opcode = RET \/ r.inst_opcode = RETFMP) ==>
    raw_return_user_arity r = arity) ==>
  !bb r. MEM bb (clone_function p fn).fn_blocks /\
    MEM r bb.bb_instructions /\
    (r.inst_opcode = RET \/ r.inst_opcode = RETFMP) ==>
    raw_return_user_arity r = arity
Proof
  simp[clone_function_def, clone_basic_block_def, MEM_MAP,
    fn_insts_def, MEM_fn_insts_blocks_iff] >> rpt strip_tac >>
  gvs[MEM_MAP] >>
  `raw_return_user_arity (clone_instruction p (fn_labels fn) y') =
   raw_return_user_arity y'` by
    (irule clone_instruction_return_arity >> gvs[clone_instruction_def]) >>
  gvs[clone_instruction_def] >> metis_tac[]
QED

Theorem inline_call_site_vars_in:
  !caller callee p ret lbl idx P bb.
    EVERY (inline_inst_vars_in P) (fn_insts caller) /\
    (!v. P (STRCAT p v)) /\
    lookup_block lbl caller.fn_blocks = SOME bb /\
    idx < LENGTH bb.bb_instructions /\
    (!r. MEM r (fn_insts callee) /\
      (r.inst_opcode = RET \/ r.inst_opcode = RETFMP) ==>
      raw_return_user_arity r =
        SOME (LENGTH (EL idx bb.bb_instructions).inst_outputs)) ==>
    EVERY (inline_inst_vars_in P)
      (fn_insts (inline_call_site p ret caller callee lbl idx))
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb caller.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `inline_inst_vars_in P (EL idx bb.bb_instructions)` by
    metis_tac[EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff, EL_MEM] >>
  `!b. MEM b caller.fn_blocks ==>
    EVERY (inline_inst_vars_in P) b.bb_instructions` by
    metis_tac[EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff] >>
  simp[inline_call_site_def] >> pairarg_tac >> simp[] >>
  `EVERY (\b. EVERY (inline_inst_vars_in P) b.bb_instructions)
    rewritten_blocks` by
    (irule rewrite_inline_blocks_vars_in >>
     goal_assum (drule_at Any) >>
     simp[clone_blocks_vars_in] >>
     conj_tac >- metis_tac[clone_blocks_return_arity] >>
     gvs[inline_inst_vars_in_def] >>
     irule rotate_invoke_vars_in >> simp[]) >>
  simp[fn_insts_def, MEM_fn_insts_blocks_iff, EVERY_MEM,
       replace_block_def, MEM_MAP] >> rpt strip_tac >>
  gvs[SF boolSimps.COND_elim_ss, inline_inst_vars_in_def] >>
  pure_rewrite_tac[GSYM inline_inst_vars_in_def] >>
  gvs[EVERY_MEM] >>
  metis_tac[MEM_TAKE, MEM_DROP_IMP]
QED

Theorem fix_inline_phis_vars_in:
  EVERY (inline_inst_vars_in P) (fn_insts fn) ==>
  EVERY (inline_inst_vars_in P) (fn_insts (fix_inline_phis old new bb fn))
Proof
  simp[fix_inline_phis_def, fn_insts_def, MEM_fn_insts_blocks_iff,
       EVERY_MEM, MEM_MAP] >> rpt strip_tac >>
  gvs[SF boolSimps.COND_elim_ss, inline_inst_vars_in_def,
      subst_label_inst_def, EVERY_MAP, EVERY_MEM, MEM_MAP]
  >- metis_tac[]
  >- (first_x_assum (qspec_then `inst` mp_tac) >>
      impl_tac >- metis_tac[] >> strip_tac >>
      conj_tac >- simp[] >> rpt strip_tac >> gvs[] >>
      qpat_x_assum `!op. MEM op inst.inst_operands ==> _` drule >>
      Cases_on `y` >> simp[subst_label_op_def, SF boolSimps.COND_elim_ss]) >>
  metis_tac[]
QED

Theorem renumber_fn_vars_in:
  EVERY (inline_inst_vars_in P) (fn_insts (renumber_fn_inst_ids fn)) =
  EVERY (inline_inst_vars_in P) (fn_insts fn)
Proof
  `MAP (inline_inst_vars_in P) (fn_insts (renumber_fn_inst_ids fn)) =
   MAP (inline_inst_vars_in P) (fn_insts fn)` by
    (irule renumber_fn_projection >> simp[inline_inst_vars_in_def]) >>
  pop_assum (mp_tac o AP_TERM ``EVERY I``) >>
  simp[EVERY_MAP, combinTheory.o_DEF, SF ETA_ss]
QED
