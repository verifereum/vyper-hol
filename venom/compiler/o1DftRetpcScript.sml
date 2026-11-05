(*
 * dft_fn keeps the return-PC shape (retpc_shape_ok) on an SSA function.
 * On SSA, dft_fn keeps every instruction of each block, up to flipping
 * the operands of a commutative or comparison instruction
 * (dft_fn_all_perm_of), keeps the pseudo-instructions and the labels and
 * successors of each block, so the CFG, reachability and the return-PC
 * variables (defined by RETPC_PARAM, ASSIGN and PHI, none of which is
 * flipped) are the same.
 *)
Theory o1DftRetpc
Ancestors
  dftCorrectness dftLifting unitShapeDefs dftDefs venomWf
  dftSsaPreserve dftShape venomEffects passSharedDefs venomInst dftStructural list

Theorem retpc_special_not_flippable[local]:
  MEM op [RETPC_PARAM; ASSIGN; PHI; RET; RETFMP; DRET] ==>
  ~is_flippable op
Proof
  strip_tac >> gvs[] >>
  EVAL_TAC
QED

Theorem dft_retpc_block_mem[local]:
  dftScheduleOrder$dft_block_rel a b /\
  ALL_DISTINCT (MAP (\i. i.inst_id) a.bb_instructions) /\
  MEM i.inst_opcode [RETPC_PARAM; ASSIGN; PHI; RET; RETFMP; DRET] ==>
  (MEM i b.bb_instructions <=> MEM i a.bb_instructions)
Proof
  strip_tac >> eq_tac >> strip_tac
  >- (drule_all dft_block_rel_origin >> strip_tac >> gvs[] >>
      drule flip_operands_special_opcode >> simp[]) >>
  drule_all dft_block_rel_member >> strip_tac >>
  metis_tac[retpc_special_not_flippable]
QED

Theorem dft_retpc_fn_mem[local]:
  wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn /\
  MEM i.inst_opcode [RETPC_PARAM; ASSIGN; PHI; RET; RETFMP; DRET] ==>
  (MEM i (fn_insts (dft_fn fn)) <=> MEM i (fn_insts fn))
Proof
  strip_tac >> drule_all dftScheduleOrderTheory.dft_fn_block_rel >>
  strip_tac >> simp[fn_insts_def, MEM_fn_insts_blocks_iff] >>
  eq_tac >> strip_tac
  >- (drule_all dft_blocks_member_right >> strip_tac >>
      metis_tac[dft_retpc_block_mem, bb_inst_ids_distinct]) >>
  drule_all dft_blocks_member_left >> strip_tac >>
  metis_tac[dft_retpc_block_mem, bb_inst_ids_distinct]
QED

Theorem dft_retpc_fn_origin[local]:
  wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn /\
  MEM i (fn_insts (dft_fn fn)) ==>
  ?j. MEM j (fn_insts fn) /\ i.inst_outputs = j.inst_outputs /\
      (i = j \/ (is_flippable j.inst_opcode /\ i = flip_operands j))
Proof
  strip_tac >> drule_all dftScheduleOrderTheory.dft_fn_block_rel >>
  strip_tac >> gvs[fn_insts_def, MEM_fn_insts_blocks_iff] >>
  drule_all dft_blocks_member_right >> strip_tac >>
  drule_all dft_block_rel_origin >> strip_tac >>
  metis_tac[flip_operands_inst_outputs]
QED

Theorem dft_retpc_cfg[local]:
  wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn ==>
  fn_cfg_edge (dft_fn fn) = fn_cfg_edge fn
Proof
  strip_tac >> drule_all dftScheduleOrderTheory.dft_fn_block_rel >>
  strip_tac >> drule_all dftSsaPreserveTheory.dft_block_rel_cfg >>
  simp[FUN_EQ_THM, fn_cfg_edge_def]
QED

Theorem dft_retpc_reachable[local]:
  wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn ==>
  (fn_reachable (dft_fn fn) lbl <=> fn_reachable fn lbl)
Proof
  strip_tac >> drule_all dftScheduleOrderTheory.dft_fn_block_rel >>
  strip_tac >> drule_all dft_block_rel_reachable >>
  disch_then (qspec_then `lbl` mp_tac) >>
  `fn_cfg_edge (fn with fn_blocks := (dft_fn fn).fn_blocks) =
   fn_cfg_edge (dft_fn fn)` by simp[FUN_EQ_THM, fn_cfg_edge_def] >>
  simp[fn_reachable_def, fn_entry_label_def, entry_block_def]
QED

Theorem dft_retpc_preds[local]:
  wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn ==>
  reachable_preds (dft_fn fn) lbl = reachable_preds fn lbl
Proof
  strip_tac >> simp[reachable_preds_def, dft_retpc_reachable,
    dft_retpc_cfg, dft_fn_labels_map]
QED

Theorem dft_retpc_reachable_inst[local]:
  wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn ==>
  reachable_inst (dft_fn fn) lbl i = reachable_inst fn lbl i
Proof
  strip_tac >> simp[reachable_inst_def, dft_retpc_preds]
QED

Theorem dft_retpc_reachable_mem[local]:
  wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn /\
  MEM i.inst_opcode [RETPC_PARAM; ASSIGN; PHI; RET; RETFMP; DRET] ==>
  (MEM i (fn_insts (reachable_fn (dft_fn fn))) <=>
   MEM i (fn_insts (reachable_fn fn)))
Proof
  strip_tac >> drule_all dftScheduleOrderTheory.dft_fn_block_rel >>
  strip_tac >> simp[MEM_reachable_fn_insts, dft_retpc_reachable,
                    dft_retpc_reachable_inst] >>
  eq_tac >> strip_tac
  >- (drule_all dft_blocks_member_right >> strip_tac >>
      `MEM i'.inst_opcode [RETPC_PARAM; ASSIGN; PHI; RET; RETFMP; DRET]`
        by metis_tac[reachable_inst_fields] >>
      `MEM i' bb'.bb_instructions` by
        metis_tac[dft_retpc_block_mem, bb_inst_ids_distinct] >>
      metis_tac[dftSsaPreserveTheory.dft_block_rel_label]) >>
  drule_all dft_blocks_member_left >> strip_tac >>
  `MEM i'.inst_opcode [RETPC_PARAM; ASSIGN; PHI; RET; RETFMP; DRET]`
    by metis_tac[reachable_inst_fields] >>
  `MEM i' bb'.bb_instructions` by
    metis_tac[dft_retpc_block_mem, bb_inst_ids_distinct] >>
  metis_tac[dftSsaPreserveTheory.dft_block_rel_label]
QED

Theorem copy_phi_var_special_mono:
  !origin f x. copy_phi_var origin f x ==>
  !g. (!i. MEM i (fn_insts f) /\
           (i.inst_opcode = origin \/ i.inst_opcode = ASSIGN \/
            i.inst_opcode = PHI) ==> MEM i (fn_insts g)) ==>
      copy_phi_var origin g x
Proof
  Induct_on `copy_phi_var` >> rpt strip_tac >>
  metis_tac[copy_phi_var_rules]
QED

Theorem dft_retpc_var[local]:
  wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn ==>
  (retpc_var (dft_fn fn) x <=> retpc_var fn x)
Proof
  strip_tac >> simp[retpc_var_def] >> eq_tac >> strip_tac >>
  drule copy_phi_var_special_mono >> disch_then irule >>
  rpt strip_tac >> metis_tac[dft_retpc_fn_mem, MEM]
QED

Theorem dft_reachable_retpc_var[local]:
  wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn ==>
  (retpc_var (reachable_fn (dft_fn fn)) x <=>
   retpc_var (reachable_fn fn) x)
Proof
  strip_tac >> simp[retpc_var_def] >> eq_tac >> strip_tac >>
  drule copy_phi_var_special_mono >> disch_then irule >>
  rpt strip_tac >> metis_tac[dft_retpc_reachable_mem, MEM]
QED

Theorem dft_retpc_writer_mem[local]:
  wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn /\
  retpc_shape_ok fn /\ MEM i (fn_insts (dft_fn fn)) /\
  MEM x i.inst_outputs /\ retpc_var (dft_fn fn) x ==>
  MEM i (fn_insts fn)
Proof
  strip_tac >> drule_all dft_retpc_fn_origin >> strip_tac >>
  `retpc_var fn x` by metis_tac[dft_retpc_var] >>
  `MEM j.inst_opcode [RETPC_PARAM; ASSIGN; PHI; RET; RETFMP; DRET]` by
    (qpat_x_assum `retpc_shape_ok fn` mp_tac >>
     simp[retpc_shape_ok_def] >> rpt strip_tac >>
     metis_tac[MEM]) >>
  metis_tac[retpc_special_not_flippable]
QED

Theorem dft_fn_retpc_shape_ok:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\ fn_pseudos_prefix fn /\
  EVERY inst_shape_ok (fn_insts fn) /\ retpc_shape_ok fn ==>
  retpc_shape_ok (dft_fn fn)
Proof
  strip_tac >>
  `!i x. MEM i (fn_insts (dft_fn fn)) /\ MEM x i.inst_outputs /\
          retpc_var (dft_fn fn) x ==> MEM i (fn_insts fn)` by
    metis_tac[dft_retpc_writer_mem] >>
  qpat_x_assum `retpc_shape_ok fn` mp_tac >>
  simp[retpc_shape_ok_def, dft_retpc_var, dft_reachable_retpc_var] >>
  strip_tac >> rpt conj_tac
  >- metis_tac[dft_retpc_reachable_mem, MEM]
  >- metis_tac[dft_retpc_reachable_mem, MEM]
  >- (rpt strip_tac >>
      `MEM inst (fn_insts fn)` by metis_tac[dft_retpc_var] >>
      qpat_x_assum `!inst x. MEM inst (fn_insts fn) /\ _ ==> _`
        (qspecl_then [`inst`, `x`] mp_tac) >> simp[]) >>
  metis_tac[dft_retpc_var]
QED
