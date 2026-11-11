(*
 * Revert-to-Assert Pass — structural properties of the supply-threaded
 * transform: it keeps SSA form and function well-formedness, because the
 * inserted ISZERO output and ISZERO/ASSERT ids come fresh from the supply.
 *)

Theory rtaSupplyProofs
Ancestors
  rtaDefs irSupply irSupplyFreshProps venomFnScheduleRunner fmpStepChunk fmpStepList venomWf
  venomInst venomState list
Libs
  listTheory

(* ===== Single instruction ===== *)

Theorem rta_transform_inst_supply_non_jnz:
  inst.inst_opcode <> JNZ ==> rta_transform_inst_supply fn s inst = ([inst],s)
Proof
  simp[rta_transform_inst_supply_def]
QED

Theorem rta_transform_inst_supply_cases:
  rta_transform_inst_supply fn s inst = (out,s') ==>
  (out = [inst] /\ s' = s) \/
  (?c a b tmp s1 iz s2 as.
     inst.inst_opcode = JNZ /\
     inst.inst_operands = [c; Label a; Label b] /\
     fresh_ir_var s = (tmp,s1) /\ fresh_inst_id s1 = (iz,s2) /\
     fresh_inst_id s2 = (as,s') /\
     out = [mk_iszero_inst iz c tmp; mk_assert_inst as (Var tmp);
            mk_jmp_inst inst.inst_id b]) \/
  (?c a b as.
     inst.inst_opcode = JNZ /\
     inst.inst_operands = [c; Label a; Label b] /\
     fresh_inst_id s = (as,s') /\
     out = [mk_assert_inst as c; mk_jmp_inst inst.inst_id a])
Proof
  simp[rta_transform_inst_supply_def] >>
  Cases_on `inst.inst_opcode = JNZ` >> simp[] >>
  Cases_on `?c a b. inst.inst_operands = [c; Label a; Label b]`
  >- (gvs[] >> rw[] >> gvs[AllCaseEqs()]) >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

Theorem rta_transform_inst_supply_fresh:
  rta_transform_inst_supply fn s inst = (out,s') ==>
  ir_fresh_ext s.irs_used_vars s'.irs_used_vars inst.inst_outputs
    (FLAT (MAP (\i. i.inst_outputs) out)) /\
  (ir_supply_inst_ok s ==>
   ir_supply_inst_ok s' /\
   ir_fresh_ext s.irs_used_inst_ids s'.irs_used_inst_ids [inst.inst_id]
     (MAP (\i. i.inst_id) out))
Proof
  strip_tac >> drule rta_transform_inst_supply_cases >> strip_tac
  >- gvs[ir_fresh_ext_refl]
  >- (drule fresh_ir_var_contract >> strip_tac >>
      `s2.irs_used_vars = s1.irs_used_vars /\
       s'.irs_used_vars = s2.irs_used_vars` by gvs[fresh_inst_id_def] >>
      conj_tac
      >- gvs[mk_iszero_inst_def, mk_assert_inst_def, mk_jmp_inst_def,
             ir_fresh_ext_def] >>
      strip_tac >>
      `ir_supply_inst_ok s1` by gvs[ir_supply_inst_ok_def] >>
      qspecl_then [`s1`,`iz`,`s2`] mp_tac
        (Q.GENL [`s`,`id`,`s'`] fresh_inst_id_contract) >>
      simp[] >> strip_tac >>
      qspecl_then [`s2`,`as`,`s'`] mp_tac
        (Q.GENL [`s`,`id`,`s'`] fresh_inst_id_contract) >>
      simp[] >> strip_tac >>
      gvs[mk_iszero_inst_def, mk_assert_inst_def, mk_jmp_inst_def,
          ir_fresh_ext_def] >>
      rpt strip_tac >> gvs[] >> metis_tac[])
  >> `s'.irs_used_vars = s.irs_used_vars` by gvs[fresh_inst_id_def] >>
  conj_tac
  >- gvs[mk_assert_inst_def, mk_jmp_inst_def, ir_fresh_ext_def] >>
  strip_tac >>
  qspecl_then [`s`,`as`,`s'`] mp_tac
    (Q.GENL [`s`,`id`,`s'`] fresh_inst_id_contract) >>
  simp[] >> strip_tac >>
  gvs[mk_assert_inst_def, mk_jmp_inst_def, ir_fresh_ext_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* Every result instruction is the original one, or JNZ's rewrite: no PHIs,
   a single terminator at the end, whose targets are among the JNZ's. *)
Theorem rta_transform_inst_supply_shape:
  rta_transform_inst_supply fn s inst = (out,s') ==>
  out = [inst] \/
  (inst.inst_opcode = JNZ /\
   EVERY (\j. j.inst_opcode <> PHI) out /\
   list_terminal (\j. is_terminator j.inst_opcode) out /\
   !l. MEM l (get_successors (LAST out)) ==> MEM l (get_successors inst))
Proof
  strip_tac >> drule rta_transform_inst_supply_cases >> strip_tac >>
  gvs[mk_iszero_inst_def, mk_assert_inst_def, mk_jmp_inst_def,
      list_terminal_def, is_terminator_def, get_successors_def, get_label_def] >>
  rw[]
QED

(* ===== Instruction lists ===== *)

Theorem rta_transform_insts_supply_fresh:
  !insts s out s'.
    rta_transform_insts_supply fn s insts = (out,s') ==>
    ir_fresh_ext s.irs_used_vars s'.irs_used_vars
      (FLAT (MAP (\i. i.inst_outputs) insts))
      (FLAT (MAP (\i. i.inst_outputs) out)) /\
    (ir_supply_inst_ok s ==>
     ir_supply_inst_ok s' /\
     ir_fresh_ext s.irs_used_inst_ids s'.irs_used_inst_ids
       (MAP (\i. i.inst_id) insts) (MAP (\i. i.inst_id) out))
Proof
  Induct >- simp[rta_transform_insts_supply_def, ir_fresh_ext_refl] >>
  rpt gen_tac >> simp[rta_transform_insts_supply_def] >>
  Cases_on `rta_transform_inst_supply fn s h` >> rename1 `rta_transform_inst_supply fn s h = (o1,s1)` >>
  Cases_on `rta_transform_insts_supply fn s1 insts` >>
  rename1 `rta_transform_insts_supply fn s1 insts = (outs,s2)` >> simp[] >> strip_tac >> gvs[] >>
  drule rta_transform_inst_supply_fresh >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  conj_tac
  >- (simp[MAP_APPEND, FLAT_APPEND] >>
      irule ir_fresh_ext_append >> metis_tac[]) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `ir_fresh_ext s.irs_used_inst_ids _ _ _` (fn th1 =>
    qpat_x_assum `ir_fresh_ext s1.irs_used_inst_ids _ _ _` (fn th2 =>
      mp_tac (MATCH_MP ir_fresh_ext_append (CONJ th1 th2)))) >>
  simp[MAP_APPEND]
QED

Theorem rta_transform_insts_supply_nonempty:
  !insts s out s'.
    rta_transform_insts_supply fn s insts = (out,s') ==>
    (out = [] <=> insts = [])
Proof
  Induct >> simp[rta_transform_insts_supply_def] >>
  rpt gen_tac >> Cases_on `rta_transform_inst_supply fn s h` >> rename1 `rta_transform_inst_supply fn s h = (o1,s1)` >>
  Cases_on `rta_transform_insts_supply fn s1 insts` >>
  rename1 `rta_transform_insts_supply fn s1 insts = (outs,s2)` >> simp[] >> strip_tac >> gvs[] >>
  drule rta_transform_inst_supply_shape >> strip_tac >>
  gvs[list_terminal_def] >> Cases_on `o1` >> gvs[list_terminal_def]
QED

Theorem rta_transform_insts_supply_no_phi:
  !insts s out s'.
    rta_transform_insts_supply fn s insts = (out,s') /\
    EVERY (\j. j.inst_opcode <> PHI) insts ==>
    EVERY (\j. j.inst_opcode <> PHI) out
Proof
  Induct >> simp[rta_transform_insts_supply_def] >>
  rpt gen_tac >> Cases_on `rta_transform_inst_supply fn s h` >> rename1 `rta_transform_inst_supply fn s h = (o1,s1)` >>
  Cases_on `rta_transform_insts_supply fn s1 insts` >>
  rename1 `rta_transform_insts_supply fn s1 insts = (outs,s2)` >> simp[] >> strip_tac >> gvs[] >>
  drule rta_transform_inst_supply_shape >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem rta_transform_insts_supply_phi_prefix:
  !insts s out s'.
    rta_transform_insts_supply fn s insts = (out,s') /\
    list_prefix (\j. j.inst_opcode = PHI) insts ==>
    list_prefix (\j. j.inst_opcode = PHI) out
Proof
  Induct >> simp[rta_transform_insts_supply_def] >>
  rpt gen_tac >> Cases_on `rta_transform_inst_supply fn s h` >> rename1 `rta_transform_inst_supply fn s h = (o1,s1)` >>
  Cases_on `rta_transform_insts_supply fn s1 insts` >>
  rename1 `rta_transform_insts_supply fn s1 insts = (outs,s2)` >> simp[] >>
  simp[list_prefix_def] >> strip_tac >> gvs[list_prefix_append] >>
  first_x_assum drule_all >> strip_tac >>
  drule rta_transform_inst_supply_shape >> strip_tac >> gvs[list_prefix_def]
  >- (strip_tac >> irule rta_transform_insts_supply_no_phi >> metis_tac[])
  >> conj_tac
  >- (irule list_prefix_none >> gvs[EVERY_MEM])
  >> strip_tac >> irule rta_transform_insts_supply_no_phi >> metis_tac[]
QED

Theorem rta_transform_insts_supply_terminal:
  !insts s out s'.
    rta_transform_insts_supply fn s insts = (out,s') /\
    list_terminal (\j. is_terminator j.inst_opcode) insts ==>
    list_terminal (\j. is_terminator j.inst_opcode) out /\
    !l. MEM l (get_successors (LAST out)) ==>
        MEM l (get_successors (LAST insts))
Proof
  Induct >> simp[rta_transform_insts_supply_def] >>
  rpt gen_tac >> Cases_on `rta_transform_inst_supply fn s h` >> rename1 `rta_transform_inst_supply fn s h = (o1,s1)` >>
  Cases_on `rta_transform_insts_supply fn s1 insts` >>
  rename1 `rta_transform_insts_supply fn s1 insts = (outs,s2)` >> simp[] >> strip_tac >> gvs[] >>
  Cases_on `insts = []`
  >- (gvs[rta_transform_insts_supply_def, list_terminal_def] >>
      drule rta_transform_inst_supply_shape >> strip_tac >>
      gvs[list_terminal_def]) >>
  gvs[list_terminal_def] >>
  `rta_transform_inst_supply fn s h = ([h],s)` by
    (irule rta_transform_inst_supply_non_jnz >> strip_tac >>
     gvs[is_terminator_def]) >>
  gvs[] >> first_x_assum drule_all >> strip_tac >>
  `outs <> []` by metis_tac[rta_transform_insts_supply_nonempty] >>
  Cases_on `outs` >> gvs[list_terminal_def, LAST_DEF] >>
  Cases_on `insts` >> gvs[LAST_DEF]
QED

(* ===== Blocks ===== *)

Theorem rta_transform_insts_supply_bb_well_formed:
  bb_well_formed bb /\
  rta_transform_insts_supply fn s bb.bb_instructions = (bb'.bb_instructions,s') ==>
  bb_well_formed bb' /\
  !l. MEM l (bb_succs bb') ==> MEM l (bb_succs bb)
Proof
  rewrite_tac[bb_well_formed_list] >> strip_tac >>
  drule_all rta_transform_insts_supply_terminal >> strip_tac >>
  drule_all rta_transform_insts_supply_phi_prefix >> strip_tac >>
  simp[bb_succs_def] >>
  Cases_on `bb'.bb_instructions` >> gvs[list_terminal_def] >>
  Cases_on `bb.bb_instructions` >> gvs[list_terminal_def, MEM_nub]
QED

Theorem rta_transform_insts_supply_append:
  !xs s ys.
    rta_transform_insts_supply fn s (xs ++ ys) =
    case rta_transform_insts_supply fn s xs of (a,s1) =>
    case rta_transform_insts_supply fn s1 ys of (b,s2) => (a ++ b,s2)
Proof
  Induct
  >- (simp[rta_transform_insts_supply_def] >> rpt gen_tac >>
      Cases_on `rta_transform_insts_supply fn s ys` >> simp[]) >>
  simp[rta_transform_insts_supply_def] >> rpt gen_tac >>
  Cases_on `rta_transform_inst_supply fn s h` >> simp[] >>
  rename1 `rta_transform_insts_supply fn s1 xs` >>
  Cases_on `rta_transform_insts_supply fn s1 xs` >> simp[] >>
  rename1 `rta_transform_insts_supply fn s2 ys` >>
  Cases_on `rta_transform_insts_supply fn s2 ys` >> simp[]
QED

Theorem rta_transform_blocks_supply_insts:
  !bbs s bbs' s'.
    rta_transform_blocks_supply fn s bbs = (bbs',s') ==>
    rta_transform_insts_supply fn s (fn_insts_blocks bbs) =
      (fn_insts_blocks bbs',s')
Proof
  Induct >> simp[rta_transform_blocks_supply_def, rta_transform_insts_supply_def,
                 fn_insts_blocks_def] >>
  rpt gen_tac >> Cases_on `rta_transform_insts_supply fn s h.bb_instructions` >>
  rename1 `rta_transform_insts_supply fn s h.bb_instructions = (is1,s1)` >>
  Cases_on `rta_transform_blocks_supply fn s1 bbs` >>
  rename1 `rta_transform_blocks_supply fn s1 bbs = (bbs1,s2)` >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  gvs[fn_insts_blocks_def, rta_transform_insts_supply_append]
QED

Theorem rta_transform_blocks_supply_rel:
  !bbs s bbs' s'.
    rta_transform_blocks_supply fn s bbs = (bbs',s') ==>
    LIST_REL (\bb bb'. bb'.bb_label = bb.bb_label /\
                       ?s1 s2. rta_transform_insts_supply fn s1 bb.bb_instructions =
                               (bb'.bb_instructions,s2)) bbs bbs'
Proof
  Induct >> simp[rta_transform_blocks_supply_def] >>
  rpt gen_tac >> Cases_on `rta_transform_insts_supply fn s h.bb_instructions` >>
  rename1 `rta_transform_insts_supply fn s h.bb_instructions = (is1,s1)` >>
  Cases_on `rta_transform_blocks_supply fn s1 bbs` >>
  rename1 `rta_transform_blocks_supply fn s1 bbs = (bbs1,s2)` >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem rta_list_rel_labels[local]:
  !xs ys.
    LIST_REL (\bb bb'. bb'.bb_label = bb.bb_label /\
                       ?s1 s2. rta_transform_insts_supply fn s1 bb.bb_instructions =
                               (bb'.bb_instructions,s2)) xs ys ==>
          MAP (\bb. bb.bb_label) ys = MAP (\bb. bb.bb_label) xs
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* ===== Function-level obligations ===== *)

Theorem rta_transform_function_supply_ssa_form:
  !s fn. ssa_form fn /\ ir_supply_covers_fn s fn ==>
         ssa_form (FST (rta_transform_function_supply s fn))
Proof
  rpt strip_tac >> simp[rta_transform_function_supply_def] >>
  Cases_on `rta_transform_blocks_supply fn s fn.fn_blocks` >> simp[] >>
  drule rta_transform_blocks_supply_insts >> strip_tac >>
  drule rta_transform_insts_supply_fresh >> simp[ir_fresh_ext_def] >>
  strip_tac >> gvs[ssa_form_def, fn_insts_def] >>
  first_x_assum irule >> simp[] >>
  gvs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM, fn_ir_vars_def] >>
  metis_tac[fn_insts_blocks_outputs_ir_vars]
QED

Theorem rta_transform_function_supply_wf_function:
  !s fn. wf_function fn /\ ir_supply_inst_ok s /\ ir_supply_covers_fn s fn ==>
         wf_function (FST (rta_transform_function_supply s fn))
Proof
  rpt strip_tac >> simp[rta_transform_function_supply_def] >>
  Cases_on `rta_transform_blocks_supply fn s fn.fn_blocks` >> simp[] >>
  rename1 `_ = (bbs',s')` >>
  drule rta_transform_blocks_supply_rel >> strip_tac >>
  `MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) fn.fn_blocks` by
    (drule rta_list_rel_labels >> simp[]) >>
  `!bb'. MEM bb' bbs' ==>
         bb_well_formed bb' /\
         ?bb. MEM bb fn.fn_blocks /\
              !l. MEM l (bb_succs bb') ==> MEM l (bb_succs bb)` by
    (rpt strip_tac >>
     drule_all LIST_REL_MEM_IMP_R >> strip_tac >> gvs[] >>
     `bb_well_formed x` by gvs[wf_function_def] >>
     drule_all rta_transform_insts_supply_bb_well_formed >> metis_tac[]) >>
  gvs[wf_function_def, fn_labels_def, fn_has_entry_def] >>
  `bbs' <> []` by (strip_tac >> gvs[]) >>
  `!bb'. MEM bb' bbs' ==> bb_well_formed bb'` by metis_tac[] >>
  `fn_succs_closed (fn with fn_blocks := bbs')` by
    (gvs[fn_succs_closed_def, fn_labels_def] >> metis_tac[]) >>
  simp[] >>
  drule rta_transform_blocks_supply_insts >> strip_tac >>
  drule rta_transform_insts_supply_fresh >> simp[ir_fresh_ext_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `ALL_DISTINCT (MAP _ (fn_insts_blocks fn.fn_blocks)) /\ _ ==> _`
    mp_tac >>
  fs[fn_inst_ids_distinct_def, blocks_inst_ids_flat, fn_insts_blocks_inst_ids,
     ir_supply_covers_fn_def, list_subset_def, EVERY_MEM, fn_ir_inst_ids_def]
QED
