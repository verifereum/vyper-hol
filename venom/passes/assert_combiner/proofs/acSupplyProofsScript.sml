(*
 * Assert Combiner — structural properties of the supply-threaded transform.
 *
 * Each instruction becomes itself, a NOP (a first assert), or, when two
 * asserts merge, an OR and an ISZERO followed by the NOP or by the assert
 * rewritten to test the ISZERO output. The OR/ISZERO ids and outputs come
 * fresh from the supply, so ids stay distinct and SSA form holds; the
 * OR's operands are the asserts' iszero sources, operands of the function,
 * so the new supply still covers the function.
 *)

Theory acSupplyProofs
Ancestors
  acChainProofs assertCombinerDefs irSupplyFreshProps irSupply
  venomFnScheduleRunner fmpStepChunk fmpStepList dfgAnalysisProps
  passSharedDefs venomInstIdsProps venomWf venomInst alist list
Libs
  listTheory

(* ===== One instruction ===== *)

Theorem ac_merge_inst_cases:
  ac_merge_inst cands mp su inst = (mp',out,su') ==>
  (su' = su /\
   out = [if EXISTS (\mc. mc.mc_first_id = inst.inst_id) cands then
            inst with <| inst_opcode := NOP; inst_operands := [];
                         inst_outputs := [] |>
          else inst]) \/
  (?mc p1 or_id s1 or_v s2 iz_id s3 iz_v.
     MEM mc cands /\ mc.mc_second_id = inst.inst_id /\
     (p1 = mc.mc_first_pred \/ ALOOKUP mp mc.mc_first_id = SOME p1) /\
     fresh_inst_id su = (or_id,s1) /\ fresh_ir_var s1 = (or_v,s2) /\
     fresh_inst_id s2 = (iz_id,s3) /\ fresh_ir_var s3 = (iz_v,su') /\
     out = [<| inst_id := or_id; inst_opcode := OR;
               inst_operands := [p1; mc.mc_second_pred];
               inst_outputs := [or_v] |>;
            <| inst_id := iz_id; inst_opcode := ISZERO;
               inst_operands := [Var or_v]; inst_outputs := [iz_v] |>;
            if EXISTS (\mc. mc.mc_first_id = inst.inst_id) cands then
              inst with <| inst_opcode := NOP; inst_operands := [];
                           inst_outputs := [] |>
            else inst with inst_operands := [Var iz_v]])
Proof
  simp[ac_merge_inst_def] >>
  Cases_on `FIND (\mc. mc.mc_second_id = inst.inst_id) cands` >> simp[]
  >- (rw[] >> simp[]) >>
  rename1 `FIND _ _ = SOME mc` >>
  `MEM mc cands /\ mc.mc_second_id = inst.inst_id` by
    (imp_res_tac FIND_MEM >> imp_res_tac FIND_P >> fs[]) >>
  Cases_on `ALOOKUP mp mc.mc_first_id` >> simp[] >>
  pairarg_tac >> gvs[] >>
  BasicProvers.every_case_tac >> rpt strip_tac >> gvs[] >>
  TRY DISJ2_TAC >> qexists_tac `mc` >> simp[]
QED

Theorem ac_merge_inst_nonempty:
  ac_merge_inst cands mp su inst = (mp',out,su') ==> out <> []
Proof
  strip_tac >> drule ac_merge_inst_cases >> strip_tac >> gvs[]
QED

Theorem ac_merge_inst_fresh:
  ac_merge_inst cands mp su inst = (mp',out,su') ==>
  ir_supply_extends su su' /\
  ir_fresh_ext su.irs_used_vars su'.irs_used_vars inst.inst_outputs
    (FLAT (MAP (\i. i.inst_outputs) out)) /\
  (ir_supply_inst_ok su ==>
   ir_supply_inst_ok su' /\
   ir_fresh_ext su.irs_used_inst_ids su'.irs_used_inst_ids [inst.inst_id]
     (MAP (\i. i.inst_id) out))
Proof
  strip_tac >> drule ac_merge_inst_cases >> strip_tac
  >- (gvs[ir_supply_extends_refl] >> rw[] >> simp[ir_fresh_ext_def]) >>
  `ir_supply_extends su su'` by
    (imp_res_tac fresh_inst_id_ir_supply_extends >>
     imp_res_tac fresh_ir_var_ir_supply_extends >>
     irule ir_supply_extends_trans >> qexists_tac `s3` >> simp[] >>
     irule ir_supply_extends_trans >> qexists_tac `s2` >> simp[] >>
     irule ir_supply_extends_trans >> qexists_tac `s1` >> simp[]) >>
  `~MEM or_v s1.irs_used_vars /\ s2.irs_used_vars = or_v :: s1.irs_used_vars /\
   s2.irs_next_inst = s1.irs_next_inst /\
   s2.irs_used_inst_ids = s1.irs_used_inst_ids` by
    (qpat_x_assum `fresh_ir_var s1 = _` mp_tac >> rpt (pop_assum kall_tac) >>
     strip_tac >> drule fresh_ir_var_contract >> simp[]) >>
  `~MEM iz_v s3.irs_used_vars /\ su'.irs_used_vars = iz_v :: s3.irs_used_vars /\
   su'.irs_next_inst = s3.irs_next_inst /\
   su'.irs_used_inst_ids = s3.irs_used_inst_ids` by
    (qpat_x_assum `fresh_ir_var s3 = _` mp_tac >> rpt (pop_assum kall_tac) >>
     strip_tac >> drule fresh_ir_var_contract >> simp[]) >>
  gvs[fresh_inst_id_def] >>
  (conj_tac >- (rw[ir_fresh_ext_def] >> gvs[] >> metis_tac[]) >>
   simp[ir_supply_inst_ok_def, EVERY_MEM] >> strip_tac >>
   `~MEM su.irs_next_inst su.irs_used_inst_ids /\
    ~MEM s2.irs_next_inst su.irs_used_inst_ids` by
     (rpt strip_tac >> res_tac >> fs[]) >>
   rw[ir_fresh_ext_def] >> gvs[] >> rpt strip_tac >> res_tac >> fs[])
QED

(* Under the premise that merge candidates name only ASSERTs, every
   instruction other than an ASSERT is kept as is, and an ASSERT becomes
   instructions that are neither PHIs nor terminators. *)
Theorem ac_merge_inst_shape:
  ac_merge_inst cands mp su inst = (mp',out,su') /\
  (!mc. MEM mc cands /\
        (mc.mc_first_id = inst.inst_id \/ mc.mc_second_id = inst.inst_id) ==>
        inst.inst_opcode = ASSERT) ==>
  out = [inst] \/
  (inst.inst_opcode = ASSERT /\
   EVERY (\j. j.inst_opcode <> PHI /\ ~is_terminator j.inst_opcode) out /\
   (inst_wf inst ==> EVERY inst_wf out))
Proof
  strip_tac >> drule ac_merge_inst_cases >> strip_tac >> gvs[]
  >- (rw[] >> gvs[EXISTS_MEM] >> res_tac >>
      simp[is_terminator_def, inst_wf_def]) >>
  `inst.inst_opcode = ASSERT` by metis_tac[] >>
  rw[] >> gvs[is_terminator_def, inst_wf_def]
QED

(* ===== Instruction lists ===== *)

Theorem ac_merge_insts_fresh:
  !insts cands mp su out su'.
    ac_merge_insts cands mp su insts = (out,su') ==>
    ir_supply_extends su su' /\
    ir_fresh_ext su.irs_used_vars su'.irs_used_vars
      (FLAT (MAP (\i. i.inst_outputs) insts))
      (FLAT (MAP (\i. i.inst_outputs) out)) /\
    (ir_supply_inst_ok su ==>
     ir_supply_inst_ok su' /\
     ir_fresh_ext su.irs_used_inst_ids su'.irs_used_inst_ids
       (MAP (\i. i.inst_id) insts) (MAP (\i. i.inst_id) out))
Proof
  Induct
  >- simp[ac_merge_insts_def, ir_fresh_ext_refl, ir_supply_extends_refl] >>
  rpt gen_tac >> simp[ac_merge_insts_def] >>
  Cases_on `ac_merge_inst cands mp su h` >> rename1 `_ = (mp1,r)` >>
  Cases_on `r` >> rename1 `_ = (mp1,o1,s1)` >>
  Cases_on `ac_merge_insts cands mp1 s1 insts` >>
  rename1 `ac_merge_insts cands mp1 s1 insts = (outs,s2)` >>
  simp[] >> strip_tac >> gvs[] >>
  drule ac_merge_inst_fresh >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  conj_tac >- metis_tac[ir_supply_extends_trans] >>
  conj_tac
  >- (simp[MAP_APPEND, FLAT_APPEND] >>
      irule ir_fresh_ext_append >> metis_tac[]) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `ir_fresh_ext su.irs_used_inst_ids _ _ _` (fn th1 =>
    qpat_x_assum `ir_fresh_ext s1.irs_used_inst_ids _ _ _` (fn th2 =>
      mp_tac (MATCH_MP ir_fresh_ext_append (CONJ th1 th2)))) >>
  simp[MAP_APPEND]
QED

Theorem ac_merge_insts_nonempty:
  !insts cands mp su out su'.
    ac_merge_insts cands mp su insts = (out,su') ==>
    (out = [] <=> insts = [])
Proof
  Induct >> simp[ac_merge_insts_def] >>
  rpt gen_tac >> Cases_on `ac_merge_inst cands mp su h` >>
  rename1 `_ = (mp1,r)` >> Cases_on `r` >> rename1 `_ = (mp1,o1,s1)` >>
  Cases_on `ac_merge_insts cands mp1 s1 insts` >>
  simp[] >> strip_tac >> gvs[] >>
  drule ac_merge_inst_nonempty >> simp[]
QED

Theorem ac_merge_insts_shape:
  !insts cands mp su out su'.
    ac_merge_insts cands mp su insts = (out,su') /\
    (!inst mc. MEM inst insts /\ MEM mc cands /\
       (mc.mc_first_id = inst.inst_id \/ mc.mc_second_id = inst.inst_id) ==>
       inst.inst_opcode = ASSERT) ==>
    (EVERY (\j. j.inst_opcode <> PHI) insts ==>
     EVERY (\j. j.inst_opcode <> PHI) out) /\
    (list_prefix (\j. j.inst_opcode = PHI) insts ==>
     list_prefix (\j. j.inst_opcode = PHI) out) /\
    (list_terminal (\j. is_terminator j.inst_opcode) insts ==>
     list_terminal (\j. is_terminator j.inst_opcode) out /\
     LAST out = LAST insts) /\
    (EVERY inst_wf insts ==> EVERY inst_wf out)
Proof
  Induct >> simp[ac_merge_insts_def] >>
  rpt gen_tac >> Cases_on `ac_merge_inst cands mp su h` >>
  rename1 `_ = (mp1,r)` >> Cases_on `r` >> rename1 `_ = (mp1,o1,s1)` >>
  Cases_on `ac_merge_insts cands mp1 s1 insts` >>
  rename1 `ac_merge_insts cands mp1 s1 insts = (outs,s2)` >>
  simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> impl_tac >- metis_tac[] >> strip_tac >>
  `outs = [] <=> insts = []` by metis_tac[ac_merge_insts_nonempty] >>
  drule ac_merge_inst_shape >> impl_tac >- metis_tac[] >> strip_tac >> gvs[]
  >- (rw[list_prefix_def] >> gvs[] >>
      Cases_on `insts = []` >> gvs[list_terminal_def, LAST_CONS_cond]) >>
  `o1 <> []` by metis_tac[ac_merge_inst_nonempty] >>
  `EVERY (\j. j.inst_opcode <> PHI) o1 /\
   EVERY (\j. ~is_terminator j.inst_opcode) o1` by gvs[EVERY_MEM] >>
  rpt conj_tac
  >- (strip_tac >> gvs[EVERY_APPEND])
  >- (strip_tac >> gvs[list_prefix_def, list_prefix_append, list_prefix_none])
  >- (strip_tac >>
      Cases_on `insts = []` >- gvs[list_terminal_def, is_terminator_def] >>
      gvs[list_terminal_def, list_terminal_append, LAST_CONS_cond,
          rich_listTheory.LAST_APPEND_NOT_NIL]) >>
  strip_tac >> gvs[EVERY_APPEND]
QED

(* ===== Blocks ===== *)

Theorem ac_mem_same_id[local]:
  !l x y. ALL_DISTINCT (MAP (\i. i.inst_id) l) /\ MEM x l /\ MEM y l /\
          x.inst_id = y.inst_id ==> x = y
Proof
  Induct >> simp[] >> rw[] >> gvs[MEM_MAP] >> metis_tac[]
QED

(* Merge candidates name only ASSERTs of the block. *)
Theorem ac_scan_names_asserts:
  ALL_DISTINCT (MAP (\i. i.inst_id) insts) ==>
  !inst mc. MEM inst insts /\ MEM mc (ac_scan_block dfg insts NONE) /\
    (mc.mc_first_id = inst.inst_id \/ mc.mc_second_id = inst.inst_id) ==>
    inst.inst_opcode = ASSERT
Proof
  rpt strip_tac
  >- (drule ac_scan_first_is_assert >> strip_tac >> gvs[] >>
      `inst' = inst` by metis_tac[ac_mem_same_id] >> gvs[]) >>
  drule ac_scan_second_is_assert >> strip_tac >> gvs[] >>
  `inst' = inst` by metis_tac[ac_mem_same_id] >> gvs[]
QED

Theorem ac_transform_block_label:
  ac_transform_block dfg su bb = (bb',su') ==> bb'.bb_label = bb.bb_label
Proof
  simp[ac_transform_block_def] >>
  Cases_on `ac_merge_insts (ac_scan_block dfg bb.bb_instructions NONE) []
              su bb.bb_instructions` >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem ac_transform_block_shape:
  ac_transform_block dfg su bb = (bb',su') /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
  (bb_well_formed bb ==> bb_well_formed bb' /\ bb_succs bb' = bb_succs bb) /\
  (EVERY inst_wf bb.bb_instructions ==> EVERY inst_wf bb'.bb_instructions)
Proof
  simp[ac_transform_block_def] >>
  Cases_on `ac_merge_insts (ac_scan_block dfg bb.bb_instructions NONE) []
              su bb.bb_instructions` >>
  simp[] >> strip_tac >> gvs[] >>
  drule ac_merge_insts_shape >>
  impl_tac >- metis_tac[ac_scan_names_asserts] >>
  strip_tac >> simp[] >> strip_tac >>
  gvs[bb_well_formed_list] >>
  `bb.bb_instructions <> []` by (strip_tac >> gvs[list_terminal_def]) >>
  `q <> []` by metis_tac[ac_merge_insts_nonempty] >>
  simp[bb_succs_def] >>
  Cases_on `q` >> Cases_on `bb.bb_instructions` >> gvs[]
QED

Theorem ac_transform_blocks_rel:
  !bbs su bbs' su'.
    ac_transform_blocks dfg su bbs = (bbs',su') ==>
    LIST_REL (\bb bb'. ?s1 s2. ac_transform_block dfg s1 bb = (bb',s2)) bbs bbs'
Proof
  Induct >> simp[ac_transform_blocks_def] >> rpt gen_tac >>
  Cases_on `ac_transform_block dfg su h` >>
  Cases_on `ac_transform_blocks dfg r bbs` >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ac_transform_blocks_fresh:
  !bbs su bbs' su'.
    ac_transform_blocks dfg su bbs = (bbs',su') ==>
    ir_supply_extends su su' /\
    ir_fresh_ext su.irs_used_vars su'.irs_used_vars
      (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)))
      (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs'))) /\
    (ir_supply_inst_ok su ==>
     ir_supply_inst_ok su' /\
     ir_fresh_ext su.irs_used_inst_ids su'.irs_used_inst_ids
       (MAP (\i. i.inst_id) (fn_insts_blocks bbs))
       (MAP (\i. i.inst_id) (fn_insts_blocks bbs')))
Proof
  Induct
  >- simp[ac_transform_blocks_def, fn_insts_blocks_def, ir_fresh_ext_refl,
          ir_supply_extends_refl] >>
  rpt gen_tac >> simp[ac_transform_blocks_def] >>
  Cases_on `ac_transform_block dfg su h` >> rename1 `_ = (bb1,s1)` >>
  Cases_on `ac_transform_blocks dfg s1 bbs` >> rename1 `_ = (bbs1,s2)` >>
  simp[] >> strip_tac >> gvs[fn_insts_blocks_def] >>
  qpat_x_assum `ac_transform_block _ _ _ = _` mp_tac >>
  simp[ac_transform_block_def] >>
  Cases_on `ac_merge_insts (ac_scan_block dfg h.bb_instructions NONE) []
              su h.bb_instructions` >>
  simp[] >> strip_tac >> gvs[] >>
  drule ac_merge_insts_fresh >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  conj_tac >- metis_tac[ir_supply_extends_trans] >>
  conj_tac
  >- (simp[MAP_APPEND, FLAT_APPEND] >> irule ir_fresh_ext_append >>
      metis_tac[]) >>
  strip_tac >> gvs[] >>
  simp[MAP_APPEND] >> irule ir_fresh_ext_append >> metis_tac[]
QED

Theorem ac_list_rel_labels[local]:
  !xs ys.
    LIST_REL (\bb bb'. ?s1 s2. ac_transform_block dfg s1 bb = (bb',s2)) xs ys ==>
    MAP (\bb. bb.bb_label) ys = MAP (\bb. bb.bb_label) xs
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[] >>
  metis_tac[ac_transform_block_label]
QED

(* ===== Function-level obligations ===== *)

Theorem ac_transform_function_ssa_form:
  !su fn. ssa_form fn /\ ir_supply_covers_fn su fn ==>
          ssa_form (FST (ac_transform_function su fn))
Proof
  rpt strip_tac >> simp[ac_transform_function_def] >>
  Cases_on `ac_transform_blocks (dfg_build_function fn) su fn.fn_blocks` >>
  simp[] >>
  drule ac_transform_blocks_fresh >> simp[ir_fresh_ext_def] >>
  strip_tac >> gvs[ssa_form_def, fn_insts_def] >>
  first_x_assum irule >> simp[] >>
  gvs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM, fn_ir_vars_def] >>
  metis_tac[fn_insts_blocks_outputs_ir_vars]
QED

(* Each transformed block comes from a block of fn by ac_transform_block. *)
Theorem ac_transform_function_blocks[local]:
  ac_transform_blocks (dfg_build_function fn) su fn.fn_blocks = (bbs',su') /\
  MEM bb' bbs' ==>
  ?bb s1 s2. MEM bb fn.fn_blocks /\
             ac_transform_block (dfg_build_function fn) s1 bb = (bb',s2)
Proof
  strip_tac >> drule ac_transform_blocks_rel >> strip_tac >>
  drule_all LIST_REL_MEM_IMP_R >> metis_tac[]
QED

Theorem ac_transform_function_wf_function:
  !su fn. wf_function fn /\ ir_supply_inst_ok su /\ ir_supply_covers_fn su fn ==>
          wf_function (FST (ac_transform_function su fn))
Proof
  rpt strip_tac >> simp[ac_transform_function_def] >>
  Cases_on `ac_transform_blocks (dfg_build_function fn) su fn.fn_blocks` >>
  simp[] >> rename1 `_ = (bbs',su')` >>
  `MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) fn.fn_blocks` by
    (irule ac_list_rel_labels >> metis_tac[ac_transform_blocks_rel]) >>
  `!bb'. MEM bb' bbs' ==>
         bb_well_formed bb' /\
         ?bb. MEM bb fn.fn_blocks /\ bb_succs bb' = bb_succs bb` by
    (rpt gen_tac >> strip_tac >>
     drule_all ac_transform_function_blocks >> strip_tac >>
     drule ac_transform_block_shape >>
     impl_tac >- metis_tac[fn_inst_ids_distinct_block, wf_function_def] >>
     gvs[wf_function_def] >> metis_tac[]) >>
  gvs[wf_function_def, fn_labels_def, fn_has_entry_def] >>
  `bbs' <> []` by (strip_tac >> gvs[]) >>
  `fn_succs_closed (fn with fn_blocks := bbs')` by
    (gvs[fn_succs_closed_def, fn_labels_def] >> metis_tac[]) >>
  simp[] >>
  drule ac_transform_blocks_fresh >> simp[ir_fresh_ext_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `ALL_DISTINCT (MAP _ (fn_insts_blocks fn.fn_blocks)) /\ _ ==> _`
    mp_tac >>
  fs[fn_inst_ids_distinct_def, blocks_inst_ids_flat, fn_insts_blocks_inst_ids,
     ir_supply_covers_fn_def, list_subset_def, EVERY_MEM, fn_ir_inst_ids_def]
QED

Theorem ac_transform_function_fn_inst_wf:
  !su fn. wf_function fn /\ fn_inst_wf fn ==>
          fn_inst_wf (FST (ac_transform_function su fn))
Proof
  rpt strip_tac >> simp[ac_transform_function_def] >>
  Cases_on `ac_transform_blocks (dfg_build_function fn) su fn.fn_blocks` >>
  simp[fn_inst_wf_def] >> rpt strip_tac >>
  drule_all ac_transform_function_blocks >> strip_tac >>
  drule ac_transform_block_shape >>
  impl_tac >- metis_tac[fn_inst_ids_distinct_block, wf_function_def] >>
  gvs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]
QED


(* ===== Operands and supply coverage ===== *)

(* An iszero source is an operand of the ISZERO the DFG found. *)
Theorem ac_get_iszero_operand_src:
  !dfg vis op p. ac_get_iszero_operand dfg vis op = SOME p ==>
    ?v i. dfg_get_def dfg v = SOME i /\ MEM p i.inst_operands
Proof
  ho_match_mp_tac ac_get_iszero_operand_ind >> rpt gen_tac >> strip_tac >>
  simp[Once ac_get_iszero_operand_def] >>
  BasicProvers.every_case_tac >> rw[] >> gvs[] >> metis_tac[MEM]
QED

Theorem ac_scan_block_preds:
  !dfg insts pending mc Q.
    MEM mc (ac_scan_block dfg insts pending) /\
    (!id p. pending = SOME (id,p) ==> Q p) /\
    (!op p. ac_get_iszero_operand dfg {} op = SOME p ==> Q p) ==>
    Q mc.mc_first_pred /\ Q mc.mc_second_pred
Proof
  Induct_on `insts` >> simp[ac_scan_block_def] >> rpt gen_tac >>
  rw[] >> BasicProvers.every_case_tac >> gvs[] >>
  TRY (first_x_assum (drule_then (qspec_then `Q` mp_tac)) >>
       impl_tac >- (rw[] >> res_tac >> fs[]) >> simp[] >> NO_TAC) >>
  res_tac >> fs[]
QED

Theorem ac_merge_inst_operands:
  ac_merge_inst cands mp su inst = (mp',out,su') ==>
  (!k p. MEM (k,p) mp' ==>
     (?k'. MEM (k',p) mp) \/ (?mc. MEM mc cands /\ p = mc.mc_first_pred) \/
     ?x. p = Var x /\ MEM x su'.irs_used_vars) /\
  (!j op. MEM j out /\ MEM op j.inst_operands ==>
     MEM op inst.inst_operands \/ (?k. MEM (k,op) mp) \/
     (?mc. MEM mc cands /\ (op = mc.mc_first_pred \/ op = mc.mc_second_pred)) \/
     ?x. op = Var x /\ MEM x su'.irs_used_vars)
Proof
  simp[ac_merge_inst_def] >>
  Cases_on `FIND (\mc. mc.mc_second_id = inst.inst_id) cands` >> simp[]
  >- (rw[] >> gvs[] >> metis_tac[]) >>
  rename1 `FIND _ _ = SOME mc` >>
  `MEM mc cands` by imp_res_tac FIND_MEM >>
  Cases_on `ALOOKUP mp mc.mc_first_id` >> simp[] >>
  imp_res_tac ALOOKUP_MEM >>
  pairarg_tac >> gvs[] >>
  BasicProvers.every_case_tac >> gvs[fresh_inst_id_def] >>
  imp_res_tac fresh_ir_var_contract >> gvs[] >>
  rw[] >> gvs[] >> metis_tac[]
QED

Theorem ac_merge_insts_operands:
  !insts cands mp su out su' P.
    ac_merge_insts cands mp su insts = (out,su') /\
    (!mc. MEM mc cands ==> P mc.mc_first_pred /\ P mc.mc_second_pred) /\
    (!k p. MEM (k,p) mp ==> P p \/ ?x. p = Var x /\ MEM x su.irs_used_vars) ==>
    !j op. MEM j out /\ MEM op j.inst_operands ==>
      (?i. MEM i insts /\ MEM op i.inst_operands) \/ P op \/
      ?x. op = Var x /\ MEM x su'.irs_used_vars
Proof
  Induct >> simp[ac_merge_insts_def] >>
  rpt gen_tac >> Cases_on `ac_merge_inst cands mp su h` >>
  rename1 `_ = (mp1,r)` >> Cases_on `r` >> rename1 `_ = (mp1,o1,s1)` >>
  Cases_on `ac_merge_insts cands mp1 s1 insts` >>
  rename1 `ac_merge_insts cands mp1 s1 insts = (outs,s2)` >>
  simp[] >> strip_tac >> gvs[] >>
  drule ac_merge_inst_operands >> strip_tac >>
  drule ac_merge_inst_fresh >> strip_tac >>
  drule ac_merge_insts_fresh >> strip_tac >>
  `!x. MEM x su.irs_used_vars ==> MEM x s1.irs_used_vars` by
    gvs[ir_supply_extends_def, list_subset_def, EVERY_MEM] >>
  `!x. MEM x s1.irs_used_vars ==> MEM x s2.irs_used_vars` by
    gvs[ir_supply_extends_def, list_subset_def, EVERY_MEM] >>
  first_x_assum (qspecl_then [`cands`, `mp1`, `s1`, `outs`, `s2`, `P`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  strip_tac >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ac_transform_blocks_operands:
  !bbs su bbs' su' P.
    ac_transform_blocks dfg su bbs = (bbs',su') /\
    (!bb mc. MEM bb bbs /\ MEM mc (ac_scan_block dfg bb.bb_instructions NONE) ==>
             P mc.mc_first_pred /\ P mc.mc_second_pred) ==>
    !j op. MEM j (fn_insts_blocks bbs') /\ MEM op j.inst_operands ==>
      (?i. MEM i (fn_insts_blocks bbs) /\ MEM op i.inst_operands) \/ P op \/
      ?x. op = Var x /\ MEM x su'.irs_used_vars
Proof
  Induct >> simp[ac_transform_blocks_def, fn_insts_blocks_def] >>
  rpt gen_tac >> Cases_on `ac_transform_block dfg su h` >>
  rename1 `_ = (bb1,s1)` >>
  Cases_on `ac_transform_blocks dfg s1 bbs` >> rename1 `_ = (bbs1,s2)` >>
  simp[] >> strip_tac >> gvs[fn_insts_blocks_def] >>
  qpat_x_assum `ac_transform_block _ _ _ = _` mp_tac >>
  simp[ac_transform_block_def] >>
  Cases_on `ac_merge_insts (ac_scan_block dfg h.bb_instructions NONE) []
              su h.bb_instructions` >>
  simp[] >> strip_tac >> gvs[] >>
  qspecl_then [`h.bb_instructions`, `ac_scan_block dfg h.bb_instructions NONE`,
               `[]`, `su`, `q`, `r`, `P`] mp_tac ac_merge_insts_operands >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  drule ac_transform_blocks_fresh >> strip_tac >>
  `!x. MEM x r.irs_used_vars ==> MEM x s2.irs_used_vars` by
    gvs[ir_supply_extends_def, list_subset_def, EVERY_MEM] >>
  first_x_assum (qspecl_then [`r`, `bbs1`, `s2`, `P`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ac_transform_function_supply:
  !su fn. ir_supply_inst_ok su /\ ir_supply_covers_fn su fn ==>
    ir_supply_inst_ok (SND (ac_transform_function su fn)) /\
    ir_supply_extends su (SND (ac_transform_function su fn)) /\
    ir_supply_covers_fn (SND (ac_transform_function su fn))
                        (FST (ac_transform_function su fn))
Proof
  rpt gen_tac >> strip_tac >> simp[ac_transform_function_def] >>
  Cases_on `ac_transform_blocks (dfg_build_function fn) su fn.fn_blocks` >>
  rename1 `_ = (bbs',su')` >> simp[] >>
  drule ac_transform_blocks_fresh >> strip_tac >> gvs[] >>
  `!bb mc. MEM bb fn.fn_blocks /\
           MEM mc (ac_scan_block (dfg_build_function fn) bb.bb_instructions NONE) ==>
           (?i. MEM i (fn_insts fn) /\ MEM mc.mc_first_pred i.inst_operands) /\
           (?i. MEM i (fn_insts fn) /\ MEM mc.mc_second_pred i.inst_operands)` by
    (rpt gen_tac >> strip_tac >>
     qspecl_then [`dfg_build_function fn`, `bb.bb_instructions`, `NONE`, `mc`,
                  `\op. ?i. MEM i (fn_insts fn) /\ MEM op i.inst_operands`]
       mp_tac ac_scan_block_preds >>
     simp[] >> disch_then irule >> rpt strip_tac >>
     drule ac_get_iszero_operand_src >> strip_tac >>
     drule dfg_build_function_correct >> metis_tac[]) >>
  qspecl_then [`fn.fn_blocks`, `su`, `bbs'`, `su'`,
               `\op. ?i. MEM i (fn_insts fn) /\ MEM op i.inst_operands`]
    mp_tac (Q.GEN `dfg` ac_transform_blocks_operands |> Q.SPEC `dfg_build_function fn`) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  simp[] >> strip_tac >>
  `MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) fn.fn_blocks` by
    (irule ac_list_rel_labels >> metis_tac[ac_transform_blocks_rel]) >>
  `!j op. MEM j (fn_insts_blocks bbs') /\ MEM op j.inst_operands ==>
     (?i. MEM i (fn_insts fn) /\ MEM op i.inst_operands) \/
     ?x. op = Var x /\ MEM x su'.irs_used_vars` by
    (gvs[fn_insts_def] >> metis_tac[]) >>
  qpat_x_assum `ir_supply_covers_fn su fn` mp_tac >>
  simp[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM, fn_ir_inst_ids_def,
       fn_ir_vars_def, fn_ir_labels_def, GSYM fn_insts_blocks_inst_ids,
       blocks_ir_vars_flat, blocks_ir_labels_mem] >>
  strip_tac >>
  gvs[ir_supply_extends_def, ir_supply_inst_ok_def, ir_fresh_ext_def,
      list_subset_def, EVERY_MEM, GSYM fn_insts_def] >>
  fs[MEM_FLAT, MEM_MAP, PULL_EXISTS, inst_ir_vars_def, inst_uses_def,
     inst_ir_labels_def, MEM_operand_ir_labels, MEM_operand_vars_eq_Var] >>
  rpt conj_tac >> rpt strip_tac >> gvs[]
  >- (qpat_x_assum `!i. MEM i (fn_insts_blocks bbs') ==> _` drule >>
      strip_tac >> gvs[] >>
      qpat_x_assum `!x. MEM x su.irs_used_inst_ids ==> MEM x _` irule >>
      metis_tac[])
  >- (qpat_x_assum `!id. MEM id su'.irs_used_inst_ids ==> _` irule >>
      qpat_x_assum `!i. MEM i (fn_insts_blocks bbs') ==> _` drule >>
      strip_tac >> gvs[] >>
      qpat_x_assum `!x. MEM x su.irs_used_inst_ids ==> MEM x _` irule >>
      metis_tac[])
  >- (qpat_x_assum `!v i. MEM i (fn_insts_blocks bbs') /\ _ ==> _` drule_all >>
      strip_tac >> gvs[] >>
      qpat_x_assum `!x. MEM x su.irs_used_vars ==> MEM x _` irule >>
      qpat_x_assum `!x y. _ ==> MEM x su.irs_used_vars` irule >> metis_tac[])
  >- (qpat_x_assum `!j op. MEM j (fn_insts_blocks bbs') /\ _ ==> _` drule_all >>
      strip_tac >> gvs[] >>
      qpat_x_assum `!x. MEM x su.irs_used_vars ==> MEM x _` irule >>
      qpat_x_assum `!x y. _ ==> MEM x su.irs_used_vars` irule >> metis_tac[])
  >- (qpat_x_assum `!x. MEM x su.irs_used_labels ==> MEM x _` irule >>
      qpat_x_assum `!x. _ ==> MEM x su.irs_used_labels` irule >> metis_tac[])
  >> (qpat_x_assum `!j op. MEM j (fn_insts_blocks bbs') /\ _ ==> _` drule_all >>
      strip_tac >> gvs[] >>
      qpat_x_assum `!x. MEM x su.irs_used_labels ==> MEM x _` irule >>
      qpat_x_assum `!x. _ ==> MEM x su.irs_used_labels` irule >> metis_tac[])
QED
