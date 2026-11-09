(*
 * The syntactic half of MakeSSA's pointer discipline: the pass keeps
 * fn_ptr_ok P, of the function and of its reachable part.
 *)
Theory o1ContractMakeSsaPtrOk
Ancestors
  ptrDiscipline pointerConfinedDefs pointerConfinedProps unitShapeDefs
  venomInst venomWf cfgWf o1PassContract makeSsaDefs makeSsaCurrentProps
  makeSsaCurrentCfg makeSsaCurrentOrigin makeSsaCurrentWfSsa
  makeSsaCurrentInputOk makeSsaCurrentNonDegenerate
  allocaRemapSSA
  venomWfProps

Definition mssa_inst_origin_def:
  mssa_inst_origin orig fn inst' <=>
    (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode <> PHI /\
       inst'.inst_id = inst.inst_id /\
       inst'.inst_opcode = inst.inst_opcode /\
       MAP orig inst'.inst_outputs = inst.inst_outputs /\
       MAP (\op. case op of Var u => Var (orig u) | _ => op)
         inst'.inst_operands = inst.inst_operands) \/
    (inst'.inst_opcode = NOP /\ inst'.inst_outputs = [] /\
       inst'.inst_operands = []) \/
    ((inst'.inst_opcode = PHI \/ inst'.inst_opcode = ASSIGN) /\
     ?w inst. inst'.inst_outputs = [w] /\ MEM inst (fn_insts fn) /\
       MEM (orig w) inst.inst_outputs /\
       (inst'.inst_opcode = ASSIGN ==> ?u. inst'.inst_operands = [Var u]) /\
       (!op. MEM op inst'.inst_operands ==> ?x. op = Var x \/ op = Label x) /\
       !u. MEM (Var u) inst'.inst_operands ==>
         orig u = orig w \/
         (inst.inst_opcode = PHI /\ MEM (Var (orig u)) inst.inst_operands))
End

Theorem mssa_origin:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  ?orig. !inst. MEM inst (fn_insts fn') ==> mssa_inst_origin orig fn inst
Proof
  strip_tac >> rewrite_tac[mssa_inst_origin_def] >>
  irule make_ssa_current_fn_origin >>
  gvs[make_ssa_input_ok_def] >> metis_tac[]
QED

Theorem mssa_wf_ssa:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==> wf_ssa fn'
Proof
  strip_tac >> irule make_ssa_current_fn_wf_ssa >>
  gvs[make_ssa_input_ok_def] >> metis_tac[]
QED

Theorem mssa_no_entry_edge:
  wf_function fn /\ first_block_no_preds fn /\
  make_ssa_current_fn s fn = (fn',s') /\
  fn_entry_label fn' = SOME entry ==> !l. ~fn_cfg_edge fn' l entry
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[wf_function_def] >>
  drule_all make_ssa_current_fn_cfg >> strip_tac >>
  gvs[fn_entry_label_def, entry_block_def, AllCaseEqs()] >>
  gvs[first_block_no_preds_def, listTheory.EVERY_MEM, fn_cfg_edge_def] >>
  metis_tac[]
QED

Theorem mssa_phi_output:
  (!i. MEM i (fn_insts fn') ==> mssa_inst_origin orig fn i) /\
  MEM inst (fn_insts fn') /\ inst.inst_opcode = PHI ==>
  ?w. inst.inst_outputs = [w]
Proof
  strip_tac >> first_x_assum drule >>
  simp[mssa_inst_origin_def] >> metis_tac[]
QED

Theorem mssa_entry_no_phi:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\
  MEM bb fn'.fn_blocks /\ fn_entry_label fn' = SOME bb.bb_label ==>
  !inst. MEM inst bb.bb_instructions ==> inst.inst_opcode <> PHI
Proof
  strip_tac >>
  `?orig. !inst. MEM inst (fn_insts fn') ==> mssa_inst_origin orig fn inst` by
    (irule mssa_origin >> metis_tac[]) >>
  drule_all make_ssa_current_fn_input_ok >> strip_tac >>
  drule_all make_ssa_current_fn_phis_non_degenerate >> strip_tac >>
  `!l. ~fn_cfg_edge fn' l bb.bb_label` by
    (irule mssa_no_entry_edge >> metis_tac[]) >>
  rpt strip_tac >>
  `MEM inst (fn_insts fn')` by
    (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `?w. inst.inst_outputs = [w]` by
    (irule mssa_phi_output >> metis_tac[]) >>
  gvs[fn_phis_non_degenerate_def] >> metis_tac[]
QED

Theorem mssa_root_output:
  fn_inst_wf fn /\ mssa_inst_origin orig fn inst' /\
  (inst'.inst_opcode = ALLOCA \/ inst'.inst_opcode = DALLOCA \/
   inst'.inst_opcode = PARAM) ==>
  ?w. inst'.inst_outputs = [w]
Proof
  simp[mssa_inst_origin_def] >> rpt strip_tac >>
  gvs[fn_inst_wf_def, listTheory.EVERY_MEM,
      fn_insts_def, MEM_fn_insts_blocks_iff] >>
  first_x_assum drule_all >> simp[inst_wf_def] >>
  strip_tac >>
  `LENGTH inst'.inst_outputs = 1` by metis_tac[listTheory.LENGTH_MAP] >>
  Cases_on `inst'.inst_outputs` >> gvs[] >>
  rename1 `LENGTH rest = 0` >> Cases_on `rest` >> gvs[]
QED

Theorem mssa_path_take:
  !path n. is_fn_path fn path ==> is_fn_path fn (TAKE n path)
Proof
  Induct >> simp[] >> Cases_on `n` >> simp[] >>
  Cases_on `path` >> simp[is_fn_path_def] >> rpt strip_tac >>
  rename1 `is_fn_path fn (head::TAKE k (next::rest))` >>
  Cases_on `k` >> simp[is_fn_path_def] >>
  rename1 `is_fn_path fn (next::TAKE nn rest)` >>
  first_x_assum (qspec_then `SUC nn` mp_tac) >>
  simp[is_fn_path_def]
QED

Theorem mssa_path_prefix_at:
  is_fn_path fn path /\ k < LENGTH path ==>
  is_fn_path fn (TAKE (SUC k) path) /\
  TAKE (SUC k) path <> [] /\
  HD (TAKE (SUC k) path) = HD path /\
  LAST (TAKE (SUC k) path) = EL k path /\
  LENGTH (TAKE (SUC k) path) = SUC k
Proof
  strip_tac >> simp[mssa_path_take, listTheory.LENGTH_TAKE] >>
  `TAKE (SUC k) path <> []` by
    (Cases_on `path` >> gvs[]) >>
  simp[listTheory.LAST_EL, listTheory.LENGTH_TAKE, listTheory.EL_TAKE] >>
  Cases_on `path` >> gvs[]
QED

Theorem mssa_def_on_path:
  def_on_all_paths fn bb point v /\
  is_fn_path fn path /\ path <> [] /\
  fn_entry_label fn = SOME (HD path) /\ LAST path = bb.bb_label ==>
  (?pre db di. is_fn_path fn pre /\ pre <> [] /\
     HD pre = HD path /\ LENGTH pre < LENGTH path /\
     LAST pre = db.bb_label /\ MEM db fn.fn_blocks /\
     di < LENGTH db.bb_instructions /\
     MEM v (EL di db.bb_instructions).inst_outputs) \/
  (?i. i < LENGTH bb.bb_instructions /\
     MEM v (EL i bb.bb_instructions).inst_outputs /\
     case point of NONE => T | SOME inst =>
       ?j. i < j /\ j < LENGTH bb.bb_instructions /\
           EL j bb.bb_instructions = inst)
Proof
  strip_tac >>
  qpat_x_assum `def_on_all_paths _ _ _ _` mp_tac >>
  simp[def_on_all_paths_def] >>
  disch_then (qspec_then `path` mp_tac) >> simp[] >> strip_tac
  >- (disj1_tac >> rename1 `kk < LENGTH path - 1` >>
      rename1 `MEM defining_inst defining_bb.bb_instructions` >>
      `kk < LENGTH path` by decide_tac >>
      drule_all mssa_path_prefix_at >> strip_tac >>
      qexistsl_tac [`TAKE (SUC kk) path`, `defining_bb`] >> gvs[] >>
      qpat_x_assum `MEM defining_inst defining_bb.bb_instructions` mp_tac >>
      simp[listTheory.MEM_EL] >> strip_tac >>
      goal_assum (drule_at Any) >> gvs[] >> metis_tac[listTheory.MEM_EL]) >>
  disj2_tac >> goal_assum (drule_at Any) >> simp[]
QED

Theorem mssa_nonphi_earlier_def:
  fn_defs_reach_uses fn /\
  (EL j bb.bb_instructions).inst_opcode <> PHI /\
  MEM (Var v) (EL j bb.bb_instructions).inst_operands /\
  ssa_form fn /\ MEM bb fn.fn_blocks /\ j < LENGTH bb.bb_instructions /\
  MEM w (EL j bb.bb_instructions).inst_outputs /\
  is_fn_path fn path /\ path <> [] /\
  fn_entry_label fn = SOME (HD path) /\ LAST path = bb.bb_label ==>
  (?pre db di. is_fn_path fn pre /\ pre <> [] /\
     HD pre = HD path /\ LENGTH pre < LENGTH path /\
     LAST pre = db.bb_label /\ MEM db fn.fn_blocks /\
     di < LENGTH db.bb_instructions /\
     MEM v (EL di db.bb_instructions).inst_outputs) \/
  (?i. i < j /\ MEM v (EL i bb.bb_instructions).inst_outputs)
Proof
  strip_tac >>
  `MEM (EL j bb.bb_instructions) bb.bb_instructions` by
    simp[listTheory.EL_MEM] >>
  `def_on_all_paths fn bb (SOME (EL j bb.bb_instructions)) v` by
    (gvs[fn_defs_reach_uses_def] >> metis_tac[]) >>
  drule_all mssa_def_on_path >> simp[] >> strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >> rename1 `EL use_j bb.bb_instructions = EL j bb.bb_instructions` >>
  `use_j = j` by
    (irule ssa_form_no_dup_in_block >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     qexists_tac `fn` >> gvs[]) >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem mssa_end_def:
  def_on_all_paths fn bb NONE v /\ MEM bb fn.fn_blocks /\
  is_fn_path fn path /\ path <> [] /\
  fn_entry_label fn = SOME (HD path) /\ LAST path = bb.bb_label ==>
  ?pre db di. is_fn_path fn pre /\ pre <> [] /\
    HD pre = HD path /\ LENGTH pre <= LENGTH path /\
    LAST pre = db.bb_label /\ MEM db fn.fn_blocks /\
    di < LENGTH db.bb_instructions /\
    MEM v (EL di db.bb_instructions).inst_outputs
Proof
  strip_tac >> drule_all mssa_def_on_path >> simp[] >> strip_tac
  >- (goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
  qexistsl_tac [`path`, `bb`] >> simp[] >> metis_tac[]
QED

Theorem mssa_path_last_edge:
  !pre lbl. pre <> [] /\ is_fn_path fn (pre ++ [lbl]) ==>
  is_fn_path fn pre /\ fn_cfg_edge fn (LAST pre) lbl
Proof
  Induct >> simp[] >> Cases_on `pre` >> simp[is_fn_path_def] >>
  gvs[] >> metis_tac[]
QED

Theorem mssa_phi_earlier_def:
  fn_defs_reach_uses fn /\ fn_phis_cover_preds fn /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  inst.inst_opcode = PHI /\ q <> [] /\
  is_fn_path fn (q ++ [bb.bb_label]) /\
  fn_entry_label fn = SOME (HD q) ==>
  ?u pre db di.
    MEM (LAST q,u) (phi_pairs inst.inst_operands) /\
    is_fn_path fn pre /\ pre <> [] /\ HD pre = HD q /\
    LENGTH pre < LENGTH (q ++ [bb.bb_label]) /\
    LAST pre = db.bb_label /\ MEM db fn.fn_blocks /\
    di < LENGTH db.bb_instructions /\
    MEM u (EL di db.bb_instructions).inst_outputs
Proof
  strip_tac >> drule_all mssa_path_last_edge >> strip_tac >>
  `?u. MEM (LAST q,u) (phi_pairs inst.inst_operands)` by
    (gvs[fn_phis_cover_preds_def] >> metis_tac[]) >>
  `?pb. MEM pb fn.fn_blocks /\ pb.bb_label = LAST q` by
    (gvs[fn_cfg_edge_def] >> metis_tac[]) >>
  `def_on_all_paths fn pb NONE u` by
    (gvs[fn_defs_reach_uses_def] >> metis_tac[]) >>
  `LAST q = pb.bb_label` by simp[] >>
  drule_all mssa_end_def >> strip_tac >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

Theorem mssa_derived_initial:
  FINITE roots /\ v IN roots ==> v IN pointer_derived_vars fn roots
Proof
  simp[pointer_derived_vars_def] >> metis_tac[pointer_use_vars_initial,
    listTheory.MEM_SET_TO_LIST]
QED

Theorem mssa_derived_closed:
  MEM inst (fn_insts fn) /\ is_pointer_preserving_op inst.inst_opcode /\
  MEM (Var u) inst.inst_operands /\ u IN pointer_derived_vars fn roots /\
  MEM v inst.inst_outputs ==> v IN pointer_derived_vars fn roots
Proof
  simp[pointer_derived_vars_def, fn_insts_def, MEM_fn_insts_blocks_iff] >>
  metis_tac[pointer_use_vars_closed]
QED

Theorem mssa_derived_least:
  FINITE roots /\ roots SUBSET pv /\
  (!inst u v. MEM inst (fn_insts fn) /\
    is_pointer_preserving_op inst.inst_opcode /\
    MEM (Var u) inst.inst_operands /\ u IN pv /\
    MEM v inst.inst_outputs ==> v IN pv) ==>
  pointer_derived_vars fn roots SUBSET pv
Proof
  strip_tac >> simp[pointer_derived_vars_def, pred_setTheory.SUBSET_DEF] >>
  ho_match_mp_tac pointer_use_vars_least >>
  gvs[pred_setTheory.SUBSET_DEF, listTheory.MEM_SET_TO_LIST,
      fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]
QED

Theorem mssa_derived_producer:
  FINITE roots /\ v IN pointer_derived_vars fn roots ==>
  v IN roots \/ ?inst u. MEM inst (fn_insts fn) /\
    MEM v inst.inst_outputs /\ is_pointer_preserving_op inst.inst_opcode /\
    MEM (Var u) inst.inst_operands /\ u IN pointer_derived_vars fn roots
Proof
  simp[pointer_derived_vars_def] >> strip_tac >>
  drule pointer_use_vars_mem_char >>
  gvs[listTheory.MEM_SET_TO_LIST, fn_insts_def, MEM_fn_insts_blocks_iff] >>
  metis_tac[]
QED

Theorem mssa_derived_definition:
  FINITE roots /\ ssa_form fn /\ MEM inst (fn_insts fn) /\
  MEM v inst.inst_outputs /\ v IN pointer_derived_vars fn roots ==>
  v IN roots \/ is_pointer_preserving_op inst.inst_opcode /\
    ?u. MEM (Var u) inst.inst_operands /\ u IN pointer_derived_vars fn roots
Proof
  strip_tac >> drule_all mssa_derived_producer >> strip_tac >- simp[] >>
  rename1 `MEM v producer.inst_outputs` >>
  `inst = producer` by (irule ssa_unique_output >> metis_tac[]) >>
  gvs[] >> metis_tac[]
QED

Theorem mssa_ptr_roots_finite:
  FINITE (ptr_roots P fn)
Proof
  simp[ptr_roots_def, FINITE_alloca_roots, pred_setTheory.FINITE_UNION] >>
  conj_tac >> irule pred_setTheory.SUBSET_FINITE >>
  qexists_tac `IMAGE (\i. THE (inst_output i)) (set (fn_insts fn))` >>
  simp[pred_setTheory.SUBSET_DEF] >> rpt strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem mssa_nonalloca_roots_finite:
  FINITE (ptr_roots P fn DIFF alloca_roots fn)
Proof
  simp[mssa_ptr_roots_finite]
QED

Theorem mssa_origin_closure_step:
  mssa_inst_origin orig fn inst' /\
  is_pointer_preserving_op inst'.inst_opcode /\
  MEM (Var u) inst'.inst_operands /\
  orig u IN pointer_derived_vars fn roots /\
  MEM v inst'.inst_outputs ==>
  orig v IN pointer_derived_vars fn roots
Proof
  simp[mssa_inst_origin_def] >> rpt strip_tac >> gvs[]
  >- (irule mssa_derived_closed >> goal_assum (drule_at Any) >>
      qexists_tac `inst` >> simp[] >> conj_tac
      >- metis_tac[listTheory.MEM_MAP] >>
      qpat_x_assum `MAP _ inst'.inst_operands = _` (SUBST1_TAC o SYM) >>
      simp[listTheory.MEM_MAP] >> qexists_tac `Var u` >> simp[])
  >> metis_tac[mssa_derived_closed, is_pointer_preserving_op_def]
QED

Theorem mssa_derived_forward:
  FINITE roots' /\
  (!i. MEM i (fn_insts fn') ==> mssa_inst_origin orig fn i) /\
  (!v. v IN roots' ==> orig v IN pointer_derived_vars fn roots) ==>
  !v. v IN pointer_derived_vars fn' roots' ==>
      orig v IN pointer_derived_vars fn roots
Proof
  strip_tac >>
  `pointer_derived_vars fn' roots' SUBSET
     {v | orig v IN pointer_derived_vars fn roots}` suffices_by
    simp[pred_setTheory.SUBSET_DEF] >>
  irule mssa_derived_least >> simp[pred_setTheory.SUBSET_DEF] >>
  rpt strip_tac >> irule mssa_origin_closure_step >> metis_tac[]
QED

Theorem mssa_origin_root:
  fn_inst_wf fn /\ mssa_inst_origin orig fn inst' /\
  (inst'.inst_opcode = ALLOCA \/ inst'.inst_opcode = DALLOCA \/
   inst'.inst_opcode = PARAM) /\ inst_output inst' = SOME v ==>
  ?inst. MEM inst (fn_insts fn) /\
    inst.inst_opcode = inst'.inst_opcode /\
    inst_output inst = SOME (orig v) /\
    inst.inst_outputs = [orig v] /\
    MAP (\op. case op of Var u => Var (orig u) | _ => op)
      inst'.inst_operands = inst.inst_operands
Proof
  strip_tac >>
  `?w. inst'.inst_outputs = [w]` by
    (irule mssa_root_output >> metis_tac[]) >>
  gvs[inst_output_def] >>
  gvs[mssa_inst_origin_def] >> qexists_tac `inst` >>
  qpat_x_assum `[_] = inst.inst_outputs` (SUBST1_TAC o SYM) >>
  gvs[inst_output_def]
QED

Theorem mssa_alloca_roots_origin:
  fn_inst_wf fn /\
  (!i. MEM i (fn_insts fn') ==> mssa_inst_origin orig fn i) /\
  v IN alloca_roots fn' ==> orig v IN alloca_roots fn
Proof
  simp[alloca_roots_def] >> strip_tac >>
  `mssa_inst_origin orig fn inst` by metis_tac[] >>
  drule_at (Pat `mssa_inst_origin _ _ _`) mssa_origin_root >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem mssa_ptr_roots_origin:
  fn_inst_wf fn /\ fn'.fn_name = fn.fn_name /\
  (!i. MEM i (fn_insts fn') ==> mssa_inst_origin orig fn i) /\
  v IN ptr_roots P fn' ==> orig v IN ptr_roots P fn
Proof
  simp[ptr_roots_def] >> strip_tac
  >- (disj1_tac >> disj1_tac >> irule mssa_alloca_roots_origin >> metis_tac[])
  >- (`mssa_inst_origin orig fn inst` by metis_tac[] >>
      drule_at (Pat `mssa_inst_origin _ _ _`) mssa_origin_root >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[])
  >> `mssa_inst_origin orig fn inst` by metis_tac[] >>
  drule_at (Pat `mssa_inst_origin _ _ _`) mssa_origin_root >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem mssa_nonalloca_definition:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  MEM v inst.inst_outputs /\ v IN ptr_roots P fn /\
  (inst.inst_opcode = DALLOCA \/ inst.inst_opcode = PARAM) ==>
  v NOTIN alloca_roots fn
Proof
  strip_tac >>
  `v IN fn_pv P fn` by
    (simp[fn_pv_def] >> irule mssa_derived_initial >> simp[mssa_ptr_roots_finite]) >>
  gvs[fn_ptr_ok_def] >>
  qpat_x_assum `!inst v. _` (drule_at Any) >>
  simp[] >> disch_then (qspec_then `inst` mp_tac) >>
  simp[is_pointer_preserving_op_def]
QED

Theorem mssa_nonalloca_roots_origin:
  fn_inst_wf fn /\ fn_ptr_ok P fn /\ fn'.fn_name = fn.fn_name /\
  (!i. MEM i (fn_insts fn') ==> mssa_inst_origin orig fn i) /\
  v IN ptr_roots P fn' DIFF alloca_roots fn' ==>
  orig v IN ptr_roots P fn DIFF alloca_roots fn
Proof
  strip_tac >>
  `orig v IN ptr_roots P fn` by
    (irule mssa_ptr_roots_origin >> metis_tac[pred_setTheory.IN_DIFF]) >>
  simp[] >>
  qpat_x_assum `v IN _ DIFF _` mp_tac >>
  simp[ptr_roots_def] >> strip_tac >>
  `mssa_inst_origin orig fn inst` by metis_tac[] >>
  drule_at (Pat `mssa_inst_origin _ _ _`) mssa_origin_root >>
  simp[] >> strip_tac >> gvs[] >>
  irule mssa_nonalloca_definition >> metis_tac[listTheory.MEM]
QED

Theorem mssa_pv_forward:
  fn_inst_wf fn /\ fn'.fn_name = fn.fn_name /\
  (!i. MEM i (fn_insts fn') ==> mssa_inst_origin orig fn i) /\
  v IN fn_pv P fn' ==> orig v IN fn_pv P fn
Proof
  simp[fn_pv_def] >> strip_tac >> irule mssa_derived_forward >> qexists_tac `fn'` >>
  qexists_tac `ptr_roots P fn'` >> simp[mssa_ptr_roots_finite] >>
  rpt strip_tac >>
  irule mssa_derived_initial >> simp[mssa_ptr_roots_finite] >>
  irule mssa_ptr_roots_origin >> metis_tac[]
QED

Theorem mssa_alloca_forward:
  fn_inst_wf fn /\
  (!i. MEM i (fn_insts fn') ==> mssa_inst_origin orig fn i) /\
  v IN pointer_derived_vars fn' (alloca_roots fn') ==>
  orig v IN pointer_derived_vars fn (alloca_roots fn)
Proof
  strip_tac >> irule mssa_derived_forward >> qexists_tac `fn'` >>
  qexists_tac `alloca_roots fn'` >> simp[FINITE_alloca_roots] >>
  rpt strip_tac >>
  irule mssa_derived_initial >> simp[FINITE_alloca_roots] >>
  irule mssa_alloca_roots_origin >> metis_tac[]
QED

Theorem mssa_nonalloca_forward:
  fn_inst_wf fn /\ fn_ptr_ok P fn /\ fn'.fn_name = fn.fn_name /\
  (!i. MEM i (fn_insts fn') ==> mssa_inst_origin orig fn i) /\
  v IN pointer_derived_vars fn' (ptr_roots P fn' DIFF alloca_roots fn') ==>
  orig v IN pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn)
Proof
  strip_tac >> irule mssa_derived_forward >> qexists_tac `fn'` >>
  qexists_tac `ptr_roots P fn' DIFF alloca_roots fn'` >>
  simp[mssa_nonalloca_roots_finite] >>
  rpt strip_tac >>
  irule mssa_derived_initial >> simp[mssa_nonalloca_roots_finite] >>
  metis_tac[mssa_nonalloca_roots_origin, pred_setTheory.IN_DIFF]
QED

Theorem mssa_input_pointer_definition:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  MEM v inst.inst_outputs /\ v IN fn_pv P fn ==>
  inst.inst_opcode = ALLOCA \/
  ((inst.inst_opcode = DALLOCA \/
    (inst.inst_opcode = PARAM /\
     ?idx. inst.inst_operands = [Lit idx] /\ w2n idx IN P fn.fn_name)) /\
   v NOTIN alloca_roots fn) \/
  (is_pointer_preserving_op inst.inst_opcode /\
   ?u. MEM (Var u) inst.inst_operands /\ u IN fn_pv P fn)
Proof
  simp[fn_ptr_ok_def] >> metis_tac[]
QED

Theorem mssa_input_phi_pointer_operand:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  MEM v inst.inst_outputs /\ v IN fn_pv P fn /\
  inst.inst_opcode = PHI /\ MEM (Var u) inst.inst_operands ==>
  u IN fn_pv P fn
Proof
  strip_tac >> drule_all mssa_input_pointer_definition >> simp[] >> strip_tac >>
  qpat_x_assum `fn_ptr_ok _ _` mp_tac >>
  simp[fn_ptr_ok_def, phi_pv_all_var_def, fn_pv_def] >>
  gvs[fn_insts_def, MEM_fn_insts_blocks_iff, fn_pv_def] >> metis_tac[]
QED

Theorem mssa_map_var_member:
  MEM (Var x) (MAP (\op. case op of Var u => Var (orig u) | _ => op) ops) <=>
  ?u. MEM (Var u) ops /\ orig u = x
Proof
  simp[listTheory.MEM_MAP] >> eq_tac >> rpt strip_tac
  >- (Cases_on `op` >> gvs[] >> metis_tac[]) >>
  qexists_tac `Var u` >> simp[]
QED

Theorem mssa_renamed_pointer_root:
  fn_inst_wf fn /\ fn'.fn_name = fn.fn_name /\
  MEM inst' (fn_insts fn') /\
  MAP orig inst'.inst_outputs = inst.inst_outputs /\
  MAP (\op. case op of Var u => Var (orig u) | _ => op)
    inst'.inst_operands = inst.inst_operands /\
  inst'.inst_opcode = inst.inst_opcode /\
  mssa_inst_origin orig fn inst' /\ MEM v inst'.inst_outputs /\
  (inst.inst_opcode = ALLOCA \/ inst.inst_opcode = DALLOCA \/
   (inst.inst_opcode = PARAM /\
    ?idx. inst.inst_operands = [Lit idx] /\ w2n idx IN P fn.fn_name)) ==>
  v IN ptr_roots P fn'
Proof
  strip_tac >>
  `?w. inst'.inst_outputs = [w]` by
    (irule mssa_root_output >> metis_tac[]) >>
  gvs[] >> simp[ptr_roots_def, alloca_roots_def] >>
  `inst_output inst' = SOME v` by simp[inst_output_def] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem mssa_renamed_pointer_definition:
  fn_inst_wf fn /\ fn_ptr_ok P fn /\ fn'.fn_name = fn.fn_name /\
  MEM inst' (fn_insts fn') /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode <> PHI /\
  MAP orig inst'.inst_outputs = inst.inst_outputs /\
  MAP (\op. case op of Var u => Var (orig u) | _ => op)
    inst'.inst_operands = inst.inst_operands /\
  inst'.inst_opcode = inst.inst_opcode /\
  mssa_inst_origin orig fn inst' /\ MEM v inst'.inst_outputs /\
  orig v IN fn_pv P fn ==>
  v IN ptr_roots P fn' \/
  (inst'.inst_opcode <> PHI /\ is_pointer_preserving_op inst'.inst_opcode /\
   ?u. MEM (Var u) inst'.inst_operands /\ orig u IN fn_pv P fn)
Proof
  strip_tac >>
  `MEM (orig v) inst.inst_outputs` by metis_tac[listTheory.MEM_MAP] >>
  drule_all mssa_input_pointer_definition >> strip_tac
  >- (disj1_tac >> irule mssa_renamed_pointer_root >> metis_tac[])
  >- (disj1_tac >> irule mssa_renamed_pointer_root >> metis_tac[])
  >- (disj1_tac >> irule mssa_renamed_pointer_root >> metis_tac[]) >>
  disj2_tac >> simp[] >>
  qpat_x_assum `MAP _ inst'.inst_operands = _` (SUBST_ALL_TAC o SYM) >>
  gvs[mssa_map_var_member] >> metis_tac[]
QED

Theorem mssa_pointer_definition_cases:
  fn_inst_wf fn /\ fn_ptr_ok P fn /\ fn'.fn_name = fn.fn_name /\
  MEM inst' (fn_insts fn') /\ mssa_inst_origin orig fn inst' /\
  MEM v inst'.inst_outputs /\ orig v IN fn_pv P fn ==>
  v IN ptr_roots P fn' \/
  (inst'.inst_opcode <> PHI /\ is_pointer_preserving_op inst'.inst_opcode /\
   ?u. MEM (Var u) inst'.inst_operands /\ orig u IN fn_pv P fn) \/
  (inst'.inst_opcode = PHI /\
   !u. MEM (Var u) inst'.inst_operands ==> orig u IN fn_pv P fn)
Proof
  strip_tac >> qpat_assum `mssa_inst_origin _ _ _` mp_tac >>
  pure_rewrite_tac[mssa_inst_origin_def] >> strip_tac
  >- (drule_all mssa_renamed_pointer_definition >> metis_tac[]) >>
  gvs[] >>
  `!u. MEM (Var u) inst'.inst_operands ==> orig u IN fn_pv P fn` by
    (simp[] >> rpt strip_tac >> metis_tac[mssa_input_phi_pointer_operand]) >>
  simp[is_pointer_preserving_op_def] >> metis_tac[]
QED

Theorem mssa_pointer_output_on_path:
  fn_inst_wf fn /\ fn_ptr_ok P fn /\ fn'.fn_name = fn.fn_name /\
  (!i. MEM i (fn_insts fn') ==> mssa_inst_origin orig fn i) /\
  fn_defs_reach_uses fn' /\ ssa_form fn' /\ fn_phis_cover_preds fn' /\
  (!bb inst. MEM bb fn'.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_entry_label fn' = SOME bb.bb_label ==> inst.inst_opcode <> PHI) ==>
  !n j path bb v.
    LENGTH path = n /\ is_fn_path fn' path /\ path <> [] /\
    fn_entry_label fn' = SOME (HD path) /\ LAST path = bb.bb_label /\
    MEM bb fn'.fn_blocks /\ j < LENGTH bb.bb_instructions /\
    MEM v (EL j bb.bb_instructions).inst_outputs /\ orig v IN fn_pv P fn ==>
    v IN fn_pv P fn'
Proof
  strip_tac >> completeInduct_on `n` >> gen_tac >>
  completeInduct_on `j` >> rpt strip_tac >>
  `MEM (EL j bb.bb_instructions) bb.bb_instructions` by simp[listTheory.EL_MEM] >>
  `MEM (EL j bb.bb_instructions) (fn_insts fn')` by
    (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `mssa_inst_origin orig fn (EL j bb.bb_instructions)` by metis_tac[] >>
  drule_all mssa_pointer_definition_cases >> strip_tac
  >- (simp[fn_pv_def] >> irule mssa_derived_initial >> simp[mssa_ptr_roots_finite])
  >- suspend "nonphi"
  >> suspend "phi"
QED

Resume mssa_pointer_output_on_path[nonphi]:
  drule_all mssa_nonphi_earlier_def >> strip_tac
  >- (`u IN fn_pv P fn'` by
        (qpat_x_assum `!m. m < n ==> _`
           (qspec_then `LENGTH pre` mp_tac) >>
         impl_tac >- decide_tac >>
         disch_then (qspecl_then [`di`, `pre`, `db`, `u`] mp_tac) >> simp[]) >>
      simp[fn_pv_def] >> irule mssa_derived_closed >> metis_tac[fn_pv_def]) >>
  `u IN fn_pv P fn'` by
    (qpat_x_assum `!m. m < j ==> _` (qspec_then `i` mp_tac) >> simp[] >>
     disch_then (qspecl_then [`path`, `bb`, `u`] mp_tac) >> simp[]) >>
  simp[fn_pv_def] >> irule mssa_derived_closed >> metis_tac[fn_pv_def]
QED

Resume mssa_pointer_output_on_path[phi]:
  qpat_x_assum `!m. m < n ==> _` (mk_asm "outer") >>
  qpat_x_assum `!m. m < j ==> _` kall_tac >>
  Cases_on `path` using listTheory.SNOC_CASES >- gvs[] >>
  rename1 `SNOC last prefix` >>
  Cases_on `prefix = []`
  >- (gvs[] >> metis_tac[]) >>
  `!xs. HD (prefix ++ xs) = HD prefix` by
    (Cases_on `prefix` >> gvs[]) >>
  gvs[listTheory.SNOC_APPEND] >>
  drule_all mssa_phi_earlier_def >> strip_tac >>
  `MEM (Var u) (EL j bb.bb_instructions).inst_operands` by
    metis_tac[cfgNormBaseTheory.phi_pairs_mem_var] >>
  `orig u IN fn_pv P fn` by metis_tac[] >>
  `u IN fn_pv P fn'` by
    (asm "outer" (qspec_then `LENGTH pre` mp_tac) >>
     impl_tac >- gvs[] >>
     disch_then (qspecl_then [`di`, `pre`, `db`, `u`] mp_tac) >> simp[]) >>
  simp[fn_pv_def] >> irule mssa_derived_closed >>
  metis_tac[fn_pv_def, is_pointer_preserving_op_def]
QED

Finalise mssa_pointer_output_on_path

Theorem mssa_pointer_output_backward:
  fn_inst_wf fn /\ fn_ptr_ok P fn /\ fn'.fn_name = fn.fn_name /\
  (!i. MEM i (fn_insts fn') ==> mssa_inst_origin orig fn i) /\
  fn_defs_reach_uses fn' /\ ssa_form fn' /\ fn_phis_cover_preds fn' /\
  all_reachable fn' /\
  (!bb inst. MEM bb fn'.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_entry_label fn' = SOME bb.bb_label ==> inst.inst_opcode <> PHI) /\
  MEM inst (fn_insts fn') /\ MEM v inst.inst_outputs /\ orig v IN fn_pv P fn ==>
  v IN fn_pv P fn'
Proof
  strip_tac >>
  `?bb. MEM bb fn'.fn_blocks /\ MEM inst bb.bb_instructions` by
    (gvs[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `fn_reachable fn' bb.bb_label` by gvs[all_reachable_def] >>
  gvs[fn_reachable_def] >> drule venomExecProofsTheory.rtc_to_fn_path >> strip_tac >>
  `?j. j < LENGTH bb.bb_instructions /\ EL j bb.bb_instructions = inst` by
    metis_tac[listTheory.MEM_EL] >>
  `!bb inst. MEM bb fn'.fn_blocks /\ MEM inst bb.bb_instructions /\
     fn_entry_label fn' = SOME bb.bb_label ==> inst.inst_opcode <> PHI` by
    (simp[] >> metis_tac[]) >>
  irule mssa_pointer_output_on_path >> simp[] >> conj_tac
  >- metis_tac[] >> conj_tac
  >- (qexistsl_tac [`fn`, `orig`] >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`bb`, `j`, `path`] >> simp[]
QED

Theorem mssa_operand_has_definition:
  wf_ssa fn /\ MEM inst (fn_insts fn) /\ MEM (Var v) inst.inst_operands ==>
  ?di. MEM di (fn_insts fn) /\ MEM v di.inst_outputs
Proof
  simp[wf_ssa_def, def_dominates_uses_def] >> strip_tac >>
  `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
    (gvs[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  first_x_assum drule_all >>
  Cases_on `inst.inst_opcode = PHI` >> simp[]
  >- (simp[phi_edge_uses_wf_def] >> strip_tac >>
      drule_all phi_well_formed_var_pair >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      gvs[def_available_at_def, fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  disch_then (qspec_then `v` mp_tac) >> simp[def_available_at_def] >>
  strip_tac >> simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]
QED

Theorem mssa_pointer_operand_backward:
  fn_inst_wf fn /\ fn_ptr_ok P fn /\ fn'.fn_name = fn.fn_name /\
  (!i. MEM i (fn_insts fn') ==> mssa_inst_origin orig fn i) /\
  fn_defs_reach_uses fn' /\ wf_ssa fn' /\ fn_phis_cover_preds fn' /\
  all_reachable fn' /\
  (!bb inst. MEM bb fn'.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_entry_label fn' = SOME bb.bb_label ==> inst.inst_opcode <> PHI) /\
  MEM inst (fn_insts fn') /\ MEM (Var v) inst.inst_operands /\ orig v IN fn_pv P fn ==>
  v IN fn_pv P fn'
Proof
  strip_tac >> drule_all mssa_operand_has_definition >> strip_tac >>
  irule mssa_pointer_output_backward >> gvs[wf_ssa_def] >> metis_tac[]
QED

Theorem mssa_reachable_inst_identity:
  all_reachable fn /\ MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  (inst.inst_opcode = PHI ==> phi_edge_uses_wf fn bb inst) ==>
  reachable_inst fn bb.bb_label inst = inst
Proof
  strip_tac >> simp[reachable_inst_def] >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  `filter_phi_ops (reachable_preds fn bb.bb_label) inst.inst_operands =
   inst.inst_operands` suffices_by simp[] >>
  irule simplifyCfgRepairDataflowTheory.filter_phi_ops_all_preds >>
  gvs[phi_edge_uses_wf_def] >> rpt strip_tac >>
  simp[reachable_preds_def, listTheory.MEM_FILTER, listTheory.MEM_MAP] >>
  `?pred_bb. MEM pred_bb fn.fn_blocks /\ pred_bb.bb_label = p /\
     fn_cfg_edge fn p bb.bb_label` by metis_tac[] >>
  gvs[all_reachable_def] >> metis_tac[]
QED

Theorem mssa_reachable_fn_identity:
  all_reachable fn /\ wf_ssa fn ==> reachable_fn fn = fn
Proof
  strip_tac >>
  `FILTER (\bb. fn_reachable fn bb.bb_label) fn.fn_blocks = fn.fn_blocks` by
    (gvs[all_reachable_def] >>
     qpat_x_assum `!bb. _` mp_tac >>
     qspec_tac (`fn.fn_blocks`, `blocks`) >> Induct >> simp[] >> metis_tac[]) >>
  simp[reachable_fn_def] >>
  `MAP (\bb. bb with bb_instructions :=
       MAP (reachable_inst fn bb.bb_label) bb.bb_instructions) fn.fn_blocks = fn.fn_blocks`
    suffices_by simp[] >>
  GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM listTheory.MAP_ID] >>
  irule listTheory.MAP_CONG >> simp[] >> rpt strip_tac >>
  rename1 `MEM bb fn.fn_blocks` >>
  `MAP (reachable_inst fn bb.bb_label) bb.bb_instructions = bb.bb_instructions`
    suffices_by simp[] >>
  GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM listTheory.MAP_ID] >>
  irule listTheory.MAP_CONG >> simp[] >> rpt strip_tac >>
  irule mssa_reachable_inst_identity >>
  gvs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]
QED

Theorem mssa_reachable_output_identity:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==> reachable_fn fn' = fn'
Proof
  strip_tac >> irule mssa_reachable_fn_identity >> conj_tac
  >- (irule make_ssa_current_fn_all_reachable >>
      gvs[make_ssa_input_ok_def, wf_function_def] >> metis_tac[]) >>
  irule mssa_wf_ssa >> metis_tac[]
QED

(* Why it holds.  make_ssa_current_fn_origin gives orig, from fn' vars to
   fn vars: each instruction of fn' is a renamed non-PHI of fn (same
   opcode and id, outputs and Var operands mapped by orig), a NOP, or a
   PHI/ASSIGN whose output w is a renamed output of some instruction of fn
   and whose Var operands u have orig u = orig w or are operands of the
   input PHI defining orig w.

   Forward: v' IN pointer_derived_vars fn' R' ==> orig v' IN
   pointer_derived_vars fn R, for R' = ptr_roots P fn', alloca_roots fn',
   and ptr_roots P fn' DIFF alloca_roots fn' against the matching R of fn
   (pointer_use_vars_least).  For the last one, a DALLOCA or pointer PARAM
   output of fn is a pointer, so fn_ptr_ok's definition clause on fn puts
   it outside alloca_roots fn.

   Backward: a variable v' of fn' with orig v' IN fn_pv P fn is in
   fn_pv P fn'.  By induction on where v' is defined, ordered by the
   shortest CFG distance of its block from the entry, then by its index:
   fn_defs_reach_uses fn' and all_reachable fn' (make_ssa_current_fn_input_ok)
   put a definition of each operand earlier on a shortest path (a PHI
   operand's at the end of the predecessor the shortest path comes
   through, fn_phis_cover_preds fn').  The definition of v' is, by fn's
   definition clause, a root (and a root of fn'), or pointer-preserving
   with a pointer operand; a PHI or ASSIGN of the second kind has only
   pointer operands (fn's clause and phi_pv_all_var fn), and has at least
   one (ASSIGN: origin; PHI: make_ssa_current_fn_phis_non_degenerate, and
   no PHI sits in the entry block: its pairs are CFG edges into the block,
   make_ssa_current_fn_cfg, first_block_no_preds).

   Then each conjunct of fn_ptr_ok P fn' follows from fn's: per
   instruction through orig and forward inclusion; the LT/GT/EQ exemption
   and phi_pv_all_var need backward inclusion; the definition clause on
   fn' follows from SSA (wf_ssa fn', make_ssa_current_fn_wf_ssa: one
   definition per variable) and fn' pv being the least closure.

   Every Var operand of a PHI of fn' sits in a (Label, Var) pair whose
   label is a CFG edge into its block: wf_ssa fn' gives phi_edge_uses_wf,
   hence phi_well_formed (phi_well_formed_var_pair).  So the backward
   induction reaches every PHI operand, and with all_reachable fn'
   filter_phi_ops drops nothing: reachable_fn fn' = fn'. *)
Theorem mssa_filter_map_singleton:
  !xs. FILTER ($= (f v)) (MAP f xs) = [f v] ==>
       MEM v xs ==> FILTER ($= v) xs = [v]
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `h = v` >> gvs[] >>
  Cases_on `f h = f v` >> gvs[] >>
  gvs[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM, listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem mssa_map_label_member:
  MEM (Label l)
    (MAP (\op. case op of Var u => Var (orig u) | _ => op) ops) <=>
  MEM (Label l) ops
Proof
  simp[listTheory.MEM_MAP] >> eq_tac >> rpt strip_tac
  >- (rename1 `MEM op ops` >> Cases_on `op` >> gvs[])
  >> goal_assum (drule_at Any) >> simp[]
QED

Theorem mssa_decode_invoke_map:
  decode_invoke (inst with inst_operands :=
    MAP (\op. case op of Var u => Var (orig u) | _ => op)
      inst.inst_operands) =
  case decode_invoke inst of
    NONE => NONE
  | SOME (nm,args) => SOME (nm,
      MAP (\op. case op of Var u => Var (orig u) | _ => op) args)
Proof
  simp[venomExecSemanticsTheory.decode_invoke_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  rename1 `op :: ops` >> Cases_on `op` >> simp[]
QED

Theorem mssa_fields:
  make_ssa_current_fn s fn = (fn',s') ==>
  fn'.fn_name = fn.fn_name /\
  fn'.fn_forced_alloc_positions = fn.fn_forced_alloc_positions
Proof
  rw[make_ssa_current_fn_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem mssa_mem_fn_insts:
  MEM inst (fn_insts fn) <=>
  ?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions
Proof
  simp[fn_insts_def, MEM_fn_insts_blocks_iff]
QED

Theorem mssa_map_var_mem:
  MEM (Var v) ops ==>
  MEM (Var (orig v))
    (MAP (\op. case op of Var u => Var (orig u) | _ => op) ops)
Proof
  simp[mssa_map_var_member] >> metis_tac[]
QED

Theorem mssa_map_two_vars:
  MAP (\op. case op of Var u => Var (orig u) | _ => op) ops =
    [Var a; Var b] ==>
  ?a' b'. ops = [Var a'; Var b'] /\ orig a' = a /\ orig b' = b
Proof
  namedCases_on `ops` ["", "x xs"] >> simp[] >>
  namedCases_on `xs` ["", "y ys"] >> simp[] >>
  Cases_on `x` >> Cases_on `y` >> simp[]
QED

Theorem mssa_map_lit:
  MAP (\op. case op of Var u => Var (orig u) | _ => op) ops = [Lit x] ==>
  ops = [Lit x]
Proof
  namedCases_on `ops` ["", "y ys"] >> simp[] >> Cases_on `y` >> simp[]
QED

Theorem mssa_filter_unique:
  !xs. FILTER ($= (f a)) (MAP f xs) = [f a] /\ MEM a xs /\ MEM b xs /\
       f b = f a ==> b = a
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `f a = f h` >> simp[] >> strip_tac >>
  gvs[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM, listTheory.MEM_MAP] >>
  metis_tac[]
QED

(* mem_write_ops and mem_read_ops look only at the opcode and the shape
   of the operand list, so a map over the operands maps the offset. *)
Theorem mssa_write_offset_map:
  inst'.inst_opcode = inst.inst_opcode /\
  MAP f inst'.inst_operands = inst.inst_operands ==>
  OPTREL (\ops ops'. ops.iao_ofst = f ops'.iao_ofst /\
                     MEM ops'.iao_ofst inst'.inst_operands)
    (mem_write_ops inst) (mem_write_ops inst')
Proof
  rewrite_tac [memLocDefsTheory.mem_write_ops_def] >> strip_tac >>
  qpat_x_assum `MAP _ _ = _` (SUBST_ALL_TAC o SYM) >>
  Cases_on `inst.inst_opcode` >>
  gvs[] >>
  namedCases_on `inst'.inst_operands` ["", "a xs"] >> gvs[] >>
  namedCases_on `xs` ["", "b ys"] >> gvs[] >>
  namedCases_on `ys` ["", "c zs"] >> gvs[] >>
  namedCases_on `zs` ["", "d ts"] >> gvs[] >>
  namedCases_on `ts` ["", "e us"] >> gvs[] >>
  namedCases_on `us` ["", "g vs"] >> gvs[] >>
  namedCases_on `vs` ["", "h ws"] >> gvs[] >>
  Cases_on `ws` >> gvs[]
QED

Theorem mssa_read_offset_map:
  inst'.inst_opcode = inst.inst_opcode /\
  MAP f inst'.inst_operands = inst.inst_operands ==>
  OPTREL (\ops ops'. ops.iao_ofst = f ops'.iao_ofst /\
                     MEM ops'.iao_ofst inst'.inst_operands)
    (mem_read_ops inst) (mem_read_ops inst')
Proof
  rewrite_tac [memLocDefsTheory.mem_read_ops_def] >> strip_tac >>
  qpat_x_assum `MAP _ _ = _` (SUBST_ALL_TAC o SYM) >>
  Cases_on `inst.inst_opcode = LOG`
  >- (gvs[] >>
      `REVERSE (MAP f inst'.inst_operands) =
       MAP f (REVERSE inst'.inst_operands)` by
        simp[listTheory.MAP_REVERSE] >>
      `!x. MEM x inst'.inst_operands <=>
           MEM x (REVERSE inst'.inst_operands)` by simp[] >>
      pop_assum (fn th => once_rewrite_tac [th]) >>
      pop_assum (fn th => rewrite_tac [th]) >>
      qspec_tac (`REVERSE inst'.inst_operands`, `xs`) >>
      namedCases_on `xs` ["", "a ys"] >> simp[] >>
      namedCases_on `ys` ["", "b zs"] >> simp[] >>
      Cases_on `zs` >> simp[]) >>
  Cases_on `inst.inst_opcode` >>
  gvs[] >>
  namedCases_on `inst'.inst_operands` ["", "a xs"] >> gvs[] >>
  namedCases_on `xs` ["", "b ys"] >> gvs[] >>
  namedCases_on `ys` ["", "c zs"] >> gvs[] >>
  namedCases_on `zs` ["", "d ts"] >> gvs[] >>
  namedCases_on `ts` ["", "e us"] >> gvs[] >>
  namedCases_on `us` ["", "g vs"] >> gvs[] >>
  namedCases_on `vs` ["", "h ws"] >> gvs[] >>
  Cases_on `ws` >> gvs[]
QED

Theorem mssa_renamed_write_var:
  inst'.inst_opcode = inst.inst_opcode /\
  MAP (\op. case op of Var u => Var (orig u) | _ => op)
    inst'.inst_operands = inst.inst_operands /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var x ==>
  ?ops' u. mem_write_ops inst' = SOME ops' /\ ops'.iao_ofst = Var u /\
           orig u = x /\ MEM (Var u) inst'.inst_operands
Proof
  strip_tac >> drule_all mssa_write_offset_map >>
  Cases_on `mem_write_ops inst'` >> simp[] >> strip_tac >>
  rename1 `mem_write_ops inst' = SOME ops'` >>
  Cases_on `ops'.iao_ofst` >> gvs[]
QED

Theorem mssa_renamed_read_var:
  inst'.inst_opcode = inst.inst_opcode /\
  MAP (\op. case op of Var u => Var (orig u) | _ => op)
    inst'.inst_operands = inst.inst_operands /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var x ==>
  ?ops' u. mem_read_ops inst' = SOME ops' /\ ops'.iao_ofst = Var u /\
           orig u = x /\ MEM (Var u) inst'.inst_operands
Proof
  strip_tac >> drule_all mssa_read_offset_map >>
  Cases_on `mem_read_ops inst'` >> simp[] >> strip_tac >>
  rename1 `mem_read_ops inst' = SOME ops'` >>
  Cases_on `ops'.iao_ofst` >> gvs[]
QED

Theorem mssa_renamed_write_back:
  inst'.inst_opcode = inst.inst_opcode /\
  MAP (\op. case op of Var u => Var (orig u) | _ => op)
    inst'.inst_operands = inst.inst_operands /\
  mem_write_ops inst' = SOME ops' /\ ops'.iao_ofst = Var u ==>
  ?ops. mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var (orig u)
Proof
  strip_tac >> drule_all mssa_write_offset_map >>
  Cases_on `mem_write_ops inst` >> gvs[]
QED

Theorem mssa_renamed_invoke:
  MAP (\op. case op of Var u => Var (orig u) | _ => op)
    inst'.inst_operands = inst.inst_operands /\
  (!v. MEM (Var v) inst'.inst_operands ==> (v IN pv' <=> orig v IN pv)) /\
  decode_invoke inst = SOME (nm,args) /\
  (!k v. k < LENGTH args /\ EL k args = Var v /\ v IN pv ==> k IN P nm) ==>
  ?nm args. decode_invoke inst' = SOME (nm,args) /\
    !k v. k < LENGTH args /\ EL k args = Var v /\ v IN pv' ==> k IN P nm
Proof
  rewrite_tac [venomExecSemanticsTheory.decode_invoke_def] >> strip_tac >>
  qpat_x_assum `MAP _ _ = _` (SUBST_ALL_TAC o SYM) >>
  gvs[] >>
  namedCases_on `inst'.inst_operands` ["", "op ops"] >> gvs[] >>
  Cases_on `op` >> gvs[] >> rpt strip_tac >>
  first_x_assum irule >> simp[listTheory.EL_MAP] >>
  metis_tac[listTheory.EL_MEM]
QED

Theorem mssa_ren_filter:
  FILTER ($= (Var (orig v)))
    (MAP (\op. case op of Var u => Var (orig u) | _ => op) ops) =
    [Var (orig v)] /\
  MEM (Var v) ops ==>
  FILTER ($= (Var v)) ops = [Var v] /\
  !u. MEM (Var u) ops /\ orig u = orig v ==> u = v
Proof
  strip_tac >> conj_tac
  >- (mp_tac (SIMP_RULE (srw_ss()) [] (Q.ISPECL
        [`\op. case op of Var u => Var (orig u) | _ => op`, `Var v`]
        (Q.GENL [`f`, `v`] mssa_filter_map_singleton))) >>
      disch_then drule_all >> simp[]) >>
  rpt strip_tac >>
  mp_tac (SIMP_RULE (srw_ss()) [] (Q.ISPECL
        [`\op. case op of Var u => Var (orig u) | _ => op`, `Var v`, `Var u`]
        (Q.GENL [`f`, `a`, `b`] mssa_filter_unique))) >>
  disch_then drule_all >> simp[]
QED

Theorem mssa_renamed_use:
  inst'.inst_opcode = inst.inst_opcode /\
  MAP (\op. case op of Var u => Var (orig u) | _ => op)
    inst'.inst_operands = inst.inst_operands /\
  (!v. MEM (Var v) inst'.inst_operands ==> (v IN pv' <=> orig v IN pv)) /\
  ptr_use_ok P pv inst ==>
  ptr_use_ok P pv' inst'
Proof
  rewrite_tac [ptr_use_ok_def] >> strip_tac >> conj_tac
  >- (strip_tac >>
      `inst.inst_opcode = INVOKE` by gvs[] >>
      qpat_x_assum `inst.inst_opcode = INVOKE ==> _` drule >> strip_tac >>
      irule mssa_renamed_invoke >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `orig v IN pv` by metis_tac[] >>
  `MEM (Var (orig v)) inst.inst_operands` by metis_tac[mssa_map_var_mem] >>
  `~((inst.inst_opcode = LT \/ inst.inst_opcode = GT \/
      inst.inst_opcode = EQ) /\
     ?u w. inst.inst_operands = [Var u; Var w] /\ u IN pv /\ w IN pv)` by
    (strip_tac >>
     `MAP (\op. case op of Var u => Var (orig u) | _ => op)
        inst'.inst_operands = [Var u; Var w]` by metis_tac[] >>
     drule mssa_map_two_vars >> strip_tac >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `!v. MEM (Var v) inst.inst_operands /\ _ ==> _`
    (qspec_then `orig v` mp_tac) >>
  impl_tac >- gvs[] >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  `FILTER ($= (Var (orig v)))
     (MAP (\op. case op of Var u => Var (orig u) | _ => op)
        inst'.inst_operands) = [Var (orig v)]` by metis_tac[] >>
  drule_all mssa_ren_filter >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `?ops. _` strip_assume_tac
  >- (drule_all mssa_renamed_write_var >> strip_tac >>
      `u = v` by metis_tac[] >> pop_assum SUBST_ALL_TAC >>
      qexists_tac `ops'` >>
      qpat_x_assum `mem_write_ops inst' = _` (fn th => rewrite_tac [th]) >>
      qpat_x_assum `ops'.iao_ofst = _` (fn th => rewrite_tac [th])) >>
  drule_all mssa_renamed_read_var >> strip_tac >>
  `u = v` by metis_tac[] >> pop_assum SUBST_ALL_TAC >>
  qexists_tac `ops'` >>
  qpat_x_assum `mem_read_ops inst' = _` (fn th => rewrite_tac [th]) >>
  qpat_x_assum `ops'.iao_ofst = _` (fn th => rewrite_tac [th])
QED

Theorem mssa_ok_inst:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) ==>
  inst.inst_opcode <> MEMTOP /\ inst.inst_opcode <> DRET /\
  inst.inst_opcode <> GETFMP /\ inst.inst_opcode <> SETFMP /\
  inst.inst_opcode <> RETFMP /\ inst.inst_opcode <> FMP_PARAM /\
  ((inst.inst_opcode = ISTORE \/ inst.inst_opcode = ILOAD) ==>
   !v. MEM (Var v) inst.inst_operands ==> v NOTIN fn_pv P fn) /\
  ((inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
   (?v. MEM (Var v) inst.inst_operands /\ v IN fn_pv P fn) ==>
   !l. ~MEM (Label l) inst.inst_operands) /\
  ptr_use_ok P (fn_pv P fn) inst
Proof
  rewrite_tac [fn_ptr_ok_def] >> strip_tac >>
  qpat_x_assum `!inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> MEMTOP /\ _`
    drule >> simp[]
QED

Theorem mssa_ok_write:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v ==>
  ~(v IN pointer_derived_vars fn (alloca_roots fn) /\
    v IN pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn))
Proof
  rewrite_tac [fn_ptr_ok_def] >> strip_tac >>
  qpat_x_assum `!inst ops v. _` drule_all >> simp[]
QED

Theorem mssa_target_inst:
  fn_ptr_ok P fn /\ mssa_inst_origin orig fn inst' /\
  (!v. MEM (Var v) inst'.inst_operands ==>
       (v IN pv' <=> orig v IN fn_pv P fn)) ==>
  inst'.inst_opcode <> MEMTOP /\ inst'.inst_opcode <> DRET /\
  inst'.inst_opcode <> GETFMP /\ inst'.inst_opcode <> SETFMP /\
  inst'.inst_opcode <> RETFMP /\ inst'.inst_opcode <> FMP_PARAM /\
  ((inst'.inst_opcode = ISTORE \/ inst'.inst_opcode = ILOAD) ==>
   !v. MEM (Var v) inst'.inst_operands ==> v NOTIN pv') /\
  ((inst'.inst_opcode = ADD \/ inst'.inst_opcode = SUB) /\
   (?v. MEM (Var v) inst'.inst_operands /\ v IN pv') ==>
   !l. ~MEM (Label l) inst'.inst_operands) /\
  ptr_use_ok P pv' inst'
Proof
  strip_tac >>
  qpat_x_assum `mssa_inst_origin _ _ _`
    (strip_assume_tac o REWRITE_RULE [mssa_inst_origin_def])
  >- (drule_all mssa_ok_inst >> strip_tac >>
      drule_all mssa_renamed_use >> strip_tac >>
      qpat_x_assum `MAP _ inst'.inst_operands = _` (SUBST_ALL_TAC o SYM) >>
      qpat_x_assum `inst'.inst_opcode = _` (SUBST_ALL_TAC o SYM) >>
      rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- (rpt strip_tac >> metis_tac[mssa_map_var_mem])
      >- (rpt strip_tac >> metis_tac[mssa_map_var_mem, mssa_map_label_member])
      >> first_assum ACCEPT_TAC)
  >> gvs[ptr_use_ok_def, is_pointer_preserving_op_def]
QED

Theorem mssa_phi_output_pv:
  MEM inst (fn_insts fn) /\ MEM (orig w) inst.inst_outputs /\
  orig v IN fn_pv P fn /\
  (orig v = orig w \/
   (inst.inst_opcode = PHI /\ MEM (Var (orig v)) inst.inst_operands)) ==>
  orig w IN fn_pv P fn
Proof
  rw[] >> gvs[fn_pv_def] >> irule mssa_derived_closed >>
  metis_tac[is_pointer_preserving_op_def]
QED

Theorem mssa_phi_operand_pv:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  MEM (orig w) inst.inst_outputs /\ orig w IN fn_pv P fn /\
  (orig u = orig w \/
   (inst.inst_opcode = PHI /\ MEM (Var (orig u)) inst.inst_operands)) ==>
  orig u IN fn_pv P fn
Proof
  rw[] >> gvs[] >> irule mssa_input_phi_pointer_operand >> metis_tac[]
QED

Theorem mssa_affine:
  fn_ptr_ok P fn /\
  (!i. MEM i (fn_insts fn') ==> mssa_inst_origin orig fn i) /\
  (!inst v. MEM inst (fn_insts fn') /\ MEM (Var v) inst.inst_operands ==>
     (v IN fn_pv P fn' <=> orig v IN fn_pv P fn)) ==>
  affine_pointer_ops fn' (ptr_roots P fn')
Proof
  strip_tac >>
  `affine_pointer_ops fn (ptr_roots P fn)` by gvs[fn_ptr_ok_def] >>
  pop_assum mp_tac >>
  simp[affine_pointer_ops_def, LET_THM, GSYM fn_pv_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  `MEM inst (fn_insts fn')` by metis_tac[mssa_mem_fn_insts] >>
  `mssa_inst_origin orig fn inst` by metis_tac[] >>
  qpat_x_assum `mssa_inst_origin _ _ inst`
    (strip_assume_tac o REWRITE_RULE [mssa_inst_origin_def]) >>
  gvs[] >>
  rename1 `MEM i0 (fn_insts fn)` >>
  `?bb0. MEM bb0 fn.fn_blocks /\ MEM i0 bb0.bb_instructions` by
    metis_tac[mssa_mem_fn_insts] >>
  `!v. MEM (Var v) inst.inst_operands ==>
       (v IN fn_pv P fn' <=> orig v IN fn_pv P fn)` by metis_tac[] >>
  qpat_x_assum `!bb inst op1 op2. _` (qspecl_then [`bb0`, `i0`] mp_tac) >>
  qpat_x_assum `_ = i0.inst_operands` (SUBST_ALL_TAC o SYM) >>
  rpt strip_tac >> gvs[]
QED

Theorem mssa_phi_all_var:
  fn_ptr_ok P fn /\
  (!i. MEM i (fn_insts fn') ==> mssa_inst_origin orig fn i) /\
  (!inst v. MEM inst (fn_insts fn') /\ MEM (Var v) inst.inst_operands ==>
     (v IN fn_pv P fn' <=> orig v IN fn_pv P fn)) ==>
  phi_pv_all_var fn' (ptr_roots P fn')
Proof
  strip_tac >>
  simp[phi_pv_all_var_def, LET_THM, GSYM fn_pv_def] >>
  rpt gen_tac >> strip_tac >>
  `MEM inst (fn_insts fn')` by metis_tac[mssa_mem_fn_insts] >>
  `mssa_inst_origin orig fn inst` by metis_tac[] >>
  qpat_x_assum `mssa_inst_origin _ _ inst`
    (strip_assume_tac o REWRITE_RULE [mssa_inst_origin_def]) >>
  gvs[] >>
  rename1 `MEM i0 (fn_insts fn)` >>
  `orig v IN fn_pv P fn` by metis_tac[] >>
  `orig w IN fn_pv P fn` by
    (irule mssa_phi_output_pv >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
               `orig v' IN fn_pv P fn` suffices_by metis_tac[] >>
               irule mssa_phi_operand_pv >> metis_tac[]) >>
  metis_tac[]
QED

Theorem mssa_write_disjoint:
  fn_inst_wf fn /\ fn_ptr_ok P fn /\ fn'.fn_name = fn.fn_name /\
  (!i. MEM i (fn_insts fn') ==> mssa_inst_origin orig fn i) /\
  MEM inst' (fn_insts fn') /\ mem_write_ops inst' = SOME ops' /\
  ops'.iao_ofst = Var v ==>
  ~(v IN pointer_derived_vars fn' (alloca_roots fn') /\
    v IN pointer_derived_vars fn' (ptr_roots P fn' DIFF alloca_roots fn'))
Proof
  rpt strip_tac >>
  drule_all mssa_alloca_forward >> strip_tac >>
  drule_all mssa_nonalloca_forward >> strip_tac >>
  `mssa_inst_origin orig fn inst'` by metis_tac[] >>
  qpat_x_assum `mssa_inst_origin _ _ inst'`
    (strip_assume_tac o REWRITE_RULE [mssa_inst_origin_def])
  >- (drule_all mssa_renamed_write_back >> strip_tac >>
      drule_all mssa_ok_write >> simp[]) >>
  gvs[memLocDefsTheory.mem_write_ops_def]
QED

Theorem mssa_pv_definition:
  fn_inst_wf fn /\ fn_ptr_ok P fn /\ fn'.fn_name = fn.fn_name /\
  (!i. MEM i (fn_insts fn') ==> mssa_inst_origin orig fn i) /\
  fn_phis_non_degenerate fn' /\
  (!inst v. MEM inst (fn_insts fn') /\ MEM (Var v) inst.inst_operands ==>
     (v IN fn_pv P fn' <=> orig v IN fn_pv P fn)) /\
  MEM inst' (fn_insts fn') /\ MEM v inst'.inst_outputs /\
  v IN fn_pv P fn' ==>
  inst'.inst_opcode = ALLOCA \/
  ((inst'.inst_opcode = DALLOCA \/
    (inst'.inst_opcode = PARAM /\
     ?idx. inst'.inst_operands = [Lit idx] /\ w2n idx IN P fn'.fn_name)) /\
   v NOTIN alloca_roots fn') \/
  (is_pointer_preserving_op inst'.inst_opcode /\
   ?u. MEM (Var u) inst'.inst_operands /\ u IN fn_pv P fn')
Proof
  strip_tac >>
  `orig v IN fn_pv P fn` by (irule mssa_pv_forward >> metis_tac[]) >>
  `mssa_inst_origin orig fn inst'` by metis_tac[] >>
  qpat_x_assum `mssa_inst_origin _ _ inst'`
    (strip_assume_tac o REWRITE_RULE [mssa_inst_origin_def])
  >- (`MEM (orig v) inst.inst_outputs` by
        metis_tac[listTheory.MEM_MAP] >>
      drule_all mssa_input_pointer_definition >> strip_tac
      >- gvs[]
      >- (`v NOTIN alloca_roots fn'` by
            (strip_tac >> drule_all mssa_alloca_roots_origin >>
             metis_tac[]) >>
          gvs[])
      >- (`v NOTIN alloca_roots fn'` by
            (strip_tac >> drule_all mssa_alloca_roots_origin >>
             metis_tac[]) >>
          `inst'.inst_operands = [Lit idx]` by
            (irule mssa_map_lit >> metis_tac[]) >>
          gvs[]) >>
      `?u'. MEM (Var u') inst'.inst_operands /\ orig u' = u` by
        metis_tac[mssa_map_var_member] >>
      `u' IN fn_pv P fn'` by metis_tac[] >>
      disj2_tac >> disj2_tac >> conj_tac >- gvs[] >>
      qexists_tac `u'` >> gvs[])
  >- gvs[]
  >> (disj2_tac >> disj2_tac >> conj_tac
      >- gvs[is_pointer_preserving_op_def] >>
      gvs[] >>
      `?u. MEM (Var u) inst'.inst_operands` by
        (Cases_on `inst'.inst_opcode = ASSIGN` >- gvs[] >>
         gvs[fn_phis_non_degenerate_def] >>
         first_x_assum drule >> simp[] >> strip_tac >>
         metis_tac[cfgNormBaseTheory.phi_pairs_mem_var]) >>
      `!x. MEM (Var x) inst'.inst_operands ==> x IN fn_pv P fn'` by
        (rpt strip_tac >>
         `orig x IN fn_pv P fn` by
           (Cases_on `inst'.inst_opcode = ASSIGN`
            >- (gvs[] >> irule mssa_input_phi_pointer_operand >>
                metis_tac[]) >>
            irule mssa_phi_operand_pv >> metis_tac[]) >>
         metis_tac[]) >>
      metis_tac[listTheory.MEM])
QED

Theorem make_ssa_current_fn_ptr_ok:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\ fn_ptr_ok P fn ==>
  fn_ptr_ok P fn' /\ fn_ptr_ok P (reachable_fn fn')
Proof
  strip_tac >>
  `reachable_fn fn' = fn'` by
    (irule mssa_reachable_output_identity >> metis_tac[]) >>
  simp[] >>
  `?orig. !inst. MEM inst (fn_insts fn') ==> mssa_inst_origin orig fn inst` by
    (irule mssa_origin >> metis_tac[]) >>
  drule mssa_fields >> strip_tac >>
  `wf_ssa fn'` by (irule mssa_wf_ssa >> metis_tac[]) >>
  drule_all make_ssa_current_fn_input_ok >> strip_tac >>
  drule_all make_ssa_current_fn_phis_non_degenerate >> strip_tac >>
  `!bb inst. MEM bb fn'.fn_blocks /\ MEM inst bb.bb_instructions /\
     fn_entry_label fn' = SOME bb.bb_label ==> inst.inst_opcode <> PHI` by
    (rpt gen_tac >> strip_tac >> irule mssa_entry_no_phi >> metis_tac[]) >>
  `!inst v. MEM inst (fn_insts fn') /\ MEM (Var v) inst.inst_operands ==>
     (v IN fn_pv P fn' <=> orig v IN fn_pv P fn)` by
    (rpt strip_tac >> eq_tac >> strip_tac
     >- (irule mssa_pv_forward >> metis_tac[]) >>
     irule mssa_pointer_operand_backward >> metis_tac[]) >>
  rewrite_tac [fn_ptr_ok_def] >> rpt conj_tac
  >- gvs[fn_ptr_ok_def]
  >- (gen_tac >> strip_tac >>
      `mssa_inst_origin orig fn inst` by metis_tac[] >>
      `!v. MEM (Var v) inst.inst_operands ==>
           (v IN fn_pv P fn' <=> orig v IN fn_pv P fn)` by metis_tac[] >>
      drule_all mssa_target_inst >> disch_then ACCEPT_TAC)
  >- (irule mssa_affine >> metis_tac[])
  >- (irule mssa_phi_all_var >> metis_tac[])
  >- (rpt strip_tac >> drule_at Any mssa_write_disjoint >> metis_tac[]) >>
  rpt strip_tac >> irule mssa_pv_definition >> metis_tac[]
QED
