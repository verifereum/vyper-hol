(* Least-closure reflection through FMP lowering. *)
Theory fmpStepOpaque
Ancestors
  fmpStepClosure fmpStepLayout fmpStepRewrite fmpStepReclaim
  unitShapeDefs o1PassContract irSupply list venomInst

Theorem copy_phi_var_in_ir_vars:
  !origin fn x. copy_phi_var origin fn x ==> MEM x (fn_ir_vars fn)
Proof
  Induct_on `copy_phi_var` >> rpt strip_tac >>
  gvs[fn_ir_vars_def, block_ir_vars_def, inst_ir_vars_def,
      fn_insts_def, fn_insts_blocks_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem fresh_runner_not_input_opaque:
  ir_supply_covers_fn s fn /\ fresh_ir_var s = (runner,s') ==>
  !origin. ~copy_phi_var origin fn runner
Proof
  strip_tac >> drule fresh_ir_var_contract >> strip_tac >>
  gvs[venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
      venomFnScheduleRunnerTheory.list_subset_def, EVERY_MEM] >>
  metis_tac[copy_phi_var_in_ir_vars]
QED

Theorem input_setfmp_not_opaque:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = SETFMP /\
  MEM (Var x) inst.inst_operands ==>
  ~retpc_var fn x
Proof
  simp[opaque_use_ok_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[retpc_use_ok_def] >> metis_tac[]
QED

Theorem fmp_lower_inst_retained_origin:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\
  MEM j out /\ MEM j.inst_opcode [GAS; PHI; PARAM; RETPC_PARAM; FMP_PARAM] ==>
  j = inst
Proof
  strip_tac >> drule_all fmp_lower_inst_retained_opcodes >>
  `MEM j (FILTER (\i. i.inst_opcode = j.inst_opcode) out)` by simp[MEM_FILTER] >>
  Cases_on `inst.inst_opcode = j.inst_opcode` >> simp[] >> strip_tac >> gvs[]
QED

Theorem fmp_lower_inst_assign_closed:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\ MEM j out /\
  MEM inst (fn_insts fn) /\ copy_phi_upper_bound origin fn P /\ ~P runner /\
  (!y. inst.inst_opcode = SETFMP /\ MEM (Var y) inst.inst_operands ==> ~P y) ==>
  !x y. j.inst_opcode = ASSIGN /\ j.inst_operands = [Var y] /\
    MEM x j.inst_outputs /\ P y ==> P x
Proof
  rpt strip_tac >> drule_all fmp_lower_inst_assign_origin >> strip_tac
  >- (gvs[copy_phi_upper_bound_def] >> metis_tac[]) >>
  gvs[] >> metis_tac[MEM]
QED

Theorem fmp_lower_blocks_upper_bound:
  fmp_lower_blocks infos ctx runner s restores fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s') /\
  MEM origin [GAS; RETPC_PARAM] /\ copy_phi_upper_bound origin fn P /\ ~P runner /\
  (!i y. MEM i (fn_insts fn) /\ i.inst_opcode = SETFMP /\
    MEM (Var y) i.inst_operands ==> ~P y) /\
  (!point base. MEM (point,base) restores ==> ~P base) ==>
  copy_phi_upper_bound origin (fn with fn_blocks := blocks) P
Proof
  strip_tac >> rewrite_tac[copy_phi_upper_bound_def] >> rpt conj_tac
  >- suspend "seed"
  >- suspend "assign"
  >> suspend "phi"
QED

Resume fmp_lower_blocks_upper_bound[seed]:
  rpt strip_tac >> gvs[fn_insts_def, fn_insts_blocks_MEM] >>
  (drule_all fmp_lower_blocks_origin >> strip_tac
   >- (`inst = i` by metis_tac[fmp_lower_inst_retained_origin, MEM] >> gvs[] >>
       gvs[copy_phi_upper_bound_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
   gvs[mk_inst_def])
QED

Resume fmp_lower_blocks_upper_bound[assign]:
  rpt strip_tac >> gvs[fn_insts_def, fn_insts_blocks_MEM] >>
  (drule_all fmp_lower_blocks_origin >> strip_tac
   >- (`MEM i (fn_insts fn)` by
         (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
       `!z. i.inst_opcode = SETFMP /\ MEM (Var z) i.inst_operands ==> ~P z` by metis_tac[] >>
       drule_all fmp_lower_inst_assign_closed >> metis_tac[]) >>
   gvs[mk_inst_def] >> metis_tac[])
QED

Resume fmp_lower_blocks_upper_bound[phi]:
  rpt strip_tac >> gvs[fn_insts_def, fn_insts_blocks_MEM] >>
  (drule_all fmp_lower_blocks_origin >> strip_tac
   >- (`inst = i` by metis_tac[fmp_lower_inst_retained_origin, MEM] >> gvs[] >>
       gvs[copy_phi_upper_bound_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
   gvs[mk_inst_def])
QED

Finalise fmp_lower_blocks_upper_bound

Theorem fmp_make_root_layout_opaque_shape:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  fmp_make_root_layout ctx fn info runner s = SOME (FmpRootLayout n root newpc s') ==>
  (!i. MEM i (OPTION_TO_LIST root) ==>
    MEM i.inst_opcode [INITIAL_FMP; FMP_PARAM]) /\
  (!i. MEM i (OPTION_TO_LIST newpc) ==> i.inst_opcode = RETPC_PARAM) /\
  MAP (\i. i.inst_outputs) (OPTION_TO_LIST newpc) =
    MAP (\i. i.inst_outputs) (OPTION_TO_LIST oldpc)
Proof
  strip_tac >>
  `!i. MEM i (OPTION_TO_LIST oldpc) ==> i.inst_opcode = RETPC_PARAM` by
    (Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def] >>
     metis_tac[fmpLowerPropsTheory.split_fmp_entry_retpc_opcode]) >>
  Cases_on `oldpc` >>
  gvs[fmpLowerDefsTheory.fmp_make_root_layout_def, AllCaseEqs(),
      callLayoutDefsTheory.OPTION_TO_LIST_def, mk_inst_def,
      fmpLowerDefsTheory.set_param_index_def]
QED


Theorem fmp_install_root_upper_bound:
  entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail /\
  (newpc = NONE <=> oldpc = NONE) /\
  (!i. MEM i (OPTION_TO_LIST oldpc) ==> i.inst_opcode = RETPC_PARAM) /\
  (!i. MEM i (OPTION_TO_LIST newpc) ==> i.inst_opcode = RETPC_PARAM) /\
  MAP (\i. i.inst_outputs) (OPTION_TO_LIST newpc) =
    MAP (\i. i.inst_outputs) (OPTION_TO_LIST oldpc) /\
  (!i. MEM i (OPTION_TO_LIST root) ==> MEM i.inst_opcode [INITIAL_FMP; FMP_PARAM]) /\
  MEM origin [GAS; RETPC_PARAM] /\
  copy_phi_upper_bound origin (fn with fn_blocks := entry::rest) P /\
  fmp_install_root ctx fn (FmpRootLayout (LENGTH users) root newpc s) (entry::rest) =
    SOME (out,s') ==>
  copy_phi_upper_bound origin (fn with fn_blocks := out) P
Proof
  strip_tac >> irule copy_phi_upper_bound_transfer >>
  qexists `fn with fn_blocks := entry::rest` >> reverse conj_tac >- simp[] >>
  gen_tac >> disch_tac >> drule_all fmp_install_root_instruction_origin >> strip_tac
  >- (disj2_tac >> qexists `j` >> simp[]) 
  >- (disj1_tac >>
      `MEM j.inst_opcode [INITIAL_FMP; FMP_PARAM]` by metis_tac[] >>
      fs[] >> metis_tac[]) >>
  drule_all fmp_optional_outputs_origin >> strip_tac >>
  `j.inst_opcode = RETPC_PARAM /\ i.inst_opcode = RETPC_PARAM` by metis_tac[] >>
  disj2_tac >> qexists `i` >> simp[] >>
  simp[fn_insts_def, fn_insts_blocks_MEM] >> qexists `entry` >> simp[]
QED

Theorem fmp_install_checked_root_upper_bound:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_make_root_layout ctx fn info runner s0 = SOME (FmpRootLayout n root newpc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root newpc s2) blocks = SOME (out,s3) /\
  MEM origin [GAS; RETPC_PARAM] /\
  copy_phi_upper_bound origin (fn with fn_blocks := blocks) P ==>
  copy_phi_upper_bound origin (fn with fn_blocks := out) P
Proof
  strip_tac >>
  drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule_all fmp_make_root_layout_opaque_shape >> strip_tac >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  `!i. MEM i (OPTION_TO_LIST oldpc) ==> i.inst_opcode = RETPC_PARAM` by
    (Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def] >>
     metis_tac[fmpLowerPropsTheory.split_fmp_entry_retpc_opcode]) >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> fs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  gvs[] >>
  irule fmp_install_root_upper_bound >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem copy_phi_upper_bound_blocks:
  fn'.fn_blocks = fn.fn_blocks ==>
  (copy_phi_upper_bound origin fn' P <=> copy_phi_upper_bound origin fn P)
Proof
  simp[copy_phi_upper_bound_def, fn_insts_def]
QED

Theorem copy_phi_upper_bound_metadata[simp]:
  copy_phi_upper_bound origin (fn with fn_fmp_signature := sig) P <=>
  copy_phi_upper_bound origin fn P
Proof
  irule copy_phi_upper_bound_blocks >> simp[]
QED

Theorem copy_phi_upper_bound_sealed_blocks[simp]:
  copy_phi_upper_bound origin
    (fn with <|fn_blocks := blocks; fn_fmp_signature := sig|>) P <=>
  copy_phi_upper_bound origin (fn with fn_blocks := blocks) P
Proof
  irule copy_phi_upper_bound_blocks >> simp[]
QED

Theorem copy_phi_upper_bound_same_blocks[simp]:
  copy_phi_upper_bound origin (fn with fn_blocks := fn.fn_blocks) P <=>
  copy_phi_upper_bound origin fn P
Proof
  irule copy_phi_upper_bound_blocks >> simp[]
QED

Theorem fmp_lower_function_opaque_upper_bound:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  o1_fn_shape ctx fn /\ ir_supply_covers_fn s fn /\
  origin = RETPC_PARAM ==>
  copy_phi_upper_bound origin fn' (copy_phi_var origin fn)
Proof
  simp[fmpLowerDefsTheory.fmp_lower_function_def,
       fmpLowerDefsTheory.fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[copy_phi_upper_bound_identity] >>
  drule fmpLowerDefsTheory.fmp_checked_seal_some >> strip_tac >>
  gvs[fmpLowerDefsTheory.fmp_seal_def, copy_phi_upper_bound_identity] >>
  Cases_on `root_layout` >> gvs[] >>
  (`?users oldpc suffix. split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix)` by
     (gvs[fmpLowerDefsTheory.fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
   `!origin. ~copy_phi_var origin fn runner` by
     metis_tac[fresh_runner_not_input_opaque] >>
   `opaque_use_ok fn` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
   `!i y. MEM i (fn_insts fn) /\ i.inst_opcode = SETFMP /\
      MEM (Var y) i.inst_operands ==>
      ~retpc_var fn y` by metis_tac[input_setfmp_not_opaque] >>
   `!point base. MEM (point,base) (fmp_plan_to_alist fn plan) ==>
      ~retpc_var fn base` by
     (rpt strip_tac >> rename1 `MEM (point,target) (fmp_plan_to_alist fn plan)` >>
      `FLOOKUP plan point = SOME target` by fs[fmpLowerPropsTheory.MEM_fmp_plan_to_alist] >>
      drule_all analyze_fmp_reclaims_output >> strip_tac >>
      fs[o1_fn_shape_def] >> metis_tac[]) >>
   `!origin. origin = RETPC_PARAM ==>
      copy_phi_upper_bound origin (fn with fn_blocks := blocks) (copy_phi_var origin fn)` by
     (gen_tac >> disch_tac >> irule fmp_lower_blocks_upper_bound >>
      conj_tac >- (fs[retpc_var_def] >> metis_tac[]) >>
      conj_tac >- (goal_assum (drule_at Any) >>
        fs[retpc_var_def] >> metis_tac[]) >>
      simp[copy_phi_upper_bound_identity]) >>
   irule fmp_install_checked_root_upper_bound >>
   conj_tac >- metis_tac[] >> simp[] >>
   goal_assum (drule_at Any) >> simp[] >> metis_tac[])
QED

Theorem fmp_lower_function_gas_upper_bound:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  o1_fn_shape ctx fn /\ ir_supply_covers_fn s fn /\
  (!i x. MEM i (fn_insts fn) /\ gas_var fn x /\
    MEM (Var x) i.inst_operands ==> gas_use_ok i x) /\
  origin = GAS ==>
  copy_phi_upper_bound origin fn' (copy_phi_var origin fn)
Proof
  simp[fmpLowerDefsTheory.fmp_lower_function_def,
       fmpLowerDefsTheory.fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[copy_phi_upper_bound_identity] >>
  drule fmpLowerDefsTheory.fmp_checked_seal_some >> strip_tac >>
  gvs[fmpLowerDefsTheory.fmp_seal_def, copy_phi_upper_bound_identity] >>
  Cases_on `root_layout` >> gvs[] >>
  (`?users oldpc suffix. split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix)` by
     (gvs[fmpLowerDefsTheory.fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
   `!origin. ~copy_phi_var origin fn runner` by
     metis_tac[fresh_runner_not_input_opaque] >>
   `!i y. MEM i (fn_insts fn) /\ i.inst_opcode = SETFMP /\
      MEM (Var y) i.inst_operands ==>
      ~gas_var fn y` by
     (rpt strip_tac >> rename1 `inst.inst_opcode = SETFMP` >>
      qpat_x_assum `!i x. MEM i (fn_insts fn) /\ gas_var fn x /\ _ ==> _`
        (qspecl_then [`inst`, `y`] mp_tac) >>
      simp[gas_use_ok_def]) >>
   `!point base. MEM (point,base) (fmp_plan_to_alist fn plan) ==>
      ~gas_var fn base` by
     (rpt strip_tac >> rename1 `MEM (point,target) (fmp_plan_to_alist fn plan)` >>
      `FLOOKUP plan point = SOME target` by fs[fmpLowerPropsTheory.MEM_fmp_plan_to_alist] >>
      drule_all analyze_fmp_reclaims_output >> strip_tac >>
      fs[o1_fn_shape_def] >> metis_tac[]) >>
   `!origin. origin = GAS ==>
      copy_phi_upper_bound origin (fn with fn_blocks := blocks) (copy_phi_var origin fn)` by
     (gen_tac >> disch_tac >> irule fmp_lower_blocks_upper_bound >>
      conj_tac >- (fs[gas_var_def] >> metis_tac[]) >>
      conj_tac >- (goal_assum (drule_at Any) >>
        fs[gas_var_def] >> metis_tac[]) >>
      simp[copy_phi_upper_bound_identity]) >>
   irule fmp_install_checked_root_upper_bound >>
   conj_tac >- metis_tac[] >> simp[] >>
   goal_assum (drule_at Any) >> simp[] >> metis_tac[])
QED

Theorem fmp_lower_function_gas_var_reflect:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  o1_fn_shape ctx fn /\ ir_supply_covers_fn s fn /\
  (!i x. MEM i (fn_insts fn) /\ gas_var fn x /\
    MEM (Var x) i.inst_operands ==> gas_use_ok i x) /\ gas_var fn' x ==>
  gas_var fn x
Proof
  strip_tac >> drule fmp_lower_function_gas_upper_bound >>
  disch_then (qspec_then `GAS` mp_tac) >> simp[] >> strip_tac >>
  fs[gas_var_def] >> metis_tac[copy_phi_upper_bound_sound]
QED

Theorem fmp_lower_function_retpc_var_reflect:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  o1_fn_shape ctx fn /\ ir_supply_covers_fn s fn /\ retpc_var fn' x ==>
  retpc_var fn x
Proof
  strip_tac >> drule fmp_lower_function_opaque_upper_bound >>
  disch_then (qspec_then `RETPC_PARAM` mp_tac) >> simp[] >> strip_tac >>
  fs[retpc_var_def] >> metis_tac[copy_phi_upper_bound_sound]
QED

Theorem last_operand_unique[local]:
  !ops x. ops <> [] /\
          (MEM x ops ==> ?front. ops = front ++ [x] /\ ~MEM x front) ==>
          ~MEM x (FRONT ops)
Proof
  rpt strip_tac >>
  `MEM x ops` by metis_tac[APPEND_FRONT_LAST, MEM_APPEND] >>
  gvs[GSYM SNOC_APPEND]
QED

Theorem fmp_lower_inst_opaque_use:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\
  MEM j out /\ MEM x s.irs_used_vars /\ x <> runner /\
  (use_ok = gas_use_ok \/ use_ok = retpc_use_ok) /\
  (MEM (Var x) inst.inst_operands ==> use_ok inst x) ==>
  (MEM (Var x) j.inst_operands ==> use_ok j x)
Proof
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (rpt strip_tac >>
      gvs[fmpLowerDefsTheory.fmp_lower_inst_def,
          fmpLowerDefsTheory.fmp_lower_inst_shape_def, AllCaseEqs(), mk_inst_def] >>
      imp_res_tac fresh_ir_var_contract >>
      gvs[gas_use_ok_def, retpc_use_ok_def] >> metis_tac[MEM]) >>
  Cases_on `inst.inst_opcode = DRET`
  >- simp[fmpLowerDefsTheory.fmp_lower_inst_def, fmpLowerDefsTheory.fmp_lower_inst_shape_def] >>
  Cases_on `inst.inst_opcode = GETFMP`
  >- (rpt strip_tac >>
      gvs[fmpLowerDefsTheory.fmp_lower_inst_def,
          fmpLowerDefsTheory.fmp_lower_inst_shape_def, AllCaseEqs(),
          gas_use_ok_def, retpc_use_ok_def]) >>
  Cases_on `inst.inst_opcode = SETFMP`
  >- (rpt strip_tac >>
      gvs[fmpLowerDefsTheory.fmp_lower_inst_def,
          fmpLowerDefsTheory.fmp_lower_inst_shape_def, AllCaseEqs(),
          gas_use_ok_def, retpc_use_ok_def]) >>
  Cases_on `inst.inst_opcode = RETFMP`
  >- (rpt strip_tac >>
      gvs[fmpLowerDefsTheory.fmp_lower_inst_def,
          fmpLowerDefsTheory.fmp_lower_inst_shape_def, AllCaseEqs(),
          gas_use_ok_def, retpc_use_ok_def] >>
      `!y. MEM y (FRONT inst.inst_operands) ==> MEM y inst.inst_operands`
        by metis_tac[APPEND_FRONT_LAST, MEM_APPEND] >>
      `MEM (LAST inst.inst_operands) inst.inst_operands`
        by metis_tac[APPEND_FRONT_LAST, MEM_APPEND, MEM] >>
      metis_tac[last_operand_unique, venomStateTheory.operand_11]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (rpt strip_tac >>
      gvs[fmpLowerDefsTheory.fmp_lower_inst_def,
          fmpLowerDefsTheory.fmp_lower_inst_shape_def, AllCaseEqs()] >>
      drule fmpLowerDefsTheory.fmp_resolve_invoke_some >> strip_tac >>
      gvs[gas_use_ok_def, retpc_use_ok_def] >>
      Cases_on `(fmp_info_of_signature sig).fi_needs_fmp` >> gvs[]) >>
  simp[fmpLowerDefsTheory.fmp_lower_inst_ordinary, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem fmp_lower_indexed_opaque_use:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') ==>
  ir_supply_inst_ok s /\ MEM x s.irs_used_vars /\
  x <> runner /\ (use_ok = gas_use_ok \/ use_ok = retpc_use_ok) /\
  (!i. MEM i insts /\ MEM (Var x) i.inst_operands ==> use_ok i x) ==>
  !j. MEM j out /\ MEM (Var x) j.inst_operands ==> use_ok j x
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`, `k`] >>
  Induct_on `insts` >- simp[fmpLowerDefsTheory.fmp_lower_indexed_def] >>
  simp[fmpLowerIndexedPropsTheory.fmp_lower_indexed_cons, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  (gvs[] >>
   drule_all fmp_emit_restores_supply >> strip_tac >>
   drule_all fmp_lower_inst_supply >> strip_tac >>
   `MEM x s0.irs_used_vars /\ MEM x s1.irs_used_vars` by
     (fs[dretDesugarProofsTheory.dret_supply_extends_def] >> metis_tac[MEM_APPEND]) >>
   gen_tac >> disch_tac >>
   `MEM (Var x) j.inst_operands` by metis_tac[] >>
   Cases_on `MEM j prefix`
   >- (drule_all fmp_emit_restores_assign_origin >> strip_tac >>
       gvs[gas_use_ok_def, retpc_use_ok_def, mk_inst_def]) >>
   Cases_on `MEM j head`
   >- (irule fmp_lower_inst_opaque_use >>
       goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
   `MEM j tail` by fs[] >>
   qpat_x_assum `!k s restores out leftover s'. _` drule >>
   disch_then (qspec_then `j` mp_tac) >> simp[])
QED


Theorem fmp_lower_blocks_opaque_use:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') ==>
  ir_supply_inst_ok s /\ MEM x s.irs_used_vars /\ x <> runner /\
  (use_ok = gas_use_ok \/ use_ok = retpc_use_ok) /\
  (!bb i. MEM bb bbs /\ MEM i bb.bb_instructions /\
     MEM (Var x) i.inst_operands ==> use_ok i x) ==>
  !bb j. MEM bb out /\ MEM j bb.bb_instructions /\
     MEM (Var x) j.inst_operands ==> use_ok j x
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`] >>
  Induct_on `bbs` >- simp[fmpLowerDefsTheory.fmp_lower_blocks_def] >>
  simp[fmpLowerDefsTheory.fmp_lower_blocks_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  (gvs[] >>
   drule_all fmp_lower_indexed_supply >> strip_tac >>
   rename1 `fmp_lower_indexed _ _ _ _ _ _ _ _ = SOME (_,_,mid)` >>
   `MEM x mid.irs_used_vars` by
     (fs[dretDesugarProofsTheory.dret_supply_extends_def] >> metis_tac[MEM_APPEND]) >>
   drule fmp_lower_indexed_opaque_use >> strip_tac >>
   qpat_x_assum `!s restores out leftover s'. _` drule >> strip_tac >>
   rpt gen_tac >> disch_tac >>
   Cases_on `bb = h with bb_instructions := insts`
   >- (qpat_x_assum `!bb j. _` kall_tac >>
       qpat_x_assum `!x use_ok j. _` (qspec_then `x` mp_tac) >>
       disch_then irule >> gvs[] >> metis_tac[]) >>
   qpat_x_assum `!x use_ok j. _` kall_tac >>
   qpat_x_assum `!bb j. _` irule >> simp[] >> metis_tac[])
QED

Theorem fmp_make_root_layout_operand_origin:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  fmp_make_root_layout ctx fn info runner s = SOME (FmpRootLayout n root newpc s') /\
  (MEM j (OPTION_TO_LIST root) \/ MEM j (OPTION_TO_LIST newpc)) /\
  MEM (Var x) j.inst_operands ==>
  MEM j (OPTION_TO_LIST oldpc)
Proof
  strip_tac >> Cases_on `oldpc` >>
  gvs[fmpLowerDefsTheory.fmp_make_root_layout_def, AllCaseEqs(),
      callLayoutDefsTheory.OPTION_TO_LIST_def, mk_inst_def,
      fmpLowerDefsTheory.set_param_index_def]
QED

Theorem fmp_install_checked_root_opaque_use:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_make_root_layout ctx fn info runner s0 = SOME (FmpRootLayout n root newpc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root newpc s2) blocks = SOME (out,s3) ==>
  !x use_ok.
  (!i. MEM i (fn_insts (fn with fn_blocks := blocks)) /\
       MEM (Var x) i.inst_operands ==> use_ok i x) ==>
  !j. MEM j (fn_insts (fn with fn_blocks := out)) /\
      MEM (Var x) j.inst_operands ==> use_ok j x
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> fs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  qpat_x_assum `blocks = entry::rest` SUBST_ALL_TAC >>
  rpt strip_tac >> drule_all fmp_install_root_instruction_origin >> strip_tac
  >- metis_tac[]
  >- (`MEM j (OPTION_TO_LIST oldpc)` by metis_tac[fmp_make_root_layout_operand_origin] >>
      `MEM j (fn_insts (fn with fn_blocks := entry::rest))` by
        (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM_APPEND]) >>
      metis_tac[]) >>
  `MEM j (OPTION_TO_LIST oldpc)` by metis_tac[fmp_make_root_layout_operand_origin] >>
  `MEM j (fn_insts (fn with fn_blocks := entry::rest))` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM_APPEND]) >>
  metis_tac[]
QED

Theorem fmp_make_root_layout_used_vars:
  fmp_make_root_layout ctx fn info runner s = SOME (FmpRootLayout n root pc s') ==>
  s'.irs_used_vars = s.irs_used_vars
Proof
  simp[fmpLowerDefsTheory.fmp_make_root_layout_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[irSupplyTheory.fresh_inst_id_def, AllCaseEqs()]
QED

Theorem fmp_lower_function_allowed_use:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ ir_supply_inst_ok s /\
  MEM x s.irs_used_vars /\ (use_ok = gas_use_ok \/ use_ok = retpc_use_ok) /\
  (!i. MEM i (fn_insts fn) /\ MEM (Var x) i.inst_operands ==> use_ok i x) ==>
  !j. MEM j (fn_insts fn') /\ MEM (Var x) j.inst_operands ==> use_ok j x
Proof
  simp[fmpLowerDefsTheory.fmp_lower_function_def,
       fmpLowerDefsTheory.fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >>
  gvs[] >>
  drule fmpLowerDefsTheory.fmp_checked_seal_some >> strip_tac >>
  gvs[fmpLowerDefsTheory.fmp_seal_def, fn_insts_def] >>
  Cases_on `root_layout` >> gvs[] >>
  drule_all irSupplyTheory.fresh_ir_var_inst_ok >> strip_tac >>
  drule fresh_ir_var_contract >> strip_tac >>
  drule_all fmp_make_root_layout_inst_ok >> strip_tac >>
  drule fmp_make_root_layout_used_vars >> strip_tac >>
  `?users oldpc suffix. split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix)` by
    (qpat_x_assum `fmp_make_root_layout _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[fmpLowerDefsTheory.fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  `x <> runner` by metis_tac[] >>
  drule fmp_lower_blocks_opaque_use >>
  disch_then (qspec_then `x` assume_tac) >>
  `!use_ok. (use_ok = gas_use_ok \/ use_ok = retpc_use_ok) /\
     (!i. MEM i (fn_insts_blocks fn.fn_blocks) /\ MEM (Var x) i.inst_operands ==> use_ok i x) ==>
     !j. MEM j (fn_insts_blocks blocks) /\ MEM (Var x) j.inst_operands ==> use_ok j x` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!use_ok bb j. _` mp_tac >>
     simp[fn_insts_blocks_MEM] >>
     fs[fn_insts_blocks_MEM] >> metis_tac[]) >>
  qpat_x_assum `!use_ok bb j. _` kall_tac >>
  drule fmp_install_checked_root_opaque_use >>
  rpt (disch_then drule) >>
  disch_then (qspec_then `x` (assume_tac o SRULE[fn_insts_def])) >>
  rpt strip_tac >>
  qpat_x_assum `!use_ok j. (!i. MEM i (fn_insts_blocks blocks) /\ _ ==> _) /\ _ ==> _`
    irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_x_assum `!use_ok. (use_ok = _ \/ _) /\ _ ==> _` irule >>
  fs[]
QED

Theorem fmp_lower_function_opaque_use_ok:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn /\
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn ==>
  opaque_use_ok fn'
Proof
  strip_tac >>
  `opaque_use_ok fn` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
  rewrite_tac[opaque_use_ok_def] >> rpt strip_tac >>
  `retpc_var fn x` by metis_tac[fmp_lower_function_retpc_var_reflect] >>
  `MEM x s.irs_used_vars` by
    (fs[venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
        venomFnScheduleRunnerTheory.list_subset_def, EVERY_MEM, retpc_var_def] >>
     metis_tac[copy_phi_var_in_ir_vars]) >>
  `!i. MEM i (fn_insts fn) /\ MEM (Var x) i.inst_operands ==> retpc_use_ok i x` by
    metis_tac[opaque_use_ok_retpc_use] >>
  drule_all (SRULE[] (Q.INST [`use_ok` |-> `retpc_use_ok`] fmp_lower_function_allowed_use)) >>
  metis_tac[]
QED
