Theory gasShadowUnitGuards
Ancestors
  gasShadowUnitObservations gasShadowUnit gasShadowState vyperCompiler venomInst
  venomWf venomExecSemantics cfgDefs memLocDefs pointerConfinedDefs fcgDefs
  defsReachCheck list

Theorem gas_shadow_lookup_function:
  !fs gs name. LIST_REL gas_shadow_function fs gs ==>
    OPTREL gas_shadow_function (lookup_function name fs) (lookup_function name gs)
Proof
  Induct >> Cases_on `gs` >> simp[lookup_function_def, FIND_thm] >>
  rpt strip_tac >>
  `h'.fn_name = h.fn_name` by metis_tac[gas_shadow_function_fields] >>
  simp[] >> IF_CASES_TAC >> simp[] >>
  fs[lookup_function_def]
QED

Theorem gas_shadow_context_entry:
  gas_shadow_context c d ==> c.ctx_entry = d.ctx_entry
Proof
  simp[gas_shadow_context_def] >> strip_tac >>
  qpat_x_assum `_ = c` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem gas_shadow_fcg_visit:
  gas_shadow_context c d ==> fcg_visit c name a = fcg_visit d name a
Proof
  strip_tac >>
  `OPTREL gas_shadow_function (lookup_function name c.ctx_functions)
                            (lookup_function name d.ctx_functions)`
    by (irule gas_shadow_lookup_function >> fs[gas_shadow_context_def]) >>
  Cases_on `lookup_function name c.ctx_functions` >>
  Cases_on `lookup_function name d.ctx_functions` >>
  gvs[fcg_visit_def] >>
  metis_tac[gas_shadow_fcg_scan_function]
QED

Theorem gas_shadow_fcg_dfs:
  !c stack visited a. !d. gas_shadow_context c d ==>
    fcg_dfs c stack visited a = fcg_dfs d stack visited a
Proof
  recInduct fcg_dfs_ind >> rpt strip_tac >- simp[fcg_dfs_def] >>
  `fcg_visit ctx fn_name fcg = fcg_visit d fn_name fcg`
    by metis_tac[gas_shadow_fcg_visit] >>
  simp[Once fcg_dfs_def] >>
  simp[SimpRHS, Once fcg_dfs_def] >>
  Cases_on `MEM fn_name visited` >- simp[] >>
  Cases_on `fcg_visit d fn_name fcg` >> gvs[] >> metis_tac[]
QED

Theorem gas_shadow_fcg_analyze:
  gas_shadow_context c d ==> fcg_analyze c = fcg_analyze d
Proof
  strip_tac >>
  `c.ctx_entry = d.ctx_entry` by metis_tac[gas_shadow_context_entry] >>
  simp[fcg_analyze_def] >> Cases_on `d.ctx_entry` >>
  simp[gas_shadow_fcg_dfs]
QED

Theorem gas_shadow_reachable_fcg_acyclic:
  gas_shadow_context c d ==>
    (reachable_fcg_acyclic c (fcg_analyze c) <=>
     reachable_fcg_acyclic d (fcg_analyze d))
Proof
  strip_tac >>
  `c.ctx_entry = d.ctx_entry` by metis_tac[gas_shadow_context_entry] >>
  `fcg_analyze c = fcg_analyze d` by metis_tac[gas_shadow_fcg_analyze] >>
  simp[reachable_fcg_acyclic_def]
QED

(* ===== Opcode-insensitive list observations ===== *)

(* Split a gas_shadow_inst assumption into its two cases and simplify. *)
fun gas_shadow_inst_tac ths =
  rpt strip_tac >>
  qpat_x_assum `gas_shadow_inst _ _`
    (strip_assume_tac o REWRITE_RULE [gas_shadow_inst_def]) >>
  gvs ths;

Theorem gas_shadow_inst_opcode:
  gas_shadow_inst i j /\ opc <> GAS /\ opc <> GASPRICE ==>
    (i.inst_opcode = opc <=> j.inst_opcode = opc) /\
    (i.inst_opcode = opc ==> i = j)
Proof
  rw[gas_shadow_inst_def] >> gvs[] >> metis_tac[]
QED

Theorem gas_shadow_list_filter_opc:
  !xs ys. LIST_REL gas_shadow_inst xs ys /\ opc <> GAS /\ opc <> GASPRICE ==>
    FILTER (\i. i.inst_opcode = opc) xs = FILTER (\i. i.inst_opcode = opc) ys
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  `FILTER (\i. i.inst_opcode = opc) xs = FILTER (\i. i.inst_opcode = opc) t`
    by metis_tac[] >>
  drule_all gas_shadow_inst_opcode >> strip_tac >>
  Cases_on `h.inst_opcode = opc` >> gvs[]
QED

Theorem gas_shadow_functions_filter_opc:
  !fs gs. LIST_REL gas_shadow_function fs gs /\ opc <> GAS /\ opc <> GASPRICE ==>
    FILTER (\i. i.inst_opcode = opc) (FLAT (MAP fn_insts fs)) =
    FILTER (\i. i.inst_opcode = opc) (FLAT (MAP fn_insts gs))
Proof
  Induct >> Cases_on `gs` >> simp[FILTER_APPEND_DISTRIB] >>
  metis_tac[gas_shadow_function_insts, gas_shadow_list_filter_opc]
QED

Theorem gas_shadow_list_last:
  !xs ys. LIST_REL R xs ys /\ xs <> [] ==> R (LAST xs) (LAST ys)
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  Cases_on `xs` >> Cases_on `t` >> gvs[LAST_CONS] >>
  first_x_assum irule >> simp[]
QED

Theorem gas_shadow_list_foldl:
  !xs ys a. LIST_REL R xs ys /\ (!m x y. R x y ==> f m x = g m y) ==>
    FOLDL f a xs = FOLDL g a ys
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >> metis_tac[]
QED

Theorem gas_shadow_list_filter_rel:
  !xs ys. LIST_REL R xs ys /\ (!x y. R x y ==> (P x <=> Q y)) ==>
    LIST_REL R (FILTER P xs) (FILTER Q ys)
Proof
  Induct >> Cases_on `ys` >> rw[] >> metis_tac[]
QED

(* ===== Control flow ===== *)

Theorem gas_shadow_inst_succs:
  gas_shadow_inst i j ==>
    get_successors i = get_successors j /\
    (is_terminator i.inst_opcode <=> is_terminator j.inst_opcode) /\
    (i.inst_opcode = PHI <=> j.inst_opcode = PHI)
Proof
  rw[gas_shadow_inst_def] >> simp[get_successors_def, is_terminator_def]
QED

Theorem gas_shadow_function_blocks:
  gas_shadow_function f g ==> LIST_REL gas_shadow_block f.fn_blocks g.fn_blocks
Proof
  simp[gas_shadow_function_def]
QED

Theorem gas_shadow_block_succs:
  gas_shadow_block b c ==> bb_succs b = bb_succs c
Proof
  rw[gas_shadow_block_def, bb_succs_def] >>
  Cases_on `b.bb_instructions` >> Cases_on `c.bb_instructions` >> gvs[] >>
  rename1 `LIST_REL gas_shadow_inst xs ys` >>
  `gas_shadow_inst (LAST (h::xs)) (LAST (h'::ys))`
    by (irule gas_shadow_list_last >> simp[]) >>
  metis_tac[gas_shadow_inst_succs]
QED

Theorem gas_shadow_cfg_analyze:
  gas_shadow_function f g ==> cfg_analyze f = cfg_analyze g
Proof
  strip_tac >> drule gas_shadow_function_blocks >> strip_tac >>
  `init_succs f.fn_blocks : string |-> string list = init_succs g.fn_blocks /\
   init_preds f.fn_blocks : string |-> string list = init_preds g.fn_blocks`
    by (simp[init_succs_def, init_preds_def] >>
        irule gas_shadow_list_foldl >> qexists_tac `gas_shadow_block` >>
        simp[gas_shadow_block_def]) >>
  `build_succs f.fn_blocks = build_succs g.fn_blocks /\
   !s. build_preds f.fn_blocks s = build_preds g.fn_blocks s`
    by (simp[build_succs_def, build_preds_def] >> rpt strip_tac >>
        irule gas_shadow_list_foldl >> qexists_tac `gas_shadow_block` >>
        simp[gas_shadow_block_def] >> metis_tac[gas_shadow_block_succs, gas_shadow_block_def]) >>
  `MAP (\bb. bb.bb_label) f.fn_blocks = MAP (\bb. bb.bb_label) g.fn_blocks`
    by metis_tac[gas_shadow_function_labels, fn_labels_def] >>
  `(case entry_block f of NONE => NONE | SOME bb => SOME bb.bb_label) =
   (case entry_block g of NONE => NONE | SOME bb => SOME bb.bb_label)`
    by (simp[entry_block_def] >>
        Cases_on `f.fn_blocks` >> Cases_on `g.fn_blocks` >>
        gvs[gas_shadow_block_def]) >>
  simp[cfg_analyze_def]
QED

Theorem gas_shadow_fn_reachable_blocks:
  gas_shadow_function f g ==>
    gas_shadow_function (fn_reachable_blocks f) (fn_reachable_blocks g)
Proof
  strip_tac >>
  `cfg_analyze f = cfg_analyze g` by metis_tac[gas_shadow_cfg_analyze] >>
  fs[gas_shadow_function_def, fn_reachable_blocks_def] >> conj_tac
  >- (qpat_x_assum `_ = f` (SUBST1_TAC o SYM) >> simp[]) >>
  irule gas_shadow_list_filter_rel >> simp[gas_shadow_block_def]
QED

Theorem gas_shadow_bb_well_formed:
  gas_shadow_block b c ==> (bb_well_formed b <=> bb_well_formed c)
Proof
  rw[gas_shadow_block_def] >>
  `LENGTH b.bb_instructions = LENGTH c.bb_instructions`
    by metis_tac[LIST_REL_LENGTH] >>
  `!n. n < LENGTH b.bb_instructions ==>
       (is_terminator (EL n b.bb_instructions).inst_opcode <=>
        is_terminator (EL n c.bb_instructions).inst_opcode) /\
       ((EL n b.bb_instructions).inst_opcode = PHI <=>
        (EL n c.bb_instructions).inst_opcode = PHI)`
    by (rpt strip_tac >>
        `gas_shadow_inst (EL n b.bb_instructions) (EL n c.bb_instructions)`
          by fs[LIST_REL_EL_EQN] >>
        metis_tac[gas_shadow_inst_succs]) >>
  `b.bb_instructions <> [] ==>
     (is_terminator (LAST b.bb_instructions).inst_opcode <=>
      is_terminator (LAST c.bb_instructions).inst_opcode)`
    by metis_tac[gas_shadow_list_last, gas_shadow_inst_succs] >>
  `b.bb_instructions = [] <=> c.bb_instructions = []`
    by metis_tac[LENGTH_NIL] >>
  simp[bb_well_formed_def] >> eq_tac >> rpt strip_tac >> metis_tac[]
QED

Theorem fn_succs_closed_flat:
  fn_succs_closed fn <=>
    !s. MEM s (FLAT (MAP bb_succs fn.fn_blocks)) ==> MEM s (fn_labels fn)
Proof
  simp[fn_succs_closed_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED

Theorem gas_shadow_wf_function:
  gas_shadow_function f g ==> (wf_function f <=> wf_function g)
Proof
  strip_tac >> drule gas_shadow_function_blocks >> strip_tac >>
  `fn_labels f = fn_labels g` by metis_tac[gas_shadow_function_labels] >>
  `fn_has_entry f <=> fn_has_entry g` by metis_tac[gas_shadow_function_entry] >>
  `fn_inst_ids_distinct f <=> fn_inst_ids_distinct g`
    by metis_tac[gas_shadow_function_ids, fn_inst_ids_distinct_def] >>
  `(!bb. MEM bb f.fn_blocks ==> bb_well_formed bb) <=>
   (!bb. MEM bb g.fn_blocks ==> bb_well_formed bb)`
    by (simp[GSYM EVERY_MEM] >> irule gas_shadow_list_every >>
        qexists_tac `gas_shadow_block` >> simp[] >>
        metis_tac[gas_shadow_bb_well_formed]) >>
  `FLAT (MAP bb_succs f.fn_blocks) = FLAT (MAP bb_succs g.fn_blocks)`
    by (AP_TERM_TAC >> irule gas_shadow_list_observe >>
        qexists_tac `gas_shadow_block` >> simp[gas_shadow_block_succs]) >>
  simp[wf_function_def, fn_succs_closed_flat]
QED

(* ===== Pointer discipline ===== *)

Theorem gas_shadow_pointer_use_step:
  gas_shadow_function f g ==> pointer_use_step f = pointer_use_step g
Proof
  strip_tac >> drule gas_shadow_function_blocks >> strip_tac >>
  simp[FUN_EQ_THM, pointer_use_step_def] >> gen_tac >>
  AP_TERM_TAC >> irule gas_shadow_list_observe >>
  qexists_tac `gas_shadow_block` >> simp[gas_shadow_block_def] >>
  rpt strip_tac >> AP_TERM_TAC >> irule gas_shadow_list_observe >>
  qexists_tac `gas_shadow_inst` >> simp[] >>
  gas_shadow_inst_tac [is_pointer_preserving_op_def]
QED

Theorem gas_shadow_pv_closure:
  gas_shadow_function f g ==> pv_closure f = pv_closure g
Proof
  strip_tac >> drule gas_shadow_pointer_use_step >> strip_tac >>
  `pointer_use_step_step f = pointer_use_step_step g`
    by simp[FUN_EQ_THM, pointer_use_step_step_def] >>
  `!n. pointer_use_vars_fuel n f = pointer_use_vars_fuel n g`
    by (Induct >> simp[FUN_EQ_THM, pointer_use_vars_fuel_def]) >>
  `LENGTH (fn_insts f) = LENGTH (fn_insts g)`
    by metis_tac[gas_shadow_function_insts, LIST_REL_LENGTH] >>
  simp[FUN_EQ_THM, pv_closure_def]
QED

Theorem gas_shadow_opcode_root_list:
  gas_shadow_function f g /\ opc <> GAS /\ opc <> GASPRICE ==>
    opcode_root_list opc f = opcode_root_list opc g
Proof
  strip_tac >> simp[opcode_root_list_def] >> AP_TERM_TAC >>
  irule gas_shadow_list_observe >> qexists_tac `gas_shadow_inst` >>
  simp[gas_shadow_function_insts] >> rpt strip_tac >>
  drule_all gas_shadow_inst_opcode >> strip_tac >>
  Cases_on `x.inst_opcode = opc` >> gvs[]
QED

Theorem gas_shadow_param_root_list:
  gas_shadow_function f g ==> param_root_list pl f = param_root_list pl g
Proof
  strip_tac >> simp[param_root_list_def] >> AP_TERM_TAC >>
  irule gas_shadow_list_observe >> qexists_tac `gas_shadow_inst` >>
  simp[gas_shadow_function_insts] >> gas_shadow_inst_tac []
QED

Theorem gas_shadow_inst_ptr_checks:
  gas_shadow_inst i j ==>
    (ptr_use_ok_check PL pv i <=> ptr_use_ok_check PL pv j) /\
    (inst_ptr_ok_check PL pv i <=> inst_ptr_ok_check PL pv j) /\
    (affine_check pv i <=> affine_check pv j) /\
    (phi_check pv i <=> phi_check pv j) /\
    (write_excl_check pva pvo i <=> write_excl_check pva pvo j) /\
    (pv_def_check pl ar pv i <=> pv_def_check pl ar pv j)
Proof
  gas_shadow_inst_tac
    [inst_ptr_ok_check_def, ptr_use_ok_check_def, ptr_cmp_exempt_def,
       addr_operand_is_def, mem_write_ops_def, mem_read_ops_def,
       is_pointer_preserving_op_def, affine_check_def, phi_check_def,
       write_excl_check_def, pv_def_check_def]
QED

Theorem gas_shadow_fn_ptr_params:
  gas_shadow_function f g ==> fn_ptr_params f = fn_ptr_params g
Proof
  strip_tac >> drule gas_shadow_pv_closure >> strip_tac >>
  `!c. EVERY (\i. i.inst_opcode = INVOKE \/ ptr_use_ok_check (K []) c i)
         (fn_insts f) <=>
       EVERY (\i. i.inst_opcode = INVOKE \/ ptr_use_ok_check (K []) c i)
         (fn_insts g)`
    by (gen_tac >> irule gas_shadow_list_every >>
        qexists_tac `gas_shadow_inst` >> simp[gas_shadow_function_insts] >>
        rpt strip_tac >>
        `x.inst_opcode = INVOKE <=> y.inst_opcode = INVOKE`
          by metis_tac[gas_shadow_inst_filter] >>
        metis_tac[gas_shadow_inst_ptr_checks]) >>
  simp[fn_ptr_params_def] >> AP_TERM_TAC >>
  irule gas_shadow_list_observe >> qexists_tac `gas_shadow_inst` >>
  simp[gas_shadow_function_insts] >> gas_shadow_inst_tac []
QED

Theorem gas_shadow_fn_ptr_ok_check:
  gas_shadow_function f g ==> (fn_ptr_ok_check PL f <=> fn_ptr_ok_check PL g)
Proof
  strip_tac >>
  `opcode_root_list ALLOCA f = opcode_root_list ALLOCA g /\
   opcode_root_list DALLOCA f = opcode_root_list DALLOCA g`
    by (conj_tac >> irule gas_shadow_opcode_root_list >> simp[]) >>
  `!pl. param_root_list pl f = param_root_list pl g`
    by metis_tac[gas_shadow_param_root_list] >>
  drule gas_shadow_pv_closure >> strip_tac >>
  `f.fn_name = g.fn_name /\
   f.fn_forced_alloc_positions = g.fn_forced_alloc_positions`
    by metis_tac[gas_shadow_function_fields] >>
  `!pv pva pvo pl ar.
     EVERY (\inst. inst_ptr_ok_check PL pv inst /\ affine_check pv inst /\
                   phi_check pv inst /\ write_excl_check pva pvo inst /\
                   pv_def_check pl ar pv inst)
       (fn_insts f) <=>
     EVERY (\inst. inst_ptr_ok_check PL pv inst /\ affine_check pv inst /\
                   phi_check pv inst /\ write_excl_check pva pvo inst /\
                   pv_def_check pl ar pv inst)
       (fn_insts g)`
    by (rpt gen_tac >> irule gas_shadow_list_every >>
        qexists_tac `gas_shadow_inst` >> simp[gas_shadow_function_insts] >>
        metis_tac[gas_shadow_inst_ptr_checks]) >>
  simp[fn_ptr_ok_check_def]
QED

Theorem gas_shadow_ctx_ptr_param_list:
  gas_shadow_context c d ==> ctx_ptr_param_list c = ctx_ptr_param_list d
Proof
  strip_tac >> simp[FUN_EQ_THM, ctx_ptr_param_list_def] >>
  qx_gen_tac `nm` >>
  `OPTREL gas_shadow_function (lookup_function nm c.ctx_functions)
                            (lookup_function nm d.ctx_functions)`
    by (irule gas_shadow_lookup_function >> fs[gas_shadow_context_def]) >>
  Cases_on `lookup_function nm c.ctx_functions` >>
  Cases_on `lookup_function nm d.ctx_functions` >> gvs[] >>
  metis_tac[gas_shadow_fn_ptr_params]
QED

Theorem gas_shadow_ptr_ok_check:
  gas_shadow_context c d ==> (ptr_ok_check c <=> ptr_ok_check d)
Proof
  strip_tac >> drule gas_shadow_ctx_ptr_param_list >> strip_tac >>
  simp[ptr_ok_check_def] >> irule gas_shadow_list_every >>
  qexists_tac `gas_shadow_function` >>
  reverse conj_tac >- fs[gas_shadow_context_def] >>
  rpt strip_tac >> rename1 `gas_shadow_function f1 g1` >>
  `!PL. fn_ptr_ok_check PL f1 <=> fn_ptr_ok_check PL g1`
    by metis_tac[gas_shadow_fn_ptr_ok_check] >>
  `!PL. fn_ptr_ok_check PL (fn_reachable_blocks f1) <=>
        fn_ptr_ok_check PL (fn_reachable_blocks g1)`
    by metis_tac[gas_shadow_fn_ptr_ok_check, gas_shadow_fn_reachable_blocks] >>
  `wf_function f1 <=> wf_function g1` by metis_tac[gas_shadow_wf_function] >>
  `EVERY (\i. i.inst_opcode <> PHI) (fn_insts f1) <=>
   EVERY (\i. i.inst_opcode <> PHI) (fn_insts g1)`
    by (irule gas_shadow_list_every >> qexists_tac `gas_shadow_inst` >>
        simp[gas_shadow_function_insts] >> metis_tac[gas_shadow_inst_succs]) >>
  simp[]
QED

(* ===== Definite assignment ===== *)

Theorem gas_shadow_inst_outputs:
  gas_shadow_inst i j ==> i.inst_outputs = j.inst_outputs
Proof
  rw[gas_shadow_inst_def] >> simp[]
QED

Theorem gas_shadow_insts_writes:
  !xs ys. LIST_REL gas_shadow_inst xs ys ==>
    (EXISTS (\inst. MEM v inst.inst_outputs) xs <=>
     EXISTS (\inst. MEM v inst.inst_outputs) ys)
Proof
  Induct >> Cases_on `ys` >> simp[] >> metis_tac[gas_shadow_inst_outputs]
QED

Theorem gas_shadow_block_writes:
  gas_shadow_block b c ==> (bb_writes v b <=> bb_writes v c)
Proof
  rw[gas_shadow_block_def, bb_writes_def] >>
  irule gas_shadow_insts_writes >> simp[]
QED

Theorem gas_shadow_avoid_sweep:
  !bs cs R. LIST_REL gas_shadow_block bs cs ==>
    avoid_sweep v bs R = avoid_sweep v cs R
Proof
  Induct >> Cases_on `cs` >> simp[avoid_sweep_def] >> rpt strip_tac >>
  `h.bb_label = h'.bb_label` by fs[gas_shadow_block_def] >>
  `bb_writes v h <=> bb_writes v h'` by metis_tac[gas_shadow_block_writes] >>
  `bb_succs h = bb_succs h'` by metis_tac[gas_shadow_block_succs] >>
  simp[] >> metis_tac[]
QED

Theorem gas_shadow_avoid_reach:
  !n R. LIST_REL gas_shadow_block bs cs ==>
    avoid_reach v bs n R = avoid_reach v cs n R
Proof
  Induct >> simp[avoid_reach_def] >> rpt strip_tac >>
  `!R. avoid_sweep v bs R = avoid_sweep v cs R`
    by metis_tac[gas_shadow_avoid_sweep] >>
  rw[] >> metis_tac[]
QED

Theorem gas_shadow_avoid_fuel:
  !bs cs. LIST_REL gas_shadow_block bs cs ==> avoid_fuel bs = avoid_fuel cs
Proof
  simp[avoid_fuel_def] >> Induct >> Cases_on `cs` >> simp[] >>
  metis_tac[gas_shadow_block_succs]
QED

Theorem gas_shadow_var_def_reaches:
  gas_shadow_function f g /\ gas_shadow_block e e' ==>
    (var_def_reaches f e lbl v <=> var_def_reaches g e' lbl v)
Proof
  strip_tac >> drule gas_shadow_function_blocks >> strip_tac >>
  `e.bb_label = e'.bb_label` by fs[gas_shadow_block_def] >>
  `bb_writes v e <=> bb_writes v e'` by metis_tac[gas_shadow_block_writes] >>
  `avoid_fuel f.fn_blocks = avoid_fuel g.fn_blocks`
    by metis_tac[gas_shadow_avoid_fuel] >>
  `!n R. avoid_reach v f.fn_blocks n R = avoid_reach v g.fn_blocks n R`
    by metis_tac[gas_shadow_avoid_reach] >>
  simp[var_def_reaches_def]
QED

Theorem gas_shadow_insts_defs_reach_check:
  !xs ys defs.
    LIST_REL gas_shadow_inst xs ys /\
    (!v. var_def_reaches f e lbl v <=> var_def_reaches g e' lbl v) ==>
    (insts_defs_reach_check f e lbl defs xs <=>
     insts_defs_reach_check g e' lbl defs ys)
Proof
  Induct >> Cases_on `ys` >> simp[insts_defs_reach_check_def] >>
  rpt strip_tac >>
  `h.inst_operands = h'.inst_operands` by metis_tac[gas_shadow_inst_fields] >>
  `h.inst_outputs = h'.inst_outputs` by metis_tac[gas_shadow_inst_outputs] >>
  `h.inst_opcode = PHI <=> h'.inst_opcode = PHI`
    by metis_tac[gas_shadow_inst_succs] >>
  `!defs. insts_defs_reach_check f e lbl defs xs <=>
          insts_defs_reach_check g e' lbl defs t` by metis_tac[] >>
  gs[]
QED

Theorem gas_shadow_fn_defs_reach_uses_check:
  gas_shadow_function f g ==>
    (fn_defs_reach_uses_check f <=> fn_defs_reach_uses_check g)
Proof
  strip_tac >> drule gas_shadow_function_blocks >> strip_tac >>
  simp[fn_defs_reach_uses_check_def] >>
  Cases_on `f.fn_blocks` >> Cases_on `g.fn_blocks` >> gvs[] >>
  `!x y. gas_shadow_block x y ==>
         (insts_defs_reach_check f h x.bb_label [] x.bb_instructions <=>
          insts_defs_reach_check g h' y.bb_label [] y.bb_instructions)`
    by (rpt strip_tac >>
        `x.bb_label = y.bb_label` by fs[gas_shadow_block_def] >>
        `LIST_REL gas_shadow_inst x.bb_instructions y.bb_instructions`
          by fs[gas_shadow_block_def] >>
        `!v. var_def_reaches f h x.bb_label v <=>
             var_def_reaches g h' x.bb_label v`
          by metis_tac[gas_shadow_var_def_reaches] >>
        drule_all gas_shadow_insts_defs_reach_check >> metis_tac[]) >>
  `EVERY (\bb. insts_defs_reach_check f h bb.bb_label [] bb.bb_instructions) t <=>
   EVERY (\bb. insts_defs_reach_check g h' bb.bb_label [] bb.bb_instructions) t'`
    by (irule gas_shadow_list_every >> qexists_tac `gas_shadow_block` >>
        conj_tac >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem gas_shadow_defs_reach_uses_check:
  gas_shadow_context c d ==>
    (EVERY fn_defs_reach_uses_check c.ctx_functions <=>
     EVERY fn_defs_reach_uses_check d.ctx_functions)
Proof
  strip_tac >> irule gas_shadow_list_every >>
  qexists_tac `gas_shadow_function` >>
  reverse conj_tac >- fs[gas_shadow_context_def] >>
  metis_tac[gas_shadow_fn_defs_reach_uses_check]
QED

Theorem gas_shadow_lowering_context_ok:
  gas_shadow_context c d ==> (lowering_context_ok c <=> lowering_context_ok d)
Proof
  strip_tac >>
  `ctx_fn_names c = ctx_fn_names d` by metis_tac[gas_shadow_ctx_fn_names] >>
  `wf_invoke_targets_check c <=> wf_invoke_targets_check d`
    by metis_tac[gas_shadow_wf_invoke_targets_check] >>
  `ctx_inst_ids_distinct c <=> ctx_inst_ids_distinct d`
    by metis_tac[gas_shadow_ctx_inst_ids_distinct] >>
  `forced_alloc_inputs_check c <=> forced_alloc_inputs_check d`
    by metis_tac[gas_shadow_forced_alloc_inputs_check] >>
  `unit_alloca_budget c = unit_alloca_budget d`
    by metis_tac[gas_shadow_unit_alloca_budget] >>
  `EVERY (\fn. ALL_DISTINCT (fn_labels fn) /\ fn_has_entry fn) c.ctx_functions <=>
   EVERY (\fn. ALL_DISTINCT (fn_labels fn) /\ fn_has_entry fn) d.ctx_functions`
    by metis_tac[gas_shadow_ctx_labels_entry] >>
  `reachable_fcg_acyclic c (fcg_analyze c) <=> reachable_fcg_acyclic d (fcg_analyze d)`
    by metis_tac[gas_shadow_reachable_fcg_acyclic] >>
  `FILTER (\i. i.inst_opcode = DLOAD) (FLAT (MAP fn_insts c.ctx_functions)) =
   FILTER (\i. i.inst_opcode = DLOAD) (FLAT (MAP fn_insts d.ctx_functions))`
    by (irule gas_shadow_functions_filter_opc >> simp[] >>
        fs[gas_shadow_context_def]) >>
  `ptr_ok_check c <=> ptr_ok_check d` by metis_tac[gas_shadow_ptr_ok_check] >>
  `EVERY fn_defs_reach_uses_check c.ctx_functions <=>
   EVERY fn_defs_reach_uses_check d.ctx_functions`
    by metis_tac[gas_shadow_defs_reach_uses_check] >>
  simp[lowering_context_ok_def]
QED
