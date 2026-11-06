(*
 * The semantics never reads a function's FMP signature, so two contexts
 * whose functions differ only there run alike.
 *
 * fn_seal_eq f g says f and g are equal up to fn_fmp_signature, and
 * ctx_seal_eq C C' lifts it to contexts, position by position.  Then a
 * run is the same in both (run_defs_seal_eq, run_context_seal_eq), each
 * raw-reachable state of one is raw-reachable in the other at a
 * seal-equal function (raw_reachable_seal_eq), and so a memory fact that
 * does not look at the signature transports (mem_inv_seal_eq).
 *
 * FmpLowering on a function with no FMP operations only seals its
 * signature, which makes it an instance.
 *
 * TOP-LEVEL:
 *   run_context_seal_eq   - context runs are equal
 *   raw_reachable_seal_eq - reachable states correspond
 *   mem_inv_seal_eq       - the memory invariant transports
 *)
Theory ctxSealAgree
Ancestors
  venomExecSemantics venomInst venomState contextRawReachable
  contextCodegenRel unitMemInv ctxLookupAgreeHelpers list

Definition fn_seal_eq_def:
  fn_seal_eq f g <=>
    f with fn_fmp_signature := NONE = g with fn_fmp_signature := NONE
End

Definition ctx_seal_eq_def:
  ctx_seal_eq C C' <=>
    C'.ctx_entry = C.ctx_entry /\
    C'.ctx_global_reserved = C.ctx_global_reserved /\
    LIST_REL fn_seal_eq C.ctx_functions C'.ctx_functions
End

Theorem fn_seal_eq_sym:
  fn_seal_eq f g ==> fn_seal_eq g f
Proof
  simp[fn_seal_eq_def]
QED

Theorem fn_seal_eq_fields:
  fn_seal_eq f g ==>
  g.fn_blocks = f.fn_blocks /\ g.fn_name = f.fn_name
Proof
  rw[fn_seal_eq_def, venomInstTheory.ir_function_component_equality]
QED

Theorem ctx_seal_eq_sym:
  ctx_seal_eq C C' ==> ctx_seal_eq C' C
Proof
  rw[ctx_seal_eq_def] >> gvs[LIST_REL_EL_EQN] >> metis_tac[fn_seal_eq_sym]
QED

(* Lookup finds seal-equal functions at the same names. *)
Theorem lookup_function_seal_eq:
  !fns fns' name.
    LIST_REL fn_seal_eq fns fns' ==>
    (lookup_function name fns = NONE <=>
     lookup_function name fns' = NONE) /\
    (!f. lookup_function name fns = SOME f ==>
         ?f'. lookup_function name fns' = SOME f' /\ fn_seal_eq f f')
Proof
  Induct >> Cases_on `fns'` >> simp[lookup_function_def, FIND_thm] >>
  rpt gen_tac >> strip_tac >> fs[GSYM lookup_function_def] >>
  drule fn_seal_eq_fields >> strip_tac >>
  first_x_assum drule >> disch_then (qspec_then `name` strip_assume_tac) >>
  rw[lookup_function_def, FIND_thm] >> gvs[GSYM lookup_function_def]
QED

Theorem run_defs_seal_eq:
  (!fuel C inst s C'. ctx_seal_eq C C' ==>
     step_inst fuel C inst s = step_inst fuel C' inst s) /\
  (!fuel C bb s C'. ctx_seal_eq C C' ==>
     exec_block fuel C bb s = exec_block fuel C' bb s) /\
  (!fuel C fn s C' fn'. ctx_seal_eq C C' /\ fn_seal_eq fn fn' ==>
     run_blocks fuel C fn s = run_blocks fuel C' fn' s)
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "run"
QED

Resume run_defs_seal_eq[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [step_inst_def])) >>
  Cases_on `inst.inst_opcode = INVOKE` >- suspend "invoke" >> simp[]
QED

Resume run_defs_seal_eq[invoke]:
  simp[] >> Cases_on `decode_invoke inst` >- simp[] >>
  rename1 `decode_invoke inst = SOME decoded` >> PairCases_on `decoded` >>
  rename1 `decode_invoke inst = SOME (nm,ops)` >> simp[] >>
  `LIST_REL fn_seal_eq C.ctx_functions C'.ctx_functions`
    by fs[ctx_seal_eq_def] >>
  drule_then (qspec_then `nm` strip_assume_tac) lookup_function_seal_eq >>
  Cases_on `lookup_function nm C.ctx_functions` >- gvs[] >>
  rename1 `lookup_function nm C.ctx_functions = SOME callee` >>
  `?f'. lookup_function nm C'.ctx_functions = SOME f' /\ fn_seal_eq callee f'`
    by metis_tac[] >> simp[] >>
  Cases_on `eval_operands ops s` >- simp[] >>
  rename1 `eval_operands ops s = SOME args` >> simp[] >>
  drule fn_seal_eq_fields >> strip_tac >>
  `setup_callee f' args s = setup_callee callee args s`
    by simp[setup_callee_def] >>
  Cases_on `setup_callee callee args s` >- simp[] >>
  rename1 `setup_callee callee args s = SOME cs` >>
  `run_blocks fuel C callee cs = run_blocks fuel C' f' cs`
    by (first_x_assum irule >> simp[]) >> simp[]
QED

Resume run_defs_seal_eq[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  Cases_on `get_instruction bb s.vs_inst_idx` >- simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `step_inst fuel C inst s = step_inst fuel C' inst s` by metis_tac[] >>
  simp[] >> Cases_on `step_inst fuel C' inst s` >> simp[] >>
  IF_CASES_TAC >> simp[] >> first_x_assum irule >> simp[]
QED

Resume run_defs_seal_eq[run]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule fn_seal_eq_fields >> strip_tac >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [run_blocks_def])) >>
  Cases_on `fuel` >- simp[] >>
  rename1 `SUC n` >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >- simp[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >> simp[] >>
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  `exec_block n C bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
   exec_block n C' bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)`
    by (first_x_assum irule >> simp[]) >>
  simp[] >>
  Cases_on `exec_block n C' bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  simp[] >> IF_CASES_TAC >> simp[] >>
  first_x_assum irule >> simp[]
QED

Finalise run_defs_seal_eq

Theorem run_context_seal_eq:
  ctx_seal_eq C C' ==> run_context fuel C s = run_context fuel C' s
Proof
  strip_tac >> simp[run_context_def] >>
  `C'.ctx_entry = C.ctx_entry /\
   LIST_REL fn_seal_eq C.ctx_functions C'.ctx_functions`
    by fs[ctx_seal_eq_def] >>
  Cases_on `C.ctx_entry` >> simp[] >>
  rename1 `C.ctx_entry = SOME entry` >>
  drule_then (qspec_then `entry` strip_assume_tac) lookup_function_seal_eq >>
  Cases_on `lookup_function entry C.ctx_functions` >- gvs[] >>
  rename1 `lookup_function entry C.ctx_functions = SOME f` >>
  `?f'. lookup_function entry C'.ctx_functions = SOME f' /\ fn_seal_eq f f'`
    by metis_tac[] >> simp[run_function_def] >>
  drule fn_seal_eq_fields >> strip_tac >>
  simp[fn_entry_label_def, entry_block_def] >>
  CASE_TAC >> simp[] >> metis_tac[run_defs_seal_eq]
QED

Theorem fn_seal_eq_views:
  fn_seal_eq f g ==>
  active_inst g = active_inst f /\ enters_block g = enters_block f /\
  fn_entry_label g = fn_entry_label f /\ setup_callee g = setup_callee f
Proof
  strip_tac >> drule fn_seal_eq_fields >>
  simp[FUN_EQ_THM, active_inst_def, enters_block_def, fn_entry_label_def,
       entry_block_def, setup_callee_def]
QED

Theorem ctx_seal_eq_lookup:
  ctx_seal_eq C C' /\ lookup_function name C.ctx_functions = SOME f ==>
  ?f'. lookup_function name C'.ctx_functions = SOME f' /\ fn_seal_eq f f'
Proof
  rw[ctx_seal_eq_def] >> metis_tac[lookup_function_seal_eq]
QED

Theorem raw_reachable_seal_eq_ind[local]:
  !vs C fn inst s. raw_reachable vs C fn inst s ==>
    !C'. ctx_seal_eq C C' ==>
      ?fn'. fn_seal_eq fn fn' /\ raw_reachable vs C' fn' inst s
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >> suspend "callee"
QED

Resume raw_reachable_seal_eq_ind[entry]:
  rpt strip_tac >> drule_all ctx_seal_eq_lookup >> strip_tac >>
  drule fn_seal_eq_views >> strip_tac >>
  `C'.ctx_entry = C.ctx_entry` by fs[ctx_seal_eq_def] >>
  qexists_tac `f'` >> simp[] >>
  irule raw_reachable_entry >> simp[] >> metis_tac[]
QED

Resume raw_reachable_seal_eq_ind[next]:
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  drule fn_seal_eq_views >> strip_tac >>
  `step_inst fuel C' inst s = step_inst fuel C inst s`
    by metis_tac[run_defs_seal_eq] >>
  qexists_tac `fn'` >> simp[] >>
  irule raw_reachable_next >> simp[] >> metis_tac[]
QED

Resume raw_reachable_seal_eq_ind[block]:
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  drule fn_seal_eq_views >> strip_tac >>
  `step_inst fuel C' inst s = step_inst fuel C inst s`
    by metis_tac[run_defs_seal_eq] >>
  qexists_tac `fn'` >> simp[] >>
  irule raw_reachable_block >> simp[] >> metis_tac[]
QED

Resume raw_reachable_seal_eq_ind[callee]:
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  rename1 `fn_seal_eq caller caller'` >>
  drule fn_seal_eq_views >> strip_tac >>
  drule_all ctx_seal_eq_lookup >> strip_tac >>
  rename1 `fn_seal_eq callee callee'` >>
  qpat_assum `fn_seal_eq callee _` (strip_assume_tac o MATCH_MP fn_seal_eq_views) >>
  qexists_tac `callee'` >> simp[] >>
  irule raw_reachable_callee >> simp[] >> metis_tac[]
QED

Finalise raw_reachable_seal_eq_ind

Theorem raw_reachable_seal_eq:
  ctx_seal_eq C C' /\ raw_reachable vs C fn inst s ==>
  ?fn'. fn_seal_eq fn fn' /\ raw_reachable vs C' fn' inst s
Proof
  metis_tac[raw_reachable_seal_eq_ind]
QED

Theorem mem_inv_seal_eq:
  ctx_seal_eq C C' /\
  (!fn fn' inst s. fn_seal_eq fn fn' /\ M C fn inst s ==>
                   M' C' fn' inst s) /\
  mem_inv M C vs ==>
  mem_inv M' C' vs
Proof
  rw[mem_inv_raw_reachable]
  >- (drule_all ctx_seal_eq_lookup >> strip_tac >>
      drule fn_seal_eq_views >> strip_tac >>
      fs[ctx_seal_eq_def] >> metis_tac[])
  >> drule ctx_seal_eq_sym >> strip_tac >>
  drule_all raw_reachable_seal_eq >> strip_tac >>
  metis_tac[fn_seal_eq_sym]
QED
