(* Installed array selection: the length loader, check and address code. *)
Theory entryCreateSubscriptArrayRun
Ancestors
  entryCreateAdminSequence entryCreateFocusSpec entryCreatePathScope
  entryCreateCompletedCut createSizePrefixReplay createMarkedPath
  exprSimArrayIndex exprLoweringProps emitHelperProps abiEncoderProps
  compileEnv context fragExec fragGasOrigin frameGasEvents instIdxIndep
  bodyFullSubscriptArrayCodeBounds fragGasOriginPtr
  venomExecSemantics venomInstProps venomInst venomState
  list arithmetic pair relation

Definition array_selector_code_def:
  array_selector_code a b <=>
    b.cs_current_bb = a.cs_current_bb /\
    b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
    a.cs_next_id <= b.cs_next_id /\
    EVERY (\i. i.inst_id IN frag_ids a b /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
          (emitted_insts a b)
End

Theorem array_selector_code_refl[simp]:
  array_selector_code a a
Proof
  simp[array_selector_code_def, emitted_insts_def]
QED

Theorem array_selector_code_join:
  array_selector_code a b /\ array_selector_code b c ==> array_selector_code a c
Proof
  simp[array_selector_code_def] >> strip_tac >>
  drule_all emitted_insts_append >> strip_tac >>
  simp[EVERY_APPEND, EVERY_MEM, frag_ids_def] >>
  fs[EVERY_MEM,frag_ids_def] >> metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Theorem array_selector_code_emit_op[local]:
  ~is_terminator opc /\ opc <> GAS /\ opc <> INVOKE /\
  opc <> CREATE /\ opc <> CREATE2 ==>
  array_selector_code a (SND (emit_op opc args a))
Proof
  Cases_on `emit_op opc args a` >> simp[] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> simp[same_blocks_def, array_selector_code_def,
                                mk_inst_def, frag_ids_def]
QED

Theorem array_selector_code_emit_void[local]:
  ~is_terminator opc /\ opc <> GAS /\ opc <> INVOKE /\
  opc <> CREATE /\ opc <> CREATE2 ==>
  array_selector_code a (SND (emit_void opc args a))
Proof
  Cases_on `emit_void opc args a` >> Cases_on `q` >> simp[] >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_extends >> simp[same_blocks_def, array_selector_code_def,
                                  mk_inst_def, frag_ids_def]
QED

Theorem array_selector_code_bind[local]:
  array_selector_code a (SND (m a)) /\
  array_selector_code (SND (m a)) (SND (k (FST (m a)) (SND (m a)))) ==>
  array_selector_code a (SND (comp_bind m k a))
Proof
  Cases_on `m a` >> simp[comp_bind_def] >> metis_tac[array_selector_code_join]
QED

Theorem array_bounds_selector_code:
  array_bounds_check idx len signed a = ((),b) ==> array_selector_code a b
Proof
  `array_selector_code a (SND (array_bounds_check idx len signed a))` suffices_by
    (strip_tac >> disch_then (fn th => fs[th])) >>
  Cases_on `signed` >>
  simp[array_bounds_check_def, array_bounds_valid_def] >>
  rpt (irule array_selector_code_bind >> conj_tac >> BETA_TAC) >>
  simp[array_selector_code_emit_op, array_selector_code_emit_void,
       is_terminator_def, comp_return_def]
QED

Theorem array_elem_selector_code:
  array_elem_ptr bop idx dyn ws elem a = (selop,b) ==> array_selector_code a b
Proof
  `array_selector_code a (SND (array_elem_ptr bop idx dyn ws elem a))` suffices_by
    (strip_tac >> disch_then (fn th => fs[th])) >>
  Cases_on `dyn` >> simp[array_elem_ptr_def] >>
  rpt (irule array_selector_code_bind >> conj_tac >> BETA_TAC) >>
  simp[array_selector_code_emit_op, is_terminator_def, comp_return_def]
QED

Theorem array_length_selector_code:
  compile_ptr_load ctor imm loc selop a = (v,b) ==> array_selector_code a b
Proof
  `array_selector_code a (SND (compile_ptr_load ctor imm loc selop a))` suffices_by
    (strip_tac >> disch_then (fn th => fs[th])) >>
  Cases_on `loc` >> simp[compile_ptr_load_def, array_selector_code_emit_op,
                         is_terminator_def] >>
  Cases_on `ctor` >> Cases_on `imm` >> simp[compile_imm_load_word_def,
       array_selector_code_emit_op, is_terminator_def] >>
  irule array_selector_code_bind >> simp[array_selector_code_emit_op,
                                         is_terminator_def]
QED

Theorem compile_array_selector_code:
  compile_array_subscript bop idx dyn cnt ws elem signed loader a = (selop,b) /\
  (!len c. loader bop a = (len,c) ==> array_selector_code a c) ==>
  array_selector_code a b
Proof
  simp[compile_array_subscript_split, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> fs[oneTheory.one] >>
  Cases_on `dyn` >> gvs[comp_return_def] >>
  metis_tac[array_selector_code_join,array_bounds_selector_code,
            array_elem_selector_code]
QED

Theorem array_selector_ok_scope:
  array_selector_code a b /\ fn_has_code a b f /\ create_operand_at a s /\
  ~s.vs_halted /\ run_inst_seq (emitted_insts a b) s = OK u ==>
  create_operand_full_scope a b E C f s []
    (OK (u with vs_inst_idx := LENGTH b.cs_current_insts))
Proof
  strip_tac >> irule create_admin_sequence_scope >>
  fs[array_selector_code_def, EVERY_MEM]
QED

Theorem array_selector_visit_inventory:
  array_selector_code a b /\ fn_has_code a b f /\ create_operand_at a s ==>
  create_operand_cut a b E C f tops cx st0 source (es,s)
Proof
  strip_tac >> irule create_admin_sequence_cut >>
  fs[array_selector_code_def, EVERY_MEM]
QED

(* For a non-branching fetch, every physical edge has exactly the result
   of the base step, except that a successful edge advances the cursor. *)
Theorem selector_edge_result[local]:
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\ ~is_terminator i.inst_opcode /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  gas_origin_edge m E C f s marks r ==>
  marks = [] /\
  r = (case step_inst_base i s of
         OK v => OK (v with vs_inst_idx := SUC s.vs_inst_idx)
       | other => other)
Proof
  simp[gas_origin_edge_def, step_inst_non_invoke, gas_events_step_plain] >>
  rpt strip_tac >> gvs[exit_result_def, step_inst_non_invoke, gas_events_step_plain] >>
  Cases_on `step_inst_base i s` >> gvs[exit_result_def]
QED

Theorem selector_edge_forget_memory[local]:
  gas_origin_edge T E C f s marks r ==> gas_origin_edge F E C f s marks r
Proof
  simp[gas_origin_edge_def] >> metis_tac[]
QED

(* Consume the supplied origin path, not a second run to an arbitrary
   abort endpoint. The base run tells us how much installed code remains. *)
Theorem selector_abort_prefix[local]:
  !code s u t bb.
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    LENGTH b.cs_current_insts = s.vs_inst_idx + LENGTH code /\
    (!j. j < LENGTH code ==>
       get_instruction bb (s.vs_inst_idx + j) = SOME (EL j code)) /\
    EVERY (\i. i.inst_id IN frag_ids a b /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS) code /\
    run_inst_seq code s = Abort err u /\
    gas_origin_path T E C f s [] (Abort err t) ==>
    create_operand_full_scope a b E C f s [] (Abort err t)
Proof
  Induct_on `code` >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >> fs[Once EVERY_DEF] >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    (qpat_assum `!j. _ ==> get_instruction bb _ = SOME (EL j (h::code))`
       (qspec_then `0` (mp_tac o SIMP_RULE (srw_ss()) [])) >> simp[]) >>
  `s.vs_inst_idx <> LENGTH b.cs_current_insts` by simp[] >>
  qpat_x_assum `gas_origin_path T _ _ _ _ [] _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [Once gas_origin_path_cases])
  >- (drule_all selector_edge_result >> simp[] >> strip_tac >>
      rename1 `gas_origin_edge T E C f s [] (OK mid)` >>
      Cases_on `step_inst_base h s` >> gvs[run_inst_seq_def, exit_result_def] >>
      rename1 `step_inst_base h s = OK v` >>
      `v.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
      qabbrev_tac `mid = v with vs_inst_idx := SUC s.vs_inst_idx` >>
      `run_inst_seq code mid = Abort err (u with vs_inst_idx := SUC s.vs_inst_idx)` by
        simp[Abbr `mid`, run_inst_seq_inst_idx, exec_result_map_def] >>
      `create_operand_full_scope a b E C f mid [] (Abort err t)` by
        (first_x_assum irule >> first_assum (irule_at Any) >>
         qexists_tac `bb` >> simp[Abbr `mid`, ADD_CLAUSES] >> rpt strip_tac >>
         qpat_assum `!j. _ ==> get_instruction bb _ = SOME (EL j (h::code))`
           (qspec_then `SUC j` (mp_tac o SIMP_RULE (srw_ss()) [ADD_CLAUSES])) >>
         simp[ADD_CLAUSES]) >>
      `create_expr_prefix a b E C f s [] mid` by
        (simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
         simp[create_marked_edge_def, create_prefix_step_def] >>
         irule selector_edge_forget_memory >> first_assum ACCEPT_TAC) >>
      fs[create_operand_full_scope_def] >>
      metis_tac[create_expr_prefix_append, APPEND_NIL]) >>
  simp[create_operand_full_scope_def] >> metis_tac[create_expr_prefix_nil]
QED

Theorem array_selector_oob_scope:
  array_selector_code a b /\ fn_has_code a b f /\ create_operand_at a s /\
  run_inst_seq (emitted_insts a b) s = Abort Revert_abort u /\
  gas_origin_path T E C f s [] (Abort Revert_abort t) ==>
  create_operand_full_scope a b E C f s [] (Abort Revert_abort t)
Proof
  strip_tac >> fs[array_selector_code_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  irule selector_abort_prefix >>
  first_assum (irule_at Any) >>
  qpat_assum `run_inst_seq _ _ = Abort _ _` (irule_at Any) >>
  qexists_tac `bb` >> fs[create_operand_at_def, EVERY_MEM]
QED

Theorem array_bounds_ok_scope:
  array_bounds_check idx len signed a = ((),b) /\
  fn_has_code a b f /\ create_operand_at a s /\ ~s.vs_halted /\
  array_bounds_native_run a b s T t ==>
  create_operand_full_scope a b E C f s [] (OK t)
Proof
  simp[array_bounds_native_run_def] >> strip_tac >> gvs[] >>
  irule array_selector_ok_scope >> metis_tac[array_bounds_selector_code]
QED

(* The failing check need not have executed any of the installed address
   code. Extend the absorbing raw abort to the enclosing selector, then
   consume the same origin path supplied by the bounds producer. *)
Theorem array_bounds_oob_scope:
  array_bounds_check idx len signed a = ((),m) /\ array_selector_code m b /\
  fn_has_code a b f /\ create_operand_at a s /\
  array_bounds_native_run a m s F t /\
  gas_origin_ptr_path (D,lo,E,C,f,PG) (s,G,tn) [] (Abort Revert_abort t,G',tn') ==>
  create_operand_full_scope a b E C f s [] (Abort Revert_abort t)
Proof
  strip_tac >> drule array_bounds_selector_code >> strip_tac >>
  `array_selector_code a b` by metis_tac[array_selector_code_join] >>
  drule gas_origin_ptr_path_projections >> strip_tac >>
  fs[array_bounds_native_run_def] >>
  `inst_extends a m /\ inst_extends m b` by fs[array_selector_code_def, inst_extends_def] >>
  drule_all run_inst_seq_abort_extends >> strip_tac >>
  irule array_selector_oob_scope >> metis_tac[]
QED
