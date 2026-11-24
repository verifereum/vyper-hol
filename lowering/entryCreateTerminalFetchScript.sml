(* The joint suffix path terminates before the compiled interval's exit.
   Empty GAS marks do not imply an empty sequence of instructions. *)
Theory entryCreateTerminalFetch
Ancestors
  entryCreateFocusSpec entryCreatePathScope entryCreateEffectFocus
  entryCreateCompletedCut createSizeCutCode createSizePrefixReplay createMarkedPath
  fragGasOriginPtr fragGasOrigin fragExec builtinSystem emitHelper
  exprSimAbiGasBridge exprLoweringProps compileEnv
  venomExecSemantics venomInst venomInstProps venomState list rich_list relation arithmetic

Theorem terminal_scope_edge[local]:
  exit_result r /\ s.vs_inst_idx < LENGTH b.cs_current_insts /\
  gas_origin_edge T E C f s marks r ==>
  create_operand_full_scope a b E C f s marks r
Proof
  strip_tac >> irule (SIMP_RULE (srw_ss()) []
    (Q.INST [`left` |-> `[]`] create_operand_full_scope_terminal)) >>
  simp[] >> qexists_tac `s` >> simp[] >> decide_tac
QED

Theorem terminal_scope_prepend[local]:
  exit_result r /\ create_prefix_step a b E C f s left u /\
  create_operand_full_scope a b E C f u right r ==>
  create_operand_full_scope a b E C f s (left ++ right) r
Proof
  strip_tac >>
  `create_expr_prefix a b E C f s left u` by
    (simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
     simp[create_marked_edge_def]) >>
  Cases_on `r` >> gvs[exit_result_def,create_operand_full_scope_def] >>
  metis_tac[create_expr_prefix_append,APPEND_ASSOC]
QED

Theorem terminal_fetch_head[local]:
  (!j. j < LENGTH (h::xs) ==> get_instruction bb (n + j) = SOME (EL j (h::xs))) ==>
  get_instruction bb n = SOME h
Proof
  disch_then (qspec_then `0:num` mp_tac) >> simp[EL]
QED

Theorem terminal_fetch_tail[local]:
  (!j. j < SUC (LENGTH xs) ==> get_instruction bb (j + n) = SOME (EL j (h::xs))) ==>
  !j. j < LENGTH xs ==> get_instruction bb (j + SUC n) = SOME (EL j xs)
Proof
  strip_tac >> rpt strip_tac >> first_x_assum (qspec_then `SUC j` mp_tac) >>
  simp[EL,ADD_CLAUSES]
QED

Theorem terminal_path_in_slice[local]:
  !is s bb marks r.
    exit_result r /\ gas_origin_path T E C f s marks r /\
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    LENGTH b.cs_current_insts = s.vs_inst_idx + LENGTH (is ++ [last]) /\
    (!j. j < LENGTH (is ++ [last]) ==>
      get_instruction bb (s.vs_inst_idx + j) = SOME (EL j (is ++ [last]))) /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_id IN frag_ids a b) is /\
    (!fuel u v. step_inst fuel C last u <> OK v) ==>
    create_operand_full_scope a b E C f s marks r
Proof
  Induct_on `is`
  >- (simp[] >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `gas_origin_path _ _ _ _ _ _ _`
        (strip_assume_tac o ONCE_REWRITE_RULE [gas_origin_path_cases]) >>
      gvs[exit_result_def]
      >- (qpat_x_assum `gas_origin_edge _ _ _ _ _ _ (OK _)`
            (strip_assume_tac o REWRITE_RULE [gas_origin_edge_def]) >>
          gvs[exit_result_def] >> metis_tac[]) >>
      irule terminal_scope_edge >> simp[] >> decide_tac) >>
  rpt gen_tac >> pure_rewrite_tac [APPEND, EVERY_DEF] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    (irule terminal_fetch_head >> metis_tac[]) >>
  `s.vs_inst_idx < LENGTH b.cs_current_insts` by
    (qpat_assum `LENGTH b.cs_current_insts = _` SUBST1_TAC >> simp[LENGTH]) >>
  qpat_x_assum `gas_origin_path _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_origin_path_cases]) >>
  gvs[exit_result_def]
  >- (rename1 `gas_origin_edge T E C f s left (OK u)` >>
      rename1 `gas_origin_path T E C f u right r` >>
      `u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = SUC s.vs_inst_idx` by
        (qpat_assum `gas_origin_edge T E C f s left (OK u)`
           (strip_assume_tac o REWRITE_RULE [gas_origin_edge_def]) >>
         gvs[exit_result_def] >>
         FIRST [drule_all step_preserves_control_flow >> simp[],
           qpat_x_assum `OK _ = step_inst _ _ _ _` (assume_tac o SYM) >>
           gvs[exit_result_def]]) >>
      `create_prefix_step a b E C f s left u` by
        (simp[create_prefix_step_def] >>
         `s.vs_inst_idx <> LENGTH b.cs_current_insts` by decide_tac >>
         fs[gas_origin_edge_def] >> metis_tac[]) >>
      irule terminal_scope_prepend >> simp[] >> qexists_tac `u` >> simp[] >>
      first_x_assum irule >> simp[] >>
      `!j. j < SUC (LENGTH (is ++ [last])) ==>
        get_instruction bb (j + s.vs_inst_idx) = SOME (EL j (h::(is ++ [last])))` by
        simp[] >>
      drule terminal_fetch_tail >> simp[]) >>
  irule terminal_scope_edge >> simp[]
QED

Theorem terminal_appended_scope[local]:
  exit_result r /\ gas_origin_path T E C f s marks r /\
  create_cut_code {} a b /\ fn_has_code a b f /\ create_operand_at a s /\
  b.cs_blocks = a.cs_blocks /\ b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ (is ++ [last]) /\
  EVERY (\i. ~is_terminator i.inst_opcode) is /\
  (!fuel u v. step_inst fuel C last u <> OK v) ==>
  create_operand_full_scope a b E C f s marks r
Proof
  strip_tac >>
  `frag_code a b = is ++ [last]` by
    (asm_simp_tac bool_ss [frag_code_def, LET_THM, emitted_blocks_def,
       emitted_insts_def, DROP_LENGTH_APPEND] >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_id IN frag_ids a b) is` by
    fs[create_cut_code_def, EVERY_MEM, MEM_APPEND] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  irule terminal_path_in_slice >> simp[] >>
  qexistsl_tac [`bb`,`is`,`last`] >> fs[create_operand_at_def]
QED

Theorem raw_revert_joint_scope:
  compile_raw_revert op a = ((),b) /\ fn_has_code a b f /\ create_operand_at a s /\
  gas_origin_ptr_path (D,lo,E,C,f,PG) (s,G,tn) [] (Abort Revert_abort w,G',tn') ==>
  create_operand_full_scope a b E C f s [] (Abort Revert_abort w)
Proof
  strip_tac >> drule raw_revert_effect_code >> strip_tac >>
  drule gas_origin_ptr_path_projections >> strip_tac >>
  qpat_x_assum `compile_raw_revert _ _ = _` mp_tac >>
  simp[compile_raw_revert_def, emit_op_def, emit_inst_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  disch_then (assume_tac o SYM) >> irule terminal_appended_scope >>
  simp[exit_result_def, mk_inst_def, is_terminator_def] >>
  rpt gen_tac >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  rpt (CASE_TAC >> simp[])
QED

Theorem selfdestruct_joint_scope:
  compile_selfdestruct op a = ((),b) /\ fn_has_code a b f /\ create_operand_at a s /\
  exit_result r /\ gas_origin_ptr_path (D,lo,E,C,f,PG) (s,G,tn) [] (r,G',tn') ==>
  create_operand_full_scope a b E C f s [] r
Proof
  strip_tac >> drule selfdestruct_effect_code >> strip_tac >>
  drule gas_origin_ptr_path_projections >> strip_tac >>
  qpat_x_assum `compile_selfdestruct _ _ = _` mp_tac >>
  simp[compile_selfdestruct_def, emit_void_def, comp_bind_def, fresh_id_def, emit_def] >>
  disch_then (assume_tac o SYM) >> irule terminal_appended_scope >> simp[] >>
  simp[mk_inst_def] >> rpt gen_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >> rpt (CASE_TAC >> simp[])
QED
