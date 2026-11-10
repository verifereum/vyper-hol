(* Symbolic emitted-opcode boundaries. *)
Theory symEmitSim
Ancestors
  symInstKinds symPostfixSim codegenSymRel asmSymSem asmSem
  strongPrefixSim asmSplice contextCodegenRel codegenRel finite_map list
  fnBlockBodyHelpers

Theorem sval_val_map:
  !ws. OPT_MMAP sval_val (MAP Val ws) = SOME ws
Proof
  Induct >> simp[sval_val_def]
QED

Theorem mem_labels_clear_disjoint:
  (!b. b IN FDOM labs ==> ~P b) ==>
  mem_labels_clear labs P = labs
Proof
  simp[mem_labels_clear_def, fmap_eq_flookup, FLOOKUP_DRESTRICT] >>
  metis_tac[FLOOKUP_DEF]
QED

Theorem sym_step_concrete_words:
  ss.sym_stack = MAP Val args ++ tail /\
  LENGTH args = asm_op_arity name /\
  (!b. b IN FDOM ss.sym_mem_labels ==>
       ~asm_op_mem_reads name args b /\ ~asm_op_mem_writes name args b) /\
  asm_step_op FEMPTY name (ss.sym_base with as_stack := args) = AsmOK cs ==>
  sym_step_concrete name ss = SymOK
    (ss with <| sym_base := cs with as_stack := [];
                sym_stack := MAP Val cs.as_stack ++ tail |>)
Proof
  strip_tac >>
  `mem_labels_clear ss.sym_mem_labels (asm_op_mem_writes name args) =
   ss.sym_mem_labels` by
    (irule mem_labels_clear_disjoint >> simp[]) >>
  `~mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name args)` by
    (simp[mem_labels_hit_def] >> metis_tac[]) >>
  qpat_x_assum `LENGTH args = _` (assume_tac o SYM) >>
  simp[sym_step_concrete_def, TAKE_APPEND1, DROP_APPEND,
       TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG,
       sval_val_map, sym_lift_def, sym_state_component_equality]
QED

Theorem sym_step_op_plain:
  ~MEM name ["POP"; "JUMP"; "JUMPI"; "ADD"; "MSTORE";
             "MLOAD"; "CODECOPY"; "CODESIZE"] /\
  ALOOKUP dup_table name = NONE /\ ALOOKUP swap_table name = NONE ==>
  sym_step_op p env name ss = sym_step_concrete name ss
Proof
  simp[sym_step_op_def]
QED

Theorem sym_step_add_data_left:
  ss.sym_stack = Lab l d :: Val w :: tail /\
  sym_data_label p env l /\ sym_delta_ok (d + w2n w) ==>
  sym_step p env (AsmOp "ADD") ss = SymOK
    (ss with <| sym_base := asm_next ss.sym_base;
                sym_stack := Lab l (d + w2n w) :: tail |>)
Proof
  simp[sym_step_def, sym_step_op_def, sym_add_def,
       sym_push_lab_def, sym_set_stack_def]
QED

Theorem sym_step_add_data_right:
  ss.sym_stack = Val w :: Lab l d :: tail /\
  sym_data_label p env l /\ sym_delta_ok (d + w2n w) ==>
  sym_step p env (AsmOp "ADD") ss = SymOK
    (ss with <| sym_base := asm_next ss.sym_base;
                sym_stack := Lab l (d + w2n w) :: tail |>)
Proof
  simp[sym_step_def, sym_step_op_def, sym_add_def,
       sym_push_lab_def, sym_set_stack_def]
QED

Theorem sym_step_add_words:
  ss.sym_stack = Val a :: Val b :: tail ==>
  sym_step_op p env "ADD" ss = sym_step_concrete "ADD" ss
Proof
  simp[sym_step_op_def, sym_add_def]
QED

Theorem sym_step_mstore_words:
  ss.sym_stack = Val a :: Val b :: tail ==>
  sym_step_op p env "MSTORE" ss = sym_step_concrete "MSTORE" ss
Proof
  simp[sym_step_op_def, sym_mstore_def]
QED

Theorem sym_step_mload_word:
  ss.sym_stack = Val off :: tail /\
  w2n off NOTIN FDOM ss.sym_mem_labels ==>
  sym_step_op p env "MLOAD" ss = sym_step_concrete "MLOAD" ss
Proof
  simp[sym_step_op_def, sym_mload_def, mem_label_at_def, FLOOKUP_DEF]
QED

Theorem sym_step_codecopy_data:
  ss.sym_stack = Val dst :: Lab l d :: Val sz :: tail /\
  sym_data_label p env l /\
  (!b. b IN FDOM ss.sym_mem_labels ==>
       ~in_mem_range (w2n dst) (w2n sz) b) /\
  asm_copy_to_mem (DROP d (env ' l))
    (ss.sym_base with as_stack := [dst; 0w; sz]) = AsmOK cs ==>
  sym_step p env (AsmOp "CODECOPY") ss = SymOK
    (ss with <| sym_base := cs with as_stack := [];
                sym_stack := MAP Val cs.as_stack ++ tail |>)
Proof
  strip_tac >>
  `mem_labels_clear ss.sym_mem_labels (in_mem_range (w2n dst) (w2n sz)) =
   ss.sym_mem_labels` by (irule mem_labels_clear_disjoint >> simp[]) >>
  simp[sym_step_def, sym_step_op_def, sym_codecopy_def, sym_lift_def,
       sym_state_component_equality]
QED

Theorem sym_steps_single_emit:
  asm_block_at p ss.sym_base.as_pc [inst] /\
  sym_step p env inst ss = SymOK ss' ==>
  sym_steps p env 1 ss = SymOK ss'
Proof
  simp[asm_block_at_def, sym_steps_def] >> rpt strip_tac >>
  simp[codegenSymRelTheory.sym_steps_compute]
QED

Theorem sym_assert_success_run:
  ss.sym_stack = Val w :: tail /\ w <> 0w /\
  asm_block_at p ss.sym_base.as_pc
    [AsmOp "ISZERO"; AsmPushLabel "revert"; AsmOp "JUMPI"] ==>
  codegenSymRel$sym_steps p env 3 ss = SymOK
    (ss with <| sym_base := (ss.sym_base with <| as_stack := [];
                              as_pc := ss.sym_base.as_pc + 3 |>);
                sym_stack := tail |>)
Proof
  simp[asm_block_at_def] >> strip_tac >>
  qpat_x_assum `!j. _` (fn th =>
    map_every (fn n => qspec_then n mp_tac th) [`0`, `1`, `2`]) >>
  simp[] >> rpt strip_tac >>
  drule asmSpliceTheory.sym_step_iszero_val >> strip_tac >>
  simp[codegenSymRelTheory.sym_steps_compute,
       asmSpliceTheory.sym_step_iszero_val,
       asmSpliceTheory.sym_step_push_label,
       asm_next_def] >>
  simp[sym_step_def, sym_step_op_def, sym_jumpi_def, sym_set_stack_def,
       asm_next_def, sym_state_component_equality, asm_state_component_equality]
QED

Theorem sym_assert_unreachable_success_run:
  ss.sym_stack = Val w :: tail /\ w <> 0w /\
  asm_block_at p ss.sym_base.as_pc
    [AsmPushLabel lbl; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel lbl] /\
  INDEX_OF (AsmLabel lbl) p = SOME (ss.sym_base.as_pc + 3) ==>
  codegenSymRel$sym_steps p env 3 ss = SymOK
    (ss with <| sym_base := (ss.sym_base with <| as_stack := [];
                              as_pc := ss.sym_base.as_pc + 4 |>);
                sym_stack := tail |>)
Proof
  simp[asm_block_at_def] >> strip_tac >>
  qpat_x_assum `!j. _` (fn th =>
    map_every (fn n => qspec_then n mp_tac th) [`0`, `1`, `3`]) >>
  simp[] >> rpt strip_tac >>
  simp[codegenSymRelTheory.sym_steps_compute,
       asmSpliceTheory.sym_step_push_label, asm_next_def] >>
  simp[sym_step_def, sym_step_op_def, sym_jumpi_def, sym_jump_dest_def,
       sym_set_stack_def, sym_lift_def, asm_step_def, asm_next_def,
       sym_state_component_equality, asm_state_component_equality]
QED

Theorem sym_emit_kinds_replace:
  sym_kinds_ok cplan fn ret srest ps ss /\
  ss'.sym_mem_labels = ss.sym_mem_labels /\
  qs.ps_spilled = ps.ps_spilled /\
  ss'.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE qs.ps_stack) top ==>
  sym_kinds_ok cplan fn ret srest qs ss'
Proof
  simp[sym_kinds_ok_def] >> metis_tac[]
QED

Theorem sym_initial_fmp_run:
  asm_block_at p ss.sym_base.as_pc [AsmPush (encode_num_bytes initial_fmp)] ==>
  codegenSymRel$sym_steps p env 1 ss = SymOK
    (ss with <| sym_base := asm_next (ss.sym_base with as_stack := []);
                sym_stack := Val (n2w initial_fmp) :: ss.sym_stack |>)
Proof
  strip_tac >> irule sym_steps_single_emit >>
  qexists `AsmPush (encode_num_bytes initial_fmp)` >>
  simp[sym_step_push_word, push_encode_num_roundtrip]
QED

Theorem sym_add_word_step:
  ss.sym_stack = Val a :: Val b :: tail ==>
  sym_step p env (AsmOp "ADD") ss = SymOK
    (ss with <| sym_base := asm_next (ss.sym_base with as_stack := []);
                sym_stack := Val (a + b) :: tail |>)
Proof
  simp[sym_step_def, sym_step_op_def, sym_add_def,
       sym_step_concrete_def, sym_lift_def, sval_val_def,
       asm_op_arity_def, asm_op_arity_table_def,
       asm_op_mem_reads_def, asm_op_mem_writes_def, log_table_def,
       mem_labels_hit_def, mem_labels_clear_def,
       asm_step_op_def, asm_step_arith_def, asm_binop_def, asm_next_def,
       sym_state_component_equality, asm_state_component_equality,
       GSYM pred_setTheory.UNIV_DEF, finite_mapTheory.DRESTRICT_UNIV]
QED

Theorem sym_bump_success_run:
  ss.sym_stack = Val delta :: Val fmp :: tail /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "DUP2"; AsmOp "ADD"] ==>
  codegenSymRel$sym_steps p env 2 ss = SymOK
    (ss with <| sym_base := ss.sym_base with <| as_stack := [];
                              as_pc := ss.sym_base.as_pc + 2 |>;
                sym_stack := Val (fmp + delta) :: Val fmp :: tail |>)
Proof
  simp[asm_block_at_def] >> strip_tac >>
  qpat_x_assum `!j. _` (fn th =>
    map_every (fn n => qspec_then n mp_tac th) [`0`, `1`]) >>
  simp[] >> rpt strip_tac >>
  simp[codegenSymRelTheory.sym_steps_compute, Once sym_step_def,
       Once sym_step_op_def, dup_table_def, sym_dup_def, sym_set_stack_def,
       asm_next_def] >>
  qmatch_goalsub_abbrev_tac `sym_step p env (AsmOp "ADD") mid` >>
  `mid.sym_stack = Val fmp :: Val delta :: Val fmp :: tail`
    by simp[Abbr `mid`] >>
  drule sym_add_word_step >>
  simp[Abbr `mid`, asm_next_def,
       sym_state_component_equality, asm_state_component_equality]
QED

Theorem sym_mstore_word_step:
  ss.sym_stack = Val off :: Val value :: tail /\
  (!b. b IN FDOM ss.sym_mem_labels ==>
       ~in_mem_range (w2n off) 32 b) ==>
  sym_step p env (AsmOp "MSTORE") ss = SymOK
    (ss with <| sym_base := ss.sym_base with <| as_stack := [];
                  as_memory := mem_write32 (w2n off) value ss.sym_base.as_memory;
                  as_pc := ss.sym_base.as_pc + 1 |>;
                sym_stack := tail |> )
Proof
  strip_tac >>
  `mem_labels_clear ss.sym_mem_labels (in_mem_range (w2n off) 32) =
   ss.sym_mem_labels` by (irule mem_labels_clear_disjoint >> simp[]) >>
  simp[sym_step_def, sym_step_op_def, sym_mstore_def,
       sym_step_concrete_def, sym_lift_def, sval_val_def,
       asm_op_arity_def, asm_op_arity_table_def,
       asm_op_mem_reads_def, asm_op_mem_writes_def, log_table_def,
       mem_labels_hit_def, asm_step_op_def, asm_step_arith_def,
       asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
       asm_mstore_def, spillSimTheory.mem_write32_def, asm_next_def, sym_state_component_equality,
       asm_state_component_equality]
QED

Theorem sym_istore_success_run:
  ss.sym_stack = Val value :: Val off :: tail /\
  (!b. b IN FDOM ss.sym_mem_labels ==>
       ~in_mem_range (w2n off) 32 b) /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "SWAP1"; AsmOp "MSTORE"] ==>
  codegenSymRel$sym_steps p env 2 ss = SymOK
    (ss with <| sym_base := ss.sym_base with <| as_stack := [];
                  as_memory := mem_write32 (w2n off) value ss.sym_base.as_memory;
                  as_pc := ss.sym_base.as_pc + 2 |>;
                sym_stack := tail |> )
Proof
  simp[asm_block_at_def] >> strip_tac >>
  qpat_x_assum `!j. _` (fn th =>
    map_every (fn n => qspec_then n mp_tac th) [`0`, `1`]) >>
  simp[] >> rpt strip_tac >>
  simp[codegenSymRelTheory.sym_steps_compute, Once sym_step_def,
       Once sym_step_op_def, dup_table_def, swap_table_def, sym_swap_def,
       sym_set_stack_def, asm_next_def, LUPDATE_compute] >>
  qmatch_goalsub_abbrev_tac `sym_step p env (AsmOp "MSTORE") mid` >>
  `mid.sym_stack = Val off :: Val value :: tail` by simp[Abbr `mid`] >>
  drule sym_mstore_word_step >>
  simp[Abbr `mid`, asm_next_def,
       sym_state_component_equality, asm_state_component_equality]
QED

(* CODESIZE is deliberately rejected by the symbolic semantics.
   label_flow_ok excludes it at every instruction in the context. *)
Theorem sym_codesize_contract_diagnostic:
  ~is_pre_codegen_opcode CODESIZE /\
  venom_to_evm_name CODESIZE = SOME "CODESIZE" /\
  sym_step p env (AsmOp "CODESIZE") ss = SymBad "CODESIZE"
Proof
  EVAL_TAC
QED

Theorem label_flow_inst_not_codesize:
  label_flow_ok ctx /\ MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) ==>
  inst.inst_opcode <> CODESIZE
Proof
  metis_tac[label_flow_ok_def]
QED

Theorem ordinary_source_input_numeric_kind:
  opaque_use_ok fn /\ label_flow_ok ctx /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  MEM op inst.inst_operands /\ ~is_label_operand op /\
  ~MEM inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET; CODECOPY] ==>
  (op_kind_ok fn ret op sv <=> ?w. sv = Val w)
Proof
  simp[MEM] >> strip_tac >> irule op_kind_ok_numeric >> simp[] >>
  metis_tac[frameViewFactsTheory.ordinary_operand_not_retpc,
            ordinary_input_not_code_end]
QED

Theorem sval_conc_numeric_list:
  !svs ws. LIST_REL (\sv w. sval_conc lo sv = SOME w) svs ws /\
    EVERY (\sv. ?w. sv = Val w) svs ==> svs = MAP Val ws
Proof
  Induct >> Cases_on `ws` >> simp[] >>
  rpt strip_tac >> gvs[asmSymBridgeTheory.sval_conc_def]
QED

Theorem numeric_operand_kinds_list:
  !ops svs. LIST_REL (op_kind_ok fn ret) ops svs /\
    EVERY (\op. !sv. op_kind_ok fn ret op sv ==> ?w. sv = Val w) ops ==>
    EVERY (\sv. ?w. sv = Val w) svs
Proof
  Induct >> Cases_on `svs` >> simp[] >> metis_tac[]
QED

Theorem asm_sym_numeric_take:
  asm_sym_rel p env cs ss /\
  EVERY (\sv. ?w. sv = Val w) (TAKE k ss.sym_stack) ==>
  TAKE k ss.sym_stack = MAP Val (TAKE k cs.as_stack)
Proof
  strip_tac >> irule sval_conc_numeric_list >> simp[] >>
  qexists `SND (compute_label_offsets p)` >>
  gvs[asmSymBridgeTheory.asm_sym_rel_def] >>
  metis_tac[rich_listTheory.EVERY2_TAKE]
QED

Theorem asm_sym_step_success_from_safe:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\ cs.as_pc < LENGTH p /\
  asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
    (EL cs.as_pc p) cs = AsmOK cs' /\
  (!msg. sym_step p env (EL cs.as_pc p) ss <> SymBad msg) ==>
  ?ss'. sym_step p env (EL cs.as_pc p) ss = SymOK ss' /\
    asm_sym_rel p env cs' ss'
Proof
  strip_tac >> drule_all asmSymBridgeTheory.asm_sym_step >>
  Cases_on `sym_step p env (EL cs.as_pc p) ss` >>
  gvs[asmSymBridgeTheory.asm_sym_step_rel_def]
QED

Theorem sym_step_concrete_numeric_safe:
  asm_op_arity name <= LENGTH ss.sym_stack /\
  EVERY (\sv. ?w. sv = Val w) (TAKE (asm_op_arity name) ss.sym_stack) /\
  ~mem_labels_hit ss.sym_mem_labels
    (asm_op_mem_reads name (TAKE (asm_op_arity name) cs.as_stack)) /\
  asm_sym_rel p env cs ss ==>
  !msg. sym_step_concrete name ss <> SymBad msg
Proof
  strip_tac >> drule_all asm_sym_numeric_take >> strip_tac >>
  simp[sym_step_concrete_def, sval_val_map] >>
  Cases_on `asm_step_op FEMPTY name
    (ss.sym_base with as_stack := TAKE (asm_op_arity name) cs.as_stack)` >>
  simp[sym_lift_def]
QED

Theorem sym_step_concrete_numeric_shape:
  asm_op_arity name <= LENGTH ss.sym_stack /\
  EVERY (\sv. ?w. sv = Val w) (TAKE (asm_op_arity name) ss.sym_stack) /\
  (!b. b IN FDOM ss.sym_mem_labels ==>
    ~asm_op_mem_writes name (TAKE (asm_op_arity name) cs.as_stack) b) /\
  asm_sym_rel p env cs ss /\ sym_step_concrete name ss = SymOK ss' ==>
  ss'.sym_mem_labels = ss.sym_mem_labels /\
  ?ws. ss'.sym_stack = MAP Val ws ++ DROP (asm_op_arity name) ss.sym_stack
Proof
  strip_tac >> drule_all asm_sym_numeric_take >> strip_tac >>
  `mem_labels_clear ss.sym_mem_labels
      (asm_op_mem_writes name (TAKE (asm_op_arity name) cs.as_stack)) =
    ss.sym_mem_labels` by (irule mem_labels_clear_disjoint >> simp[]) >>
  qpat_x_assum `sym_step_concrete _ _ = _` mp_tac >>
  simp[sym_step_concrete_def, sval_val_map] >>
  Cases_on `mem_labels_hit ss.sym_mem_labels
    (asm_op_mem_reads name (TAKE (asm_op_arity name) cs.as_stack))` >> simp[] >>
  Cases_on `asm_step_op FEMPTY name
    (ss.sym_base with as_stack := TAKE (asm_op_arity name) cs.as_stack)` >>
  simp[sym_lift_def] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem sym_single_step_replay_safe:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  asm_block_at p cs.as_pc [inst] /\
  asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p) inst cs = AsmOK cs' /\
  (!msg. sym_step p env inst ss <> SymBad msg) ==>
  ?ss'. sym_steps p env 1 ss = SymOK ss' /\ asm_sym_rel p env cs' ss'
Proof
  strip_tac >>
  `cs.as_pc < LENGTH p /\ EL cs.as_pc p = inst` by
    (fs[asm_block_at_def] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `ss.sym_base.as_pc = cs.as_pc` by
    fs[asmSymBridgeTheory.asm_sym_rel_def] >>
  `?ss'. sym_step p env inst ss = SymOK ss' /\ asm_sym_rel p env cs' ss'` by
    metis_tac[asm_sym_step_success_from_safe] >>
  qexists `ss'` >> simp[] >> irule sym_steps_single_emit >> metis_tac[]
QED

(* Ordinary operand lists may be evaluated in the source state even when
   preparation uses a frame view with compiler-owned memory. *)
Theorem ordinary_selected_operands_frame_view:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> PHI /\
  inst.inst_opcode <> RET /\ inst.inst_opcode <> RETFMP /\
  inst.inst_opcode <> DRET /\
  (!op. MEM op operands ==> MEM op inst.inst_operands) ==>
  eval_operands operands (frame_view fn ra vs with vs_memory := m) =
    eval_operands operands vs
Proof
  strip_tac >> irule frameViewFactsTheory.eval_operands_frame_view >>
  metis_tac[frameViewFactsTheory.ordinary_operand_not_retpc]
QED

Theorem prepared_selected_evaluation:
  plan_stack_rel lo vs (residual ++ selected) astk /\
  EVERY (\op. op <> dead_stack_marker) selected /\
  (!op. MEM op selected ==> eval_operand op vs = operand_val vs lo op) ==>
  eval_operands (REVERSE selected) vs =
    SOME (TAKE (LENGTH selected) astk)
Proof
  strip_tac >> irule venomStateTheory.log_operands_values >>
  gvs[plan_stack_rel_def, LIST_REL_EL_EQN, EVERY_MEM] >>
  rpt strip_tac >> simp[EL_TAKE] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  simp[REVERSE_APPEND, EL_APPEND_EQN] >>
  metis_tac[MEM_EL, MEM_REVERSE, LENGTH_REVERSE]
QED

Theorem ordinary_prepared_source_evaluation:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> PHI /\
  inst.inst_opcode <> RET /\ inst.inst_opcode <> RETFMP /\
  inst.inst_opcode <> DRET /\
  (!op. MEM op selected ==> MEM op inst.inst_operands) /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) st /\
  ps.ps_stack = residual ++ selected /\
  EVERY (\op. op <> dead_stack_marker) selected /\
  (!op. MEM op selected ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) ==>
  eval_operands (REVERSE selected) vs =
    SOME (TAKE (LENGTH selected) st.as_stack)
Proof
  strip_tac >>
  `eval_operands (REVERSE selected)
     (frame_view fn ra vs with vs_memory := m) =
     SOME (TAKE (LENGTH selected) st.as_stack)` by
    (irule prepared_selected_evaluation >> simp[] >>
     qexistsl [`lo`, `residual`] >> fs[venom_asm_rel_def]) >>
  `eval_operands (REVERSE selected)
     (frame_view fn ra vs with vs_memory := m) =
     eval_operands (REVERSE selected) vs` by
    (irule ordinary_selected_operands_frame_view >> simp[] >>
     qexists `inst` >> simp[]) >> gvs[]
QED

Theorem ordinary_prepared_source_arguments:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> PHI /\
  inst.inst_opcode <> RET /\ inst.inst_opcode <> RETFMP /\
  inst.inst_opcode <> DRET /\
  (!op. MEM op selected ==> MEM op inst.inst_operands) /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) st /\
  ps.ps_stack = residual ++ selected /\
  EVERY (\op. op <> dead_stack_marker) selected /\
  (!op. MEM op selected ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  eval_operands (REVERSE selected) vs = SOME args ==>
  st.as_stack = args ++ DROP (LENGTH selected) st.as_stack
Proof
  strip_tac >>
  `eval_operands (REVERSE selected)
     (frame_view fn ra vs with vs_memory := m) = SOME args` by
    (sg `eval_operands (REVERSE selected)
       (frame_view fn ra vs with vs_memory := m) =
       eval_operands (REVERSE selected) vs`
     >- (irule ordinary_selected_operands_frame_view >> simp[] >>
         qexists `inst` >> simp[]) >> simp[]) >>
  drule_at (Pat `eval_operands _ _ = SOME _`)
    emitSimTheory.arranged_eval_operands_stack >>
  simp[] >> disch_then irule >>
  qexistsl_tac [`lo`, `ps`, `residual`] >> simp[]
QED

Theorem commutative_emission_memory_empty:
  is_commutative opc /\ venom_to_evm_name opc = SOME name ==>
  ~asm_op_mem_reads name args b /\ ~asm_op_mem_writes name args b
Proof
  Cases_on `opc` >>
  simp[venomEffectsTheory.is_commutative_def, asmIRTheory.venom_to_evm_name_def,
       asm_op_mem_reads_def, asm_op_mem_writes_def, log_table_def]
QED

Theorem call_source_read_write_coverage:
  inst.inst_opcode = CALL /\
  inst.inst_operands = [gas; addr; value; off; len; ret_off; ret_len] /\
  eval_operands inst.inst_operands vs = SOME args /\
  asm_op_mem_reads "CALL" args b ==>
  source_memory_read_byte inst vs b \/
  (?range. MEM range (source_memory_write_ranges inst vs) /\
           byte_in_memory_range range b)
Proof
  rpt strip_tac >>
  gvs[venomStateTheory.eval_operands_def, AllCaseEqs()] >>
  gvs[asm_op_mem_reads_def, source_memory_read_byte_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def,
      memory_range_of_operands_def, byte_in_memory_range_def,
      in_mem_range_def, log_table_def]
QED

Theorem readonly_call_source_read_write_coverage:
  MEM inst.inst_opcode [STATICCALL; DELEGATECALL] /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  inst.inst_operands = [gas; addr; off; len; ret_off; ret_len] /\
  eval_operands inst.inst_operands vs = SOME args /\
  asm_op_mem_reads name args b ==>
  source_memory_read_byte inst vs b \/
  (?range. MEM range (source_memory_write_ranges inst vs) /\
           byte_in_memory_range range b)
Proof
  rpt strip_tac >>
  gvs[venomStateTheory.eval_operands_def, AllCaseEqs()] >>
  gvs[asmIRTheory.venom_to_evm_name_def, asm_op_mem_reads_def,
      source_memory_read_byte_def, source_memory_read_ranges_def,
      source_memory_write_ranges_def, memory_range_of_operands_def,
      byte_in_memory_range_def, in_mem_range_def, log_table_def]
QED

Theorem call_emission_memory_writes_empty:
  MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"] ==>
  ~asm_op_mem_writes name args b
Proof
  strip_tac >> gvs[asm_op_mem_writes_def]
QED

Theorem mload_source_read_coverage:
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [off] /\
  eval_operands inst.inst_operands vs = SOME args /\
  asm_op_mem_reads "MLOAD" args b ==>
  source_memory_read_byte inst vs b
Proof
  rpt strip_tac >>
  gvs[venomStateTheory.eval_operands_def, AllCaseEqs()] >>
  gvs[asm_op_mem_reads_def, source_memory_read_byte_def,
      source_memory_read_ranges_def, byte_in_memory_range_def, in_mem_range_def]
QED

Theorem sha3_source_read_coverage:
  inst.inst_opcode = SHA3 /\ inst.inst_operands = [off; len] /\
  eval_operands inst.inst_operands vs = SOME args /\
  asm_op_mem_reads "SHA3" args b ==>
  source_memory_read_byte inst vs b
Proof
  rpt strip_tac >>
  gvs[venomStateTheory.eval_operands_def, AllCaseEqs()] >>
  gvs[asm_op_mem_reads_def, source_memory_read_byte_def,
      source_memory_read_ranges_def, memory_range_of_operands_def,
      byte_in_memory_range_def, in_mem_range_def]
QED

Theorem copy_create_source_read_coverage:
  MEM inst.inst_opcode [MCOPY; CREATE] /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  inst.inst_operands = [x; off; len] /\
  eval_operands inst.inst_operands vs = SOME args /\
  asm_op_mem_reads name args b ==>
  source_memory_read_byte inst vs b
Proof
  rpt strip_tac >>
  gvs[venomStateTheory.eval_operands_def, AllCaseEqs()] >>
  gvs[asmIRTheory.venom_to_evm_name_def, asm_op_mem_reads_def,
      source_memory_read_byte_def, source_memory_read_ranges_def,
      memory_range_of_operands_def, byte_in_memory_range_def,
      in_mem_range_def, log_table_def]
QED

Theorem create2_source_read_coverage:
  inst.inst_opcode = CREATE2 /\
  inst.inst_operands = [value; off; len; salt] /\
  eval_operands inst.inst_operands vs = SOME args /\
  asm_op_mem_reads "CREATE2" args b ==>
  source_memory_read_byte inst vs b
Proof
  rpt strip_tac >>
  gvs[venomStateTheory.eval_operands_def, AllCaseEqs()] >>
  gvs[asm_op_mem_reads_def, source_memory_read_byte_def,
      source_memory_read_ranges_def, memory_range_of_operands_def,
      byte_in_memory_range_def, in_mem_range_def, log_table_def]
QED

Theorem copy_source_write_coverage:
  MEM inst.inst_opcode [MCOPY; CALLDATACOPY; RETURNDATACOPY; CODECOPY] /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  inst.inst_operands = [dst; src; len] /\
  eval_operands inst.inst_operands vs = SOME args /\
  asm_op_mem_writes name args b ==>
  ?range. MEM range (source_memory_write_ranges inst vs) /\
          byte_in_memory_range range b
Proof
  rpt strip_tac >>
  gvs[venomStateTheory.eval_operands_def, AllCaseEqs()] >>
  gvs[asmIRTheory.venom_to_evm_name_def, asm_op_mem_writes_def,
      source_memory_write_ranges_def, sized_source_write_range_def,
      byte_in_memory_range_def, in_mem_range_def]
QED

Theorem extcodecopy_source_write_coverage:
  inst.inst_opcode = EXTCODECOPY /\
  inst.inst_operands = [addr; dst; src; len] /\
  eval_operands inst.inst_operands vs = SOME args /\
  asm_op_mem_writes "EXTCODECOPY" args b ==>
  ?range. MEM range (source_memory_write_ranges inst vs) /\
          byte_in_memory_range range b
Proof
  rpt strip_tac >>
  gvs[venomStateTheory.eval_operands_def, AllCaseEqs()] >>
  gvs[asm_op_mem_writes_def, source_memory_write_ranges_def,
      sized_source_write_range_def, byte_in_memory_range_def, in_mem_range_def]
QED

Theorem mstore_source_write_coverage:
  MEM inst.inst_opcode [MSTORE; MSTORE8] /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  inst.inst_operands = [dst; value] /\
  eval_operands inst.inst_operands vs = SOME args /\
  asm_op_mem_writes name args b ==>
  ?range. MEM range (source_memory_write_ranges inst vs) /\
          byte_in_memory_range range b
Proof
  rpt strip_tac >>
  gvs[venomStateTheory.eval_operands_def, AllCaseEqs()] >>
  gvs[asmIRTheory.venom_to_evm_name_def, asm_op_mem_writes_def,
      source_memory_write_ranges_def, fixed_source_write_range_def,
      byte_in_memory_range_def, in_mem_range_def]
QED

Theorem log_source_read_coverage:
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: rest /\
  LENGTH rest = w2n tc + 2 /\ REVERSE rest = off :: len :: topics /\
  MEM name ["LOG0"; "LOG1"; "LOG2"; "LOG3"; "LOG4"] /\
  eval_operands (REVERSE rest) vs = SOME args /\
  asm_op_mem_reads name args b ==>
  source_memory_read_byte inst vs b
Proof
  rpt strip_tac >>
  gvs[venomStateTheory.eval_operands_def, AllCaseEqs()] >>
  gvs[asm_op_mem_reads_def, source_memory_read_byte_def,
      source_memory_read_ranges_def, memory_range_of_operands_def,
      byte_in_memory_range_def, in_mem_range_def, log_table_def]
QED

Theorem nonmemory_emission_reads_empty:
  ~MEM name ["MLOAD"; "SHA3"; "RETURN"; "REVERT";
    "LOG0"; "LOG1"; "LOG2"; "LOG3"; "LOG4";
    "MCOPY"; "CREATE"; "CREATE2"; "CALL"; "STATICCALL"; "DELEGATECALL"] ==>
  ~asm_op_mem_reads name args b
Proof
  simp[asm_op_mem_reads_def, log_table_def] >> metis_tac[]
QED

Theorem nonmemory_emission_writes_empty:
  ~MEM name ["MSTORE"; "MSTORE8"; "MCOPY"; "CALLDATACOPY";
             "RETURNDATACOPY"; "CODECOPY"; "EXTCODECOPY"] ==>
  ~asm_op_mem_writes name args b
Proof
  simp[asm_op_mem_writes_def] >> metis_tac[]
QED

Theorem source_read_byte_no_labels:
  source_memory_reads_disjoint cplan inst vs /\
  (!b. b IN FDOM labs ==> context_spill_byte cplan b) /\
  source_memory_read_byte inst vs b ==>
  b NOTIN FDOM labs
Proof
  simp[source_memory_read_byte_def] >> rpt strip_tac >>
  rename1 `MEM rng (source_memory_read_ranges inst vs)` >>
  PairCases_on `rng` >>
  gvs[source_memory_reads_disjoint_def, byte_in_memory_range_def,
      GSYM in_mem_range_def] >>
  drule_all (SRULE [arithmeticTheory.ADD_COMM] spill_disjoint_ranges_no_labels) >> simp[]
QED

Theorem source_write_byte_no_labels:
  context_source_memory_writes_disjoint cplan inst vs /\
  (!b. b IN FDOM labs ==> context_spill_byte cplan b) /\
  MEM rng (source_memory_write_ranges inst vs) /\
  byte_in_memory_range rng b ==>
  b NOTIN FDOM labs
Proof
  PairCases_on `rng` >> rpt strip_tac >>
  gvs[context_source_memory_writes_disjoint_def, byte_in_memory_range_def,
      GSYM in_mem_range_def] >>
  drule_all (SRULE [arithmeticTheory.ADD_COMM] spill_disjoint_ranges_no_labels) >> simp[]
QED

Theorem source_footprint_symbolic_memory_safe:
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  (!b. b IN FDOM labs ==> context_spill_byte cplan b) /\
  (!b. asm_op_mem_reads name args b ==>
    source_memory_read_byte inst vs b \/
    (?rng. MEM rng (source_memory_write_ranges inst vs) /\
           byte_in_memory_range rng b)) /\
  (!b. asm_op_mem_writes name args b ==>
    ?rng. MEM rng (source_memory_write_ranges inst vs) /\
          byte_in_memory_range rng b) ==>
  !b. b IN FDOM labs ==>
    ~asm_op_mem_reads name args b /\ ~asm_op_mem_writes name args b
Proof
  metis_tac[source_read_byte_no_labels, source_write_byte_no_labels]
QED

Theorem sym_numeric_emit_replay:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  asm_block_at p cs.as_pc [AsmOp name] /\
  asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
    (AsmOp name) cs = AsmOK cs' /\
  asm_op_arity name <= LENGTH ss.sym_stack /\
  EVERY (\sv. ?w. sv = Val w) (TAKE (asm_op_arity name) ss.sym_stack) /\
  (!b. b IN FDOM ss.sym_mem_labels ==>
    ~asm_op_mem_reads name (TAKE (asm_op_arity name) cs.as_stack) b /\
    ~asm_op_mem_writes name (TAKE (asm_op_arity name) cs.as_stack) b) /\
  sym_step_op p env name ss = sym_step_concrete name ss ==>
  ?ss'. sym_steps p env 1 ss = SymOK ss' /\
    asm_sym_rel p env cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    ?ws. ss'.sym_stack = MAP Val ws ++ DROP (asm_op_arity name) ss.sym_stack
Proof
  strip_tac >>
  `!msg. sym_step_concrete name ss <> SymBad msg` by
    (irule sym_step_concrete_numeric_safe >>
     simp[mem_labels_hit_def] >> metis_tac[]) >>
  `?ss'. sym_step p env (AsmOp name) ss = SymOK ss' /\
    asm_sym_rel p env cs' ss'` by
    (`cs.as_pc < LENGTH p /\ EL cs.as_pc p = AsmOp name` by
       (fs[asm_block_at_def] >>
        first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
     drule asm_sym_step_success_from_safe >>
     disch_then (qspecl_then [`ss`, `env`, `cs'`, `cs`] mp_tac) >>
     simp[sym_step_def]) >>
  qexists `ss'` >>
  `sym_steps p env 1 ss = SymOK ss'` by
    (irule sym_steps_single_emit >>
     fs[asmSymBridgeTheory.asm_sym_rel_def] >> metis_tac[]) >>
  simp[] >> irule sym_step_concrete_numeric_shape >>
  fs[sym_step_def] >> metis_tac[]
QED

Theorem sym_emit_kinds_numeric_result:
  sym_kinds_ok cplan fn ret srest ps ss /\
  k <= LENGTH ps.ps_stack /\
  ss'.sym_mem_labels = ss.sym_mem_labels /\
  ss'.sym_stack = MAP Val ws ++ DROP k ss.sym_stack /\
  qs.ps_spilled = ps.ps_spilled /\
  REVERSE qs.ps_stack = outputs ++ DROP k (REVERSE ps.ps_stack) /\
  LIST_REL (op_kind_ok fn ret) outputs (MAP Val ws) ==>
  sym_kinds_ok cplan fn ret srest qs ss'
Proof
  simp[sym_kinds_ok_def] >> rpt strip_tac
  >- (qexists `MAP Val ws ++ DROP k top` >>
      `LENGTH top = LENGTH ps.ps_stack` by
        metis_tac[LIST_REL_LENGTH, LENGTH_REVERSE] >>
      simp[DROP_APPEND1] >> irule LIST_REL_APPEND_suff >> simp[] >>
      irule rich_listTheory.LIST_REL_DROP >> simp[])
QED

Theorem numeric_prefix_two:
  2 <= LENGTH svs /\ EVERY (\sv. ?w. sv = Val w) (TAKE 2 svs) ==>
  ?a b tail. svs = Val a :: Val b :: tail
Proof
  Cases_on `svs` >> simp[] >> rename1 `TAKE 1 tail` >>
  Cases_on `tail` >> simp[] >> metis_tac[]
QED

Theorem sym_step_add_numeric_dispatch:
  2 <= LENGTH ss.sym_stack /\
  EVERY (\sv. ?w. sv = Val w) (TAKE 2 ss.sym_stack) ==>
  sym_step_op p env "ADD" ss = sym_step_concrete "ADD" ss
Proof
  strip_tac >> drule_all numeric_prefix_two >>
  metis_tac[sym_step_add_words]
QED

Theorem sym_step_mstore_numeric_dispatch:
  2 <= LENGTH ss.sym_stack /\
  EVERY (\sv. ?w. sv = Val w) (TAKE 2 ss.sym_stack) ==>
  sym_step_op p env "MSTORE" ss = sym_step_concrete "MSTORE" ss
Proof
  strip_tac >> drule_all numeric_prefix_two >>
  metis_tac[sym_step_mstore_words]
QED

Theorem sym_step_mload_numeric_dispatch:
  asm_sym_rel p env cs ss /\
  1 <= LENGTH ss.sym_stack /\
  EVERY (\sv. ?w. sv = Val w) (TAKE 1 ss.sym_stack) /\
  (!b. b IN FDOM ss.sym_mem_labels ==>
    ~asm_op_mem_reads "MLOAD" (TAKE 1 cs.as_stack) b) ==>
  sym_step_op p env "MLOAD" ss = sym_step_concrete "MLOAD" ss
Proof
  strip_tac >>
  `TAKE 1 ss.sym_stack = MAP Val (TAKE 1 cs.as_stack)` by
    metis_tac[asm_sym_numeric_take] >>
  Cases_on `ss.sym_stack` >> gvs[] >>
  Cases_on `cs.as_stack` >> gvs[] >>
  rename1 `ss.sym_stack = Val off :: tail` >>
  `w2n off NOTIN FDOM ss.sym_mem_labels` by
    (qpat_x_assum `!b. _` (qspec_then `w2n off` mp_tac) >>
     simp[asm_op_mem_reads_def, in_mem_range_def]) >>
  irule sym_step_mload_word >> metis_tac[]
QED

Theorem sym_step_numeric_dispatch:
  ~MEM name ["POP"; "JUMP"; "JUMPI"; "CODECOPY"; "CODESIZE"] /\
  ALOOKUP dup_table name = NONE /\ ALOOKUP swap_table name = NONE /\
  asm_sym_rel p env cs ss /\
  asm_op_arity name <= LENGTH ss.sym_stack /\
  EVERY (\sv. ?w. sv = Val w) (TAKE (asm_op_arity name) ss.sym_stack) /\
  (!b. b IN FDOM ss.sym_mem_labels ==>
    ~asm_op_mem_reads name (TAKE (asm_op_arity name) cs.as_stack) b) ==>
  sym_step_op p env name ss = sym_step_concrete name ss
Proof
  strip_tac >> Cases_on `name = "ADD"`
  >- (gvs[] >> irule sym_step_add_numeric_dispatch >>
      fs[asm_op_arity_def, asm_op_arity_table_def]) >>
  Cases_on `name = "MSTORE"`
  >- (gvs[] >> irule sym_step_mstore_numeric_dispatch >>
      fs[asm_op_arity_def, asm_op_arity_table_def]) >>
  Cases_on `name = "MLOAD"`
  >- (gvs[] >> irule sym_step_mload_numeric_dispatch >>
      fs[asm_op_arity_def, asm_op_arity_table_def] >> metis_tac[]) >>
  irule sym_step_op_plain >> fs[]
QED

Theorem sym_prepared_numeric_emit:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p cs.as_pc [AsmOp name] /\
  asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
    (AsmOp name) cs = AsmOK cs' /\
  ~MEM name ["POP"; "JUMP"; "JUMPI"; "CODECOPY"; "CODESIZE"] /\
  ALOOKUP dup_table name = NONE /\ ALOOKUP swap_table name = NONE /\
  asm_op_arity name <= LENGTH ps.ps_stack /\
  asm_op_arity name <= LENGTH ss.sym_stack /\
  EVERY (\sv. ?w. sv = Val w) (TAKE (asm_op_arity name) ss.sym_stack) /\
  (!b. b IN FDOM ss.sym_mem_labels ==>
    ~asm_op_mem_reads name (TAKE (asm_op_arity name) cs.as_stack) b /\
    ~asm_op_mem_writes name (TAKE (asm_op_arity name) cs.as_stack) b) /\
  qs.ps_spilled = ps.ps_spilled /\
  REVERSE qs.ps_stack = outputs ++ DROP (asm_op_arity name) (REVERSE ps.ps_stack) /\
  (!op w. MEM op outputs ==> op_kind_ok fn ret op (Val w)) /\
  LENGTH cs'.as_stack + asm_op_arity name = LENGTH cs.as_stack + LENGTH outputs ==>
  ?ss'. sym_steps p env 1 ss = SymOK ss' /\ asm_sym_rel p env cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  strip_tac >>
  `sym_step_op p env name ss = sym_step_concrete name ss` by
    (irule sym_step_numeric_dispatch >> metis_tac[]) >>
  drule_all sym_numeric_emit_replay >> strip_tac >>
  `LENGTH ss.sym_stack = LENGTH cs.as_stack /\
   LENGTH ss'.sym_stack = LENGTH cs'.as_stack` by
    metis_tac[asmSymBridgeTheory.asm_sym_rel_def, LIST_REL_LENGTH] >>
  `LENGTH ws = LENGTH outputs` by
    (qpat_x_assum `ss'.sym_stack = _` (mp_tac o AP_TERM ``LENGTH:sval list -> num``) >>
     simp[] >> decide_tac) >>
  `LIST_REL (op_kind_ok fn ret) outputs (MAP Val ws)` by
    (rw[LIST_REL_EL_EQN] >> simp[EL_MAP] >>
     first_x_assum irule >> metis_tac[MEM_EL]) >>
  qexists `ss'` >> simp[] >>
  drule_all sym_emit_kinds_numeric_result >> simp[]
QED

Theorem sym_prepared_selected_numeric:
  sym_kinds_ok cplan fn ret srest ps ss /\
  ps.ps_stack = residual ++ selected /\
  EVERY (\op. !sv. op_kind_ok fn ret op sv ==> ?w. sv = Val w) selected ==>
  LENGTH selected <= LENGTH ss.sym_stack /\
  EVERY (\sv. ?w. sv = Val w) (TAKE (LENGTH selected) ss.sym_stack)
Proof
  simp[sym_kinds_ok_def] >> rpt strip_tac >>
  `LENGTH top = LENGTH residual + LENGTH selected` by
    metis_tac[LIST_REL_LENGTH, LENGTH_REVERSE, LENGTH_APPEND]
  >- simp[] >>
  `LIST_REL (op_kind_ok fn ret) (REVERSE selected)
    (TAKE (LENGTH selected) top)` by
    (drule rich_listTheory.EVERY2_TAKE >>
     disch_then (qspec_then `LENGTH selected` mp_tac) >>
     simp[REVERSE_APPEND, TAKE_APPEND1, TAKE_LENGTH_TOO_LONG]) >>
  simp[TAKE_APPEND1] >> irule numeric_operand_kinds_list >>
  qexistsl [`fn`, `REVERSE selected`, `ret`] >> simp[]
QED

Theorem ordinary_prepared_selected_numeric:
  opaque_use_ok fn /\ label_flow_ok ctx /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  (!op. MEM op selected ==> MEM op inst.inst_operands /\ ~is_label_operand op) /\
  ~MEM inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET; CODECOPY] /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  ps.ps_stack = residual ++ selected ==>
  LENGTH selected <= LENGTH ss.sym_stack /\
  EVERY (\sv. ?w. sv = Val w) (TAKE (LENGTH selected) ss.sym_stack)
Proof
  strip_tac >> irule sym_prepared_selected_numeric >>
  qexistsl [`cplan`, `fn`, `ps`, `residual`, `ret`, `srest`] >> simp[] >>
  rw[EVERY_MEM] >> metis_tac[ordinary_source_input_numeric_kind]
QED

Theorem sym_numeric_emit_output_plan:
  k <= LENGTH ps.ps_stack /\
  qs = ps with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
    (stack_pop k ps.ps_stack) outs ==>
  qs.ps_spilled = ps.ps_spilled /\
  REVERSE qs.ps_stack = REVERSE (MAP Var outs) ++ DROP k (REVERSE ps.ps_stack)
Proof
  `!stk. FOLDL (\stk out. stack_push (Var out) stk) stk outs =
    stk ++ MAP Var outs` by
    (Induct_on `outs` >> simp[stackModelTheory.stack_push_def,
       SNOC_APPEND, APPEND_ASSOC]) >>
  simp[stackModelTheory.stack_pop_def, REVERSE_APPEND,
       rich_listTheory.DROP_REVERSE, rich_listTheory.BUTLASTN_TAKE_UNCOND]
QED

Theorem sym_emit_concrete_output_count:
  venom_asm_rel lo ps vs cs /\ venom_asm_rel lo qs vs' cs' /\
  k <= LENGTH ps.ps_stack /\
  REVERSE qs.ps_stack = outputs ++ DROP k (REVERSE ps.ps_stack) ==>
  LENGTH cs'.as_stack + k = LENGTH cs.as_stack + LENGTH outputs
Proof
  strip_tac >>
  `LENGTH ps.ps_stack = LENGTH cs.as_stack /\
   LENGTH qs.ps_stack = LENGTH cs'.as_stack` by
    fs[venom_asm_rel_def, plan_stack_rel_def] >>
  qpat_x_assum `REVERSE _ = _` (mp_tac o AP_TERM ``LENGTH:operand list -> num``) >>
  simp[] >> decide_tac
QED

Theorem named_numeric_dispatch_names:
  venom_to_evm_name opc = SOME name /\ opc <> CODECOPY /\ opc <> CODESIZE ==>
  ~MEM name ["POP"; "JUMP"; "JUMPI"; "CODECOPY"; "CODESIZE"] /\
  ALOOKUP dup_table name = NONE /\ ALOOKUP swap_table name = NONE
Proof
  Cases_on `opc` >>
  simp[asmIRTheory.venom_to_evm_name_def] >> strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem named_numeric_emission_arity:
  venom_to_evm_name inst.inst_opcode = SOME name /\ inst_wf inst /\
  step_inst fuel ctx inst vs = OK vs' /\
  ~is_pre_codegen_opcode inst.inst_opcode /\ inst.inst_opcode <> GAS /\
  inst.inst_opcode <> CODESIZE /\ inst.inst_opcode <> CODECOPY /\
  (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) ==>
  asm_op_arity name = LENGTH (compute_operands inst)
Proof
  strip_tac >> drule_all regularPlanSimTheory.regular_named_ok_families >>
  Cases_on `inst.inst_opcode` >>
  simp[asmIRTheory.venom_to_evm_name_def, opcodeClassTheory.ef_pure1_def,
       opcodeClassTheory.ef_arith1_def, opcodeClassTheory.ef_arith2_def,
       opcodeClassTheory.ef_cmp_def, opcodeClassTheory.ef_bits_def,
       opcodeClassTheory.ef_pure3_def, opcodeClassTheory.ef_read0_def,
       opcodeClassTheory.ef_read1_def] >>
  gvs[asmIRTheory.venom_to_evm_name_def, opcodeClassTheory.ef_read0_def] >>
  fs[venomWfTheory.inst_wf_def] >>
  simp[stackPlanGenTheory.compute_operands_def] >>
  simp[venomInstTheory.python_stack_operands_def] >>
  simp[venomInstTheory.ir_specific_operand_order_def] >>
  EVAL_TAC
QED

Theorem regular_numeric_selection_shape:
  (selected = operands \/
   (is_commutative opc /\ 2 <= LENGTH operands /\
    selected = TAKE (LENGTH operands - 2) operands ++
      [EL (LENGTH operands - 1) operands; EL (LENGTH operands - 2) operands])) ==>
  LENGTH selected = LENGTH operands /\
  (!op. MEM op selected <=> MEM op operands)
Proof
  disch_then (mp_tac o MATCH_MP generatedPrefixSimTheory.regular_plan_selected_perm) >>
  metis_tac[sortingTheory.PERM_LENGTH, sortingTheory.PERM_MEM_EQ]
QED

Theorem numeric_add_label_free:
  label_positions_ok inst /\ inst.inst_opcode = ADD /\
  ~(?op. inst.inst_operands = [op; Label "code_end"]) ==>
  EVERY (\op. ~is_label_operand op) inst.inst_operands
Proof
  strip_tac >> gvs[unitShapeDefsTheory.label_positions_ok_def] >>
  last_x_assum mp_tac >>
  rpt BasicProvers.TOP_CASE_TAC >> gvs[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem named_opcode_operand_cases:
  venom_to_evm_name opc = SOME name ==>
  ~MEM opc [JMP; DJMP; JNZ; PHI; INVOKE; LOG]
Proof
  Cases_on `opc` >> simp[asmIRTheory.venom_to_evm_name_def]
QED

Theorem named_numeric_source_no_labels:
  fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  inst.inst_opcode <> CODECOPY /\
  ~(?op. inst.inst_opcode = ADD /\ inst.inst_operands = [op; Label "code_end"]) ==>
  EVERY (\op. ~is_label_operand op) inst.inst_operands
Proof
  strip_tac >>
  `label_positions_ok inst` by
    metis_tac[unitShapeDefsTheory.fn_shape_ok_def, EVERY_MEM,
              unitShapeDefsTheory.inst_shape_ok_def] >>
  Cases_on `inst.inst_opcode = ADD`
  >- (irule numeric_add_label_free >> gvs[]) >>
  irule fnBlockBodyHelpersTheory.label_positions_ok_other >>
  drule named_opcode_operand_cases >> simp[]
QED

Theorem named_compute_operands_membership:
  venom_to_evm_name inst.inst_opcode = SOME name ==>
  !op. MEM op (compute_operands inst) <=> MEM op inst.inst_operands
Proof
  strip_tac >> drule named_opcode_operand_cases >>
  simp[stackPlanGenTheory.compute_operands_def]
QED

Theorem named_numeric_selected_operands:
  fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  inst.inst_opcode <> CODECOPY /\
  ~(?op. inst.inst_opcode = ADD /\ inst.inst_operands = [op; Label "code_end"]) /\
  (selected = compute_operands inst \/
   (is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst) /\
    selected = TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
      [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
       EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)])) ==>
  LENGTH selected = LENGTH (compute_operands inst) /\
  (!op. MEM op selected ==> MEM op inst.inst_operands /\ ~is_label_operand op)
Proof
  strip_tac >>
  `LENGTH selected = LENGTH (compute_operands inst) /\
   (!op. MEM op selected <=> MEM op (compute_operands inst))` by
    metis_tac[regular_numeric_selection_shape] >>
  drule_all named_numeric_source_no_labels >>
  drule named_compute_operands_membership >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem memory_family_selected_order:
  MEM inst.inst_opcode [MLOAD; SHA3; MSTORE; MSTORE8; MCOPY;
    CALLDATACOPY; RETURNDATACOPY; CODECOPY; EXTCODECOPY;
    CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  inst_wf inst /\
  (selected = compute_operands inst \/
   (is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst) /\
    selected = TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
      [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
       EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)])) ==>
  REVERSE selected = inst.inst_operands
Proof
  strip_tac >>
  gvs[venomEffectsTheory.is_commutative_def, stackPlanGenTheory.compute_operands_def,
      venomInstTheory.python_stack_operands_def,
      venomInstTheory.ir_specific_operand_order_def, venomWfTheory.inst_wf_def,
      LENGTH_EQ_1]
QED

Theorem iload_source_read_coverage:
  inst.inst_opcode = ILOAD /\ inst.inst_operands = [off] /\
  eval_operands inst.inst_operands vs = SOME args /\
  asm_op_mem_reads "MLOAD" args b ==>
  source_memory_read_byte inst vs b
Proof
  rpt strip_tac >>
  gvs[venomStateTheory.eval_operands_def, AllCaseEqs()] >>
  gvs[asm_op_mem_reads_def, source_memory_read_byte_def,
      source_memory_read_ranges_def, byte_in_memory_range_def, in_mem_range_def]
QED

Theorem named_source_footprint_families:
  venom_to_evm_name inst.inst_opcode = SOME name /\
  step_inst fuel ctx inst vs = OK vs' ==>
  MEM inst.inst_opcode [ILOAD; MLOAD; SHA3; MSTORE; MSTORE8; MCOPY;
    CALLDATACOPY; RETURNDATACOPY; CODECOPY; EXTCODECOPY;
    CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] \/
  (~MEM name ["MLOAD"; "SHA3"; "RETURN"; "REVERT";
    "LOG0"; "LOG1"; "LOG2"; "LOG3"; "LOG4";
    "MCOPY"; "CREATE"; "CREATE2"; "CALL"; "STATICCALL"; "DELEGATECALL"] /\
   ~MEM name ["MSTORE"; "MSTORE8"; "MCOPY"; "CALLDATACOPY";
             "RETURNDATACOPY"; "CODECOPY"; "EXTCODECOPY"])
Proof
  strip_tac >> drule_all regularPlanSimTheory.regular_named_ok_nonterminator >>
  Cases_on `inst.inst_opcode` >>
  qpat_x_assum `venom_to_evm_name _ = _` mp_tac >>
  pure_rewrite_tac[asmIRTheory.venom_to_evm_name_def, optionTheory.SOME_11,
                  optionTheory.NOT_NONE_SOME] >>
  strip_tac >> gvs[venomInstTheory.is_terminator_def] >> EVAL_TAC
QED

Theorem memory_family_source_read_coverage:
  MEM inst.inst_opcode [ILOAD; MLOAD; SHA3; MSTORE; MSTORE8; MCOPY;
    CALLDATACOPY; RETURNDATACOPY; CODECOPY; EXTCODECOPY;
    CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  venom_to_evm_name inst.inst_opcode = SOME name /\ inst_wf inst /\
  eval_operands inst.inst_operands vs = SOME args /\
  asm_op_mem_reads name args b ==>
  source_memory_read_byte inst vs b \/
  (?rng. MEM rng (source_memory_write_ranges inst vs) /\ byte_in_memory_range rng b)
Proof
  strip_tac >> gvs[asmIRTheory.venom_to_evm_name_def,
    nonmemory_emission_reads_empty, venomWfTheory.inst_wf_def, LENGTH_EQ_NUM_compute] >>
  simp[call_source_read_write_coverage, readonly_call_source_read_write_coverage,
    mload_source_read_coverage, iload_source_read_coverage, sha3_source_read_coverage,
    copy_create_source_read_coverage, create2_source_read_coverage, MEM,
    asmIRTheory.venom_to_evm_name_def]
QED

Theorem memory_family_source_write_coverage:
  MEM inst.inst_opcode [ILOAD; MLOAD; SHA3; MSTORE; MSTORE8; MCOPY;
    CALLDATACOPY; RETURNDATACOPY; CODECOPY; EXTCODECOPY;
    CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  venom_to_evm_name inst.inst_opcode = SOME name /\ inst_wf inst /\
  eval_operands inst.inst_operands vs = SOME args /\
  asm_op_mem_writes name args b ==>
  ?rng. MEM rng (source_memory_write_ranges inst vs) /\ byte_in_memory_range rng b
Proof
  strip_tac >> gvs[asmIRTheory.venom_to_evm_name_def,
    nonmemory_emission_writes_empty, venomWfTheory.inst_wf_def, LENGTH_EQ_NUM_compute] >>
  simp[copy_source_write_coverage, extcodecopy_source_write_coverage,
    mstore_source_write_coverage, MEM, asmIRTheory.venom_to_evm_name_def]
QED

Theorem named_source_order_read_coverage:
  venom_to_evm_name inst.inst_opcode = SOME name /\ inst_wf inst /\
  ~is_pre_codegen_opcode inst.inst_opcode /\
  step_inst fuel ctx inst vs = OK vs' /\
  eval_operands inst.inst_operands vs = SOME args /\
  asm_op_mem_reads name args b ==>
  source_memory_read_byte inst vs b \/
  (?rng. MEM rng (source_memory_write_ranges inst vs) /\ byte_in_memory_range rng b)
Proof
  strip_tac >> drule_all named_source_footprint_families >> strip_tac
  >- (irule memory_family_source_read_coverage >> metis_tac[]) >>
  metis_tac[nonmemory_emission_reads_empty]
QED

Theorem named_source_order_write_coverage:
  venom_to_evm_name inst.inst_opcode = SOME name /\ inst_wf inst /\
  step_inst fuel ctx inst vs = OK vs' /\
  eval_operands inst.inst_operands vs = SOME args /\
  asm_op_mem_writes name args b ==>
  ?rng. MEM rng (source_memory_write_ranges inst vs) /\ byte_in_memory_range rng b
Proof
  strip_tac >> drule_all named_source_footprint_families >> strip_tac
  >- (irule memory_family_source_write_coverage >> metis_tac[]) >>
  metis_tac[nonmemory_emission_writes_empty]
QED

Theorem memory_family_selected_source_order:
  MEM inst.inst_opcode [ILOAD; MLOAD; SHA3; MSTORE; MSTORE8; MCOPY;
    CALLDATACOPY; RETURNDATACOPY; CODECOPY; EXTCODECOPY;
    CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  inst_wf inst /\
  (selected = compute_operands inst \/
   (is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst) /\
    selected = TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
      [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
       EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)])) ==>
  REVERSE selected = inst.inst_operands
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `inst.inst_opcode = ILOAD`
  >- gvs[venomEffectsTheory.is_commutative_def, stackPlanGenTheory.compute_operands_def,
      venomInstTheory.python_stack_operands_def, venomInstTheory.ir_specific_operand_order_def,
      venomWfTheory.inst_wf_def, LENGTH_EQ_1] >>
  irule memory_family_selected_order >> gvs[MEM]
QED

Theorem named_selected_read_coverage:
  venom_to_evm_name inst.inst_opcode = SOME name /\ inst_wf inst /\
  step_inst fuel ctx inst vs = OK vs' /\
  (selected = compute_operands inst \/
   (is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst) /\
    selected = TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
      [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
       EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)])) /\
  eval_operands (REVERSE selected) vs = SOME args /\
  asm_op_mem_reads name args b ==>
  source_memory_read_byte inst vs b \/
  (?rng. MEM rng (source_memory_write_ranges inst vs) /\ byte_in_memory_range rng b)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all named_source_footprint_families >> strip_tac
  >- (drule_all memory_family_selected_source_order >> strip_tac >>
      irule memory_family_source_read_coverage >> metis_tac[]) >>
  metis_tac[nonmemory_emission_reads_empty]
QED

Theorem named_selected_write_coverage:
  venom_to_evm_name inst.inst_opcode = SOME name /\ inst_wf inst /\
  step_inst fuel ctx inst vs = OK vs' /\
  (selected = compute_operands inst \/
   (is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst) /\
    selected = TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
      [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
       EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)])) /\
  eval_operands (REVERSE selected) vs = SOME args /\
  asm_op_mem_writes name args b ==>
  ?rng. MEM rng (source_memory_write_ranges inst vs) /\ byte_in_memory_range rng b
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all named_source_footprint_families >> strip_tac
  >- (drule_all memory_family_selected_source_order >> strip_tac >>
      irule memory_family_source_write_coverage >> metis_tac[]) >>
  metis_tac[nonmemory_emission_writes_empty]
QED

Theorem sym_named_numeric_source_emit:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p cs.as_pc [AsmOp name] /\
  asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
    (AsmOp name) cs = AsmOK cs' /\
  venom_to_evm_name inst.inst_opcode = SOME name /\ inst_wf inst /\
  step_inst fuel ctx inst vs = OK vs' /\
  ~is_pre_codegen_opcode inst.inst_opcode /\ inst.inst_opcode <> GAS /\
  inst.inst_opcode <> CODECOPY /\
  (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
  ~(?op. inst.inst_opcode = ADD /\ inst.inst_operands = [op; Label "code_end"]) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ MEM fn ctx.ctx_functions /\
  fn_shape_ok fn /\ ssa_form fn /\ MEM inst (fn_insts fn) /\
  (selected = compute_operands inst \/
   (is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst) /\
    selected = TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
      [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
       EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)])) /\
  ps.ps_stack = residual ++ selected /\
  EVERY (\op. op <> dead_stack_marker) selected /\
  (!op. MEM op selected ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  venom_asm_rel lo qs vsout cs' /\
  qs = ps with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
    (stack_pop (LENGTH selected) ps.ps_stack) inst.inst_outputs /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs ==>
  ?ss'. sym_steps p env 1 ss = SymOK ss' /\ asm_sym_rel p env cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `inst.inst_opcode <> CODESIZE` by metis_tac[label_flow_inst_not_codesize] >>
  `~MEM inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET; CODECOPY; RETPC_PARAM]` by
    (qpat_x_assum `venom_to_evm_name _ = _` mp_tac >>
     Cases_on `inst.inst_opcode` >>
     simp[asmIRTheory.venom_to_evm_name_def] >> fs[]) >>
  drule_all named_numeric_selected_operands >> strip_tac >>
  drule_all named_numeric_emission_arity >> strip_tac >>
  `eval_operands (REVERSE selected) vs =
     SOME (TAKE (LENGTH selected) cs.as_stack)` by
    (irule ordinary_prepared_source_evaluation >> simp[] >>
     qexistsl [`fn`, `inst`, `lo`, `m`, `ps`, `ra`, `residual`] >> fs[MEM]) >>
  `LENGTH selected <= LENGTH ss.sym_stack /\
   EVERY (\sv. ?w. sv = Val w) (TAKE (LENGTH selected) ss.sym_stack)` by
    (irule ordinary_prepared_selected_numeric >>
     qexistsl [`cplan`, `ctx`, `fn`, `inst`, `ps`, `residual`, `ret`, `srest`] >>
     fs[MEM]) >>
  `!b. b IN FDOM ss.sym_mem_labels ==>
    ~asm_op_mem_reads name (TAKE (LENGTH selected) cs.as_stack) b /\
    ~asm_op_mem_writes name (TAKE (LENGTH selected) cs.as_stack) b` by
    (ho_match_mp_tac source_footprint_symbolic_memory_safe >>
     simp[] >>
     conj_tac >- fs[sym_kinds_ok_def] >>
     conj_tac >- (gen_tac >> strip_tac >> irule named_selected_read_coverage >>
       metis_tac[]) >>
     gen_tac >> strip_tac >> irule named_selected_write_coverage >>
     metis_tac[]) >>
  `qs.ps_spilled = ps.ps_spilled /\
   REVERSE qs.ps_stack = REVERSE (MAP Var inst.inst_outputs) ++
     DROP (asm_op_arity name) (REVERSE ps.ps_stack)` by
    (irule sym_numeric_emit_output_plan >> simp[]) >>
  `LENGTH (compute_operands inst) <= LENGTH ps.ps_stack` by simp[] >>
  `LENGTH cs'.as_stack + asm_op_arity name =
   LENGTH cs.as_stack + LENGTH (REVERSE (MAP Var inst.inst_outputs))` by
    (irule sym_emit_concrete_output_count >> simp[] >>
     metis_tac[]) >>
  drule_all named_numeric_dispatch_names >> strip_tac >>
  irule sym_prepared_numeric_emit >> simp[] >>
  qexistsl [`cs`, `name`, `REVERSE (MAP Var inst.inst_outputs)`, `ps`] >>
  simp[] >> conj_tac
  >- (simp[MEM_MAP] >> rpt strip_tac >> gvs[] >>
      irule ordinary_output_kind >> fs[MEM] >> metis_tac[]) >>
  metis_tac[MEM]
QED

Theorem sym_emit_run_endpoint:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  sym_steps p env n ss = SymOK ss' /\
  asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p)
    p n cs = AsmOK cs' ==>
  asm_sym_rel p env cs' ss'
Proof
  metis_tac[asm_sym_steps_lockstep, asmSemTheory.asm_result_11]
QED

Theorem sym_initial_fmp_source_emit:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  inst.inst_opcode = INITIAL_FMP /\ inst.inst_outputs = [x] /\
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  qs = ps with ps_stack := stack_push (Var x) ps.ps_stack /\
  asm_block_at p ss.sym_base.as_pc [AsmPush (encode_num_bytes initial_fmp)] /\
  asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p)
    p 1 cs = AsmOK cs' ==>
  ?ss'. sym_steps p env 1 ss = SymOK ss' /\ asm_sym_rel p env cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  strip_tac >> drule sym_initial_fmp_run >> strip_tac >>
  qmatch_asmsub_abbrev_tac `sym_steps p env 1 ss = SymOK final` >>
  qexists `final` >> simp[] >>
  conj_tac >- (irule sym_emit_run_endpoint >> metis_tac[]) >>
  simp[Abbr `final`] >>
  `op_kind_ok fn ret (Var x) (Val (n2w initial_fmp))` by
    (irule ordinary_output_kind >> simp[] >> qexists `inst` >> simp[]) >>
  fs[sym_kinds_ok_def, stackModelTheory.stack_push_def, SNOC_APPEND,
     REVERSE_APPEND] >> metis_tac[]
QED
