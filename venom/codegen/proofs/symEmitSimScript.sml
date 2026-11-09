(* Symbolic emitted-opcode boundaries. *)
Theory symEmitSim
Ancestors
  symInstKinds symPostfixSim codegenSymRel asmSymSem asmSem
  strongPrefixSim asmSplice finite_map list

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
