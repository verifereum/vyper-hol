(* LOG planner/emission composition shared by canonical and relocated machines. *)
Theory symInstLogOwn
Ancestors asmSymBridge symInstPiecesFacts symInstPrefixOwn symEmitOwn asmSymModeOwn
  symPostfixSim symPlannerSim stackPlanGen stackPlanOps stackModel asmSplice
  planExec codegenSymRel asmSymSem doSwapSim genBlockSim symEmitSim fnFrameDeepInst

val log_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", log_bridge_core_tm);

Theorem sym_log_name_dispatch:
  n <= 4 ==>
  ALOOKUP log_table ("LOG" ++ num_to_dec_string n) = SOME n /\
  ~MEM ("LOG" ++ num_to_dec_string n) ["POP"; "JUMP"; "JUMPI"; "CODESIZE"] /\
  ALOOKUP dup_table ("LOG" ++ num_to_dec_string n) = NONE /\
  ALOOKUP swap_table ("LOG" ++ num_to_dec_string n) = NONE /\
  asm_op_arity ("LOG" ++ num_to_dec_string n) = n + 2
Proof
  strip_tac >> `n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4` by decide_tac >>
  gvs[] >> EVAL_TAC
QED

Theorem sym_log_prepared_suffix_mode_core:
  (!cs ss ai cs'. bridge_core slo code_ok cs ss /\ asm_block_at p cs.as_pc [ai] /\
    asm_step slo (build_offset_to_pc p) ai cs = AsmOK cs' /\
    (!msg. (if allow_own then sym_step_own p env own ai ss
            else sym_step p env ai ss) <> SymBad msg) ==>
    ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
      bridge_core slo code_ok cs' ss') /\
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: selected /\
  LENGTH selected = w2n tc + 2 /\ REVERSE selected = off :: len :: topics /\
  w2n tc <= 4 /\ opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_static_wf p /\ bridge_core slo code_ok cs ss /\
  sym_kinds_ok cplan fn ret [] ps ss /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  venom_asm_rel lo qs vsout cs' /\ ps.ps_stack = residual ++ selected /\
  EVERY (\op. op <> dead_stack_marker) selected /\
  (!op. MEM op selected ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  qs = ps with ps_stack := stack_pop (LENGTH selected) ps.ps_stack /\
  asm_block_at p cs.as_pc [AsmOp ("LOG" ++ num_to_dec_string (w2n tc))] /\
  asm_step slo (build_offset_to_pc p)
    (AsmOp ("LOG" ++ num_to_dec_string (w2n tc))) cs = AsmOK cs' /\
  LIST_REL (\sv w. sval_conc slo sv = SOME w) stail wtail ==>
  ?full. sym_steps_mode allow_own p env own 1 (ss with sym_stack := ss.sym_stack ++ stail) =
      SymOK full /\
    bridge_core slo code_ok (cs' with as_stack := cs'.as_stack ++ wtail) full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret stail (release_dead_spills nl qs) full
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all sym_log_name_dispatch >> strip_tac >>
  `!cs ss. bridge_core slo code_ok cs ss ==>
    ss.sym_base.as_pc = cs.as_pc /\
    LIST_REL (\sv w. sval_conc slo sv = SOME w) ss.sym_stack cs.as_stack` by
    (rpt strip_tac >> gvs[]) >>
  `bridge_core slo code_ok cs ss` by (gvs[] >> metis_tac[]) >>
  drule_all (BETA_RULE (Q.INST [`R` |-> `bridge_core slo code_ok`]
    sym_log_source_emit_core)) >> strip_tac >>
  `asm_block_at p ss.sym_base.as_pc
    [AsmOp ("LOG" ++ num_to_dec_string (w2n tc))]` by gvs[] >>
  `asm_op_arity ("LOG" ++ num_to_dec_string (w2n tc)) <= LENGTH ss.sym_stack` by
    (drule_all prepared_suffix_concrete_height >>
     imp_res_tac listTheory.LIST_REL_LENGTH >> gvs[]) >>
  drule_at (Pat `sym_steps_mode _ _ _ _ _ _ = _`)
    sym_named_steps_ok_stack_suffix_mode >>
  disch_then (qspec_then `stail` assume_tac) >>
  qexists_tac `ss' with sym_stack := ss'.sym_stack ++ stail` >>
  simp[sym_kinds_ok_release_dead_spills, sym_kinds_ok_restore_stack] >>
  conj_tac >- (first_x_assum (qspec_then `"LOG" ++ num_to_dec_string (w2n tc)` mp_tac) >> gvs[]) >>
  conj_tac >- simp[listTheory.LIST_REL_APPEND_suff] >>
  conj_tac >- (qexists `m''` >> gvs[]) >>
  gvs[] >> metis_tac[]
QED

Theorem sym_log_prepared_run_mode_core:
  (!cs ss ai cs'. bridge_core slo code_ok cs ss /\ asm_block_at p cs.as_pc [ai] /\
    asm_step slo (build_offset_to_pc p) ai cs = AsmOK cs' /\
    (!msg. (if allow_own then sym_step_own p env own ai ss
            else sym_step p env ai ss) <> SymBad msg) ==>
    ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
      bridge_core slo code_ok cs' ss') /\
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: selected /\
  REVERSE selected = offop :: lenop :: topicops /\ w2n tc <= 4 /\
  step_inst fuel ctx inst (frame_view fn ra vs with vs_memory := m) = OK vsout /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_static_wf p /\ bridge_core slo code_ok cs ss /\
  sym_kinds_ok cplan fn ret [] ps ss /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = stack_pop (LENGTH selected) ps.ps_stack ++ selected /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) selected /\
  (!op. MEM op selected ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  EVERY (\(off,len). len = 0 \/ off + len <= qs.ps_alloc.sa_spill_base \/
    qs.ps_alloc.sa_next_offset <= off)
    (source_memory_read_ranges inst (frame_view fn ra vs with vs_memory := m)) /\
  qs = release_dead_spills nl
    (ps with ps_stack := stack_pop (LENGTH selected) ps.ps_stack) /\
  asm_block_at p cs.as_pc [AsmOp ("LOG" ++ num_to_dec_string (w2n tc))] /\
  LIST_REL (\sv w. sval_conc slo sv = SOME w) stail wtail ==>
  ?full. sym_steps_mode allow_own p env own 1 (ss with sym_stack := ss.sym_stack ++ stail) =
      SymOK full /\
    full.sym_mem_labels = ss.sym_mem_labels /\ sym_kinds_ok cplan fn ret stail qs full
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all step_inst_log_ok >> strip_tac >> gvs[] >>
  drule_at (Pat `venom_asm_rel _ _ _ _`) log_runtime_stack >>
  disch_then (qspecl_then [`rest`, `dfg`, `w2n tc`, `off`, `sz`, `topics`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_at (Pat `inst.inst_operands = _`) log_read_disjoint_emit >>
  disch_then (qspecl_then [`frame_view fn ra vs with vs_memory := m`,
    `off`, `sz`, `topics`,
    `release_dead_spills nl (ps with ps_stack := stack_pop (LENGTH rest) ps.ps_stack)`,
    `nl`, `ps`] mp_tac) >> simp[] >> disch_then assume_tac >>
  drule_at (Pat `venom_asm_rel _ _ _ _`) log_asm_rel >>
  disch_then (qspecl_then [`w2n tc`, `off`, `sz`, `topics`, `tail`] mp_tac) >>
  simp[] >> strip_tac >>
  `asm_step slo (build_offset_to_pc p)
    (AsmOp ("LOG" ++ num_to_dec_string (w2n tc))) cs = AsmOK st'` by
    simp[log_opcode_dispatch] >>
  `EVERY (\op. op <> dead_stack_marker) rest` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_at (Pat `asm_step _ _ _ _ = _`) sym_log_prepared_suffix_mode_core >>
  disch_then (drule_at (Pat `inst.inst_operands = _`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ [] _ _`)) >>
  disch_then (drule_at (Pat `venom_asm_rel _ _ _ cs`)) >>
  disch_then (drule_at (Pat `venom_asm_rel _ _ _ st'`)) >>
  disch_then (drule_at (Pat `LIST_REL _ stail wtail`)) >>
  disch_then (drule_at (Pat `REVERSE rest = _`)) >>
  disch_then (drule_at (Pat `ps.ps_stack = _`)) >>
  disch_then (drule_at (Pat `if _ then label_flow_own_ok _ else _`)) >>
  disch_then (qspecl_then [`own`, `nl`, `env`, `code_ok`] mp_tac) >> simp[] >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexists `m'` >> simp[]) >>
     rpt strip_tac >> first_x_assum drule >> simp[])) >>
  strip_tac >> qexists `full` >> simp[]
QED

Theorem reverse_two_operands:
  2 <= LENGTH (xs:operand list) ==> ?a b tail. REVERSE xs = a :: b :: tail
Proof
  Cases_on `REVERSE xs` >> gvs[] >>
  rename1 `REVERSE xs = h :: t` >> Cases_on `t` >>
  gvs[] >> metis_tac[listTheory.LENGTH_REVERSE, listTheory.LENGTH]
QED

Theorem successful_log_operand_shape:
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: selected /\
  step_inst fuel ctx inst vs = OK vsout ==>
  ?offop lenop topicops. REVERSE selected = offop :: lenop :: topicops
Proof
  strip_tac >> drule_all step_inst_log_ok >> strip_tac >> gvs[] >>
  irule reverse_two_operands >> simp[]
QED
