(* LOG execution after operand preparation.
   TOP-LEVEL: asm_log_venom_asm_rel.
   Helpers: stack and memory relations after appending a source event. *)
Theory logEmitSim
Ancestors
  preparedStackValues
  memoryReadRel codegenRel asmSem stackModel stackPlanTypes stackOpSim
  spillSim strongPrefixSim list rich_list arithmetic
  asmTargetSafety codegen symbolResolve ASCIInumbers alist
  venomExecSemantics venomState venomInst contextCodegenRel spillWordBounds
  stackPlanGen asmIR venomEffects

(* These are existing successful-codegen checks, not additional source
   restrictions.  In particular an emitted LOG has an EVM opcode. *)
Theorem assembly_target_safe_opcodes:
  assembly_target_safe caps prog ==>
  !name. MEM (AsmOp name) prog ==> IS_SOME (evm_opcode_byte name)
Proof
  simp[assembly_target_safe_def, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >>
  simp[asm_inst_target_safe_def, asm_opcode_target_supported_def]
QED

Theorem codegen_assembly_opcodes:
  codegen_assembly rpolicy unit = SOME prog ==>
  !name. MEM (AsmOp name) prog ==> IS_SOME (evm_opcode_byte name)
Proof
  rpt gen_tac >> strip_tac >>
  `assembly_target_safe rpolicy.rpol_target prog` by
    gvs[codegen_assembly_def, LET_THM, AllCaseEqs()] >>
  drule assembly_target_safe_opcodes >> simp_tac bool_ss []
QED

Theorem encodable_log_topic_count:
  IS_SOME (evm_opcode_byte ("LOG" ++ num_to_dec_string n)) ==> n <= 4
Proof
  Cases_on `evm_opcode_byte ("LOG" ++ num_to_dec_string n)` >> simp[] >>
  fs[evm_opcode_byte_def] >>
  imp_res_tac ALOOKUP_MEM >> gvs[evm_opcode_table_def] >>
  qpat_x_assum `num_to_dec_string n = _`
    (mp_tac o AP_TERM ``num_from_dec_string``) >>
  simp[toNum_toString,
    EVAL ``num_from_dec_string "0"``, EVAL ``num_from_dec_string "1"``,
    EVAL ``num_from_dec_string "2"``, EVAL ``num_from_dec_string "3"``,
    EVAL ``num_from_dec_string "4"``]
QED

Theorem asm_step_log:
  n <= 4 ==>
  asm_step lo o2pc (AsmOp ("LOG" ++ num_to_dec_string n)) st = asm_log n st
Proof
  strip_tac >> `n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4` by decide_tac >>
  gvs[] >>
  simp[asm_step_def, asm_step_op_def, asm_step_arith_def,
       asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
       asm_step_control_def, asm_step_extcall_def, asm_step_copy_def,
       asm_step_context_def, dup_table_def, swap_table_def, log_table_def,
       EVAL ``num_to_dec_string 0``, EVAL ``num_to_dec_string 1``,
       EVAL ``num_to_dec_string 2``, EVAL ``num_to_dec_string 3``,
       EVAL ``num_to_dec_string 4``]
QED

Theorem log_plan_decompose:
  !liveness dfg cfg func inst nl is_halting next_is_term bb ps
   tc operands input_ops mid reorder_ops prepared.
    inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: operands /\
    inst.inst_outputs = [] /\
    emit_input_plan LOG operands nl ps = (input_ops,mid) /\
    reorder_plan dfg operands mid = (reorder_ops,prepared) ==>
    generate_regular_inst_plan liveness dfg cfg func inst nl
      is_halting next_is_term bb ps =
    (input_ops ++ reorder_ops ++
       [SOEmit ("LOG" ++ num_to_dec_string (w2n tc))],
     release_dead_spills nl
       (prepared with ps_stack := stack_pop (LENGTH operands) prepared.ps_stack))
Proof
  rpt gen_tac >> strip_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       generate_emit_ops_def, venom_to_evm_name_def,
       is_commutative_def, LET_THM]
QED

Theorem step_inst_log:
  inst.inst_opcode = LOG /\
  inst.inst_operands = Lit tc :: REVERSE (off_op :: sz_op :: topic_ops) /\
  w2n tc = LENGTH topic_ops /\
  eval_operand off_op vs = SOME off /\
  eval_operand sz_op vs = SOME sz /\
  eval_operands topic_ops vs = SOME topics ==>
  step_inst fuel ctx inst vs = OK
    (vs with vs_logs := vs.vs_logs ++
      [<|logger := w2w vs.vs_call_ctx.cc_address;
         topics := topics;
         data := TAKE (w2n sz)
           (DROP (w2n off) vs.vs_memory ++ REPLICATE (w2n sz) 0w)|>])
Proof
  rpt strip_tac >>
  simp[step_inst_non_invoke] >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  qpat_assum `inst.inst_opcode = LOG`
    (fn th => PURE_REWRITE_TAC[th]) >>
  simp[LET_THM, ADD_COMM, REVERSE_APPEND]
QED

Theorem source_memory_read_ranges_log:
  inst.inst_opcode = LOG /\
  inst.inst_operands = Lit tc :: REVERSE (off_op :: sz_op :: topic_ops) /\
  w2n tc = LENGTH topic_ops /\
  eval_operand off_op vs = SOME off /\
  eval_operand sz_op vs = SOME sz /\
  eval_operands topic_ops vs = SOME topics ==>
  source_memory_read_ranges inst vs = [(w2n off,w2n sz)]
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[source_memory_read_ranges_def] >>
  qpat_assum `inst.inst_opcode = LOG`
    (fn th => PURE_REWRITE_TAC[th]) >>
  simp[memory_range_of_operands_def, LET_THM, ADD_COMM, REVERSE_APPEND]
QED

Theorem operand_val_logs[simp]:
  operand_val (vs with vs_logs := logs) lo op = operand_val vs lo op
Proof
  Cases_on `op` >> simp[operand_val_def]
QED

Theorem eval_operands_length:
  !ops vs vals. eval_operands ops vs = SOME vals ==>
    LENGTH vals = LENGTH ops
Proof
  Induct >> simp[eval_operands_def, AllCaseEqs()] >>
  rpt strip_tac >> res_tac >> gvs[]
QED

Theorem plan_stack_rel_logs[simp]:
  plan_stack_rel lo (vs with vs_logs := logs) ps stk =
  plan_stack_rel lo vs ps stk
Proof
  simp[plan_stack_rel_def]
QED

Theorem plan_spill_rel_logs[simp]:
  plan_spill_rel lo (vs with vs_logs := logs) spilled mem =
  plan_spill_rel lo vs spilled mem
Proof
  simp[plan_spill_rel_def]
QED

Theorem log_memory_relations:
  memory_rel alloc vm am /\ plan_spill_rel lo vs spilled am ==>
  memory_rel alloc vm
    (if sz = 0 then am else asm_expand_memory (off + sz) am) /\
  plan_spill_rel lo vs spilled
    (if sz = 0 then am else asm_expand_memory (off + sz) am)
Proof
  rpt strip_tac >> Cases_on `sz = 0` >>
  simp[memory_rel_expand, plan_spill_rel_expand]
QED

Theorem log_data_agree:
  memory_rel alloc vm am /\
  (!i. off <= i /\ i < off + sz ==>
       ~(alloc.sa_spill_base <= i /\ i < alloc.sa_next_offset)) ==>
  TAKE sz (DROP off vm ++ REPLICATE sz (0w:byte)) =
  TAKE sz (DROP off
    (if sz = 0 then am else asm_expand_memory (off + sz) am))
Proof
  rpt strip_tac >> Cases_on `sz = 0` >> simp[] >>
  irule memory_rel_read_range >> qexists_tac `alloc` >>
  asm_rewrite_tac []
QED

Theorem asm_log_venom_asm_rel:
  !lo ps vs st off sz topics rest.
    venom_asm_rel lo ps vs st /\
    st.as_stack = off :: sz :: (topics ++ rest) /\
    (!i. w2n off <= i /\ i < w2n off + w2n sz ==>
         ~(ps.ps_alloc.sa_spill_base <= i /\
           i < ps.ps_alloc.sa_next_offset)) ==>
    ?st'. asm_log (LENGTH topics) st = AsmOK st' /\
      venom_asm_rel lo
        (ps with ps_stack := stack_pop (LENGTH topics + 2) ps.ps_stack)
        (vs with vs_logs := vs.vs_logs ++
          [<|logger := w2w vs.vs_call_ctx.cc_address;
             topics := topics;
             data := TAKE (w2n sz)
               (DROP (w2n off) vs.vs_memory ++
                REPLICATE (w2n sz) (0w:byte))|>]) st' /\
      st'.as_pc = st.as_pc + 1
Proof
  rpt gen_tac >> strip_tac >>
  `plan_stack_rel lo vs
     (stack_pop (LENGTH topics + 2) ps.ps_stack) rest` by
    (fs[venom_asm_rel_def] >>
     mp_tac (Q.ISPECL [`lo:(string,num) fmap`,`vs:venom_state`,
       `(ps:plan_state).ps_stack`,`(st:asm_state).as_stack`,
       `LENGTH (topics:bytes32 list) + 2`] plan_stack_rel_pop) >>
     impl_tac >- (fs[plan_stack_rel_def] >> decide_tac) >>
     simp[stack_pop_def, DROP_APPEND]) >>
  `TAKE (w2n sz) (DROP (w2n off) vs.vs_memory ++
       REPLICATE (w2n sz) (0w:byte)) =
   TAKE (w2n sz) (DROP (w2n off)
     (if w2n sz = 0 then st.as_memory else
        asm_expand_memory (w2n off + w2n sz) st.as_memory))` by
    (irule log_data_agree >> qexists_tac `ps.ps_alloc` >>
     fs[venom_asm_rel_def]) >>
  `memory_rel ps.ps_alloc vs.vs_memory
      (if w2n sz = 0 then st.as_memory else
        asm_expand_memory (w2n off + w2n sz) st.as_memory) /\
   plan_spill_rel lo vs ps.ps_spilled
      (if w2n sz = 0 then st.as_memory else
        asm_expand_memory (w2n off + w2n sz) st.as_memory)` by
    (irule log_memory_relations >> fs[venom_asm_rel_def]) >>
  simp[asm_log_def, LET_THM, DROP_APPEND] >>
  fs[venom_asm_rel_def] >>
  simp[asm_next_def, venom_asm_rel_def, TAKE_APPEND]
QED

(* The emitted instruction is checked against the actual program.  The
   context's existing read-footprint condition supplies the memory premise. *)
Theorem log_instruction_emit_sim:
  !inst tc off_op sz_op topic_ops off sz topics rest
   fuel ctx lo o2pc prog ps vs vs' st.
    inst.inst_opcode = LOG /\
    inst.inst_operands = Lit tc :: REVERSE (off_op :: sz_op :: topic_ops) /\
    w2n tc = LENGTH topic_ops /\
    eval_operand off_op vs = SOME off /\
    eval_operand sz_op vs = SOME sz /\
    eval_operands topic_ops vs = SOME topics /\
    venom_asm_rel lo ps vs st /\
    st.as_stack = off :: sz :: (topics ++ rest) /\
    (!i. source_memory_read_byte inst vs i ==>
         ~(ps.ps_alloc.sa_spill_base <= i /\ i < ps.ps_alloc.sa_next_offset)) /\
    (!name. MEM (AsmOp name) prog ==> IS_SOME (evm_opcode_byte name)) /\
    asm_block_at prog st.as_pc [AsmOp ("LOG" ++ num_to_dec_string (w2n tc))] /\
    step_inst fuel ctx inst vs = OK vs' ==>
    ?st'. asm_steps lo o2pc prog 1 st = AsmOK st' /\
      venom_asm_rel lo
        (ps with ps_stack := stack_pop (LENGTH topic_ops + 2) ps.ps_stack)
        vs' st' /\ st'.as_pc = st.as_pc + 1
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH topics = LENGTH topic_ops` by
    (drule eval_operands_length >> simp[]) >>
  `source_memory_read_ranges inst vs = [(w2n off,w2n sz)]` by
    (drule_all source_memory_read_ranges_log >> simp[]) >>
  `!i. w2n off <= i /\ i < w2n off + w2n sz ==>
       ~(ps.ps_alloc.sa_spill_base <= i /\ i < ps.ps_alloc.sa_next_offset)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. source_memory_read_byte inst vs i ==> _`
       (qspec_then `i` mp_tac) >>
     asm_simp_tac (srw_ss())
       [source_memory_read_byte_def, byte_in_memory_range_def]) >>
  `IS_SOME (evm_opcode_byte ("LOG" ++ num_to_dec_string (w2n tc)))` by
    (first_x_assum irule >> irule asm_block_at_member >>
     qexistsl_tac [`[AsmOp ("LOG" ++ num_to_dec_string (w2n tc))]`,
       `st.as_pc`] >> asm_simp_tac (srw_ss()) []) >>
  `w2n tc <= 4` by (drule encodable_log_topic_count >> simp[]) >>
  `vs' = vs with vs_logs := vs.vs_logs ++
      [<|logger := w2w vs.vs_call_ctx.cc_address;
         topics := topics;
         data := TAKE (w2n sz)
           (DROP (w2n off) vs.vs_memory ++ REPLICATE (w2n sz) 0w)|>]` by
    (drule_all step_inst_log >>
     disch_then (qspecl_then [`fuel`,`ctx`] mp_tac) >>
     asm_simp_tac (srw_ss()) []) >>
  mp_tac (Q.ISPECL [`lo:(string,num) fmap`,`ps:plan_state`,
    `vs:venom_state`,`st:asm_state`,`off:bytes32`,`sz:bytes32`,
    `topics:bytes32 list`,`rest:bytes32 list`] asm_log_venom_asm_rel) >>
  (impl_tac >- asm_rewrite_tac []) >>
  disch_then (qx_choose_then `st'` strip_assume_tac) >>
  qexists_tac `st'` >> gvs[] >>
  rewrite_tac [DECIDE ``1 = SUC 0``] >> simp[asm_steps_def] >>
  fs[asm_block_at_def] >>
  simp[SIMP_RULE (srw_ss()) [] asm_step_log]
QED

Theorem log_instruction_prepared_sim:
  !inst tc operands off_op sz_op topic_ops off sz topics
   fuel ctx lo o2pc prog ps vs vs' st.
    inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: operands /\
    operands = REVERSE (off_op :: sz_op :: topic_ops) /\
    w2n tc = LENGTH topic_ops /\
    eval_operand off_op vs = SOME off /\
    eval_operand sz_op vs = SOME sz /\
    eval_operands topic_ops vs = SOME topics /\
    EVERY (\op. op <> dead_stack_marker) operands /\
    (!op. MEM op operands ==> eval_operand op vs = operand_val vs lo op) /\
    venom_asm_rel lo ps vs st /\
    ps.ps_stack = stack_pop (LENGTH operands) ps.ps_stack ++ operands /\
    (!i. source_memory_read_byte inst vs i ==>
      ~(ps.ps_alloc.sa_spill_base <= i /\ i < ps.ps_alloc.sa_next_offset)) /\
    (!name. MEM (AsmOp name) prog ==> IS_SOME (evm_opcode_byte name)) /\
    asm_block_at prog st.as_pc [AsmOp ("LOG" ++ num_to_dec_string (w2n tc))] /\
    step_inst fuel ctx inst vs = OK vs' ==>
    ?st'. asm_steps lo o2pc prog 1 st = AsmOK st' /\
      venom_asm_rel lo
        (ps with ps_stack := stack_pop (LENGTH topic_ops + 2) ps.ps_stack)
        vs' st' /\ st'.as_pc = st.as_pc + 1
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operands (REVERSE operands) vs = SOME (off::sz::topics)` by
    (qpat_assum `operands = _` (fn shape =>
       rewrite_tac [shape, REVERSE_REVERSE, eval_operands_def]) >>
     asm_simp_tac (srw_ss()) []) >>
  mp_tac (Q.SPECL [`lo`,`ps`,`vs`,`st`,`operands`,
    `(off:bytes32)::sz::topics`] prepared_operands_values) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `rest` strip_assume_tac) >>
  qpat_x_assum `ps.ps_stack = _` kall_tac >>
  mp_tac (Q.SPECL [`inst`,`tc`,`off_op`,`sz_op`,`topic_ops`,`off`,`sz`,
    `topics`,`rest`,`fuel`,`ctx`,`lo`,`o2pc`,`prog`,`ps`,`vs`,`vs'`,`st`]
    log_instruction_emit_sim) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [] >>
    qpat_assum `!i. source_memory_read_byte inst vs i ==> _`
      (ACCEPT_TAC o REWRITE_RULE [DE_MORGAN_THM]))) >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed LOG execution proof: " ^ name)
  end) (DB.thms "logEmitSim")
