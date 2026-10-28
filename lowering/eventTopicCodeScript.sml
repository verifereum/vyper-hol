(* TOP-LEVEL: compile_topics_code certifies straight topic code, old operands
   and the final variable frontier. Helpers: compile_topic_code and
   run_inst_seq_operand_frame. *)
Theory eventTopicCode
Ancestors
  eventTopicsExecProps abiFieldOperands abiBytestringCode abiStaticLoopCode
  context stmtLowering compileEnv exprLoweringProps emitHelper emitHelperProps
  venomInstProofs1 venomExecSemantics venomState venomInst list rich_list words arithmetic
Libs pairLib

Theorem run_inst_seq_operand_frame:
  !insts before after arg_op.
    run_inst_seq insts before = OK after /\
    EVERY (\inst. ~is_terminator inst.inst_opcode /\
      EVERY (\name. arg_op <> Var name) inst.inst_outputs) insts ==>
    eval_operand arg_op after = eval_operand arg_op before
Proof
  rpt gen_tac >> strip_tac >>
  irule (SRULE [] (Q.ISPEC `\ss. eval_operand arg_op ss` run_inst_seq_preserves_field)) >>
  qexists_tac `insts` >> reverse conj_tac >- first_assum MATCH_ACCEPT_TAC >> rpt gen_tac >> strip_tac >>
    rename1 `step_inst_base inst ss1 = OK ss2` >>
    `~is_terminator inst.inst_opcode /\ EVERY (\name. arg_op <> Var name) inst.inst_outputs` by
      (qpat_x_assum `EVERY _ insts` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
       disch_then (qspec_then `inst` mp_tac) >> simp[EVERY_MEM]) >>
    drule_all step_inst_base_preserves_all >> strip_tac >>
    Cases_on `arg_op` >> fs[eval_operand_def] >>
    rename1 `lookup_var name ss2 = lookup_var name ss1` >>
    qpat_x_assum `!v. _ ==> lookup_var v ss2 = _` irule >>
    qpat_x_assum `EVERY _ inst.inst_outputs` mp_tac >> simp_tac (srw_ss()) [EVERY_MEM] >>
    disch_then (qspec_then `name` mp_tac) >> simp[]
QED

Theorem compile_topic_code:
  !ptr is_bytes cs op cs'.
    compile_encode_log_topic ptr is_bytes cs = (op,cs') ==>
    same_blocks cs cs' /\ cs.cs_next_var <= cs'.cs_next_var /\
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs' /\
    EVERY (\inst. inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode) (emitted_insts cs cs') /\
    (abi_operand_before cs.cs_next_var ptr ==> abi_operand_before cs'.cs_next_var op) /\
    (!old. abi_operand_before cs.cs_next_var old ==>
      EVERY (\inst. EVERY (\name. old <> Var name) inst.inst_outputs) (emitted_insts cs cs'))
Proof
  rpt gen_tac >> Cases_on `is_bytes` >>
  simp[compile_encode_log_topic_def, comp_return_def] >> strip_tac
  >- (gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, fresh_id_def, fresh_var_def, emit_def,
       emitted_insts_def, same_blocks_def, DROP_APPEND1, DROP_LENGTH_NIL, mk_inst_def, is_terminator_def] >>
      conj_tac
      >- (DISCH_TAC >> mp_tac (Q.SPECL [`cs.cs_next_var + 2`, `cs.cs_next_var + 3`] abi_operand_before_reserved) >>
          simp[compiler_var_name_def]) >>
      qx_gen_tac `old` >> DISCH_TAC >>
      mp_tac (Q.SPECL [`cs.cs_next_var`, `old`, `cs.cs_next_var`, `3`] abi_operand_before_names) >>
      impl_tac >- simp[] >> simp[compiler_var_names_def, GENLIST]) >>
  gvs[emitted_insts_def, same_blocks_def]
QED

Theorem compile_topics_code:
  !args cs ops cs'.
    compile_log_topic_ops args cs = (ops,cs') /\
    EVERY (\arg. abi_operand_before cs.cs_next_var (FST arg)) args ==>
    same_blocks cs cs' /\ cs.cs_next_var <= cs'.cs_next_var /\
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs' /\
    EVERY (\inst. inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode) (emitted_insts cs cs') /\
    EVERY (abi_operand_before cs'.cs_next_var) ops /\
    (!old. abi_operand_before cs.cs_next_var old ==>
      EVERY (\inst. EVERY (\name. old <> Var name) inst.inst_outputs) (emitted_insts cs cs'))
Proof
  Induct_on `args`
  >- (rpt gen_tac >> simp[compile_log_topic_ops_def, comp_return_def] >> strip_tac >>
      gvs[emitted_insts_def, same_blocks_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_log_topic_ops _ cs = (ops,cs')` mp_tac >>
  simp_tac (srw_ss()) [Once compile_log_topic_ops_def, comp_bind_def, comp_return_def, LET_THM] >>
  strip_tac >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_encode_log_topic _ _ cs = (head_op,mid)` >>
  rename1 `compile_log_topic_ops args mid = (tail_ops,cs')` >>
  drule compile_topic_code >> strip_tac >>
  `EVERY (\arg. abi_operand_before mid.cs_next_var (FST arg)) args` by
    (simp_tac bool_ss [EVERY_MEM] >> rpt strip_tac >>
     irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> fs[EVERY_MEM]) >>
  qpat_x_assum `!cs ops cs'. _` (qspecl_then [`mid`, `tail_ops`, `cs'`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  drule_all emitted_insts_append >> DISCH_TAC >>
  `same_blocks cs cs'` by (irule same_blocks_trans >> qexists_tac `mid` >> simp[]) >>
  `cs.cs_next_var <= cs'.cs_next_var` by decide_tac >>
  `abi_operand_before cs'.cs_next_var head_op` by
    (irule abi_operand_before_mono >> qexists_tac `mid.cs_next_var` >> fs[]) >>
  `cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs'` by
    asm_simp_tac bool_ss [APPEND_ASSOC] >>
  asm_simp_tac bool_ss [EVERY_DEF, EVERY_APPEND] >>
  qx_gen_tac `old` >> DISCH_TAC >>
  `abi_operand_before mid.cs_next_var old` by
    (irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> simp[]) >>
  asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed indexed-topic code and operand frames: " ^ name)
  end) (DB.thms "eventTopicCode")
