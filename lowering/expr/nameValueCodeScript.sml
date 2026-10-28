(* TOP-LEVEL: actual memory name loads preserve typed values and older
   operands, including when generated SSA outputs already have bindings.
   Helpers expose the one-MLOAD or identity compiler program. *)
Theory nameValueCode
Ancestors
  nameLoweringProps valueLoadProps memoryValueDefs valueEncoding valueEncodingProps
  exprLoweringProps context compileEnv emitHelper emitHelperProps
  abiFieldOperands abiStaticLoopCode ssaOperandFrame
  venomState venomExecSemantics venomInst list words arithmetic

Theorem generated_update_before_operand:
  !var_base arg_op value ss.
    abi_operand_before var_base arg_op ==>
    eval_operand arg_op (update_var (STRING #"%" (toString var_base)) value ss) = eval_operand arg_op ss
Proof
  rpt gen_tac >> DISCH_TAC >> irule eval_operand_update_var_avoids >>
  qpat_x_assum `abi_operand_before _ _` (mp_tac o REWRITE_RULE [abi_operand_before_def]) >>
  disch_then (qspec_then `var_base` mp_tac) >> simp[compiler_var_name_def]
QED

Theorem typed_memory_load_word:
  !tenv ann tv v ptr_addr ss.
    evaluate_type tenv ann = SOME tv /\ is_word_type ann /\ value_has_type tv v /\
    memory_value_rel tv v (w2n ptr_addr) ss.vs_memory ==>
    mload (w2n ptr_addr) ss = typed_val_to_w256 tv v
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[GSYM mem_word_at_eq_mload] >>
  drule_all memory_value_rel_word >> simp[]
QED

Theorem unwrap_memory_value_code:
  !cenv ann ptr_op cs op cs'.
    unwrap_value cenv (LocatedValue ann (mk_ptr ptr_op LocMemory)) cs = (op,cs') ==>
    same_blocks cs cs' /\ cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs' /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts cs cs') /\
    cs'.cs_next_var = cs.cs_next_var + (if is_word_type ann then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_word_type ann`
  >- (fs[unwrap_memory_value_eq] >> drule emitted_insts_emit_op >> strip_tac >>
      drule emit_op_extends >> simp[mk_inst_def, is_terminator_def]) >>
  gvs[unwrap_memory_value_eq] >> simp[emitted_insts_def, same_blocks_def]
QED

Theorem emit_typed_memory_load_execution:
  !tenv ann tv v ptr_op cs op cs' ss ptr_addr.
    evaluate_type tenv ann = SOME tv /\ is_word_type ann /\ value_has_type tv v /\
    memory_value_rel tv v (w2n ptr_addr) ss.vs_memory /\ eval_operand ptr_op ss = SOME ptr_addr /\
    emit_op MLOAD [ptr_op] cs = (op,cs') ==>
    ?out. run_inst_seq (emitted_insts cs cs') ss = OK out /\ lowered_value_rel ann tv v op out /\
      out with vs_vars := ss.vs_vars = ss /\ out.vs_memory = ss.vs_memory /\
      (fresh_vars_wrt cs ss ==> fresh_vars_wrt cs' out) /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      abi_operand_before cs'.cs_next_var op /\ cs.cs_next_var <= cs'.cs_next_var
Proof
  rpt gen_tac >> strip_tac >> drule_all typed_memory_load_word >> DISCH_TAC >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `out = update_var (STRING #"%" (toString cs.cs_next_var)) (typed_val_to_w256 tv v) ss` >>
  `fresh_vars_wrt cs ss ==> fresh_vars_wrt cs' out` by
    (DISCH_TAC >> mp_tac (Q.SPECL [`cs`, `cs'`, `ss`,
       `STRING #"%" (toString cs.cs_next_var)`, `cs.cs_next_var`, `typed_val_to_w256 tv v`]
       fresh_vars_wrt_advance) >> impl_tac >- simp[] >> simp[Abbr`out`]) >>
  `abi_operand_before cs'.cs_next_var op` by
    (mp_tac (Q.SPECL [`cs.cs_next_var`, `cs'.cs_next_var`] abi_operand_before_reserved) >>
     simp[compiler_var_name_def]) >>
  `!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss` by
    simp[Abbr`out`, generated_update_before_operand] >>
  `step_inst_base (mk_inst cs.cs_next_id MLOAD [ptr_op]
    [STRING #"%" (toString cs.cs_next_var)]) ss = OK out` by
    (mp_tac (Q.SPECL [`ptr_op`, `STRING #"%" (toString cs.cs_next_var)`,
       `cs.cs_next_id`, `ss`, `ptr_addr`] step_MLOAD_local) >> simp[Abbr`out`]) >>
  `run_inst_seq (emitted_insts cs cs') ss = OK out` by simp[run_inst_seq_def] >>
  `lowered_value_rel ann tv v op out` by
    simp[Abbr`out`, lowered_value_rel_def, eval_operand_update_var] >>
  `out with vs_vars := ss.vs_vars = ss /\ out.vs_memory = ss.vs_memory` by
    simp[Abbr`out`, update_var_def] >>
  qexists_tac `out` >> simp[]
QED

Theorem unwrap_memory_value_execution:
  !tenv cenv ann tv v ptr_op cs op cs' ss ptr_addr.
    evaluate_type tenv ann = SOME tv /\ value_has_type tv v /\
    memory_value_rel tv v (w2n ptr_addr) ss.vs_memory /\ eval_operand ptr_op ss = SOME ptr_addr /\
    abi_operand_before cs.cs_next_var ptr_op /\
    unwrap_value cenv (LocatedValue ann (mk_ptr ptr_op LocMemory)) cs = (op,cs') ==>
    ?out. run_inst_seq (emitted_insts cs cs') ss = OK out /\ lowered_value_rel ann tv v op out /\
      out with vs_vars := ss.vs_vars = ss /\ out.vs_memory = ss.vs_memory /\
      (fresh_vars_wrt cs ss ==> fresh_vars_wrt cs' out) /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      abi_operand_before cs'.cs_next_var op /\ cs.cs_next_var <= cs'.cs_next_var
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_word_type ann`
  >- (fs[unwrap_memory_value_eq] >> drule_all emit_typed_memory_load_execution >> simp[]) >>
  gvs[unwrap_memory_value_eq] >> qexists_tac `ss` >>
  simp[run_inst_seq_def, emitted_insts_def, lowered_value_rel_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed typed memory name code: " ^ name)
  end) (DB.thms "nameValueCode")
