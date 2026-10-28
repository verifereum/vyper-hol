(* TOP-LEVEL: an actual native child result supplies the exact register
   contract consumed by the real array head/tail update and latch. Saved
   loop registers precede the child's fresh SSA interval. *)
Theory abiNativeDynamicArrayCallReturn
Ancestors
  abiNativeDynamicArrayPrefixState abiNativeEncodingDefs abiMemoryLeafRun abiDynamicLoopIteration abiDynamicLoopStep
  abiDynamicLoopCode abiStaticLoopCode abiFieldOperands abiStateFrame compileEnv venomMemDefs venomState list words arithmetic

Theorem abi_native_dynamic_array_call_return:
  !ctx func cs dst src width stride len_op dst_addr root_addr counter_addr dyn_addr length_word ss index child_len mid payload out.
    abi_native_encoding_result ctx func (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid child_len
      (dst_addr + 32w + mload (w2n dyn_addr) ss) payload
      (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
        counter_addr dyn_addr length_word ss) out /\
    ~ss.vs_halted /\ mload (w2n counter_addr) ss = n2w index /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) ss = SOME counter_addr /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 1)) ss = SOME dyn_addr ==>
    abi_dynamic_loop_child_return cs.cs_next_var mid child_len dst_addr width counter_addr dyn_addr
      (n2w index) (mload (w2n dyn_addr) ss) (n2w (LENGTH payload)) out
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_native_encoding_result _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_encoding_result_def, abi_encoding_result_def]) >>
  qspecl_then [`cs.cs_next_var`, `cs.cs_next_label`, `dst_addr`, `root_addr`, `width`, `stride`, `counter_addr`, `dyn_addr`,
    `length_word`, `ss`] mp_tac abi_dynamic_loop_child_state_values >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  `!offset. offset < 15 ==>
    eval_operand (Var (compiler_var_name cs.cs_next_var offset)) out =
      eval_operand (Var (compiler_var_name cs.cs_next_var offset))
        (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
          counter_addr dyn_addr length_word ss)` by
    (rpt gen_tac >> DISCH_TAC >> first_x_assum irule >>
     simp_tac (srw_ss()) [abi_dynamic_loop_prefix_cut_def, abi_operand_before_def, compiler_var_name_def] >>
     rpt strip_tac >> decide_tac) >>
  qpat_assum `!offset. offset < 15 ==> _` (fn th =>
    MAP_EVERY (fn arg => ASSUME_TAC (SIMP_RULE (srw_ss()) [] (Q.SPEC arg th))) [`0`, `1`, `6`, `12`, `13`]) >>
  `!offset. offset < 3 ==>
    eval_operand (Var (compiler_var_name cs.cs_next_var offset))
      (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
        counter_addr dyn_addr length_word ss) = eval_operand (Var (compiler_var_name cs.cs_next_var offset)) ss` by
    (rpt gen_tac >> DISCH_TAC >> irule abi_native_dynamic_array_prefix_old_operand >>
     simp_tac (srw_ss()) [abi_operand_before_def, compiler_var_name_def] >> rpt strip_tac >> decide_tac) >>
  qpat_assum `!offset. offset < 3 ==> _` (fn th =>
    MAP_EVERY (fn arg => ASSUME_TAC (SIMP_RULE (srw_ss()) [] (Q.SPEC arg th))) [`0`, `1`]) >>
  `~out.vs_halted` by (drule_all abi_state_frame_observables >> asm_simp_tac bool_ss []) >>
  asm_simp_tac (srw_ss()) [abi_dynamic_loop_child_return_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual recursive array child return registers: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayCallReturn")
