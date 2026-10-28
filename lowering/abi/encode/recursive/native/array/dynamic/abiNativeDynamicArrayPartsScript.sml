(* TOP-LEVEL: the real loop compilation supplies both child code intervals
   and its continuation bounds. No code-containment contract is assumed
   separately from the actual compiler equation and enclosing function. *)
Theory abiNativeDynamicArrayParts
Ancestors
  abiDynamicLoopFactor abiDynamicLoopStructure abiDynamicLoopCode abiChildCode abiChildStructure abiStaticLoopCode
  compileEnv fragExec venomState list words arithmetic

Theorem abi_native_dynamic_array_parts:
  !dst src info width stride len_op cs ret after child_len mid func.
    compile_abi_encode_dyn_loop dst src info width stride len_op cs = (ret,after) /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14)) (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) = (child_len,mid) /\ fn_has_code cs after func ==>
    fn_has_code cs (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) func /\
    fn_has_code (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid func /\
    cs_extends mid after /\ cs.cs_next_var + 15 <= mid.cs_next_var
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_dynamic_loop_child_next_var >> DISCH_TAC >>
  `after = abi_dynamic_loop_exit_cut src (Var (compiler_var_name cs.cs_next_var 1))
    (fresh_label_output "enc_dyn_exit" (cs.cs_next_label + 2))
    (abi_dynamic_loop_latch_cut (Var (compiler_var_name cs.cs_next_var 0))
      (Var (compiler_var_name cs.cs_next_var 6)) (fresh_label_output "enc_dyn_hdr" cs.cs_next_label)
      (abi_child_suffix_cut (Var (compiler_var_name cs.cs_next_var 12))
        (Var (compiler_var_name cs.cs_next_var 13)) (Var (compiler_var_name cs.cs_next_var 1)) child_len mid))` by
    fs[compile_abi_dynamic_loop_factor, LET_THM] >>
  qpat_assum `after = _` (fn th => qpat_assum `fn_has_code cs after func` (ASSUME_TAC o PURE_REWRITE_RULE [th])) >>
  drule_all abi_dynamic_loop_contains_parts >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `stored = abi_child_suffix_cut (Var (compiler_var_name cs.cs_next_var 12))
    (Var (compiler_var_name cs.cs_next_var 13)) (Var (compiler_var_name cs.cs_next_var 1)) child_len mid` >>
  qabbrev_tac `latched = abi_dynamic_loop_latch_cut (Var (compiler_var_name cs.cs_next_var 0))
    (Var (compiler_var_name cs.cs_next_var 6)) (fresh_label_output "enc_dyn_hdr" cs.cs_next_label) stored` >>
  `cs_extends mid stored` by simp[Abbr`stored`, abi_child_suffix_extends] >>
  `cs_extends stored latched` by simp[Abbr`latched`, abi_dynamic_loop_cuts_extend] >>
  `cs_extends latched after` by simp[Abbr`latched`, Abbr`stored`, abi_dynamic_loop_cuts_extend] >>
  rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    irule cs_extends_trans >> qexists_tac `stored` >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
    irule cs_extends_trans >> qexists_tac `latched` >> asm_simp_tac bool_ss []]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic array compiler intervals and flow: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayParts")
