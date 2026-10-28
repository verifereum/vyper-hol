(* TOP-LEVEL: containing code exposes every dynamic-loop phase, even when
   the recursive child introduces blocks between the body prefix and latch. *)
Theory abiDynamicLoopStructure
Ancestors
  abiDynamicLoopCode abiDynamicLoopFactor abiChildCode abiChildStructure abiEncoderStructure abiStaticLoopCode
  compileEnv fragExec venomExecSemantics venomInst list rich_list arithmetic

Theorem abi_dynamic_loop_cuts_extend:
  (!dst src abi_sz mem_sz len_op cs.
    cs_extends cs (abi_dynamic_loop_prefix_cut dst src abi_sz mem_sz len_op cs)) /\
  (!i_ptr i_op header_label cs. cs_extends cs (abi_dynamic_loop_latch_cut i_ptr i_op header_label cs)) /\
  (!src dyn_ptr exit_label cs. cs_extends cs (abi_dynamic_loop_exit_cut src dyn_ptr exit_label cs))
Proof
  rpt conj_tac >> rpt gen_tac
  >- (simp[cs_extends_def, abi_dynamic_loop_prefix_cut_def] >>
      qexists_tac
        `[<|bb_label := fresh_label_output "enc_dyn_hdr" cs.cs_next_label;
            bb_instructions := abi_dynamic_loop_header cs.cs_next_id cs.cs_next_var cs.cs_next_label len_op|>;
          <|bb_label := cs.cs_current_bb; bb_instructions := cs.cs_current_insts ++
            abi_dynamic_loop_entry cs.cs_next_id cs.cs_next_var cs.cs_next_label abi_sz len_op|>]` >>
      simp[IS_PREFIX_APPEND])
  >- (irule cs_extends_same_block >> simp[abi_dynamic_loop_latch_cut_def, IS_PREFIX_APPEND]) >>
  simp[cs_extends_def, abi_dynamic_loop_exit_cut_def] >>
  qexists_tac `[<|bb_label := cs.cs_current_bb; bb_instructions := cs.cs_current_insts|>]` >> simp[]
QED

Theorem abi_dynamic_loop_contains_parts:
  !dst src info abi_sz mem_sz len_op cs child_len mid func.
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14))
      (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src abi_sz mem_sz len_op cs) = (child_len,mid) /\
    fn_has_code cs
      (abi_dynamic_loop_exit_cut src (Var (compiler_var_name cs.cs_next_var 1))
        (fresh_label_output "enc_dyn_exit" (cs.cs_next_label + 2))
        (abi_dynamic_loop_latch_cut (Var (compiler_var_name cs.cs_next_var 0))
          (Var (compiler_var_name cs.cs_next_var 6)) (fresh_label_output "enc_dyn_hdr" cs.cs_next_label)
          (abi_child_suffix_cut (Var (compiler_var_name cs.cs_next_var 12))
            (Var (compiler_var_name cs.cs_next_var 13)) (Var (compiler_var_name cs.cs_next_var 1)) child_len mid))) func ==>
    let prefix = abi_dynamic_loop_prefix_cut dst src abi_sz mem_sz len_op cs in
    let stored = abi_child_suffix_cut (Var (compiler_var_name cs.cs_next_var 12))
      (Var (compiler_var_name cs.cs_next_var 13)) (Var (compiler_var_name cs.cs_next_var 1)) child_len mid in
    let latched = abi_dynamic_loop_latch_cut (Var (compiler_var_name cs.cs_next_var 0))
      (Var (compiler_var_name cs.cs_next_var 6)) (fresh_label_output "enc_dyn_hdr" cs.cs_next_label) stored in
    let finished = abi_dynamic_loop_exit_cut src (Var (compiler_var_name cs.cs_next_var 1))
      (fresh_label_output "enc_dyn_exit" (cs.cs_next_label + 2)) latched in
    fn_has_code cs prefix func /\ fn_has_code prefix mid func /\ fn_has_code mid stored func /\
    fn_has_code stored latched func /\ fn_has_code latched finished func
Proof
  rpt gen_tac >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `prefix = abi_dynamic_loop_prefix_cut dst src abi_sz mem_sz len_op cs` >>
  qabbrev_tac `stored = abi_child_suffix_cut (Var (compiler_var_name cs.cs_next_var 12))
    (Var (compiler_var_name cs.cs_next_var 13)) (Var (compiler_var_name cs.cs_next_var 1)) child_len mid` >>
  qabbrev_tac `latched = abi_dynamic_loop_latch_cut (Var (compiler_var_name cs.cs_next_var 0))
    (Var (compiler_var_name cs.cs_next_var 6)) (fresh_label_output "enc_dyn_hdr" cs.cs_next_label) stored` >>
  qabbrev_tac `finished = abi_dynamic_loop_exit_cut src (Var (compiler_var_name cs.cs_next_var 1))
    (fresh_label_output "enc_dyn_exit" (cs.cs_next_label + 2)) latched` >>
  `cs_extends cs prefix` by simp[Abbr`prefix`, abi_dynamic_loop_cuts_extend] >>
  `cs_extends prefix mid` by (drule_all compile_abi_encode_extends >> simp[]) >>
  `cs_extends mid stored` by simp[Abbr`stored`, abi_child_suffix_extends] >>
  `cs_extends stored latched` by simp[Abbr`latched`, abi_dynamic_loop_cuts_extend] >>
  `cs_extends latched finished` by simp[Abbr`finished`, abi_dynamic_loop_cuts_extend] >>
  `cs_extends cs mid` by (irule cs_extends_trans >> qexists_tac `prefix` >> simp[]) >>
  `cs_extends stored finished` by (irule cs_extends_trans >> qexists_tac `latched` >> simp[]) >>
  `cs_extends mid finished` by (irule cs_extends_trans >> qexists_tac `stored` >> simp[]) >>
  mp_tac (Q.SPECL [`cs`, `mid`, `finished`, `func`] fn_has_code_split) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.SPECL [`cs`, `prefix`, `mid`, `func`] fn_has_code_split) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.SPECL [`mid`, `stored`, `finished`, `func`] fn_has_code_split) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.SPECL [`stored`, `latched`, `finished`, `func`] fn_has_code_split) >> simp[]
QED

Theorem abi_dynamic_loop_contains_child:
  !dst src info abi_sz mem_sz len_op cs op cs' child_len mid func.
    compile_abi_encode_dyn_loop dst src info abi_sz mem_sz len_op cs = (op,cs') /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14))
      (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src abi_sz mem_sz len_op cs) = (child_len,mid) /\
    fn_has_code cs cs' func ==>
    fn_has_code (abi_dynamic_loop_prefix_cut dst src abi_sz mem_sz len_op cs) mid func
Proof
  rpt gen_tac >> strip_tac >>
  `cs' = abi_dynamic_loop_exit_cut src (Var (compiler_var_name cs.cs_next_var 1))
    (fresh_label_output "enc_dyn_exit" (cs.cs_next_label + 2))
    (abi_dynamic_loop_latch_cut (Var (compiler_var_name cs.cs_next_var 0))
      (Var (compiler_var_name cs.cs_next_var 6)) (fresh_label_output "enc_dyn_hdr" cs.cs_next_label)
      (abi_child_suffix_cut (Var (compiler_var_name cs.cs_next_var 12))
        (Var (compiler_var_name cs.cs_next_var 13)) (Var (compiler_var_name cs.cs_next_var 1)) child_len mid))` by
    fs[compile_abi_dynamic_loop_factor, LET_THM] >>
  gvs[] >> drule_all abi_dynamic_loop_contains_parts >> simp[LET_THM]
QED

Theorem abi_dynamic_loop_contains_prefix:
  !dst src abi_sz mem_sz len_op cs func.
    fn_has_code cs (abi_dynamic_loop_prefix_cut dst src abi_sz mem_sz len_op cs) func ==>
    lookup_block (fresh_label_output "enc_dyn_hdr" cs.cs_next_label) func.fn_blocks =
      SOME <|bb_label := fresh_label_output "enc_dyn_hdr" cs.cs_next_label;
        bb_instructions := abi_dynamic_loop_header cs.cs_next_id cs.cs_next_var cs.cs_next_label len_op|> /\
    lookup_block cs.cs_current_bb func.fn_blocks =
      SOME <|bb_label := cs.cs_current_bb; bb_instructions := cs.cs_current_insts ++
        abi_dynamic_loop_entry cs.cs_next_id cs.cs_next_var cs.cs_next_label abi_sz len_op|> /\
    ?body_bb. lookup_block (fresh_label_output "enc_dyn_body" (cs.cs_next_label + 1)) func.fn_blocks = SOME body_bb /\
      isPREFIX (abi_dynamic_loop_body_prefix cs.cs_next_id cs.cs_next_var dst src abi_sz mem_sz) body_bb.bb_instructions
Proof
  rpt gen_tac >> simp[fn_has_code_def, abi_dynamic_loop_prefix_cut_def,
    emitted_blocks_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem abi_dynamic_loop_contains_exit:
  !src dyn_ptr exit_label cs func.
    fn_has_code cs (abi_dynamic_loop_exit_cut src dyn_ptr exit_label cs) func ==>
    lookup_block cs.cs_current_bb func.fn_blocks =
      SOME <|bb_label := cs.cs_current_bb; bb_instructions := cs.cs_current_insts|> /\
    ?exit_bb. lookup_block exit_label func.fn_blocks = SOME exit_bb /\
      isPREFIX (abi_dynamic_loop_exit cs.cs_next_id cs.cs_next_var src dyn_ptr) exit_bb.bb_instructions
Proof
  rpt gen_tac >> simp[fn_has_code_def, abi_dynamic_loop_exit_cut_def, emitted_blocks_def]
QED

Theorem abi_dynamic_loop_no_phi:
  (!id var_base labels len_op. phi_prefix_length (abi_dynamic_loop_header id var_base labels len_op) = 0) /\
  (!id var_base dst src abi_sz mem_sz insts.
    isPREFIX (abi_dynamic_loop_body_prefix id var_base dst src abi_sz mem_sz) insts ==> phi_prefix_length insts = 0) /\
  (!id var_base src dyn_ptr insts.
    isPREFIX (abi_dynamic_loop_exit id var_base src dyn_ptr) insts ==> phi_prefix_length insts = 0)
Proof
  simp[IS_PREFIX_APPEND, PULL_EXISTS, abi_dynamic_loop_header_def,
    abi_dynamic_loop_body_prefix_def, abi_dynamic_loop_exit_def, phi_prefix_length_def, mk_inst_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic-child ABI loop code containment: " ^ name)
  end) (DB.thms "abiDynamicLoopStructure")
