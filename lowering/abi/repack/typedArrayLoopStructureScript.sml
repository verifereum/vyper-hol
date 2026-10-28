(* TOP-LEVEL: a containing function holds the parent loop prefix, recursive
   child fragment and parent suffix, even when that child adds blocks.
   Helpers establish append-only code cuts for the shared loop scaffolding. *)
Theory typedArrayLoopStructure
Ancestors
  typedArrayLoopCode typedCopyAppend compileAppendProps abiStaticLoopCode
  context compileEnv fragExec exprLoweringProps venomInst list rich_list pair arithmetic

Theorem typed_array_loop_start_extends:
  !cs cond_label body_label exit_label len_op dst src dst_size src_size.
    cs_extends cs
      (typed_array_loop_start cs cond_label body_label exit_label len_op dst src dst_size src_size)
Proof
  rpt gen_tac >> rewrite_tac[cs_extends_def] >>
  qexists_tac
    `[<| bb_label := cond_label;
         bb_instructions := typed_array_loop_header cs.cs_next_id cs.cs_next_var
           body_label exit_label len_op |>;
      <| bb_label := cs.cs_current_bb;
         bb_instructions := cs.cs_current_insts ++
           typed_array_loop_entry cs.cs_next_id cs.cs_next_var cond_label |>]` >>
  simp[typed_array_loop_start_def, IS_PREFIX_APPEND]
QED

Theorem typed_array_loop_finish_extends:
  !counter cond_label exit_label after.
    cs_extends after (typed_array_loop_finish counter cond_label exit_label after)
Proof
  rpt gen_tac >> rewrite_tac[cs_extends_def] >>
  qexists_tac
    `[<| bb_label := after.cs_current_bb;
         bb_instructions := after.cs_current_insts ++
           typed_array_loop_counter after.cs_next_id after.cs_next_var counter cond_label |>]` >>
  simp[typed_array_loop_finish_def, IS_PREFIX_APPEND]
QED

Theorem typed_array_loop_prefix_contains:
  !cs cond_label body_label exit_label len_op dst src dst_size src_size func.
    fn_has_code cs
      (typed_array_loop_start cs cond_label body_label exit_label len_op dst src dst_size src_size)
      func ==>
    lookup_block cond_label func.fn_blocks = SOME
      <| bb_label := cond_label;
         bb_instructions := typed_array_loop_header cs.cs_next_id cs.cs_next_var
           body_label exit_label len_op |> /\
    lookup_block cs.cs_current_bb func.fn_blocks = SOME
      <| bb_label := cs.cs_current_bb;
         bb_instructions := cs.cs_current_insts ++
           typed_array_loop_entry cs.cs_next_id cs.cs_next_var cond_label |> /\
    ?body_bb. lookup_block body_label func.fn_blocks = SOME body_bb /\
      isPREFIX (typed_array_loop_addresses cs.cs_next_id cs.cs_next_var dst src dst_size src_size)
        body_bb.bb_instructions
Proof
  rpt strip_tac >> fs[fn_has_code_def, emitted_blocks_def, typed_array_loop_start_def] >>
  qmatch_goalsub_abbrev_tac `SOME wanted` >>
  qpat_x_assum `!bb. _` (qspec_then `wanted` mp_tac) >> simp[Abbr`wanted`]
QED

Theorem typed_array_loop_suffix_contains:
  !counter cond_label exit_label after func.
    fn_has_code after (typed_array_loop_finish counter cond_label exit_label after) func ==>
    lookup_block after.cs_current_bb func.fn_blocks = SOME
      <| bb_label := after.cs_current_bb;
         bb_instructions := after.cs_current_insts ++
           typed_array_loop_counter after.cs_next_id after.cs_next_var counter cond_label |>
Proof
  rpt strip_tac >> fs[fn_has_code_def, emitted_blocks_def, typed_array_loop_finish_def] >>
  qmatch_goalsub_abbrev_tac `SOME wanted` >>
  qpat_x_assum `!bb. _` (qspec_then `wanted` mp_tac) >> simp[Abbr`wanted`]
QED

Theorem typed_array_loop_contains:
  !cs cond_label body_label exit_label len_op dst src dst_size src_size m ret after func.
    let start = typed_array_loop_start cs cond_label body_label exit_label len_op dst src dst_size src_size in
    let finish = typed_array_loop_finish (compiler_var_name cs.cs_next_var 0) cond_label exit_label after in
    cs_appends m /\ m start = (ret,after) /\ fn_has_code cs finish func ==>
    fn_has_code cs start func /\ fn_has_code start after func /\ fn_has_code after finish func
Proof
  rpt gen_tac >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `start = typed_array_loop_start cs cond_label body_label exit_label len_op dst src dst_size src_size` >>
  qabbrev_tac `parent_end = typed_array_loop_finish (compiler_var_name cs.cs_next_var 0) cond_label exit_label after` >>
  `cs_extends cs start` by simp[Abbr`start`, typed_array_loop_start_extends] >>
  `cs_extends start after` by (drule_all cs_appends_result_extends >> simp[]) >>
  `cs_extends after parent_end` by simp[Abbr`parent_end`, typed_array_loop_finish_extends] >>
  `cs_extends start parent_end` by
    (irule cs_extends_trans >> qexists_tac `after` >> simp[]) >>
  mp_tac (Q.SPECL [`cs`, `start`, `parent_end`, `func`] fn_has_code_split) >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`start`, `after`, `parent_end`, `func`] fn_has_code_split) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive array-loop containment theorem: " ^ name)
  end) (DB.thms "typedArrayLoopStructure")
