(* Allocation history at the real cursor of a straight-line decoder fragment. *)
Theory entryDecoderHistoryFrame
Ancestors
  allocaHistoryFragment fragExec exprLoweringProps rich_list

Theorem entry_straight_line_code_slice:
  fn_has_code sa sb fn /\
  sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts ==>
  ?bb rest.
    lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    DROP (LENGTH sa.cs_current_insts) bb.bb_instructions =
      emitted_insts sa sb ++ rest
Proof
  strip_tac >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  simp[fn_has_code_def] >> strip_tac >>
  gvs[IS_PREFIX_APPEND] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem entry_straight_line_alloca_history:
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  fn_has_code sa sb fn /\
  sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  alloca_history fn (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `LENGTH sb.cs_current_insts =
   s.vs_inst_idx + LENGTH (emitted_insts sa sb)` by
    (gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest`
    by simp[] >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

val () =
  List.app (fn th =>
    let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
    in if null axioms andalso null (Thm.hyp th) andalso
          List.all (fn name => name = "DISK_THM") oracles
       then () else raise Fail "entry history frame inherited admission"
    end) [entry_straight_line_code_slice, entry_straight_line_alloca_history];
