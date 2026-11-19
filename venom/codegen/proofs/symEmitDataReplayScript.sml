(* Labelled data-source CODECOPY: replay only the selected successful run.
   The clients supply the step equation and endpoint correspondence. *)
Theory symEmitDataReplay
Ancestors codegenSymRel asmSymOwnCode[qualified,ignore_grammar]
  asmSymSem asmSem list

Theorem sym_codecopy_data_replay_selected:
  !allow_own own.
  (!t. asm_copy_to_mem (DROP d (env ' l))
      (ss.sym_base with as_stack := [dst; 0w; sz]) = AsmOK t ==>
    (if allow_own then sym_step_own p env own (AsmOp "CODECOPY") ss
     else sym_step p env (AsmOp "CODECOPY") ss) = SymOK
      (ss with <| sym_base := t with as_stack := [];
                  sym_stack := MAP Val t.as_stack ++ tail |>)) /\
  ss.sym_base.as_pc = cs.as_pc /\
  asm_block_at p cs.as_pc [AsmOp "CODECOPY"] /\
  asm_step lo (build_offset_to_pc p) (AsmOp "CODECOPY") cs = AsmOK cs' /\
  (!out. sym_steps_mode allow_own p env own 1 ss = SymOK out /\
    asm_steps lo (build_offset_to_pc p) p 1 cs = AsmOK cs' ==> R cs' out) ==>
  ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
    R cs' ss' /\ ss'.sym_mem_labels = ss.sym_mem_labels /\ ss'.sym_stack = tail
Proof
  rpt gen_tac >> strip_tac >>
  `?t. asm_copy_to_mem (DROP d (env ' l))
     (ss.sym_base with as_stack := [dst; 0w; sz]) = AsmOK t /\ t.as_stack = []` by
    simp[asm_copy_to_mem_def, asm_next_def] >>
  qpat_x_assum `!t. _` (qspec_then `t` mp_tac) >> simp[] >> strip_tac >>
  qabbrev_tac `out = ss with <| sym_base := t with as_stack := [];
                               sym_stack := tail |>` >>
  `asm_block_at p ss.sym_base.as_pc [AsmOp "CODECOPY"]` by simp[] >>
  `sym_steps_mode allow_own p env own 1 ss = SymOK out` by
    (qpat_assum `asm_block_at p ss.sym_base.as_pc _`
       (mp_tac o MATCH_MP sym_steps_mode_single) >>
     disch_then SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  qexists `out` >> simp[] >>
  `R cs' out` suffices_by simp[Abbr `out`] >>
  qpat_x_assum `!out. _` (qspec_then `out` irule) >> simp[] >>
  fs[asm_block_at_def] >>
  pure_rewrite_tac [numLib.num_CONV ``1:num``] >>
  pure_once_rewrite_tac [asm_steps_def] >> simp[asm_steps_def]
QED
