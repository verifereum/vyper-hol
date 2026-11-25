(* A builtin's child and suffix share the installed split cursor. *)
Theory entryCreateBuiltinSplitScope
Ancestors
  entryCreateWordArgsGeometry createSizeCutCode fragExec

(* Closed code establishes both extensions and ID inequalities. The outer
   installation restricts to each piece; it need not fetch at the exit b. *)
Theorem create_builtin_split_scopes:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  create_layout a b /\ fn_has_code a b f /\ create_operand_at a s /\
  create_cut_code {} a m /\ create_cut_code {} m b ==>
  (!marks. create_operand_focus_scope a m E C f s marks ==>
           create_operand_focus_scope a b E C f s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E C f s marks r ==>
             create_operand_full_scope a b E C f s marks r) /\
  (!left t right. create_operand_full_scope a m E C f s left (OK t) /\
                  create_operand_focus_scope m b E C f t right ==>
                  create_operand_focus_scope a b E C f s (left ++ right)) /\
  (!left t right r. create_operand_full_scope a m E C f s left (OK t) /\
                    create_operand_full_scope m b E C f t right r ==>
                    create_operand_full_scope a b E C f s (left ++ right) r)
Proof
  strip_tac >>
  `cs_extends a m /\ cs_extends m b /\
   a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id` by
    fs[create_cut_code_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all create_word_args_scope_embeddings >>
  disch_then (qspec_then `E` ACCEPT_TAC)
QED
