(* Compiler-side factoring and instruction layout for membership. *)
Theory exprSimBopRestWordLayout
Ancestors
  exprLowering exprLoweringProps compileEnv emitHelper emitHelperProps venomInst
  list rich_list pair
Libs
  monadsyntax

Datatype:
  rest_word_loop_handles = <|
    rw_entry : string; rw_cond : string; rw_body : string;
    rw_found : string; rw_incr : string; rw_exit : string;
    rw_result : string; rw_idx : string; rw_addr : operand
  |>
End

val () = enable_monad "compilation";
val () = enable_monadsyntax ();

Definition rest_word_loop_prefix_def:
  rest_word_loop_prefix needle arr len stride off =
    do result_var <- fresh_var;
       entry_lbl <- fresh_label "in_entry";
       cond_lbl <- fresh_label "in_cond";
       body_lbl <- fresh_label "in_body";
       found_lbl <- fresh_label "in_found";
       incr_lbl <- fresh_label "in_incr";
       exit_lbl <- fresh_label "in_exit";
       emit_inst JMP [Label entry_lbl] [];
       new_block entry_lbl;
       idx_var <- fresh_var;
       emit_inst ASSIGN [Lit 0w] [idx_var];
       emit_inst ASSIGN [Lit 0w] [result_var];
       emit_inst JMP [Label cond_lbl] [];
       new_block cond_lbl;
       done_op <- emit_op EQ [Var idx_var; len];
       emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [];
       new_block body_lbl;
       idx_offset <- emit_op MUL [Var idx_var; Lit (n2w stride)];
       total_offset <- (if off > 0 then
                         emit_op ADD [Lit (n2w off); idx_offset]
                        else return idx_offset);
       elem_addr <- emit_op ADD [arr; total_offset];
       return <|rw_entry := entry_lbl; rw_cond := cond_lbl;
                rw_body := body_lbl; rw_found := found_lbl;
                rw_incr := incr_lbl; rw_exit := exit_lbl;
                rw_result := result_var; rw_idx := idx_var;
                rw_addr := elem_addr|>
    od
End

Definition rest_word_loop_suffix_def:
  rest_word_loop_suffix h elem_val needle is_in =
    do match_op <- emit_op EQ [elem_val; needle];
       emit_inst JNZ [match_op; Label h.rw_found; Label h.rw_incr] [];
       new_block h.rw_found;
       emit_inst ASSIGN [Lit 1w] [h.rw_result];
       emit_inst JMP [Label h.rw_exit] [];
       new_block h.rw_incr;
       new_idx <- emit_op ADD [Var h.rw_idx; Lit 1w];
       emit_inst ASSIGN [new_idx] [h.rw_idx];
       emit_inst JMP [Label h.rw_cond] [];
       new_block h.rw_exit;
       if is_in then return (Var h.rw_result)
       else emit_op ISZERO [Var h.rw_result]
    od
End

Theorem rest_word_bind_return[local]:
  comp_bind (comp_return x) f = f x
Proof
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def]
QED

Theorem rest_word_loop_factor:
  compile_array_membership_loop needle arr len stride off loader is_in =
  do h <- rest_word_loop_prefix needle arr len stride off;
     v <- loader h.rw_addr;
     rest_word_loop_suffix h v needle is_in
  od
Proof
  simp[compile_array_membership_loop_def, rest_word_loop_prefix_def,
       rest_word_loop_suffix_def, comp_ignore_bind_def, comp_bind_assoc,
       rest_word_bind_return]
QED

Theorem rest_word_loop_factor_eq:
  compile_array_membership_loop needle arr len stride off loader is_in cs = (out,ct) <=>
  ?h cl cm v.
    rest_word_loop_prefix needle arr len stride off cs = (h,cl) /\
    loader h.rw_addr cl = (v,cm) /\
    rest_word_loop_suffix h v needle is_in cm = (out,ct)
Proof
  rewrite_tac[rest_word_loop_factor, comp_bind_def] >>
  Cases_on `rest_word_loop_prefix needle arr len stride off cs` >> simp[] >>
  rename1 `rest_word_loop_prefix needle arr len stride off cs = (h,cl)` >>
  Cases_on `loader h.rw_addr cl` >> simp[comp_bind_def]
QED

Definition rest_word_loop_prefix_shape_def:
  rest_word_loop_prefix_shape cs cl h arr len stride off <=>
  ?j0 j1 j2 j3 j4 j5 j6 j7 j8 done mul total addr.
    h.rw_addr = Var addr /\ cl.cs_current_bb = h.rw_body /\
    cl.cs_blocks =
      <|bb_label := h.rw_cond;
        bb_instructions := [mk_inst j4 EQ [Var h.rw_idx; len] [done];
                            mk_inst j5 JNZ [Var done; Label h.rw_exit; Label h.rw_body] []]|> ::
      <|bb_label := h.rw_entry;
        bb_instructions := [mk_inst j1 ASSIGN [Lit 0w] [h.rw_idx];
                            mk_inst j2 ASSIGN [Lit 0w] [h.rw_result];
                            mk_inst j3 JMP [Label h.rw_cond] []]|> ::
      <|bb_label := cs.cs_current_bb;
        bb_instructions := cs.cs_current_insts ++ [mk_inst j0 JMP [Label h.rw_entry] []]|> ::
      cs.cs_blocks /\
    cl.cs_current_insts =
      [mk_inst j6 MUL [Var h.rw_idx; Lit (n2w stride)] [mul]] ++
      (if 0 < off then [mk_inst j7 ADD [Lit (n2w off); Var mul] [total]] else []) ++
      [mk_inst j8 ADD [arr; if 0 < off then Var total else Var mul] [addr]]
End

Theorem rest_word_loop_prefix_shape:
  rest_word_loop_prefix needle arr len stride off cs = (h,cl) ==>
  rest_word_loop_prefix_shape cs cl h arr len stride off
Proof
  Cases_on `0 < off` >>
  simp[rest_word_loop_prefix_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_label_def, fresh_id_def,
       emit_inst_def, emit_op_def, emit_def, new_block_def] >>
  strip_tac >> gvs[] >>
  simp[rest_word_loop_prefix_shape_def, APPEND_ASSOC] >>
  metis_tac[]
QED

Definition rest_word_loop_suffix_shape_def:
  rest_word_loop_suffix_shape cm ct h v needle is_in out <=>
  ?j0 j1 j2 j3 j4 j5 j6 j7 match next outvar.
    ct.cs_current_bb = h.rw_exit /\
    ct.cs_blocks =
      <|bb_label := h.rw_incr;
        bb_instructions := [mk_inst j4 ADD [Var h.rw_idx; Lit 1w] [next];
                            mk_inst j5 ASSIGN [Var next] [h.rw_idx];
                            mk_inst j6 JMP [Label h.rw_cond] []]|> ::
      <|bb_label := h.rw_found;
        bb_instructions := [mk_inst j2 ASSIGN [Lit 1w] [h.rw_result];
                            mk_inst j3 JMP [Label h.rw_exit] []]|> ::
      <|bb_label := cm.cs_current_bb;
        bb_instructions := cm.cs_current_insts ++
          [mk_inst j0 EQ [v; needle] [match];
           mk_inst j1 JNZ [Var match; Label h.rw_found; Label h.rw_incr] []]|> ::
      cm.cs_blocks /\
    (if is_in then ct.cs_current_insts = [] /\ out = Var h.rw_result
     else ct.cs_current_insts = [mk_inst j7 ISZERO [Var h.rw_result] [outvar]] /\
          out = Var outvar)
End

Theorem rest_word_loop_suffix_shape:
  rest_word_loop_suffix h v needle is_in cm = (out,ct) ==>
  rest_word_loop_suffix_shape cm ct h v needle is_in out
Proof
  Cases_on `is_in` >>
  simp[rest_word_loop_suffix_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def,
       emit_inst_def, emit_op_def, emit_def, new_block_def] >>
  strip_tac >> gvs[] >>
  simp[rest_word_loop_suffix_shape_def, APPEND_ASSOC] >> metis_tac[]
QED

Theorem rest_word_loop_prefix_allocation:
  rest_word_loop_prefix needle arr len stride off cs = (h,cl) ==>
  h.rw_result = STRING #"%" (toString cs.cs_next_var) /\
  h.rw_idx = STRING #"%" (toString (cs.cs_next_var + 1)) /\
  h.rw_entry = fresh_label_output "in_entry" cs.cs_next_label /\
  h.rw_cond = fresh_label_output "in_cond" (cs.cs_next_label + 1) /\
  h.rw_body = fresh_label_output "in_body" (cs.cs_next_label + 2) /\
  h.rw_found = fresh_label_output "in_found" (cs.cs_next_label + 3) /\
  h.rw_incr = fresh_label_output "in_incr" (cs.cs_next_label + 4) /\
  h.rw_exit = fresh_label_output "in_exit" (cs.cs_next_label + 5) /\
  cl.cs_next_var = cs.cs_next_var + (if 0 < off then 6 else 5) /\
  cl.cs_next_label = cs.cs_next_label + 6 /\
  cl.cs_next_id = cs.cs_next_id + (if 0 < off then 9 else 8)
Proof
  Cases_on `0 < off` >>
  simp[rest_word_loop_prefix_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_label_def, fresh_id_def,
       emit_inst_def, emit_op_def, emit_def, new_block_def] >>
  strip_tac >> gvs[]
QED

Theorem rest_word_loop_prefix_idx_result:
  rest_word_loop_prefix needle arr len stride off cs = (h,cl) ==>
  h.rw_idx <> h.rw_result
Proof
  strip_tac >> drule rest_word_loop_prefix_allocation >> strip_tac >>
  gvs[] >> qspecl_then [`cs.cs_next_var`, `1`] mp_tac fresh_var_neq >> simp[]
QED

Theorem rest_word_loop_prefix_labels_distinct:
  rest_word_loop_prefix needle arr len stride off cs = (h,cl) ==>
  ALL_DISTINCT [h.rw_entry; h.rw_cond; h.rw_body;
                h.rw_found; h.rw_incr; h.rw_exit]
Proof
  strip_tac >> drule rest_word_loop_prefix_allocation >> strip_tac >>
  simp[ALL_DISTINCT, MEM] >> rpt conj_tac >> strip_tac >>
  drule fresh_label_output_inj >> simp[]
QED
