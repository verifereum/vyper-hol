(* Compiler-side factoring and instruction layout for membership. *)
Theory exprSimBopRestWordLayout
Ancestors
  exprLowering exprLoweringProps compileEnv emitHelper emitHelperProps venomInst
  list rich_list pair fragExec freshWrites
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
  rest_word_loop_prefix needle arr len stride off bound_opt =
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
       (case bound_opt of
          NONE => return ()
        | SOME cap =>
            do too_long <- emit_op GT [len; Lit (n2w cap)];
               valid <- emit_op ISZERO [too_long];
               emit_inst ASSERT [valid] []
            od);
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
  compile_array_membership_loop needle arr len stride off loader bound_opt is_in =
  do h <- rest_word_loop_prefix needle arr len stride off bound_opt;
     v <- loader h.rw_addr;
     rest_word_loop_suffix h v needle is_in
  od
Proof
  simp[compile_array_membership_loop_def, rest_word_loop_prefix_def,
       rest_word_loop_suffix_def, comp_ignore_bind_def, comp_bind_assoc,
       rest_word_bind_return]
QED

Theorem rest_word_loop_factor_eq:
  compile_array_membership_loop needle arr len stride off loader bound_opt is_in cs = (out,ct) <=>
  ?h cl cm v.
    rest_word_loop_prefix needle arr len stride off bound_opt cs = (h,cl) /\
    loader h.rw_addr cl = (v,cm) /\
    rest_word_loop_suffix h v needle is_in cm = (out,ct)
Proof
  rewrite_tac[rest_word_loop_factor, comp_bind_def] >>
  Cases_on `rest_word_loop_prefix needle arr len stride off bound_opt cs` >> simp[] >>
  rename1 `rest_word_loop_prefix needle arr len stride off bound_opt cs = (h,cl)` >>
  Cases_on `loader h.rw_addr cl` >> simp[comp_bind_def]
QED

Theorem rest_word_prefix_temporary[local]:
  2 <= k ==>
  !x. (not_fresh_at cs x \/
       x = STRING #"%" (toString cs.cs_next_var) \/
       x = STRING #"%" (toString (cs.cs_next_var + 1))) ==>
      x <> STRING #"%" (toString (cs.cs_next_var + k))
Proof
  strip_tac >> gen_tac >> strip_tac
  >- (gvs[not_fresh_at_def] >> first_x_assum irule >> simp[]) >>
  gvs[ASCIInumbersTheory.toString_inj]
QED

Definition rest_word_loop_prefix_shape_def:
  rest_word_loop_prefix_shape cs cl h arr len stride off bound_opt <=>
  ?j0 j1 j2 j3 j4 j5 j6 j7 j8 done mul total addr jc0 jc1 jc2 inv valid.
    (case bound_opt of NONE => T | SOME cap =>
      !x. (not_fresh_at cs x \/ x = h.rw_idx \/ x = h.rw_result) ==>
          x <> inv /\ x <> valid) /\
    (!x. (not_fresh_at cs x \/ x = h.rw_idx \/ x = h.rw_result) ==>
         x <> done /\ x <> mul /\ x <> total /\ x <> addr) /\
    h.rw_addr = Var addr /\ cl.cs_current_bb = h.rw_body /\
    cl.cs_blocks =
      <|bb_label := h.rw_cond;
        bb_instructions := [mk_inst j4 EQ [Var h.rw_idx; len] [done];
                            mk_inst j5 JNZ [Var done; Label h.rw_exit; Label h.rw_body] []]|> ::
      <|bb_label := h.rw_entry;
        bb_instructions := [mk_inst j1 ASSIGN [Lit 0w] [h.rw_idx];
                            mk_inst j2 ASSIGN [Lit 0w] [h.rw_result]] ++
          (case bound_opt of NONE => [] | SOME cap =>
            [mk_inst jc0 GT [len; Lit (n2w cap)] [inv];
             mk_inst jc1 ISZERO [Var inv] [valid];
             mk_inst jc2 ASSERT [Var valid] []]) ++
          [mk_inst j3 JMP [Label h.rw_cond] []]|> ::
      <|bb_label := cs.cs_current_bb;
        bb_instructions := cs.cs_current_insts ++ [mk_inst j0 JMP [Label h.rw_entry] []]|> ::
      cs.cs_blocks /\
    cl.cs_current_insts =
      [mk_inst j6 MUL [Var h.rw_idx; Lit (n2w stride)] [mul]] ++
      (if 0 < off then [mk_inst j7 ADD [Lit (n2w off); Var mul] [total]] else []) ++
      [mk_inst j8 ADD [arr; if 0 < off then Var total else Var mul] [addr]]
End

Theorem rest_word_loop_prefix_shape:
  rest_word_loop_prefix needle arr len stride off bound_opt cs = (h,cl) ==>
  rest_word_loop_prefix_shape cs cl h arr len stride off bound_opt
Proof
  Cases_on `bound_opt` >> Cases_on `0 < off` >>
  simp[rest_word_loop_prefix_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_label_def, fresh_id_def,
       emit_inst_def, emit_op_def, emit_def, new_block_def] >>
  strip_tac >> gvs[] >>
  simp[rest_word_loop_prefix_shape_def, APPEND_ASSOC, mk_inst_def]
  >- (gen_tac >> disch_tac >> rpt conj_tac >>
      irule rest_word_prefix_temporary >> simp[] >> metis_tac[])
  >- (qexists `STRING #"%" (toString (cs.cs_next_var + 2))` >>
      gen_tac >> disch_tac >> rpt conj_tac >>
      irule rest_word_prefix_temporary >> simp[] >> metis_tac[])
  >- (conj_tac >> gen_tac >> disch_tac >> rpt conj_tac >>
      irule rest_word_prefix_temporary >> simp[] >> metis_tac[]) >>
  qexists `STRING #"%" (toString (cs.cs_next_var + 4))` >>
  conj_tac >> gen_tac >> disch_tac >> rpt conj_tac >>
  irule rest_word_prefix_temporary >> simp[] >> metis_tac[]
QED

Theorem rest_word_three_fresh[local]:
  !x. not_fresh_at cs x ==>
      x <> STRING #"%" (toString cs.cs_next_var) /\
      x <> STRING #"%" (toString (cs.cs_next_var + 1)) /\
      x <> STRING #"%" (toString (cs.cs_next_var + 2))
Proof
  simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

Definition rest_word_loop_suffix_shape_def:
  rest_word_loop_suffix_shape cm ct h v needle is_in out <=>
  ?j0 j1 j2 j3 j4 j5 j6 j7 match next outvar.
    (!x. not_fresh_at cm x ==> x <> match /\ x <> next /\ x <> outvar) /\
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
  simp[rest_word_loop_suffix_shape_def, APPEND_ASSOC] >>
  qspec_then `cm` mp_tac (GEN_ALL rest_word_three_fresh) >> metis_tac[]
QED

Theorem rest_word_loop_prefix_allocation:
  rest_word_loop_prefix needle arr len stride off bound_opt cs = (h,cl) ==>
  h.rw_result = STRING #"%" (toString cs.cs_next_var) /\
  h.rw_idx = STRING #"%" (toString (cs.cs_next_var + 1)) /\
  h.rw_entry = fresh_label_output "in_entry" cs.cs_next_label /\
  h.rw_cond = fresh_label_output "in_cond" (cs.cs_next_label + 1) /\
  h.rw_body = fresh_label_output "in_body" (cs.cs_next_label + 2) /\
  h.rw_found = fresh_label_output "in_found" (cs.cs_next_label + 3) /\
  h.rw_incr = fresh_label_output "in_incr" (cs.cs_next_label + 4) /\
  h.rw_exit = fresh_label_output "in_exit" (cs.cs_next_label + 5) /\
  cl.cs_next_var = cs.cs_next_var + (if 0 < off then 6 else 5) +
    (case bound_opt of NONE => 0 | SOME _ => 2) /\
  cl.cs_next_label = cs.cs_next_label + 6 /\
  cl.cs_next_id = cs.cs_next_id + (if 0 < off then 9 else 8) +
    (case bound_opt of NONE => 0 | SOME _ => 3)
Proof
  Cases_on `bound_opt` >> Cases_on `0 < off` >>
  simp[rest_word_loop_prefix_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_label_def, fresh_id_def,
       emit_inst_def, emit_op_def, emit_def, new_block_def] >>
  strip_tac >> gvs[]
QED

Theorem rest_word_loop_prefix_idx_result:
  rest_word_loop_prefix needle arr len stride off bound_opt cs = (h,cl) ==>
  h.rw_idx <> h.rw_result
Proof
  strip_tac >> drule rest_word_loop_prefix_allocation >> strip_tac >>
  gvs[] >> qspecl_then [`cs.cs_next_var`, `1`] mp_tac fresh_var_neq >> simp[]
QED

Theorem rest_word_loop_prefix_labels_distinct:
  rest_word_loop_prefix needle arr len stride off bound_opt cs = (h,cl) ==>
  ALL_DISTINCT [h.rw_entry; h.rw_cond; h.rw_body;
                h.rw_found; h.rw_incr; h.rw_exit]
Proof
  strip_tac >> drule rest_word_loop_prefix_allocation >> strip_tac >>
  simp[ALL_DISTINCT, MEM] >> rpt conj_tac >> strip_tac >>
  drule fresh_label_output_inj >> simp[]
QED

Definition rest_word_loop_layout_def:
  rest_word_loop_layout cs ct fn needle arr len stride off bound_opt is_in out h loadcode <=>
  ?a0 a1 a2 a3 a4 a5 a6 a7 a8 b0 b1 b2 b3 b4 b5 b6 b7
   done mul total addr match next outvar v caller exitbb jc0 jc1 jc2 inv valid.
    h.rw_addr = Var addr /\ ct.cs_current_bb = h.rw_exit /\
    lookup_block cs.cs_current_bb fn.fn_blocks = SOME caller /\
    get_instruction caller (LENGTH cs.cs_current_insts) =
      SOME (mk_inst a0 JMP [Label h.rw_entry] []) /\
    lookup_block h.rw_entry fn.fn_blocks = SOME
      <|bb_label := h.rw_entry;
        bb_instructions := [mk_inst a1 ASSIGN [Lit 0w] [h.rw_idx];
                            mk_inst a2 ASSIGN [Lit 0w] [h.rw_result]] ++
          (case bound_opt of NONE => [] | SOME cap =>
            [mk_inst jc0 GT [len; Lit (n2w cap)] [inv];
             mk_inst jc1 ISZERO [Var inv] [valid];
             mk_inst jc2 ASSERT [Var valid] []]) ++
          [mk_inst a3 JMP [Label h.rw_cond] []]|> /\
    lookup_block h.rw_cond fn.fn_blocks = SOME
      <|bb_label := h.rw_cond;
        bb_instructions := [mk_inst a4 EQ [Var h.rw_idx; len] [done];
                            mk_inst a5 JNZ [Var done; Label h.rw_exit; Label h.rw_body] []]|> /\
    lookup_block h.rw_body fn.fn_blocks = SOME
      <|bb_label := h.rw_body;
        bb_instructions :=
          [mk_inst a6 MUL [Var h.rw_idx; Lit (n2w stride)] [mul]] ++
          (if 0 < off then [mk_inst a7 ADD [Lit (n2w off); Var mul] [total]] else []) ++
          [mk_inst a8 ADD [arr; if 0 < off then Var total else Var mul] [addr]] ++
          loadcode ++ [mk_inst b0 EQ [v; needle] [match];
                       mk_inst b1 JNZ [Var match; Label h.rw_found; Label h.rw_incr] []]|> /\
    lookup_block h.rw_found fn.fn_blocks = SOME
      <|bb_label := h.rw_found;
        bb_instructions := [mk_inst b2 ASSIGN [Lit 1w] [h.rw_result];
                            mk_inst b3 JMP [Label h.rw_exit] []]|> /\
    lookup_block h.rw_incr fn.fn_blocks = SOME
      <|bb_label := h.rw_incr;
        bb_instructions := [mk_inst b4 ADD [Var h.rw_idx; Lit 1w] [next];
                            mk_inst b5 ASSIGN [Var next] [h.rw_idx];
                            mk_inst b6 JMP [Label h.rw_cond] []]|> /\
    lookup_block h.rw_exit fn.fn_blocks = SOME exitbb /\
    isPREFIX ct.cs_current_insts exitbb.bb_instructions /\
    (if is_in then ct.cs_current_insts = [] /\ out = Var h.rw_result
     else ct.cs_current_insts = [mk_inst b7 ISZERO [Var h.rw_result] [outvar]] /\
          out = Var outvar)
End

Definition rest_word_loop_layout_safe_def:
  rest_word_loop_layout_safe cs ct fn needle arr len stride off bound_opt is_in out h loadcode (cl:compile_state) cm v <=>
  ?a0 a1 a2 a3 a4 a5 a6 a7 a8 b0 b1 b2 b3 b4 b5 b6 b7
   done mul total addr match next outvar caller exitbb jc0 jc1 jc2 inv valid.
    (case bound_opt of NONE => T | SOME cap =>
      !x. (not_fresh_at cs x \/ x = h.rw_idx \/ x = h.rw_result) ==>
          x <> inv /\ x <> valid) /\
    (!x. (not_fresh_at cs x \/ x = h.rw_idx \/ x = h.rw_result) ==>
         x <> done /\ x <> mul /\ x <> total /\ x <> addr) /\
    (!x. not_fresh_at cm x ==> x <> match /\ x <> next /\ x <> outvar) /\
    h.rw_addr = Var addr /\ ct.cs_current_bb = h.rw_exit /\
    lookup_block cs.cs_current_bb fn.fn_blocks = SOME caller /\
    get_instruction caller (LENGTH cs.cs_current_insts) =
      SOME (mk_inst a0 JMP [Label h.rw_entry] []) /\
    lookup_block h.rw_entry fn.fn_blocks = SOME
      <|bb_label := h.rw_entry;
        bb_instructions := [mk_inst a1 ASSIGN [Lit 0w] [h.rw_idx];
                            mk_inst a2 ASSIGN [Lit 0w] [h.rw_result]] ++
          (case bound_opt of NONE => [] | SOME cap =>
            [mk_inst jc0 GT [len; Lit (n2w cap)] [inv];
             mk_inst jc1 ISZERO [Var inv] [valid];
             mk_inst jc2 ASSERT [Var valid] []]) ++
          [mk_inst a3 JMP [Label h.rw_cond] []]|> /\
    lookup_block h.rw_cond fn.fn_blocks = SOME
      <|bb_label := h.rw_cond;
        bb_instructions := [mk_inst a4 EQ [Var h.rw_idx; len] [done];
                            mk_inst a5 JNZ [Var done; Label h.rw_exit; Label h.rw_body] []]|> /\
    lookup_block h.rw_body fn.fn_blocks = SOME
      <|bb_label := h.rw_body;
        bb_instructions :=
          [mk_inst a6 MUL [Var h.rw_idx; Lit (n2w stride)] [mul]] ++
          (if 0 < off then [mk_inst a7 ADD [Lit (n2w off); Var mul] [total]] else []) ++
          [mk_inst a8 ADD [arr; if 0 < off then Var total else Var mul] [addr]] ++
          loadcode ++ [mk_inst b0 EQ [v; needle] [match];
                       mk_inst b1 JNZ [Var match; Label h.rw_found; Label h.rw_incr] []]|> /\
    lookup_block h.rw_found fn.fn_blocks = SOME
      <|bb_label := h.rw_found;
        bb_instructions := [mk_inst b2 ASSIGN [Lit 1w] [h.rw_result];
                            mk_inst b3 JMP [Label h.rw_exit] []]|> /\
    lookup_block h.rw_incr fn.fn_blocks = SOME
      <|bb_label := h.rw_incr;
        bb_instructions := [mk_inst b4 ADD [Var h.rw_idx; Lit 1w] [next];
                            mk_inst b5 ASSIGN [Var next] [h.rw_idx];
                            mk_inst b6 JMP [Label h.rw_cond] []]|> /\
    lookup_block h.rw_exit fn.fn_blocks = SOME exitbb /\
    isPREFIX ct.cs_current_insts exitbb.bb_instructions /\
    (if is_in then ct.cs_current_insts = [] /\ out = Var h.rw_result
     else ct.cs_current_insts = [mk_inst b7 ISZERO [Var h.rw_result] [outvar]] /\
          out = Var outvar)
End

Theorem rest_word_loop_layout_safe_extract:
  rest_word_loop_prefix needle arr len stride off bound_opt cs = (h,cl) /\
  cm.cs_current_bb = cl.cs_current_bb /\ cm.cs_blocks = cl.cs_blocks /\
  cm.cs_current_insts = cl.cs_current_insts ++ loadcode /\
  rest_word_loop_suffix h v needle is_in cm = (out,ct) /\
  fn_has_code cs ct fn ==>
  rest_word_loop_layout_safe cs ct fn needle arr len stride off bound_opt is_in out h loadcode cl cm v
Proof
  strip_tac >>
  drule rest_word_loop_prefix_shape >>
  drule rest_word_loop_suffix_shape >>
  rewrite_tac[rest_word_loop_prefix_shape_def, rest_word_loop_suffix_shape_def] >>
  rpt strip_tac >>
  gvs[fn_has_code_def, emitted_blocks_def, LENGTH_APPEND, APPEND_ASSOC,
      DISJ_IMP_THM, FORALL_AND_THM, arithmeticTheory.ADD1] >>
  qpat_x_assum `rest_word_loop_prefix _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `rest_word_loop_suffix _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `cm.cs_blocks = _` kall_tac >>
  qpat_x_assum `cm.cs_current_insts = _` kall_tac >>
  qpat_x_assum `ct.cs_blocks = _` kall_tac >>
  qpat_x_assum `cl.cs_blocks = _` kall_tac >>
  qpat_x_assum `cl.cs_current_insts = _` kall_tac >>
  simp[rest_word_loop_layout_safe_def, APPEND_ASSOC] >>
  qexistsl [`j0'`, `j1'`, `j2'`, `j3'`, `j4'`, `j5'`, `j6'`, `j7'`, `j8`,
            `j0`, `j1`, `j2`, `j3`, `j4`, `j5`, `j6`, `j7`,
            `done`, `mul'`, `total'`, `match`, `next`, `outvar`,
            `jc0`, `jc1`, `jc2`, `inv'`, `valid`] >>
  simp[get_instruction_def, EL_APPEND_EQN, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem rest_word_loop_layout_safe_forget:
  rest_word_loop_layout_safe cs ct fn needle arr len stride off bound_opt is_in out h code cl cm v ==>
  rest_word_loop_layout cs ct fn needle arr len stride off bound_opt is_in out h code
Proof
  simp[rest_word_loop_layout_safe_def, rest_word_loop_layout_def] >>
  rpt strip_tac >>
  qexistsl [`a0`, `a1`, `a2`, `a3`, `a4`, `a5`, `a6`, `a7`, `a8`,
            `b0`, `b1`, `b2`, `b3`, `b4`, `b5`, `b6`, `b7`,
            `done`, `mul'`, `total'`, `addr`, `match`, `next`, `outvar`,
            `v`, `caller`, `exitbb`, `jc0`, `jc1`, `jc2`, `inv'`, `valid`] >> simp[]
QED

Theorem rest_word_loop_layout_extract:
  rest_word_loop_prefix needle arr len stride off bound_opt cs = (h,cl) /\
  cm.cs_current_bb = cl.cs_current_bb /\ cm.cs_blocks = cl.cs_blocks /\
  cm.cs_current_insts = cl.cs_current_insts ++ loadcode /\
  rest_word_loop_suffix h v needle is_in cm = (out,ct) /\
  fn_has_code cs ct fn ==>
  rest_word_loop_layout cs ct fn needle arr len stride off bound_opt is_in out h loadcode
Proof
  strip_tac >> irule rest_word_loop_layout_safe_forget >>
  qexistsl [`cl`, `cm`, `v`] >>
  irule rest_word_loop_layout_safe_extract >> simp[]
QED

Theorem rest_word_ptr_load_shape:
  compile_ptr_load is_ctor imm loc op cs = (v,ct) ==>
  ?code. ct.cs_blocks = cs.cs_blocks /\
         ct.cs_current_bb = cs.cs_current_bb /\
         ct.cs_current_insts = cs.cs_current_insts ++ code
Proof
  strip_tac >>
  drule compile_ptr_load_same_blocks >>
  drule compile_ptr_load_prefix >>
  simp[same_blocks_def, IS_PREFIX_APPEND] >> metis_tac[]
QED

Theorem rest_word_ptr_loop_layout:
  compile_array_membership_loop needle arr len stride off
    (compile_ptr_load is_ctor imm loc) bound_opt is_in cs = (out,ct) /\
  fn_has_code cs ct fn ==>
  ?h code. rest_word_loop_layout cs ct fn needle arr len stride off bound_opt is_in out h code
Proof
  rewrite_tac[rest_word_loop_factor_eq] >> strip_tac >>
  drule rest_word_ptr_load_shape >> strip_tac >>
  irule_at Any rest_word_loop_layout_extract >> goal_assum drule >> simp[] >>
  goal_assum drule >> simp[] >> metis_tac[]
QED

Theorem rest_word_loop_prefix_labels_new:
  rest_word_loop_prefix needle arr len stride off bound_opt cs = (h,cl) /\
  compile_state_ok cs ==>
  !lbl. MEM lbl [h.rw_entry; h.rw_cond; h.rw_body;
                  h.rw_found; h.rw_incr; h.rw_exit] ==>
        lbl NOTIN bound_labels cs
Proof
  strip_tac >> drule rest_word_loop_prefix_allocation >> strip_tac >>
  gvs[compile_state_ok_def, pred_setTheory.DISJOINT_DEF,
      pred_setTheory.EXTENSION, MEM] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!x. _` mp_tac >>
  simp[GSYM IMP_DISJ_THM] >>
  goal_assum drule >> simp[fresh_label_output_in_future]
QED

Theorem rest_word_loop_prefix_protect:
  rest_word_loop_prefix needle arr len stride off bound_opt cs = (h,cl) /\
  not_fresh_at cs x ==>
  x <> h.rw_idx /\ x <> h.rw_result
Proof
  strip_tac >> drule rest_word_loop_prefix_allocation >> strip_tac >>
  gvs[not_fresh_at_def] >> conj_tac >> first_x_assum irule >> simp[]
QED

Theorem rest_word_loop_prefix_handles_old:
  rest_word_loop_prefix needle arr len stride off bound_opt cs = (h,cl) ==>
  not_fresh_at cl h.rw_idx /\ not_fresh_at cl h.rw_result
Proof
  strip_tac >> drule rest_word_loop_prefix_allocation >> strip_tac >>
  simp[not_fresh_at_def] >> gvs[] >>
  conj_tac >> rpt strip_tac >> gvs[ASCIInumbersTheory.toString_inj] >>
  Cases_on `0 < off` >> gvs[]
QED

Theorem rest_word_loop_suffix_allocation:
  rest_word_loop_suffix h v needle is_in cm = (out,ct) ==>
  ct.cs_next_var = cm.cs_next_var + (if is_in then 2 else 3) /\
  ct.cs_next_label = cm.cs_next_label
Proof
  Cases_on `is_in` >>
  simp[rest_word_loop_suffix_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def,
       emit_inst_def, emit_op_def, emit_def, new_block_def] >>
  strip_tac >> gvs[]
QED

Theorem rest_word_ptr_load_fresh:
  compile_ptr_load ctor imm loc addr cs = (v,ct) ==>
  (!x. not_fresh_at cs x ==>
       EVERY (\i. ~MEM x i.inst_outputs) (emitted_insts cs ct)) /\
  (?y. v = Var y /\ !x. not_fresh_at cs x ==> x <> y)
Proof
  Cases_on `loc` >> Cases_on `ctor` >> Cases_on `imm` >>
  simp[contextTheory.compile_ptr_load_def, contextTheory.compile_imm_load_word_def,
       emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> once_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >>
  simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem rest_word_loop_ptr_protected:
  rest_word_loop_prefix needle arr len stride off bound_opt cs = (h,cl) /\
  compile_ptr_load ctor imm loc h.rw_addr cl = (v,cm) ==>
  not_fresh_at cm h.rw_idx /\ not_fresh_at cm h.rw_result /\
  (!x. not_fresh_at cs x ==> not_fresh_at cm x)
Proof
  strip_tac >> drule rest_word_loop_prefix_handles_old >> strip_tac >>
  drule rest_word_loop_prefix_allocation >> strip_tac >>
  qspecl_then [`ctor`, `imm`, `loc`, `h.rw_addr`, `cl`] mp_tac
    ci_mono_compile_ptr_load >>
  gvs[ci_mono_def] >> strip_tac >>
  `cs.cs_next_var <= cm.cs_next_var` by
    (Cases_on `0 < off` >> gvs[]) >>
  metis_tac[not_fresh_at_mono]
QED

Theorem rest_word_loop_layout_entry:
  rest_word_loop_layout cs ct fn needle arr len stride off bound_opt is_in out h code ==>
  ?a b c jc0 jc1 jc2 inv valid.
    lookup_block h.rw_entry fn.fn_blocks = SOME
    <|bb_label := h.rw_entry;
      bb_instructions := [mk_inst a ASSIGN [Lit 0w] [h.rw_idx];
                          mk_inst b ASSIGN [Lit 0w] [h.rw_result]] ++
        (case bound_opt of NONE => [] | SOME cap =>
          [mk_inst jc0 GT [len; Lit (n2w cap)] [inv];
           mk_inst jc1 ISZERO [Var inv] [valid];
           mk_inst jc2 ASSERT [Var valid] []]) ++
        [mk_inst c JMP [Label h.rw_cond] []]|>
Proof
  simp[rest_word_loop_layout_def] >> metis_tac[]
QED

Theorem rest_word_loop_layout_safe_entry:
  rest_word_loop_layout_safe cs ct fn needle arr len stride off bound_opt is_in out h code cl cm v ==>
  ?a b c jc0 jc1 jc2 inv valid.
    (case bound_opt of NONE => T | SOME cap =>
      !x. (not_fresh_at cs x \/ x = h.rw_idx \/ x = h.rw_result) ==>
          x <> inv /\ x <> valid) /\
    lookup_block h.rw_entry fn.fn_blocks = SOME
    <|bb_label := h.rw_entry;
      bb_instructions := [mk_inst a ASSIGN [Lit 0w] [h.rw_idx];
                          mk_inst b ASSIGN [Lit 0w] [h.rw_result]] ++
        (case bound_opt of NONE => [] | SOME cap =>
          [mk_inst jc0 GT [len; Lit (n2w cap)] [inv];
           mk_inst jc1 ISZERO [Var inv] [valid];
           mk_inst jc2 ASSERT [Var valid] []]) ++
        [mk_inst c JMP [Label h.rw_cond] []]|>
Proof
  simp[rest_word_loop_layout_safe_def] >> metis_tac[]
QED

Theorem rest_word_loop_layout_cond:
  rest_word_loop_layout cs ct fn needle arr len stride off bound_opt is_in out h code ==>
  ?a b done. lookup_block h.rw_cond fn.fn_blocks = SOME
    <|bb_label := h.rw_cond;
      bb_instructions := [mk_inst a EQ [Var h.rw_idx; len] [done];
        mk_inst b JNZ [Var done; Label h.rw_exit; Label h.rw_body] []]|>
Proof
  simp[rest_word_loop_layout_def] >> metis_tac[]
QED

Theorem rest_word_loop_layout_found:
  rest_word_loop_layout cs ct fn needle arr len stride off bound_opt is_in out h code ==>
  ?a b. lookup_block h.rw_found fn.fn_blocks = SOME
    <|bb_label := h.rw_found;
      bb_instructions := [mk_inst a ASSIGN [Lit 1w] [h.rw_result];
                          mk_inst b JMP [Label h.rw_exit] []]|>
Proof
  simp[rest_word_loop_layout_def] >> metis_tac[]
QED

Theorem rest_word_loop_layout_incr:
  rest_word_loop_layout cs ct fn needle arr len stride off bound_opt is_in out h code ==>
  ?a b c next. lookup_block h.rw_incr fn.fn_blocks = SOME
    <|bb_label := h.rw_incr;
      bb_instructions := [mk_inst a ADD [Var h.rw_idx; Lit 1w] [next];
                          mk_inst b ASSIGN [Var next] [h.rw_idx];
                          mk_inst c JMP [Label h.rw_cond] []]|>
Proof
  simp[rest_word_loop_layout_def] >> metis_tac[]
QED

Theorem rest_word_loop_layout_exit:
  rest_word_loop_layout cs ct fn needle arr len stride off bound_opt is_in out h code ==>
  ct.cs_current_bb = h.rw_exit /\
  ?bb. lookup_block h.rw_exit fn.fn_blocks = SOME bb /\
       isPREFIX ct.cs_current_insts bb.bb_instructions /\
       (if is_in then ct.cs_current_insts = [] /\ out = Var h.rw_result
        else ?a v. ct.cs_current_insts = [mk_inst a ISZERO [Var h.rw_result] [v]] /\
                   out = Var v)
Proof
  simp[rest_word_loop_layout_def] >> rpt strip_tac >> simp[] >>
  Cases_on `is_in` >> gvs[] >> metis_tac[]
QED

Theorem rest_word_loop_layout_body:
  rest_word_loop_layout cs ct fn needle arr len stride off bound_opt is_in out h code ==>
  ?a b c d e mul total addr match v.
    h.rw_addr = Var addr /\
    lookup_block h.rw_body fn.fn_blocks = SOME
      <|bb_label := h.rw_body;
        bb_instructions :=
          [mk_inst a MUL [Var h.rw_idx; Lit (n2w stride)] [mul]] ++
          (if 0 < off then [mk_inst b ADD [Lit (n2w off); Var mul] [total]] else []) ++
          [mk_inst c ADD [arr; if 0 < off then Var total else Var mul] [addr]] ++
          code ++ [mk_inst d EQ [v; needle] [match];
                   mk_inst e JNZ [Var match; Label h.rw_found; Label h.rw_incr] []]|>
Proof
  simp[rest_word_loop_layout_def] >> metis_tac[]
QED

Theorem rest_word_ptr_loop_layout_safe:
  compile_array_membership_loop needle arr len stride off
    (compile_ptr_load ctor imm loc) bound_opt is_in cs = (out,ct) /\
  fn_has_code cs ct fn ==>
  ?h cl cm v.
    rest_word_loop_prefix needle arr len stride off bound_opt cs = (h,cl) /\
    compile_ptr_load ctor imm loc h.rw_addr cl = (v,cm) /\
    rest_word_loop_suffix h v needle is_in cm = (out,ct) /\
    rest_word_loop_layout_safe cs ct fn needle arr len stride off bound_opt is_in out h
      (emitted_insts cl cm) cl cm v
Proof
  rewrite_tac[rest_word_loop_factor_eq] >> strip_tac >>
  drule rest_word_ptr_load_shape >> strip_tac >>
  `emitted_insts cl cm = code` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  qexistsl [`h`, `cl`, `cm`, `v`] >> simp[] >>
  irule rest_word_loop_layout_safe_extract >> simp[]
QED

Theorem rest_word_loop_layout_safe_cond:
  rest_word_loop_layout_safe cs ct fn needle arr len stride off bound_opt is_in out h code cl cm v ==>
  ?a b done.
    (!x. (not_fresh_at cs x \/ x = h.rw_idx \/ x = h.rw_result) ==> x <> done) /\
    lookup_block h.rw_cond fn.fn_blocks = SOME
      <|bb_label := h.rw_cond;
        bb_instructions := [mk_inst a EQ [Var h.rw_idx; len] [done];
          mk_inst b JNZ [Var done; Label h.rw_exit; Label h.rw_body] []]|>
Proof
  simp[rest_word_loop_layout_safe_def] >> rpt strip_tac >>
  qexistsl [`a4`, `a5`, `done`] >> simp[] >> metis_tac[]
QED

Theorem rest_word_loop_layout_safe_body:
  rest_word_loop_layout_safe cs ct fn needle arr len stride off bound_opt is_in out h code cl cm v ==>
  ?a b c d e mulvar totalvar addr matched.
    h.rw_addr = Var addr /\
    (!x. (not_fresh_at cs x \/ x = h.rw_idx \/ x = h.rw_result) ==>
         x <> mulvar /\ x <> totalvar /\ x <> addr) /\
    (!x. not_fresh_at cm x ==> x <> matched) /\
    lookup_block h.rw_body fn.fn_blocks = SOME
      <|bb_label := h.rw_body;
        bb_instructions :=
          [mk_inst a MUL [Var h.rw_idx; Lit (n2w stride)] [mulvar]] ++
          (if 0 < off then [mk_inst b ADD [Lit (n2w off); Var mulvar] [totalvar]] else []) ++
          [mk_inst c ADD [arr; if 0 < off then Var totalvar else Var mulvar] [addr]] ++
          code ++ [mk_inst d EQ [v; needle] [matched];
                   mk_inst e JNZ [Var matched; Label h.rw_found; Label h.rw_incr] []]|>
Proof
  simp[rest_word_loop_layout_safe_def] >> rpt strip_tac >>
  qexistsl [`a6`, `a7`, `a8`, `b0`, `b1`, `mul'`, `total'`, `addr`, `match`] >>
  simp[] >> metis_tac[]
QED

Theorem rest_word_loop_layout_safe_incr:
  rest_word_loop_layout_safe cs ct fn needle arr len stride off bound_opt is_in out h code cl cm v ==>
  ?a b c next.
    (!x. not_fresh_at cm x ==> x <> next) /\
    lookup_block h.rw_incr fn.fn_blocks = SOME
      <|bb_label := h.rw_incr;
        bb_instructions := [mk_inst a ADD [Var h.rw_idx; Lit 1w] [next];
                            mk_inst b ASSIGN [Var next] [h.rw_idx];
                            mk_inst c JMP [Label h.rw_cond] []]|>
Proof
  simp[rest_word_loop_layout_safe_def] >> rpt strip_tac >>
  qexistsl [`b4`, `b5`, `b6`, `next`] >> simp[] >> metis_tac[]
QED

Theorem rest_word_loop_layout_safe_exit:
  rest_word_loop_layout_safe cs ct fn needle arr len stride off bound_opt is_in out h code cl cm v ==>
  ct.cs_current_bb = h.rw_exit /\
  ?bb. lookup_block h.rw_exit fn.fn_blocks = SOME bb /\
       isPREFIX ct.cs_current_insts bb.bb_instructions /\
       (if is_in then ct.cs_current_insts = [] /\ out = Var h.rw_result
        else ?a z. (!x. not_fresh_at cm x ==> x <> z) /\
                   ct.cs_current_insts = [mk_inst a ISZERO [Var h.rw_result] [z]] /\
                   out = Var z)
Proof
  simp[rest_word_loop_layout_safe_def] >> rpt strip_tac >> simp[] >>
  Cases_on `is_in` >> gvs[] >>
  qexists `b7` >> simp[] >> metis_tac[]
QED
