Theory bodyPtrBytestringBuiltinsConcatLookup
Ancestors
  bodyPtrBytestringBuiltinsConcatFixed bodyPtrBytestringBuiltinsConcatBytes
  fragExec context emitHelperProps list
Libs monadsyntax

Theorem concat_fixed_cut_lookup:
  (do offset_op <- emit_op MLOAD [off_ptr];
      dst <- emit_op ADD [data_ptr; offset_op];
      emit_void MSTORE [dst; value];
      new_offset <- emit_op ADD [offset_op; Lit (n2w m)];
      emit_void MSTORE [off_ptr; new_offset]
   od) sa = ((),sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  sb.cs_current_bb = s.vs_current_bb /\
  LENGTH sb.cs_current_insts = s.vs_inst_idx + 5 /\
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst sa.cs_next_id MLOAD [off_ptr] [STRING #"%" (toString sa.cs_next_var)]) /\
    get_instruction bb (s.vs_inst_idx+1) =
      SOME (mk_inst (sa.cs_next_id+1) ADD
        [data_ptr; Var (STRING #"%" (toString sa.cs_next_var))]
        [STRING #"%" (toString (sa.cs_next_var+1))]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (sa.cs_next_id+2) MSTORE
        [Var (STRING #"%" (toString (sa.cs_next_var+1))); value] []) /\
    get_instruction bb (s.vs_inst_idx+3) =
      SOME (mk_inst (sa.cs_next_id+3) ADD
        [Var (STRING #"%" (toString sa.cs_next_var)); Lit (n2w m)]
        [STRING #"%" (toString (sa.cs_next_var+2))]) /\
    get_instruction bb (s.vs_inst_idx+4) =
      SOME (mk_inst (sa.cs_next_id+4) MSTORE
        [off_ptr; Var (STRING #"%" (toString (sa.cs_next_var+2)))] [])
Proof
  strip_tac >> drule compile_concat_fixed_layout >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >> simp[] >>
  first_x_assum (fn th => map_every (fn n => mp_tac (Q.SPEC n th))
    [`0`, `1`, `2`, `3`, `4`]) >> simp[]
QED

Theorem concat_bytes_cut_lookup:
  (do arg_len <- emit_op MLOAD [value];
      arg_data <- emit_op ADD [value; Lit 32w];
      offset_op <- emit_op MLOAD [off_ptr];
      dst <- emit_op ADD [data_ptr; offset_op];
      emit_void MCOPY [dst;arg_data;arg_len];
      new_offset <- emit_op ADD [offset_op;arg_len];
      emit_void MSTORE [off_ptr;new_offset]
   od) sa = ((),sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  sb.cs_current_bb = s.vs_current_bb /\
  LENGTH sb.cs_current_insts = s.vs_inst_idx + 7 /\
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst sa.cs_next_id MLOAD [value] [STRING #"%" (toString sa.cs_next_var)]) /\
    get_instruction bb (s.vs_inst_idx+1) =
      SOME (mk_inst (sa.cs_next_id+1) ADD [value;Lit 32w]
        [STRING #"%" (toString (sa.cs_next_var+1))]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (sa.cs_next_id+2) MLOAD [off_ptr]
        [STRING #"%" (toString (sa.cs_next_var+2))]) /\
    get_instruction bb (s.vs_inst_idx+3) =
      SOME (mk_inst (sa.cs_next_id+3) ADD
        [data_ptr;Var (STRING #"%" (toString (sa.cs_next_var+2)))]
        [STRING #"%" (toString (sa.cs_next_var+3))]) /\
    get_instruction bb (s.vs_inst_idx+4) =
      SOME (mk_inst (sa.cs_next_id+4) MCOPY
        [Var (STRING #"%" (toString (sa.cs_next_var+3)));
         Var (STRING #"%" (toString (sa.cs_next_var+1)));
         Var (STRING #"%" (toString sa.cs_next_var))] []) /\
    get_instruction bb (s.vs_inst_idx+5) =
      SOME (mk_inst (sa.cs_next_id+5) ADD
        [Var (STRING #"%" (toString (sa.cs_next_var+2)));
         Var (STRING #"%" (toString sa.cs_next_var))]
        [STRING #"%" (toString (sa.cs_next_var+4))]) /\
    get_instruction bb (s.vs_inst_idx+6) =
      SOME (mk_inst (sa.cs_next_id+6) MSTORE
        [off_ptr;Var (STRING #"%" (toString (sa.cs_next_var+4)))] [])
Proof
  strip_tac >> drule compile_concat_bytes_layout >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >> simp[] >>
  first_x_assum (fn th => map_every (fn n => mp_tac (Q.SPEC n th))
    [`0`, `1`, `2`, `3`, `4`, `5`, `6`]) >> simp[]
QED

(* Old operands stay distinct from every temporary in either arm, including
   when the lowering cut has moved past the original reservation cut. *)
Theorem reserved_name_generated_temp_distinct:
  not_fresh_at sa x /\ sa.cs_next_var <= sm.cs_next_var ==>
  !k. x <> STRING #"%" (toString (sm.cs_next_var+k))
Proof
  rw[compileEnvTheory.not_fresh_at_def] >>
  first_x_assum irule >> decide_tac
QED
