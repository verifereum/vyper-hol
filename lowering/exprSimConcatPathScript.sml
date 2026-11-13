(*
 * Concat case: each arm of the per-operand store as a gas path.
 *
 * TOP-LEVEL:
 *   concat_fixed_step_path, concat_bytes_step_path — each arm's store as a
 *     gas_path with no GAS reads
 *)
Theory exprSimConcatPath
Ancestors
  exprSimConcatStep exprSimConcatStore concatMemory fragGasSeq fragGasPath
  fragExec exprLowering exprLoweringProps emitHelperProps emitHelper context
  compileEnv
  venomInst venomState venomExecSemantics words arithmetic list rich_list
Libs
  monadsyntax

Theorem concat_fixed_code_shape:
  (do offset_op <- emit_op MLOAD [off_ptr];
      dst <- emit_op ADD [data_ptr; offset_op];
      emit_void MSTORE [dst; v];
      new_offset <- emit_op ADD [offset_op; Lit (n2w m)];
      emit_void MSTORE [off_ptr; new_offset]
   od) sa = ((), sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb
Proof
  simp[comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND]
QED

Theorem concat_bytes_code_shape:
  (do arg_len <- emit_op MLOAD [mem_ptr];
      arg_data <- emit_op ADD [mem_ptr; Lit 32w];
      offset_op <- emit_op MLOAD [off_ptr];
      dst <- emit_op ADD [data_ptr; offset_op];
      emit_void MCOPY [dst; arg_data; arg_len];
      new_offset <- emit_op ADD [offset_op; arg_len];
      emit_void MSTORE [off_ptr; new_offset]
   od) sa = ((), sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb
Proof
  simp[comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND]
QED

Theorem concat_code_prefix:
  fn_has_code sa sb func /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >> gvs[fn_has_code_def, IS_PREFIX_APPEND] >> simp[DROP_APPEND]
QED

Theorem concat_fixed_step_path:
  !data_ptr off_ptr v m sa sb s dp off vw ctx func.
    (do offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr; offset_op];
        emit_void MSTORE [dst; v];
        new_offset <- emit_op ADD [offset_op; Lit (n2w m)];
        emit_void MSTORE [off_ptr; new_offset]
     od) sa = ((), sb) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    eval_operand data_ptr s = SOME dp /\ eval_operand off_ptr s = SOME off /\
    eval_operand v s = SOME vw /\
    (!z. data_ptr = Var z ==> not_fresh_at sa z) /\
    (!z. off_ptr = Var z ==> not_fresh_at sa z) /\
    (!z. v = Var z ==> not_fresh_at sa z) ==>
    ?V. gas_path ctx func s 0
          (OK (mstore (w2n off) (mload (w2n off) s + n2w m)
                 (mstore (w2n (dp + mload (w2n off) s)) vw s) with
               <|vs_vars := V; vs_inst_idx := LENGTH sb.cs_current_insts|>)) /\
        !z. not_fresh_at sa z ==> FLOOKUP V z = FLOOKUP s.vs_vars z
Proof
  rpt strip_tac >>
  drule_all concat_fixed_step_run >> strip_tac >>
  qexists_tac `V` >> simp[] >>
  drule concat_fixed_code_shape >> strip_tac >>
  drule_all concat_code_prefix >> strip_tac >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  drule concat_fixed_shape >> strip_tac >> gvs[] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem concat_bytes_step_path:
  !mem_ptr data_ptr off_ptr sa sb s src dp off ctx func.
    (do arg_len <- emit_op MLOAD [mem_ptr];
        arg_data <- emit_op ADD [mem_ptr; Lit 32w];
        offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr; offset_op];
        emit_void MCOPY [dst; arg_data; arg_len];
        new_offset <- emit_op ADD [offset_op; arg_len];
        emit_void MSTORE [off_ptr; new_offset]
     od) sa = ((), sb) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    eval_operand mem_ptr s = SOME src /\
    eval_operand data_ptr s = SOME dp /\ eval_operand off_ptr s = SOME off /\
    (!z. mem_ptr = Var z ==> not_fresh_at sa z) /\
    (!z. data_ptr = Var z ==> not_fresh_at sa z) /\
    (!z. off_ptr = Var z ==> not_fresh_at sa z) ==>
    ?V. gas_path ctx func s 0
          (OK (mstore (w2n off) (mload (w2n off) s + mload (w2n src) s)
                 (mcopy (w2n (dp + mload (w2n off) s)) (w2n (src + 32w))
                    (w2n (mload (w2n src) s)) s) with
               <|vs_vars := V; vs_inst_idx := LENGTH sb.cs_current_insts|>)) /\
        !z. not_fresh_at sa z ==> FLOOKUP V z = FLOOKUP s.vs_vars z
Proof
  rpt strip_tac >>
  drule_all concat_bytes_step_run >> strip_tac >>
  qexists_tac `V` >> simp[] >>
  drule concat_bytes_code_shape >> strip_tac >>
  drule_all concat_code_prefix >> strip_tac >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  drule concat_bytes_shape >> strip_tac >> gvs[] >>
  simp[mk_inst_def, is_terminator_def]
QED

(* compile_concat's arms run the store, then the rest of the loop. *)
Theorem concat_fixed_split:
  (do offset_op <- emit_op MLOAD [off_ptr];
      dst <- emit_op ADD [data_ptr; offset_op];
      emit_void MSTORE [dst; v];
      new_offset <- emit_op ADD [offset_op; Lit (n2w m)];
      emit_void MSTORE [off_ptr; new_offset];
      rest
   od) sa = (x, sb) ==>
  ?s2. (do offset_op <- emit_op MLOAD [off_ptr];
           dst <- emit_op ADD [data_ptr; offset_op];
           emit_void MSTORE [dst; v];
           new_offset <- emit_op ADD [offset_op; Lit (n2w m)];
           emit_void MSTORE [off_ptr; new_offset]
        od) sa = ((), s2) /\ rest s2 = (x, sb)
Proof
  simp[comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def]
QED

Theorem concat_bytes_split:
  (do arg_len <- emit_op MLOAD [mem_ptr];
      arg_data <- emit_op ADD [mem_ptr; Lit 32w];
      offset_op <- emit_op MLOAD [off_ptr];
      dst <- emit_op ADD [data_ptr; offset_op];
      emit_void MCOPY [dst; arg_data; arg_len];
      new_offset <- emit_op ADD [offset_op; arg_len];
      emit_void MSTORE [off_ptr; new_offset];
      rest
   od) sa = (x, sb) ==>
  ?s2. (do arg_len <- emit_op MLOAD [mem_ptr];
           arg_data <- emit_op ADD [mem_ptr; Lit 32w];
           offset_op <- emit_op MLOAD [off_ptr];
           dst <- emit_op ADD [data_ptr; offset_op];
           emit_void MCOPY [dst; arg_data; arg_len];
           new_offset <- emit_op ADD [offset_op; arg_len];
           emit_void MSTORE [off_ptr; new_offset]
        od) sa = ((), s2) /\ rest s2 = (x, sb)
Proof
  simp[comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def]
QED

(* One operand of compile_concat: its value, its store arm, the rest. *)
Theorem compile_concat_bytes_cons:
  compile_concat cfn cenv (e::es) data_ptr ((T,m)::infos) off_ptr sa = (x, sb) ==>
  ?mem_ptr s1 s2.
    lower_value cfn cenv (expr_type e) e sa = (mem_ptr, s1) /\
    (do arg_len <- emit_op MLOAD [mem_ptr];
        arg_data <- emit_op ADD [mem_ptr; Lit 32w];
        offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr; offset_op];
        emit_void MCOPY [dst; arg_data; arg_len];
        new_offset <- emit_op ADD [offset_op; arg_len];
        emit_void MSTORE [off_ptr; new_offset]
     od) s1 = ((), s2) /\
    compile_concat cfn cenv es data_ptr infos off_ptr s2 = (x, sb)
Proof
  simp[compile_concat_def, Once comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> drule concat_bytes_split >> strip_tac >> metis_tac[]
QED

Theorem compile_concat_fixed_cons:
  compile_concat cfn cenv (e::es) data_ptr ((F,m)::infos) off_ptr sa = (x, sb) ==>
  ?v s1 s2.
    lower_value cfn cenv (expr_type e) e sa = (v, s1) /\
    (do offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr; offset_op];
        emit_void MSTORE [dst; v];
        new_offset <- emit_op ADD [offset_op; Lit (n2w m)];
        emit_void MSTORE [off_ptr; new_offset]
     od) s1 = ((), s2) /\
    compile_concat cfn cenv es data_ptr infos off_ptr s2 = (x, sb)
Proof
  simp[compile_concat_def, Once comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> drule concat_fixed_split >> strip_tac >> metis_tac[]
QED
