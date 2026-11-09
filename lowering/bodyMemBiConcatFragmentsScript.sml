(* Memory-counted paths for concat operand stores. *)
Theory bodyMemBiConcatFragments
Ancestors
  exprSimConcatPath exprSimConcatStep concatMemory fragGasSeqMem loweringStateRelDefs
  emitHelper venomInst exprSimConcatResult instMemFrontier
  venomExecSemantics exprLoweringProps venomState fragExecMem
  allocaFootprint compileEnv emitHelperProps
Libs
  monadsyntax

Theorem concat_fixed_step_path_mem:
  !data_ptr off_ptr v m sa sb s dp off vw ctx func.
    (do offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr; offset_op];
        emit_void MSTORE [dst; v];
        new_offset <- emit_op ADD [offset_op; Lit (n2w m)];
        emit_void MSTORE [off_ptr; new_offset]
     od) sa = ((), sb) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\ fresh_vars_wrt sa s /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    eval_operand data_ptr s = SOME dp /\ eval_operand off_ptr s = SOME off /\
    eval_operand v s = SOME vw /\
    (!z. data_ptr = Var z ==> not_fresh_at sa z) /\
    (!z. off_ptr = Var z ==> not_fresh_at sa z) /\
    (!z. v = Var z ==> not_fresh_at sa z) /\
    w2n off + 32 <= s.vs_alloca_next /\
    w2n dp + w2n (mload (w2n off) s) + 32 <= s.vs_alloca_next ==>
    ?V. gas_path_mem ctx func s 0
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
  drule_all compile_concat_fixed_step_mem_ok >> strip_tac >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) run_inst_seq_gas_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  drule concat_fixed_shape >> strip_tac >>
  gvs[mk_inst_def, is_terminator_def]
QED

Theorem concat_bytes_step_path_mem:
  !mem_ptr data_ptr off_ptr sa sb s src dp off ctx func.
    (do arg_len <- emit_op MLOAD [mem_ptr];
        arg_data <- emit_op ADD [mem_ptr; Lit 32w];
        offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr; offset_op];
        emit_void MCOPY [dst; arg_data; arg_len];
        new_offset <- emit_op ADD [offset_op; arg_len];
        emit_void MSTORE [off_ptr; new_offset]
     od) sa = ((), sb) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\ fresh_vars_wrt sa s /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    eval_operand mem_ptr s = SOME src /\
    eval_operand data_ptr s = SOME dp /\ eval_operand off_ptr s = SOME off /\
    (!z. mem_ptr = Var z ==> not_fresh_at sa z) /\
    (!z. data_ptr = Var z ==> not_fresh_at sa z) /\
    (!z. off_ptr = Var z ==> not_fresh_at sa z) /\
    w2n src + 32 + w2n (mload (w2n src) s) <= s.vs_alloca_next /\
    w2n off + 32 <= s.vs_alloca_next /\
    w2n dp + w2n (mload (w2n off) s) + w2n (mload (w2n src) s)
      <= s.vs_alloca_next ==>
    ?V. gas_path_mem ctx func s 0
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
  drule_all compile_concat_bytes_step_mem_ok >> strip_tac >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) run_inst_seq_gas_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  drule concat_bytes_shape >> strip_tac >>
  gvs[mk_inst_def, is_terminator_def]
QED

Theorem concat_suffix_mem_ok:
  !ov bv sa fo sm u sb s ow bw.
    emit_op MLOAD [Var ov] sa = (fo, sm) /\
    emit_void MSTORE [Var bv; fo] sm = (u, sb) /\
    lookup_var ov s = SOME ow /\ lookup_var bv s = SOME bw /\
    not_fresh_at sa bv /\
    w2n ow + 32 <= s.vs_alloca_next /\
    w2n bw + 32 <= s.vs_alloca_next ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >> drule_all concat_suffix_code >> strip_tac >>
  `bv <> STRING #"%" (toString sa.cs_next_var)` by
    fs[not_fresh_at_def] >>
  gvs[Once run_inst_seq_mem_ok_cons, below_frontier_MLOAD,
      eval_operand_def] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE,
       eval_operand_def, lookup_var_update_var]
QED

Theorem concat_suffix_path_mem:
  !ov bv sa fo sm u sb s ow bw ctx func.
    emit_op MLOAD [Var ov] sa = (fo, sm) /\
    emit_void MSTORE [Var bv; fo] sm = (u, sb) /\
    lookup_var ov s = SOME ow /\ lookup_var bv s = SOME bw /\
    not_fresh_at sa bv /\
    w2n ow + 32 <= s.vs_alloca_next /\
    w2n bw + 32 <= s.vs_alloca_next /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_path_mem ctx func s 0
      (OK (mstore (w2n bw) (mload (w2n ow) s)
            (update_var (STRING #"%" (toString sa.cs_next_var))
              (mload (w2n ow) s) s) with
            vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  rpt strip_tac >>
  drule_all concat_suffix_run >> strip_tac >>
  drule_all concat_suffix_mem_ok >> strip_tac >>
  drule_all concat_suffix_code >> strip_tac >>
  drule_all concat_code_prefix >> strip_tac >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) run_inst_seq_gas_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  gvs[mk_inst_def, is_terminator_def]
QED
