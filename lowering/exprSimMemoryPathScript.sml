(* Compiler and actual instruction boundaries for memory forcing. *)
Theory exprSimMemoryPath
Ancestors
  exprSimUnwrapProps emitHelperProps fragGasMode exprLoweringProps
  exprLowering context compileEnv loweringStateRelDefs freshWrites venomInst venomState emitHelper

Theorem unwrap_memory_compile:
  p.ptr_location = LocMemory ==>
  unwrap_value cenv (LocatedValue t p) =
    if is_word_type t then emit_op MLOAD [p.ptr_operand]
    else comp_return p.ptr_operand
Proof
  simp[unwrap_value_def, contextTheory.compile_ptr_load_def]
QED

Theorem unwrap_memory_extends:
  p.ptr_location = LocMemory /\
  unwrap_value cenv (LocatedValue t p) sa = (op,sb) ==>
  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id
Proof
  strip_tac >> gvs[unwrap_memory_compile] >>
  Cases_on `is_word_type t` >> gvs[comp_return_def] >>
  simp[cs_extends_refl] >>
  metis_tac[fragExecTheory.cs_appends_emit_helpers,
            fragExecTheory.cs_appends_def, ci_mono_emit_op, ci_mono_def,
            pairTheory.SND]
QED

Theorem emit_mload_marked_path:
  emit_op MLOAD [arg] sa = (op,sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand arg s = SOME w ==>
  gas_marked_path F ctx func s 0
    (OK ((update_var (STRING #"%" (toString sa.cs_next_var))
      (mload (w2n w) s) s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> pure_rewrite_tac[gas_marked_path_def, COND_CLAUSES] >>
  irule emit_op_zero_path >> simp[] >>
  qexistsl_tac [`[arg]`, `op`, `MLOAD`, `sb`] >>
  simp[step_MLOAD, is_terminator_def]
QED

Theorem emit_mload_endpoint:
  emit_op MLOAD [arg] sa = (op,sb) /\
  eval_operand arg s = SOME w /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    eval_operand op ((update_var (STRING #"%" (toString sa.cs_next_var))
      (mload (w2n w) s) s) with vs_inst_idx := SUC s.vs_inst_idx) = SOME (mload (w2n w) s) /\
    ((update_var (STRING #"%" (toString sa.cs_next_var))
      (mload (w2n w) s) s) with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb = sb.cs_current_bb /\
    ((update_var (STRING #"%" (toString sa.cs_next_var))
      (mload (w2n w) s) s) with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x w'. not_fresh_at sa x /\ lookup_var x s = SOME w' ==>
             lookup_var x ((update_var (STRING #"%" (toString sa.cs_next_var))
      (mload (w2n w) s) s) with vs_inst_idx := SUC s.vs_inst_idx) = SOME w') /\
    ((update_var (STRING #"%" (toString sa.cs_next_var))
      (mload (w2n w) s) s) with vs_inst_idx := SUC s.vs_inst_idx).vs_allocas = s.vs_allocas /\ ((update_var (STRING #"%" (toString sa.cs_next_var))
      (mload (w2n w) s) s) with vs_inst_idx := SUC s.vs_inst_idx).vs_memory = s.vs_memory
Proof
  simp[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
       comp_ignore_bind_def, comp_return_def, emit_def] >>
  rpt strip_tac >> gvs[eval_operand_def, update_var_def, lookup_var_def,
                        not_fresh_at_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED
