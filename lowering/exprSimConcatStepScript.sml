(*
 * The two arms of compile_concat's per-operand store, run as
 * straight-line code from any state whose input operands are defined:
 * a full-word MSTORE of a bytesM word at the running offset, or an MCOPY
 * of a bytestring's data, then the offset word bumped.  Only fresh
 * registers change besides memory.
 *
 * TOP-LEVEL:
 *   concat_fixed_step_run, concat_bytes_step_run
 *)
Theory exprSimConcatStep
Ancestors
  concatMemory allocaFootprint exprLoweringProps emitHelperProps emitHelper
  compileEnv venomInst venomState venomExecSemantics words arithmetic
  finite_map list
Libs
  monadsyntax

(* A register handed out before sa is none of the step's fresh outputs. *)
Theorem concat_operand_update_fresh:
  !op sa n w t.
    (!z. op = Var z ==> not_fresh_at sa z) /\ sa.cs_next_var <= n ==>
    eval_operand (op:operand) (update_var (STRING #"%" (toString n)) w t) =
    eval_operand op t
Proof
  Cases >> simp[eval_operand_def, lookup_var_update_var, not_fresh_at_def]
QED

Theorem concat_step_vars_frame[local]:
  !sa z V k w.
    not_fresh_at sa z ==>
    FLOOKUP (V |+ (STRING #"%" (toString sa.cs_next_var), w)) z = FLOOKUP V z /\
    FLOOKUP (V |+ (STRING #"%" (toString (sa.cs_next_var + k)), w)) z =
      FLOOKUP V z
Proof
  rpt strip_tac >> simp[FLOOKUP_UPDATE] >> IF_CASES_TAC >> simp[] >>
  gvs[not_fresh_at_def]
QED

(* Memory writes and register writes touch disjoint fields. *)
Theorem concat_mstore_with_vars[local]:
  !a w t V. mstore a w (t with vs_vars := V) = mstore a w t with vs_vars := V
Proof
  simp[mstore_def]
QED

Theorem concat_mcopy_with_vars[local]:
  !d src n t V. mcopy d src n (t with vs_vars := V) = mcopy d src n t with vs_vars := V
Proof
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem concat_mstore_vars[local]:
  !a w t. (mstore a w t).vs_vars = t.vs_vars
Proof
  simp[mstore_def]
QED

Theorem concat_mcopy_vars[local]:
  !d src n t. (mcopy d src n t).vs_vars = t.vs_vars
Proof
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem concat_mload_with_vars[local]:
  !a t V. mload a (t with vs_vars := V) = mload a t
Proof
  simp[mload_def]
QED

Theorem concat_fixed_step_run:
  !data_ptr off_ptr v m sa sb s dp off vw.
    (do offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr; offset_op];
        emit_void MSTORE [dst; v];
        new_offset <- emit_op ADD [offset_op; Lit (n2w m)];
        emit_void MSTORE [off_ptr; new_offset]
     od) sa = ((), sb) /\
    eval_operand data_ptr s = SOME dp /\ eval_operand off_ptr s = SOME off /\
    eval_operand v s = SOME vw /\
    (!z. data_ptr = Var z ==> not_fresh_at sa z) /\
    (!z. off_ptr = Var z ==> not_fresh_at sa z) /\
    (!z. v = Var z ==> not_fresh_at sa z) ==>
    ?V. run_inst_seq (emitted_insts sa sb) s =
          OK (mstore (w2n off) (mload (w2n off) s + n2w m)
                (mstore (w2n (dp + mload (w2n off) s)) vw s)
              with vs_vars := V) /\
        !z. not_fresh_at sa z ==> FLOOKUP V z = FLOOKUP s.vs_vars z
Proof
  rpt strip_tac >> drule concat_fixed_shape >> disch_then SUBST1_TAC >>
  qabbrev_tac `x0 = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `x1 = STRING #"%" (toString (sa.cs_next_var + 1))` >>
  qabbrev_tac `x2 = STRING #"%" (toString (sa.cs_next_var + 2))` >>
  qabbrev_tac `kw = mload (w2n off) s` >>
  `x0 <> x1 /\ x1 <> x2 /\ x0 <> x2` by
    simp[Abbr `x0`, Abbr `x1`, Abbr `x2`] >>
  `!op w t. (!z. op = Var z ==> not_fresh_at sa z) ==>
      eval_operand op (update_var x0 w t) = eval_operand op t /\
      eval_operand op (update_var x1 w t) = eval_operand op t /\
      eval_operand op (update_var x2 w t) = eval_operand op t` by
    (rpt strip_tac >> unabbrev_all_tac >>
     irule concat_operand_update_fresh >> qexists_tac `sa` >> simp[]) >>
  qabbrev_tac `s1 = update_var x0 kw s` >>
  `step_inst_base (mk_inst sa.cs_next_id MLOAD [off_ptr] [x0]) s = OK s1` by
    (simp[Abbr `s1`, Abbr `kw`] >> irule step_MLOAD >> simp[]) >>
  qabbrev_tac `s2 = update_var x1 (dp + kw) s1` >>
  `step_inst_base (mk_inst (sa.cs_next_id + 1) ADD [data_ptr; Var x0] [x1]) s1 =
     OK s2` by
    (simp[Abbr `s2`] >> irule step_ADD >>
     simp[Abbr `s1`, eval_operand_update_var]) >>
  qabbrev_tac `s3 = mstore (w2n (dp + kw)) vw s2` >>
  `step_inst_base (mk_inst (sa.cs_next_id + 2) MSTORE [Var x1; v] []) s2 =
     OK s3` by
    (simp[Abbr `s3`] >> irule step_MSTORE >>
     simp[Abbr `s2`, Abbr `s1`, eval_operand_update_var]) >>
  qabbrev_tac `s4 = update_var x2 (kw + n2w m) s3` >>
  `step_inst_base (mk_inst (sa.cs_next_id + 3) ADD [Var x0; Lit (n2w m)] [x2])
     s3 = OK s4` by
    (simp[Abbr `s4`] >> irule step_ADD >>
     simp[Abbr `s3`, Abbr `s2`, Abbr `s1`, eval_operand_def,
          lookup_var_update_var]) >>
  `step_inst_base (mk_inst (sa.cs_next_id + 4) MSTORE [off_ptr; Var x2] []) s4 =
     OK (mstore (w2n off) (kw + n2w m) s4)` by
    (irule step_MSTORE >>
     simp[Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`, eval_operand_update_var]) >>
  simp[run_inst_seq_def] >>
  qexists_tac `s.vs_vars |+ (x0,kw) |+ (x1,dp + kw) |+ (x2,kw + n2w m)` >>
  conj_tac
  >- simp[Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`, update_var_def,
          concat_mstore_with_vars, concat_mstore_vars] >>
  rpt strip_tac >> unabbrev_all_tac >>
  simp[concat_step_vars_frame]
QED

Theorem concat_bytes_step_run:
  !mem_ptr data_ptr off_ptr sa sb s src dp off.
    (do arg_len <- emit_op MLOAD [mem_ptr];
        arg_data <- emit_op ADD [mem_ptr; Lit 32w];
        offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr; offset_op];
        emit_void MCOPY [dst; arg_data; arg_len];
        new_offset <- emit_op ADD [offset_op; arg_len];
        emit_void MSTORE [off_ptr; new_offset]
     od) sa = ((), sb) /\
    eval_operand mem_ptr s = SOME src /\
    eval_operand data_ptr s = SOME dp /\ eval_operand off_ptr s = SOME off /\
    (!z. mem_ptr = Var z ==> not_fresh_at sa z) /\
    (!z. data_ptr = Var z ==> not_fresh_at sa z) /\
    (!z. off_ptr = Var z ==> not_fresh_at sa z) ==>
    ?V. run_inst_seq (emitted_insts sa sb) s =
          OK (mstore (w2n off) (mload (w2n off) s + mload (w2n src) s)
                (mcopy (w2n (dp + mload (w2n off) s)) (w2n (src + 32w))
                   (w2n (mload (w2n src) s)) s)
              with vs_vars := V) /\
        !z. not_fresh_at sa z ==> FLOOKUP V z = FLOOKUP s.vs_vars z
Proof
  rpt strip_tac >> drule concat_bytes_shape >> disch_then SUBST1_TAC >>
  qabbrev_tac `x0 = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `x1 = STRING #"%" (toString (sa.cs_next_var + 1))` >>
  qabbrev_tac `x2 = STRING #"%" (toString (sa.cs_next_var + 2))` >>
  qabbrev_tac `x3 = STRING #"%" (toString (sa.cs_next_var + 3))` >>
  qabbrev_tac `x4 = STRING #"%" (toString (sa.cs_next_var + 4))` >>
  qabbrev_tac `lw = mload (w2n src) s` >>
  qabbrev_tac `kw = mload (w2n off) s` >>
  `x0 <> x1 /\ x0 <> x2 /\ x0 <> x3 /\ x0 <> x4 /\ x1 <> x2 /\ x1 <> x3 /\
   x1 <> x4 /\ x2 <> x3 /\ x2 <> x4 /\ x3 <> x4` by
    simp[Abbr `x0`, Abbr `x1`, Abbr `x2`, Abbr `x3`, Abbr `x4`] >>
  `!op w t. (!z. op = Var z ==> not_fresh_at sa z) ==>
      eval_operand op (update_var x0 w t) = eval_operand op t /\
      eval_operand op (update_var x1 w t) = eval_operand op t /\
      eval_operand op (update_var x2 w t) = eval_operand op t /\
      eval_operand op (update_var x3 w t) = eval_operand op t /\
      eval_operand op (update_var x4 w t) = eval_operand op t` by
    (rpt strip_tac >> unabbrev_all_tac >>
     irule concat_operand_update_fresh >> qexists_tac `sa` >> simp[]) >>
  qabbrev_tac `s1 = update_var x0 lw s` >>
  `step_inst_base (mk_inst sa.cs_next_id MLOAD [mem_ptr] [x0]) s = OK s1` by
    (simp[Abbr `s1`, Abbr `lw`] >> irule step_MLOAD >> simp[]) >>
  qabbrev_tac `s2 = update_var x1 (src + 32w) s1` >>
  `step_inst_base (mk_inst (sa.cs_next_id + 1) ADD [mem_ptr; Lit 32w] [x1]) s1 =
     OK s2` by
    (simp[Abbr `s2`] >> irule step_ADD >> simp[Abbr `s1`, eval_operand_def]) >>
  `mload (w2n off) s2 = kw` by
    simp[Abbr `s2`, Abbr `s1`, Abbr `kw`, mload_def, update_var_def] >>
  qabbrev_tac `s3 = update_var x2 kw s2` >>
  `step_inst_base (mk_inst (sa.cs_next_id + 2) MLOAD [off_ptr] [x2]) s2 = OK s3` by
    (simp[Abbr `s3`] >>
     qpat_x_assum `mload _ s2 = kw` (SUBST1_TAC o SYM) >>
     irule step_MLOAD >> simp[Abbr `s2`, Abbr `s1`]) >>
  qabbrev_tac `s4 = update_var x3 (dp + kw) s3` >>
  `step_inst_base (mk_inst (sa.cs_next_id + 3) ADD [data_ptr; Var x2] [x3]) s3 =
     OK s4` by
    (simp[Abbr `s4`] >> irule step_ADD >>
     simp[Abbr `s3`, Abbr `s2`, Abbr `s1`, eval_operand_update_var]) >>
  `eval_operand (Var x0) s4 = SOME lw /\ eval_operand (Var x1) s4 = SOME (src + 32w) /\
   eval_operand (Var x2) s4 = SOME kw /\ eval_operand (Var x3) s4 = SOME (dp + kw) /\
   eval_operand off_ptr s4 = SOME off` by
    simp[Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`, eval_operand_def,
         lookup_var_update_var] >>
  qabbrev_tac `s5 = mcopy (w2n (dp + kw)) (w2n (src + 32w)) (w2n lw) s4` >>
  `step_inst_base (mk_inst (sa.cs_next_id + 4) MCOPY [Var x3; Var x1; Var x0] [])
     s4 = OK s5` by
    simp[Abbr `s5`, step_inst_base_opcode_eqs, mk_inst_def] >>
  `!op. eval_operand op s5 = eval_operand op s4` by
    (gen_tac >> simp[Abbr `s5`] >> irule eval_operand_same_vars >>
     simp[mcopy_def, write_memory_with_expansion_def]) >>
  qabbrev_tac `s6 = update_var x4 (kw + lw) s5` >>
  `step_inst_base (mk_inst (sa.cs_next_id + 5) ADD [Var x2; Var x0] [x4]) s5 =
     OK s6` by
    (simp[Abbr `s6`] >> irule step_ADD >> simp[]) >>
  `step_inst_base (mk_inst (sa.cs_next_id + 6) MSTORE [off_ptr; Var x4] []) s6 =
     OK (mstore (w2n off) (kw + lw) s6)` by
    (irule step_MSTORE >>
     simp[Abbr `s6`, eval_operand_update_var]) >>
  simp[run_inst_seq_def] >>
  qexists_tac `s.vs_vars |+ (x0,lw) |+ (x1,src + 32w) |+ (x2,kw) |+
                 (x3,dp + kw) |+ (x4,kw + lw)` >>
  conj_tac
  >- simp[Abbr `s6`, Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`,
          update_var_def, concat_mstore_with_vars, concat_mstore_vars,
          concat_mcopy_with_vars, concat_mcopy_vars] >>
  rpt strip_tac >> unabbrev_all_tac >>
  simp[concat_step_vars_frame]
QED
