(* Raw execution deliberately includes checked narrowing and m=0.
   Typed consumer audit: valid_conversion (vyperTypeSystem) requires
   bits <= 8*m for BOTH IntT and UintT to fixed bytes. Thus its valid
   integer inputs never execute the assertion prefix; positive source bits
   also exclude m=0. evaluate_convert's IntV/Fixed arm returns the low m
   bytes unconditionally when m<=32. The remaining typed bridge needs
   typing inversion, mk_convert_op normalization and
   convertScalarEncoding.scalar_word_to_fixed, not a narrowing range lemma. *)
Theory bodyPtrTypeBuiltinsIntegerBytesRun
Ancestors bodyPtrTypeBuiltinsCheckedArithmetic bodyPtrTypeBuiltinsScalarCompose
  exprLowering exprLoweringProps
  emitHelperProps compileEnv venomExecSemantics venomState venomInst
  words list finite_map arithmetic

Theorem integer_bytes_signed_prefix:
  eval_operand x s = SOME w /\ (!z. x = Var z ==> z <> a /\ z <> b) ==>
  ?t. run_inst_seq
    [mk_inst id SIGNEXTEND [Lit index;x] [a];
     mk_inst (id+1) EQ [x;Var a] [b]; mk_inst (id+2) ASSERT [Var b] []] s =
    (if sign_extend index w = w then OK t else Abort Revert_abort t) /\
    eval_operand x t = SOME w
Proof
  strip_tac >>
  `eval_operand x (update_var a (sign_extend index w) s) = SOME w` by
    (irule eval_operand_update_var_mstore >> simp[] >> metis_tac[]) >>
  rewrite_tac[run_inst_seq_def] >>
  pure_rewrite_tac[step_inst_base_def, mk_inst_def, instruction_accfupds,
    instruction_accessors, combinTheory.K_THM, opcode_case_def] >>
  simp[mk_inst_def, exec_pure2_def, eval_operand_def,
       eval_operand_update_var] >>
  Cases_on `sign_extend index w = w` >>
  Cases_on `x` >> gvs[eval_operand_def, lookup_var_def] >>
  gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
      bool_to_word_def, revert_state_def, set_returndata_def]
QED

Theorem integer_bytes_unsigned_prefix:
  eval_operand x s = SOME w /\ (!z. x = Var z ==> z <> a /\ z <> b) ==>
  ?t. run_inst_seq
    [mk_inst id GT [x;Lit hi] [a];
     mk_inst (id+1) ISZERO [Var a] [b]; mk_inst (id+2) ASSERT [Var b] []] s =
    (if w2n w <= w2n hi then OK t else Abort Revert_abort t) /\
    eval_operand x t = SOME w
Proof
  strip_tac >> rewrite_tac[run_inst_seq_def] >>
  pure_rewrite_tac[step_inst_base_def, mk_inst_def, instruction_accfupds,
    instruction_accessors, combinTheory.K_THM, opcode_case_def] >>
  simp[mk_inst_def, exec_pure2_def, exec_pure1_def, eval_operand_def,
       eval_operand_update_var] >>
  Cases_on `w2n w <= w2n hi` >>
  Cases_on `x` >> gvs[eval_operand_def, lookup_var_def] >>
  gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
      bool_to_word_def, revert_state_def, set_returndata_def]
QED

Theorem integer_bytes_shift_run:
  emit_op SHL [Lit (n2w (8*(32-m)));x] sa = (out,sb) /\
  m <= 32 /\ eval_operand x s = SOME w ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand out t = SOME (w << (8*(32-m)))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[] >> rewrite_tac[run_inst_seq_def] >>
  `w2n (n2w (8*(32-m)):bytes32) = 8*(32-m)` by
    simp[dimword_def] >>
  pure_rewrite_tac[step_inst_base_def, mk_inst_def, instruction_accfupds,
    instruction_accessors, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE]
QED

Theorem integer_bytes_prefix_run:
  (if 8*m < bits then
     ?a b. emitted_insts sa mid =
       (if sg then
         [mk_inst sa.cs_next_id SIGNEXTEND [Lit (n2w (m-1));x] [a];
          mk_inst (sa.cs_next_id+1) EQ [x;Var a] [b];
          mk_inst (sa.cs_next_id+2) ASSERT [Var b] []]
        else
         [mk_inst sa.cs_next_id GT [x;Lit (n2w (2 ** (8*m)-1))] [a];
          mk_inst (sa.cs_next_id+1) ISZERO [Var a] [b];
          mk_inst (sa.cs_next_id+2) ASSERT [Var b] []]) /\
       (!p. not_fresh_at sa p ==> p <> a /\ p <> b)
   else mid = sa) /\
  eval_operand x s = SOME w /\ (!z. x = Var z ==> not_fresh_at sa z) ==>
  ?t. run_inst_seq (emitted_insts sa mid) s =
    (if 8*m < bits /\
        ~(if sg then sign_extend (n2w (m-1)) w = w
          else w2n w <= w2n (n2w (2 ** (8*m)-1):bytes32))
     then Abort Revert_abort t else OK t) /\ eval_operand x t = SOME w
Proof
  Cases_on `8*m < bits` >> simp[] >> strip_tac
  >- (Cases_on `sg` >> gvs[]
      >- (`!z. x = Var z ==> z <> a /\ z <> b` by metis_tac[] >>
          drule_all integer_bytes_signed_prefix >>
          disch_then (qspecl_then [`n2w (m-1)`,`sa.cs_next_id`] mp_tac) >>
          Cases_on `sign_extend (n2w (m-1)) w = w` >> simp[]) >>
      `!z. x = Var z ==> z <> a /\ z <> b` by metis_tac[] >>
      drule_all integer_bytes_unsigned_prefix >>
      disch_then (qspecl_then [`sa.cs_next_id`,`n2w (2 ** (8*m)-1)`] mp_tac) >>
      Cases_on `w2n w <= w2n (n2w (2 ** (8*m)-1):bytes32)` >> gvs[]) >>
  gvs[emitted_insts_def, run_inst_seq_def]
QED

Theorem integer_bytes_actual_run:
  compile_type_convert x (ConvIntToBytesM sg bits m) sa = (out,sb) /\
  m <= 32 /\ eval_operand x s = SOME w /\
  (!z. x = Var z ==> not_fresh_at sa z) ==>
  if bits <= 8*m \/
     (if sg then sign_extend (n2w (m-1)) w = w
      else w2n w <= w2n (n2w (2 ** (8*m)-1):bytes32)) then
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand out t = SOME (w << (8*(32-m))) /\
      (t with vs_vars := s.vs_vars) = s /\
      (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s)
  else ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  strip_tac >> drule convert_int_bytes_decompose >> strip_tac >> fs[] >>
  drule_all integer_bytes_prefix_run >> strip_tac >>
  Cases_on `bits <= 8*m \/
     (if sg then sign_extend (n2w (m-1)) w = w
      else w2n w <= w2n (n2w (2 ** (8*m)-1):bytes32))` >> simp[]
  >- (`~(8*m < bits /\
         ~(if sg then sign_extend (n2w (m-1)) w = w
           else w2n w <= w2n (n2w (2 ** (8*m)-1):bytes32)))` by metis_tac[NOT_LESS] >>
      fs[] >> drule_all integer_bytes_shift_run >> strip_tac >>
      `run_inst_seq (emitted_insts sa sb) s = OK t'` by
        (asm_rewrite_tac[] >> simp[bodyPtrBopHashSuffixTheory.bop_run_inst_seq_append_ok] >> metis_tac[]) >>
      drule_all convert_int_bytes_runtime_frame >> strip_tac >>
      qexists_tac `t'` >> metis_tac[]) >>
  `8*m < bits /\
   ~(if sg then sign_extend (n2w (m-1)) w = w
     else w2n w <= w2n (n2w (2 ** (8*m)-1):bytes32))` by metis_tac[NOT_LESS] >>
  gvs[] >> qexists_tac `t` >> asm_rewrite_tac[] >>
  simp[scalar_seq_append_abort_iff]
QED
