(* Shared SHR/SHL interface for dynamic bytes and String fixed-byte results. *)
Theory bodyPtrTypeBuiltinsFixedContinue
Ancestors bodyPtrTypeBuiltinsUintContinue bodyPtrTypeBuiltinsUnsignedValue
  bodyPtrTypeBuiltinsUnsignedSemantics bodyPtrTypeBuiltinsScalarArithmetic
  exprLowering exprLoweringProps builtinConvertPrefix emitHelperProps
  compileEnv vyperTypeSystem vyperValue venomExecSemantics venomState venomInst
  fragExec finite_map list

Theorem dynamic_scalar_conversion_partition:
  is_bytestring_type src /\ valid_conversion src dst /\
  ~is_bytestring_type dst /\ (!b. dst <> BaseT (IntT b)) /\ dst <> BaseT DecimalT ==>
  (?n. src = BaseT (BytesT (Dynamic n)) /\
       ((?b. dst = BaseT (UintT b)) \/ dst = BaseT BoolT \/
        dst = BaseT AddressT \/ (?m. dst = BaseT (BytesT (Fixed m))))) \/
  (?n m. src = BaseT (StringT n) /\ dst = BaseT (BytesT (Fixed m)))
Proof
  Cases_on `src` >> gvs[is_bytestring_type_def] >>
  Cases_on `b` >> gvs[is_bytestring_type_def] >>
  Cases_on `dst` >> gvs[valid_conversion_def, is_bytestring_type_def] >>
  Cases_on `b` >> gvs[valid_conversion_def, is_bytestring_type_def] >>
  Cases_on `b'` >> gvs[valid_conversion_def, is_bytestring_type_def] >>
  Cases_on `b''` >> gvs[valid_conversion_def, is_bytestring_type_def]
QED

Theorem bytestring_fixed_convert_parts:
  compile_type_convert x (ConvBytestringToBytesM m) sa = (out,sb) ==>
  ?word bits sm.
    load_bytestring_as_word x SHR sa = ((word,bits),sm) /\
    emitHelper$emit_op SHL [bits;word] sm = (out,sb) /\
    inst_extends sa sm /\ inst_extends sm sb
Proof
  simp_tac pure_ss [compile_type_convert_def, comp_bind_def, comp_return_def,
                   LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[inst_extends_load_bytestring_as_word, inst_extends_emit_op]
QED

Theorem fixed_shl_run_actual:
  emitHelper$emit_op SHL [bits;word] sa = (out,sb) /\
  eval_operand bits s = SOME k /\ eval_operand word s = SOME w ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand out t = SOME (word_lsl w (w2n k)) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id SHL [bits;word]
     [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
      (word_lsl w (w2n k)) s)` by (irule step_SHL >> simp[]) >>
  `run_inst_seq (emitted_insts sa sb) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
      (word_lsl w (w2n k)) s)` by simp[run_inst_seq_def] >>
  `MEM SHL [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV]` by simp[] >>
  drule_all scalar_emit_runtime_frame >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED
