(* Signed conversion origins on the actual child state. *)
Theory bodyFullConvertSignedOrigin
Ancestors
  bodyFullConvertBytesWordSuffix bodyFullConvertSignedLoader
  bodyFullConvertSignedClamp exprSimConvertFromBytes exprLowering
  builtinConvertPrefix exprLoweringProps compileEnv finite_map words arithmetic list

(* Semantic actualization is the destination-generic
   bytes_word_conversion_run_actual, including signed and empty inputs. *)
Theorem decimal_compiler_signed_normalize[local]:
  (i2w lower : bytes32) = i2w (- &(2 ** (168-1))) /\
  (i2w upper : bytes32) = i2w (&(2 ** (168-1)-1)) ==>
  compile_type_convert x (ConvBytestringToDecimal divisor lower upper n) =
  compile_type_convert x (ConvBytestringToInt T 168 n)
Proof
  strip_tac >>
  simp[compile_type_convert_def, compile_int_clamp_def] >>
  Cases_on `n*8 <= 168` >> simp[]
QED

Theorem signed_compiler_normalize[local]:
  is_bytestring_type src /\
  ((?k. dst = BaseT (IntT k)) \/ dst = BaseT DecimalT) ==>
  ?b n. compile_type_convert x (mk_convert_op src dst) =
    compile_type_convert x (ConvBytestringToInt T b n)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac)
  >- (gvs[mk_convert_op_def] >> metis_tac[]) >>
  gvs[mk_convert_op_def, type_bounds_def, type_bits_def, is_signed_type_def] >>
  qexistsl [`168`,`case src of BaseT (BytesT (Dynamic n)) => n |
    BaseT (StringT n) => n | _ => 0`] >>
  irule decimal_compiler_signed_normalize >> simp[]
QED
