Theory bodyPtrPrecompileBuiltinsArithmeticValue
Ancestors bodyPtrPrecompileBuiltinsArithmeticSource exprSimPrecompiles
          extCallOracle vfmExecution bn254 vfmBuffer vfmTypes byte list rich_list
          valueEncoding valueEncodingProps valueEncodingProofs loweringPosts
          exprLowering exprSimDefs compileEnv vyperValue vyperValueOperation vyperTypeBuiltins vyperContext
          bodyPtrDefs ptrCoverage representationCleanPtr

Theorem ec_precompile_words:
  (!x1 y1 x2 y2.
  precompile_result 6w
    (word_to_bytes (x1:bytes32) T ++ word_to_bytes (y1:bytes32) T ++
     word_to_bytes (x2:bytes32) T ++ word_to_bytes (y2:bytes32) T) =
  SOME (OPTION_MAP (\(x,y).
    PAD_LEFT 0w 32 (num_to_be_bytes x) ++ PAD_LEFT 0w 32 (num_to_be_bytes y))
    (vfmExecution$ecadd (w2n x1,w2n y1) (w2n x2,w2n y2)))) /\
  (!x y n.
  precompile_result 7w
    (word_to_bytes (x:bytes32) T ++ word_to_bytes (y:bytes32) T ++
     word_to_bytes (n:bytes32) T) =
  SOME (OPTION_MAP (\(x,y).
    PAD_LEFT 0w 32 (num_to_be_bytes x) ++ PAD_LEFT 0w 32 (num_to_be_bytes y))
    (vfmExecution$ecmul (w2n x,w2n y) (w2n n))))
Proof
  conj_tac >> rpt gen_tac >>
  rewrite_tac[precompile_result_ecadd, precompile_result_ecmul,
              SRULE [] (Q.INST [`n` |-> `0`] drop_word_prefix),
              SRULE [] (Q.INST [`n` |-> `32`] drop_word_prefix),
              SRULE [] (Q.INST [`n` |-> `64`] drop_word_prefix),
              take_pad_word_prefix] >>
  simp[take_pad_0_def, LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``, listTheory.TAKE_APPEND1,
       listTheory.DROP_APPEND, listTheory.TAKE_LENGTH_TOO_LONG,
       listTheory.DROP_LENGTH_TOO_LONG, PAD_RIGHT,
       num_of_be_bytes_word32, word_to_bytes_word_of_bytes_32,
       word_of_bytes_be_def]
QED

Theorem ecadd_success_bounds:
  vfmExecution$ecadd a b = SOME (x,y) ==> x < 2 ** 256 /\ y < 2 ** 256
Proof
  simp[vfmExecutionTheory.ecadd_def, AllCaseEqs()] >> strip_tac >>
  mp_tac (Q.SPECL [`a`, `b`] addAffine_bounded) >> gvs[]
QED

Theorem ecmul_success_bounds:
  vfmExecution$ecmul a n = SOME (x,y) ==> x < 2 ** 256 /\ y < 2 ** 256
Proof
  simp[vfmExecutionTheory.ecmul_def, AllCaseEqs()] >> strip_tac >>
  mp_tac (Q.SPECL [`a`, `n`] mulAffine_bounded) >>
  PairCases_on `a` >> gvs[bn254Theory.validAffine_def]
QED

Theorem ec_precompile_success:
  (!x1 y1 x2 y2 x y.
  vfmExecution$ecadd (w2n x1,w2n y1) (w2n x2,w2n y2) = SOME (x,y) ==>
  precompile_result 6w
    (word_to_bytes (x1:bytes32) T ++ word_to_bytes (y1:bytes32) T ++
     word_to_bytes (x2:bytes32) T ++ word_to_bytes (y2:bytes32) T) =
  SOME (SOME (word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T))) /\
  (!px py scalar x y.
  vfmExecution$ecmul (w2n px,w2n py) (w2n scalar) = SOME (x,y) ==>
  precompile_result 7w
    (word_to_bytes (px:bytes32) T ++ word_to_bytes (py:bytes32) T ++
     word_to_bytes (scalar:bytes32) T) =
  SOME (SOME (word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T)))
Proof
  conj_tac >> rpt gen_tac >> strip_tac >>
  `x < 2 ** 256 /\ y < 2 ** 256` by
    metis_tac[ecadd_success_bounds, ecmul_success_bounds] >>
  simp[ec_precompile_words, padded_num_to_be_bytes_word32]
QED

Theorem ec_result_memory:
  mem_word_at off mem = n2w x /\ mem_word_at (off + 32) mem = n2w y ==>
  val_in_memory (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) (mk_ec_result (x,y)) off mem
Proof
  strip_tac >>
  simp[mk_ec_result_def, make_array_value_def, enumerate_static_array_def,
       default_value_def] >>
  Cases_on `x = 0` >> Cases_on `y = 0` >>
  gvs[val_in_memory_def, val_to_w256_def, integer_wordTheory.i2w_def,
      type_memory_size_def, default_value_def] >>
  rpt strip_tac >> `i = 0 \/ i = 1` by decide_tac >> gvs[]
QED
