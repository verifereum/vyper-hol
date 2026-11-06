Theory bodyPtrPrecompileBuiltinsArithmeticValue
Ancestors bodyPtrPrecompileBuiltinsArithmeticSource exprSimPrecompiles
          extCallOracle vfmExecution bn254 vfmBuffer vfmTypes byte list rich_list
          valueEncoding valueEncodingProps valueEncodingProofs loweringPosts
          exprLowering exprSimDefs compileEnv vyperValue vyperValueOperation vyperTypeBuiltins vyperContext
          bodyPtrDefs ptrCoverage representationCleanPtr exprSimProps venomState entryDecodeStaticProps vyperAST

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

Theorem clean_window_mem_agree:
  mem_agree_outside m mem mem' /\
  (!i. a <= i /\ i < a+n ==> i NOTIN m) ==>
  mem_bytes_at a n mem = mem_bytes_at a n mem'
Proof
  strip_tac >> irule LIST_EQ >> simp[EL_mem_bytes_at] >> rpt strip_tac >>
  `a+x NOTIN m` by (first_x_assum irule >> decide_tac) >>
  `mem_bytes_at (a+x) 1 mem = mem_bytes_at (a+x) 1 mem'` by
    metis_tac[mem_agree_outside_def] >>
  `EL 0 (mem_bytes_at (a+x) 1 mem) = EL 0 (mem_bytes_at (a+x) 1 mem')` by simp[] >>
  gvs[EL_mem_bytes_at]
QED

Theorem clean_word_mem_agree:
  mem_agree_outside m mem mem' /\
  (!i. a <= i /\ i < a+32 ==> i NOTIN m) ==>
  mem_word_at a mem = mem_word_at a mem'
Proof
  strip_tac >> drule_all clean_window_mem_agree >>
  simp[mem_word_at_def, mem_bytes_at_def]
QED

Theorem ec_result_robust_memory:
  mem_word_at a mem = n2w x /\ mem_word_at (a+32) mem = n2w y /\
  (!i. a <= i /\ i < a+64 ==> i NOTIN m) ==>
  !mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) (mk_ec_result (x,y)) a mem'
Proof
  rpt strip_tac >> irule ec_result_memory >>
  `mem_word_at a mem = mem_word_at a mem'` by
    (irule clean_word_mem_agree >> goal_assum (drule_at Any) >>
     rpt strip_tac >> gvs[] >>
     qpat_x_assum `!i. _` (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
  `mem_word_at (a+32) mem = mem_word_at (a+32) mem'` by
    (irule clean_word_mem_agree >> goal_assum (drule_at Any) >>
     rpt strip_tac >> gvs[] >>
     qpat_x_assum `!i. _` (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >> metis_tac[]
QED

Theorem ec_result_sizes:
  val_footprint (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) (mk_ec_result (x,y)) = 64 /\
  val_store_size (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) (mk_ec_result (x,y)) = 64
Proof
  simp[mk_ec_result_def, make_array_value_def, val_footprint_def,
       val_store_size_def, type_memory_size_def]
QED

Theorem ec_result_ptr_val_ok:
  evaluate_type (get_tenv cx) ty = SOME (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) /\
  ~is_word_type ty /\ eval_operand (Var dst) s = SOME w /\
  ptr_covers G tn dst s 64 /\
  (!i. w2n w <= i /\ i < w2n w+64 ==> i NOTIN tn.t_mem) /\
  mem_word_at (w2n w) s.vs_memory = n2w x /\
  mem_word_at (w2n w+32) s.vs_memory = n2w y ==>
  ptr_val_ok cx ty (mk_ec_result (x,y)) (Var dst) G tn s
Proof
  strip_tac >> simp[ptr_val_ok_def] >> conj_tac
  >- gvs[ptr_covers_def] >>
  simp[ptr_mem_ok_def] >> conj_tac
  >- (rpt strip_tac >> irule ec_result_robust_memory >>
      goal_assum (drule_at Any) >> simp[]) >>
  gvs[ptr_covers_def, ec_result_sizes, eval_operand_def]
QED

Theorem ec_result_word_contents:
  mem_bytes_at a 64 mem =
    word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T ==>
  mem_word_at a mem = n2w x /\ mem_word_at (a+32) mem = n2w y
Proof
  strip_tac >>
  `mem_bytes_at a 32 mem = word_to_bytes (n2w x:bytes32) T /\
   mem_bytes_at (a+32) 32 mem = word_to_bytes (n2w y:bytes32) T` by
    (irule mem_bytes_at_split_eq >>
     simp[LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:256)``]) >>
  gvs[mem_bytes_at_word_eq]
QED

Theorem ec_result_full_write_contents:
  mem' = (write_memory_with_expansion a
    (TAKE 64 (word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T)) s).vs_memory ==>
  mem_word_at a mem' = n2w x /\ mem_word_at (a+32) mem' = n2w y
Proof
  strip_tac >> irule ec_result_word_contents >>
  `LENGTH (word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T) = 64` by
    simp[LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  gvs[TAKE_LENGTH_TOO_LONG] >>
  qspecl_then [`a`, `word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T`, `s`]
    mp_tac write_memory_mem_bytes_at_same >>
  simp[LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem ec_result_val_wf:
  val_wf (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) (mk_ec_result (x,y))
Proof
  simp[mk_ec_result_def, make_array_value_def, enumerate_static_array_def,
       default_value_def] >>
  Cases_on `x = 0` >> Cases_on `y = 0` >>
  simp[val_wf_def, type_memory_size_def]
QED

Theorem ec_result_pointer_post:
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  stmt_state_rel ctx fn cenv cx es' t /\ wb_frame cenv es sa s0 t /\
  eval_operand pop t = SOME w /\
  mem_bytes_at (w2n w) 64 t.vs_memory =
    word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,64) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!name b sz. local_region cenv es'.scopes t name b sz ==>
     regions_disjoint (w2n w) 64 b sz) ==>
  vv_post ctx fn cenv cx e es sa sb s0 es' (Value (mk_ec_result (x,y)))
    (FST (as_ptr_val (expr_type e) LocMemory (pop,sb))) t
Proof
  strip_tac >> drule ec_result_word_contents >> strip_tac >>
  drule_all ec_result_memory >> strip_tac >>
  simp[as_ptr_val_def, contextTheory.mk_ptr_def,
       vv_post_def, vv_holds_def, vv_at_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def,
       evaluate_type_def, is_word_type_def, ec_result_val_wf,
       type_slot_size_def, wordsTheory.dimword_def, ec_result_sizes] >>
  conj_tac
  >- (disj1_tac >> qexistsl [`aid`, `w2n w`, `64`] >>
      simp[] >> gvs[regions_disjoint_def]) >>
  gvs[wb_frame_def] >> metis_tac[]
QED

Theorem ec_result_buffer_ok:
  ptr_covers G tn dst s 64 /\
  type_memory_bytes cenv (lowered_value_type cenv e) = 64 ==>
  ptr_buf_ok cenv e (Var dst) G s
Proof
  simp[ptr_covers_def, ptr_buf_ok_def, eval_operand_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ec_builtin_buffer_size:
  type_memory_bytes cenv
    (lowered_value_type cenv (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) bt args)) = 64
Proof
  simp[lowered_value_type_def, expr_type_def, type_memory_bytes_def, type_slot_size_def]
QED

Theorem ec_builtin_result_ptr_ok:
  eval_operand (Var dst) s = SOME w /\ ptr_covers G tn dst s 64 /\
  (!i. w2n w <= i /\ i < w2n w+64 ==> i NOTIN tn.t_mem) /\
  s.vs_memory = (write_memory_with_expansion (w2n w)
    (TAKE 64 (word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T)) u).vs_memory ==>
  ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2))
    (mk_ec_result (x,y)) (Var dst) G tn s /\
  ptr_buf_ok cenv (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) bt args) (Var dst) G s
Proof
  strip_tac >> drule ec_result_full_write_contents >> strip_tac >> conj_tac
  >- (irule ec_result_ptr_val_ok >> goal_assum (drule_at Any) >>
      gvs[evaluate_type_def, is_word_type_def, type_slot_size_def, wordsTheory.dimword_def]) >>
  irule ec_result_buffer_ok >> simp[ec_builtin_buffer_size] >>
  qexists `tn` >> simp[]
QED

(* The memory-place returned by as_ptr_val uses the same pointer obligation
   already established for the non-word value. *)
Theorem ec_result_pointer_vv_ok:
  ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v op G tn s ==>
  ptr_vv_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) (Value v)
    (FST (as_ptr_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) LocMemory (op,sb)))
    es G tn s
Proof
  simp[ptr_val_ok_def, ptr_vv_ok_def, as_ptr_val_def,
       contextTheory.mk_ptr_def, evaluate_type_def, is_word_type_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def]
QED
