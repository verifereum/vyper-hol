Theory bodyPtrPrecompileBuiltinsArithmeticValue
Ancestors bodyPtrPrecompileBuiltinsArithmeticSource exprSimECArith exprPtrCleanBufferPost exprSimPrecompiles
          extCallOracle vfmExecution bn254 vfmBuffer vfmTypes byte list rich_list
          valueEncoding valueEncodingDefs valueEncodingProps valueEncodingProofs loweringPosts
          exprLowering exprSimDefs compileEnv loweringStateRelDefs vyperValue vyperValueOperation vyperTypeBuiltins vyperContext
          bodyPtrDefs ptrCoverage representationCleanPtr exprSimProps venomState entryDecodeStaticProps vyperAST

Theorem clean_word_mem_agree:
  mem_agree_outside m mem mem' /\
  (!i. a <= i /\ i < a+32 ==> i NOTIN m) ==>
  mem_word_at a mem = mem_word_at a mem'
Proof
  strip_tac >> drule_all clean_window_memory_agree >>
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

Theorem ec_result_buffer_ok:
  ptr_covers G tn dst s 64 /\
  type_memory_bytes cenv (lowered_value_type cenv e) = 64 ==>
  ptr_buf_ok cenv e (Var dst) G s
Proof
  simp[ptr_covers_def, ptr_buf_ok_def, eval_operand_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* Concat lowers to a bytestring buffer, so the size needs bt <> Concat. *)
Theorem ec_builtin_buffer_size:
  (!c. bt <> Concat c) ==>
  type_memory_bytes cenv
    (lowered_value_type cenv (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) bt args)) = 64
Proof
  strip_tac >>
  `lowered_value_type cenv (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) bt args) =
   ArrayT (BaseT (UintT 256)) (Fixed 2)` by
    (Cases_on `bt` >> fs[lowered_value_type_def, expr_type_def] >>
     namedCases_on `args` ["", "arg rest"] >>
     fs[lowered_value_type_def, expr_type_def] >>
     Cases_on `rest` >> Cases_on `arg` >>
     fs[lowered_value_type_def, expr_type_def] >>
     rename1 `lowered_value_type _ (Builtin _ NamedConst (Literal _ lit :: _)) = _` >>
     Cases_on `lit` >> fs[lowered_value_type_def, expr_type_def]) >>
  simp[type_memory_bytes_def, type_slot_size_def]
QED

Theorem ec_builtin_result_ptr_ok:
  (!c. bt <> Concat c) /\
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

(* The pointer carried by the stack value uses the same obligation
   already established for the non-word value. *)
Theorem ec_result_pointer_vv_ok:
  ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v op G tn s ==>
  ptr_vv_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) (Value v)
    (FST (as_stack_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) (op,sb)))
    es G tn s
Proof
  simp[ptr_vv_ok_def, as_stack_val_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def]
QED

(* Common ordinary and pointer posts for the arithmetic memory result. *)
Theorem ec_builtin_result_posts:
  (!c. bt <> Concat c) /\
  stmt_state_rel H ctx fn cenv cx es' t /\
  storage_well_formed_on cx es' (FST H) /\ wb_frame cenv es es' sa s0 t /\
  eval_operand (Var dst) t = SOME w /\ ptr_covers G tn dst t 64 /\
  (!i. w2n w <= i /\ i < w2n w+64 ==> i NOTIN tn.t_mem) /\
  mem_bytes_at (w2n w) 64 t.vs_memory =
    word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,64) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!name b sz. local_region cenv es'.scopes t name b sz ==>
    regions_disjoint (w2n w) 64 b sz) /\
  pure_frame cenv fn es sa s0 t ==>
  ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2))
    (mk_ec_result (x,y)) (Var dst) G tn t /\
  ptr_buf_ok cenv (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) bt args) (Var dst) G t /\
  vv_post H ctx fn cenv cx (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) bt args)
    es sa sb s0 es' (Value (mk_ec_result (x,y)))
    (FST (as_stack_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) (Var dst,sb))) t /\
  ptr_vv_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) (Value (mk_ec_result (x,y)))
    (FST (as_stack_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) (Var dst,sb))) es' G tn t
Proof
  strip_tac >> drule ec_result_word_contents >> strip_tac >>
  `ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2))
    (mk_ec_result (x,y)) (Var dst) G tn t` by
    (irule ec_result_ptr_val_ok >> goal_assum (drule_at Any) >>
     simp[evaluate_type_def, is_word_type_def, type_slot_size_def, wordsTheory.dimword_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (irule ec_result_buffer_ok >> simp[ec_builtin_buffer_size] >>
               qexists `tn` >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (irule (SRULE [expr_type_def, loweringPostsTheory.post_value_type_def] (Q.INST
        [`e` |-> `Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) bt args`]
        ec_result_pointer_post)) >>
      conj_tac >- (qexistsl [`aid`,`w`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule ec_result_pointer_vv_ok >> first_assum ACCEPT_TAC
QED
