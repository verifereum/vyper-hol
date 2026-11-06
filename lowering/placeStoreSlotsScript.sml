(*
 * place_store_value_run (placeStore) at a slot in storage or transient
 * storage: a word by one SSTORE or TSTORE; any other value laid out at the
 * place's type in memory (through a fresh buffer when the value's type
 * differs and is not a bytestring), then copied to the slots by
 * compile_store_slots, which writes only the slots live in the value: a
 * DynArray's length and its first length elements, a bytestring's length
 * word and the words holding its bytes, at any depth.
 *
 * store_slots_entry says what compile_store_slots does for one type and
 * value: it stores memory word j at slot dw + j for each j of a list ks,
 * and every slot holding a live byte of the value's encoding is in ks.
 * store_slots_rank_entry proves it for every type by induction on
 * type_rank; place_store_value_storage_run uses it.
 *
 * TOP-LEVEL: place_store_value_storage_run
 *)

Theory placeStoreSlots
Ancestors
  placeStoreStorage placeDynLayout placeStoreAllocPath placeStoreStatePatch
  stmtSimDefs exprSimHypsDefs typedCopyDomain vyperStoragePlaceProvenance
  loweringPosts fragGasMode accountsRelProps copyExecution stmtSimStoreCopy
  placeStoreCopyChunk fragGasSeq typedMemoryCopy
  stmtLowering exprLowering compileEnv context
  vyperInterpreter vyperState vyperValue vyperTypeSystem vyperTyping
  vyperStorage valueEncoding valueEncodingProps
  venomState fragGasPath arithmetic venomExecSemantics venomInst
  exprLoweringProps list rich_list

(* compile_store_slots run from memory holding v at src (type tv) to the
   slots from dw: the stored slots ks, each holding the memory word at the
   same offset, cover every slot with a live byte in any storage that
   holds v's encoding at dw. *)
Definition store_slots_entry_def:
  store_slots_entry cenv ctx ty tv v <=>
    !src slot tr sa sb func s sw dw writes.
      compile_store_slots cenv src slot ty tr sa = ((),sb) /\
      (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
      eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
      val_in_memory tv v (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size tv < dimword (:256) /\
      w2n dw + type_slot_size tv <= dimword (:256) /\
      encode_value tv v = SOME writes /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      ~s.vs_call_ctx.cc_static ==>
      ?t ks.
        gas_marked_path F ctx func s 0 (OK t) /\
        store_copy_normalize s t =
          FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
                   (mload (w2n sw + 32 * j) s) q) s ks /\
        EVERY (\j. j < type_slot_size tv) ks /\
        (!st j b.
           apply_writes dw writes st = st /\
           j < type_slot_size tv /\ b < 32 /\
           ~dead_bytes st (w2n dw) tv (w2n dw + j) b ==>
           MEM j ks) /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
        t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
End

(* The memory-to-slots word copy loop with its word count in an operand,
   as a bytestring's copy loads it. *)
Theorem place_store_runtime_copy_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop_op src dst count LocMemory loc ctor sa = (u,sb) /\
  fn_has_code sa sb func /\ n < dimword (:256) /\
  (!x. src = Var x \/ dst = Var x \/ count = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME b /\ eval_operand dst s0 = SOME k /\
  eval_operand count s0 = SOME (n2w n) /\
  ~s0.vs_call_ctx.cc_static /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s0 0 (OK t) /\
      store_copy_frame sa loc b k s0 n t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

(* place_store_memory_to_slots_path with the word count in an operand. *)
Theorem place_store_memory_to_slots_op_path:
  compile_word_copy_loop_op src dst cnt LocMemory
    (if tr then LocTransient else LocStorage) F sa = (result,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x \/ cnt = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand cnt s = SOME (n2w n) /\
  n < dimword (:256) /\ w2n sw + 32*n < dimword (:256) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      store_copy_normalize s t =
        FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
                 (mload (w2n sw + 32*j) s) q) s (COUNT_LIST n) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
      t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  mp_tac (Q.INST [`loc` |-> `if tr then LocTransient else LocStorage`,
                  `count` |-> `cnt`, `ctor` |-> `F`, `u` |-> `result`,
                  `s0` |-> `s`, `b` |-> `sw`, `k` |-> `dw`]
    place_store_runtime_copy_path) >>
  (impl_tac >- (Cases_on `tr` >> simp[] >> metis_tac[])) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  drule place_store_copy_frame_observations >> strip_tac >> simp[] >>
  fs[store_copy_frame_def, store_copy_prefix_def] >>
  irule listTheory.FOLDL_CONG >> simp[] >>
  simp[rich_listTheory.MEM_COUNT_LIST] >> rpt strip_tac >>
  `32*x + w2n sw < dimword (:256)` by (simp[] >> decide_tac) >>
  `sw + n2w x * 32w = n2w (32*x + w2n sw)` by
    simp[GSYM wordsTheory.word_add_n2w, GSYM wordsTheory.word_mul_n2w,
         wordsTheory.WORD_ADD_COMM, wordsTheory.WORD_MULT_COMM] >>
  Cases_on `tr` >> simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]
QED

(* A type with no DynArray or bytestring inside: copied whole. *)
Theorem store_slots_static_entry:
  !cenv tenv ctx ty tv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    ~is_abi_dynamic cenv.ce_struct_fields ty /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
    store_slots_entry cenv ctx ty tv v
Proof
  cheat
QED

(* A bytestring: its length word and the words holding its bytes. *)
Theorem store_slots_bytes_entry:
  !cenv tenv ctx ty tv v.
    is_bytestring_type ty /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
    store_slots_entry cenv ctx ty tv v
Proof
  cheat
QED

(* The element loop over count elements el 0, ..., el (N - 1) of type etv,
   element i at memory src + i * size and at slot dw + i * slots. *)
Theorem store_slots_elements_run:
  !cenv ctx elem etv el N src slot cnt tr sa sb func s sw dw.
    compile_copy_elements_to_slots cenv src slot elem cnt tr sa = ((),sb) /\
    type_memory_bytes cenv elem = type_memory_size etv /\
    (!i. i < N ==>
       store_slots_entry cenv ctx elem etv (el i) /\
       IS_SOME (encode_value etv (el i)) /\
       val_in_memory etv (el i) (w2n sw + i * type_memory_size etv)
         s.vs_memory) /\
    (!x. src = Var x \/ slot = Var x \/ cnt = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
    eval_operand cnt s = SOME (n2w N) /\ N < dimword (:256) /\
    w2n sw + N * type_memory_size etv < dimword (:256) /\
    w2n dw + N * type_slot_size etv <= dimword (:256) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~s.vs_call_ctx.cc_static ==>
    ?t ks.
      gas_marked_path F ctx func s 0 (OK t) /\
      store_copy_normalize s t =
        FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
                 (mload (w2n sw + 32 * j) s) q) s ks /\
      EVERY (\j. j < N * type_slot_size etv) ks /\
      (!i writes st j b.
         i < N /\ encode_value etv (el i) = SOME writes /\
         apply_writes (dw + n2w (i * type_slot_size etv)) writes st = st /\
         j < type_slot_size etv /\ b < 32 /\
         ~dead_bytes st (w2n dw + i * type_slot_size etv) etv
            (w2n dw + i * type_slot_size etv + j) b ==>
         MEM (i * type_slot_size etv + j) ks) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
      t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

(* A DynArray: its live elements, then its length word. *)
Theorem store_slots_dynarray_entry:
  !cenv tenv ctx elem n tv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    evaluate_type tenv (ArrayT elem (Dynamic n)) = SOME tv /\
    value_has_type tv v /\
    (!cty ctv cv.
       type_rank cenv.ce_struct_fields cty <
         type_rank cenv.ce_struct_fields (ArrayT elem (Dynamic n)) /\
       evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv ==>
       store_slots_entry cenv ctx cty ctv cv) ==>
    store_slots_entry cenv ctx (ArrayT elem (Dynamic n)) tv v
Proof
  cheat
QED

(* A static array with a DynArray or bytestring inside: each element. *)
Theorem store_slots_sarray_entry:
  !cenv tenv ctx elem n tv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    is_abi_dynamic cenv.ce_struct_fields (ArrayT elem (Fixed n)) /\
    evaluate_type tenv (ArrayT elem (Fixed n)) = SOME tv /\
    value_has_type tv v /\
    (!cty ctv cv.
       type_rank cenv.ce_struct_fields cty <
         type_rank cenv.ce_struct_fields (ArrayT elem (Fixed n)) /\
       evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv ==>
       store_slots_entry cenv ctx cty ctv cv) ==>
    store_slots_entry cenv ctx (ArrayT elem (Fixed n)) tv v
Proof
  cheat
QED

(* Struct or tuple members as (type, memory size) pairs, member i at
   memory src + mo + its memory prefix and at slot dw + so + its slot
   prefix. *)
Theorem store_slots_members_run:
  !members tvs vs cenv ctx mo so src slot tr sa sb func s sw dw.
    compile_store_slots_members cenv src slot members mo so tr sa = ((),sb) /\
    LIST_REL (\(ty,sz) (tv,v). sz = type_memory_size tv /\
                               store_slots_entry cenv ctx ty tv v /\
                               IS_SOME (encode_value tv v))
      members (ZIP (tvs,vs)) /\
    LENGTH vs = LENGTH tvs /\ mo = 32 * so /\
    tuple_in_memory vs tvs (w2n sw + mo) s.vs_memory /\
    (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
    w2n sw + mo + type_memory_size_list tvs < dimword (:256) /\
    w2n dw + so + type_slot_size_list tvs <= dimword (:256) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~s.vs_call_ctx.cc_static ==>
    ?t ks.
      gas_marked_path F ctx func s 0 (OK t) /\
      store_copy_normalize s t =
        FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
                 (mload (w2n sw + 32 * j) s) q) s ks /\
      EVERY (\j. so <= j /\ j < so + type_slot_size_list tvs) ks /\
      (!i writes st j b.
         i < LENGTH tvs /\ encode_value (EL i tvs) (EL i vs) = SOME writes /\
         apply_writes (dw + n2w (so + tuple_prefix_slot_size i tvs)) writes st =
           st /\
         j < type_slot_size (EL i tvs) /\ b < 32 /\
         ~dead_bytes st (w2n dw + so + tuple_prefix_slot_size i tvs) (EL i tvs)
            (w2n dw + so + tuple_prefix_slot_size i tvs + j) b ==>
         MEM (so + tuple_prefix_slot_size i tvs + j) ks) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
      t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

(* A tuple with a DynArray or bytestring inside: each member. *)
Theorem store_slots_tuple_entry:
  !cenv tenv ctx tys tv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    is_abi_dynamic cenv.ce_struct_fields (TupleT tys) /\
    evaluate_type tenv (TupleT tys) = SOME tv /\ value_has_type tv v /\
    (!cty ctv cv.
       type_rank cenv.ce_struct_fields cty <
         type_rank cenv.ce_struct_fields (TupleT tys) /\
       evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv ==>
       store_slots_entry cenv ctx cty ctv cv) ==>
    store_slots_entry cenv ctx (TupleT tys) tv v
Proof
  cheat
QED

(* A struct with a DynArray or bytestring inside: each field. *)
Theorem store_slots_struct_entry:
  !cenv tenv ctx nsid tv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    is_abi_dynamic cenv.ce_struct_fields (StructT nsid) /\
    evaluate_type tenv (StructT nsid) = SOME tv /\ value_has_type tv v /\
    (!cty ctv cv.
       type_rank cenv.ce_struct_fields cty <
         type_rank cenv.ce_struct_fields (StructT nsid) /\
       evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv ==>
       store_slots_entry cenv ctx cty ctv cv) ==>
    store_slots_entry cenv ctx (StructT nsid) tv v
Proof
  cheat
QED

Theorem store_slots_rank_entry:
  !n cenv tenv ctx ty tv v.
    type_rank cenv.ce_struct_fields ty = n /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
    store_slots_entry cenv ctx ty tv v
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `is_abi_dynamic cenv.ce_struct_fields ty`
  >- suspend "dynamic" >>
  irule store_slots_static_entry >> simp[] >> qexists_tac `tenv` >> gvs[]
QED
Resume store_slots_rank_entry[dynamic]:
  `!cty ctv cv.
     type_rank cenv.ce_struct_fields cty < type_rank cenv.ce_struct_fields ty /\
     evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv ==>
     store_slots_entry cenv ctx cty ctv cv` by
    (rpt strip_tac >>
     last_x_assum (qspec_then `type_rank cenv.ce_struct_fields cty` mp_tac) >>
     simp[] >> disch_then irule >> qexists_tac `tenv` >> gvs[]) >>
  Cases_on `is_bytestring_type ty`
  >- (irule store_slots_bytes_entry >> qexists_tac `tenv` >> gvs[]) >>
  Cases_on `ty`
  >~ [`ArrayT elem bd`]
  >- (Cases_on `bd`
      >- (irule store_slots_sarray_entry >> qexists_tac `tenv` >> gvs[])
      >> irule store_slots_dynarray_entry >> qexists_tac `tenv` >> gvs[])
  >~ [`TupleT tys`]
  >- (irule store_slots_tuple_entry >> qexists_tac `tenv` >> gvs[])
  >~ [`StructT nsid`]
  >- (irule store_slots_struct_entry >> qexists_tac `tenv` >> gvs[])
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> gvs[is_abi_dynamic_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_abi_dynamic_def, is_bytestring_type_def]) >>
  gvs[is_abi_dynamic_def]
QED

(* Writing an encoding twice is writing it once. *)
Theorem place_store_apply_writes_idem:
  !writes k st.
    apply_writes k writes (apply_writes k writes st) = apply_writes k writes st
Proof
  rpt gen_tac >> rewrite_tac[place_store_apply_writes_fold] >>
  qabbrev_tac `xs = MAP (\(off,v). (k + n2w off,v)) writes` >>
  simp[FUN_EQ_THM] >> qx_gen_tac `a` >>
  mp_tac (Q.SPECL [`xs`, `a`] place_store_updates_lookup) >>
  simp[vfmStateTheory.lookup_storage_def] >> strip_tac >>
  asm_rewrite_tac[] >> BasicProvers.every_case_tac >> gvs[]
QED

(* place_store_encoded_copy_agree with the copied slots any list ks that
   covers the live slots. *)
Theorem place_store_encoded_copy_agree_sparse:
  !cx tr mid name subs rootk root path delta tv base writes v ks read_word st1 st2.
    declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
    storage_subregion root path delta tv /\
    base = w2n rootk + delta /\ 0 < type_slot_size tv /\
    w2n rootk + type_slot_size root <= dimword (:256) /\
    (!mid' name' subs' k' tv'.
       declared_storage_region cx mid' name' subs' = SOME (tr,k',tv') /\
       (k',tv') <> (rootk,root) ==>
       ranges_disjoint (w2n rootk) (type_slot_size root)
                       (w2n k') (type_slot_size tv')) /\
    encode_value tv v = SOME writes /\ value_has_type tv v /\
    base + type_slot_size tv <= dimword (:256) /\
    EVERY (\i. i < type_slot_size tv) ks /\
    (!i b. i < type_slot_size tv /\ b < 32 /\
       ~dead_bytes (apply_writes (n2w base) writes st1) base tv (base+i) b ==>
       MEM i ks /\
       EL b (word_to_bytes (lookup_storage (n2w (base+i))
         (apply_writes (n2w base) writes st1)) T) =
       EL b (word_to_bytes (read_word i) T)) /\
    storage_agree (storage_dead cx tr st1) st1 st2 ==>
    storage_agree (storage_dead cx tr (apply_writes (n2w base) writes st1))
      (apply_writes (n2w base) writes st1)
      (FOLDL (\st i. update_storage (n2w (base+i)) (read_word i) st) st2 ks)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `apply_writes (n2w start) writes st1` >>
  `start < dimword (:256)` by decide_tac >>
  irule place_store_subregion_agree >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  qexists_tac `(n2w start):bytes32` >>
  goal_assum (drule_at (Pat `storage_agree _ _ _`)) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  `w2n ((n2w start):bytes32) = start` by simp[wordsTheory.w2n_n2w] >>
  qpat_x_assum `start = _` (mk_asm "origin") >>
  simp[wordsTheory.w2n_n2w, GSYM wordsTheory.word_add_n2w] >>
  conj_tac >- suspend "frame" >> suspend "live"
QED
Resume place_store_encoded_copy_agree_sparse[frame]:
  gen_tac >> disch_tac >> conj_tac
  >- (rewrite_tac[place_store_apply_writes_fold] >>
      irule place_store_updates_miss >>
      simp[listTheory.MAP_MAP_o, combinTheory.o_DEF, listTheory.MEM_MAP,
           pairTheory.EXISTS_PROD] >>
      rpt strip_tac >>
      rename1 `MEM (off,word) writes` >>
      `off < type_slot_size tv` by
        (irule (CONJUNCT1 vyperEncodeDecodeTheory.encode_writes_bounded) >>
         goal_assum (drule_at (Pat `encode_value _ _ = _`)) >>
         simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
      `start + off < dimword (:256)` by decide_tac >>
      gvs[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >> decide_tac) >>
  rename1 `FOLDL (\st i. update_storage (n2w start + n2w i) (rd i) st) st2 ks` >>
  `~MEM q (MAP FST (MAP (\i. ((n2w start + n2w i):bytes32,rd i)) ks))` by
    (simp[listTheory.MAP_MAP_o, combinTheory.o_DEF, listTheory.MEM_MAP] >>
     rpt strip_tac >> gvs[listTheory.EVERY_MEM] >> res_tac >>
     `start + i < dimword (:256)` by decide_tac >>
     gvs[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >> decide_tac) >>
  drule place_store_updates_miss >>
  disch_then (qspec_then `st2` mp_tac) >> simp[rich_listTheory.FOLDL_MAP]
QED
Resume place_store_encoded_copy_agree_sparse[live]:
  reverse conj_tac >- (asm "origin" mp_tac >> simp[ADD_COMM]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `FOLDL (\st j. update_storage (n2w start + n2w j) (rd j) st) st2 ks` >>
  `MEM i ks /\
   EL b (word_to_bytes (lookup_storage (n2w (start+i))
     (apply_writes (n2w start) writes st1)) T) =
   EL b (word_to_bytes (rd i) T)` by
    (first_x_assum irule >> simp[ADD_COMM]) >>
  `lookup_storage (n2w start + n2w i)
     (FOLDL (\st j. update_storage (n2w start + n2w j) (rd j) st) st2 ks) =
   rd i` suffices_by gvs[GSYM wordsTheory.word_add_n2w] >>
  `MEM ((n2w start + n2w i):bytes32,rd i) (MAP (\j. (n2w start + n2w j,rd j)) ks)` by
    (simp[listTheory.MEM_MAP] >> qexists_tac `i` >> simp[]) >>
  drule place_store_updates_hit >>
  disch_then (qspec_then `st2` mp_tac) >>
  simp[rich_listTheory.FOLDL_MAP, listTheory.MEM_MAP] >>
  impl_tac >- (rpt strip_tac >> gvs[listTheory.EVERY_MEM] >> res_tac >>
    `i < dimword (:256)` by decide_tac >>
    `j < dimword (:256)` by decide_tac >>
    gvs[wordsTheory.n2w_11]) >> simp[]
QED
Finalise place_store_encoded_copy_agree_sparse

(* place_store_encoded_leaf_state with the stored slots any list ks that
   covers the live slots. *)
Theorem place_store_encoded_leaf_state_sparse:
  !cenv cx env ee ctx func s mid name subs tr rootk root path delta tv
   start writes v ks rd.
  expr_sim_inv cenv cx env ee /\
  stmt_state_rel ctx func cenv cx ee s /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\
  start = w2n rootk + delta /\ 0 < type_slot_size tv /\
  encode_value tv v = SOME writes /\ value_has_type tv v /\
  start + type_slot_size tv <= dimword (:256) /\
  EVERY (\i. i < type_slot_size tv) ks /\
  (!i b. i < type_slot_size tv /\ b < 32 /\
    ~dead_bytes (apply_writes (n2w start) writes (get_storage cx ee tr))
       start tv (start+i) b ==>
    MEM i ks /\
    EL b (word_to_bytes (lookup_storage (n2w (start+i))
      (apply_writes (n2w start) writes (get_storage cx ee tr))) T) =
    EL b (word_to_bytes (rd i) T)) ==>
  stmt_state_rel ctx func cenv cx
    (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr)))
    (FOLDL (\t i. (if tr then tstore else sstore)
       (n2w (start+i)) (rd i) t) s ks)
Proof
  rpt gen_tac >> strip_tac >>
  `storage_agree (storage_dead cx tr (get_storage cx ee tr))
    (get_storage cx ee tr)
    (if tr then contract_transient s else contract_storage s)` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     Cases_on `tr` >>
     simp[stmt_state_rel_def, state_rel_def, accounts_rel_def,
          accounts_agree_def, transient_agree_def,
          vyperStorageBackendTheory.get_storage_def,
          vfmStateTheory.lookup_account_def,
          contract_storage_def, contract_transient_def,
          call_ctx_rel_def] >> metis_tac[]) >>
  drule_all place_store_root_layout >> strip_tac >>
  `storage_agree
    (storage_dead cx tr (apply_writes (n2w start) writes (get_storage cx ee tr)))
    (apply_writes (n2w start) writes (get_storage cx ee tr))
    (FOLDL (\st i. update_storage (n2w (start+i)) (rd i) st)
      (if tr then contract_transient s else contract_storage s) ks)` by
    (irule place_store_encoded_copy_agree_sparse >>
     conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     gvs[] >> metis_tac[]) >>
  `!is s. FOLDL (\t i. (if tr then tstore else sstore)
        (n2w (start+i)) (rd i) t) s is =
     if tr then s with vs_transient :=
       (s.vs_call_ctx.cc_address =+
         FOLDL (\st i. update_storage (n2w (start+i)) (rd i) st)
           (contract_transient s) is) s.vs_transient
     else s with vs_accounts :=
       (s.vs_call_ctx.cc_address =+
         (lookup_account s.vs_call_ctx.cc_address s.vs_accounts with storage :=
           FOLDL (\st i. update_storage (n2w (start+i)) (rd i) st)
             (contract_storage s) is)) s.vs_accounts` by
    (Induct
     >- (gen_tac >> pure_rewrite_tac[listTheory.FOLDL] >> Cases_on `tr` >>
         simp[contract_storage_def, contract_transient_def,
              vfmStateTheory.lookup_account_def, place_store_update_identity]) >>
     map_every qx_gen_tac [`h`, `acc`] >>
     once_rewrite_tac[listTheory.FOLDL] >>
     first_x_assum (qspec_then `(if tr then tstore else sstore)
       (n2w (start+h)) (rd h) acc` mp_tac) >>
     Cases_on `tr` >>
     simp[sstore_def, tstore_def, contract_storage_def, contract_transient_def,
          vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM,
          combinTheory.UPDATE_EQ]) >>
  drule_all place_store_storage_replace >> Cases_on `tr` >> gvs[]
QED

(* The store of a value of type tv laid out at src in memory: a state
   related at the source state after the write. *)
Theorem place_store_slots_suffix_run:
  !cenv src dst dty tr sa sb tv func s sw start ctx cx env ee mid name subs
   rootk root path delta writes v.
  compile_store_slots cenv src dst dty tr sa = ((),sb) /\
  evaluate_type (get_tenv cx) dty = SOME tv /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME (n2w start) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  local_ptrs_reserved cenv sa /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  0 < type_slot_size tv /\ encode_value tv v = SOME writes /\ value_has_type tv v /\
  start + type_slot_size tv <= dimword (:256) /\
  val_in_memory tv v (w2n sw) s.vs_memory ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx
      (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr))) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  `start < dimword (:256)` by decide_tac >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv cx) fty = SOME tv ==>
        sz = type_memory_size tv) fields)` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  `store_slots_entry cenv ctx dty tv v` by
    (irule store_slots_rank_entry >> simp[] >> qexists_tac `get_tenv cx` >>
     simp[]) >>
  `well_formed_type_value tv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  qpat_x_assum `store_slots_entry _ _ _ _ _` mp_tac >>
  simp_tac std_ss [store_slots_entry_def] >>
  disch_then (qspecl_then [`src`, `dst`, `tr`, `sa`, `sb`, `func`, `s`, `sw`,
    `n2w start`, `writes`] mp_tac) >>
  (impl_tac >- (simp[wordsTheory.w2n_n2w] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`t`, `ks`] strip_assume_tac) >>
  qspecl_then [`cenv`, `cx`, `env`, `ee`, `ctx`, `func`, `s`, `mid`, `name`,
    `subs`, `tr`, `rootk`, `root`, `path`, `delta`, `tv`, `start`, `writes`,
    `v`, `ks`, `\i. mload (w2n sw + 32*i) s`]
    mp_tac place_store_encoded_leaf_state_sparse >>
  impl_tac
  >- (simp[] >> rpt gen_tac >> strip_tac >> conj_tac
      >- (first_x_assum (qspecl_then
            [`apply_writes (n2w start) writes (get_storage cx ee tr)`, `i`, `b`]
            mp_tac) >>
          simp[place_store_apply_writes_idem, wordsTheory.w2n_n2w]) >>
      irule place_store_memory_live_at >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`tv`, `v`] >> pure_asm_rewrite_tac[] >> simp[]) >>
  strip_tac >> qexists_tac `t` >> simp[] >>
  irule place_store_normalized_stmt_state >>
  goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  qexists_tac `s` >> simp[] >>
  qpat_x_assum `store_copy_normalize _ _ = _` SUBST1_TAC >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ (FOLDL _ _ _)` mp_tac >>
  simp_tac bool_ss [GSYM wordsTheory.word_add_n2w]
QED

(* place_store_slots_suffix_run for a bytestring laid out at its source
   type stv, of a capacity at most the place's. *)
Theorem place_store_slots_bytes_run:
  !cenv src dst dty sty tr sa sb stv tv func s sw start ctx cx env ee mid name
   subs rootk root path delta writes v.
  compile_store_slots cenv src dst dty tr sa = ((),sb) /\
  is_bytestring_type dty /\ is_bytestring_type sty /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME tv /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME (n2w start) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  local_ptrs_reserved cenv sa /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  0 < type_slot_size tv /\ encode_value tv v = SOME writes /\
  value_has_type stv v /\ value_has_type tv v /\
  start + type_slot_size tv <= dimword (:256) /\
  val_in_memory stv v (w2n sw) s.vs_memory ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx
      (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr))) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

Theorem place_store_storage_compile:
  compile_assign_value cenv dst (slot_loc tr) src (is_word_type dty)
    src_loc dty sty (type_memory_bytes cenv dty) sa = ((), sb) ==>
  ?src' sc.
    (((~is_word_type dty /\ dty <> sty /\
       ~(is_bytestring_type dty /\ is_bytestring_type sty)) /\
      ?a sm. compile_alloc_buffer (type_memory_bytes cenv dty) sa = (a,sm) /\
        compile_store_memory_typed cenv a.buf_operand dty src sty sm = ((),sc) /\
        src' = a.buf_operand) \/
     ((is_word_type dty \/ dty = sty \/
       (is_bytestring_type dty /\ is_bytestring_type sty)) /\ src' = src /\ sc = sa)) /\
    (if is_word_type dty then
       emit_void (if tr then TSTORE else SSTORE) [dst;src'] sc = ((),sb)
     else compile_store_slots cenv src' dst dty tr sc = ((),sb))
Proof
  strip_tac >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  simp[slot_loc_def, stmtLoweringTheory.compile_assign_value_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `~is_word_type dty /\ dty <> sty /\
    ~(is_bytestring_type dty /\ is_bytestring_type sty)` >>
  gvs[] >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `is_word_type dty` >> gvs[] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

(* compile_assign_value into (transient) storage. *)
Theorem place_store_value_storage_run:
  !ctx func cenv cx env ee ff s p w loc dst_op op src_loc dty sty stv v sa sb.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_assign_value cenv dst_op loc op (is_word_type dty) src_loc dty sty
      (type_memory_bytes cenv dty) sa = ((), sb) /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    expr_val_rel cx sty v op s /\ cenv.ce_target CapMcopy /\
    (loc = LocMemory /\ src_loc <> SOME LocMemory /\ ~is_word_type dty /\
     ~is_bytestring_type dty /\ dty <> sty ==>
     !sw dtv. eval_operand op s = SOME sw /\
              evaluate_type (get_tenv cx) dty = SOME dtv ==>
              type_memory_size stv = 0 \/
              w2n sw + type_memory_size stv <= w2n w \/
              w2n w + type_memory_size dtv <= w2n sw \/
              sw = w /\ stv = dtv) /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0.
       p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (~is_word_type sty ==>
     !sw. eval_operand op s = SOME sw ==>
          w2n sw + type_memory_size stv <= s.vs_alloca_next /\
          !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
                     sa.cs_next_id <= aid ==>
                     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
    (loc = LocMemory ==>
     !dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           w2n w + type_memory_size dtv + 64 < dimword (:256)) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           0 < type_slot_size dtv) /\
    (dty <> sty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty) ==>
     type_alloc_ok cenv dty) /\
    stmt_state_rel ctx func cenv cx ee s /\
    write_place cx p v ee = (INL (), ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        stmt_state_rel ctx func cenv cx ff t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all place_store_storage_destination >> strip_tac >>
  qpat_x_assum `loc = LocStorage \/ loc = LocTransient` kall_tac >> gvs[] >>
  drule_all place_store_storage_write_inv >> strip_tac >> gvs[] >>
  drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> strip_tac >> gvs[] >>
  drule_all place_store_storage_leaf_bounds >> strip_tac >>
  Cases_on `is_word_type dty`
  >- suspend "word"
  >> suspend "memory"
QED
Resume place_store_value_storage_run[word]:
  drule_all place_store_storage_compile >> simp[] >> strip_tac >>
  `sty = dty` by metis_tac[compileEnvTheory.type_widens_to_word] >> gvs[] >>
  `eval_operand op s = SOME (typed_val_to_w256 dtv v)` by
    fs[expr_val_rel_def] >>
  drule_all place_store_emit_slot_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  `stmt_state_rel ctx func cenv cx
    (set_storage cx ee tr (apply_writes (n2w (w2n root+delta)) writes
      (get_storage cx ee tr)))
    (FOLDL (\u i. (if tr then tstore else sstore)
       (n2w (w2n root+delta+i)) (typed_val_to_w256 dtv v) u) s (COUNT_LIST 1))` by
    (irule (BETA_RULE (Q.INST [`rd` |-> `\i. typed_val_to_w256 dtv v`]
       (SPEC_ALL place_store_encoded_leaf_state))) >>
     conj_tac >- metis_tac[] >>
     reverse conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     simp[] >> rpt strip_tac >>
     drule_all place_store_word_live_copy >>
     disch_then (qspecl_then [`get_storage cx ee tr`, `root+n2w delta`, `b`] mp_tac) >>
     simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  qmatch_asmsub_abbrev_tac `gas_marked_path F ctx func s 0 (OK t)` >>
  qexists_tac `t` >> simp[] >>
  reverse conj_tac
  >- (unabbrev_all_tac >> Cases_on `tr` >>
      simp[tstore_def, sstore_def, lookup_var_def]) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ (FOLDL _ _ _)` mp_tac >>
  `COUNT_LIST 1 = [0]` by EVAL_TAC >>
  simp[] >>
  unabbrev_all_tac >>
  simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n,
       wordsTheory.WORD_ADD_COMM]
QED
Resume place_store_value_storage_run[memory]:
  drule_all place_store_storage_compile >> simp[] >>
  disch_then (qx_choose_then `src` (qx_choose_then `sc`
    (map_every assume_tac o CONJUNCTS))) >>
  Cases_on `dty <> sty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty)`
  >- suspend "normalize"
  >> suspend "direct"
QED
Resume place_store_value_storage_run[direct]:
  gvs[]
  >- suspend "equal"
  >> suspend "bytes"
QED
Resume place_store_value_storage_run[equal]:
  fs[expr_val_rel_def] >>
  `val_in_memory dtv v (w2n w) s.vs_memory` by metis_tac[] >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `w2n w + type_memory_size dtv < dimword (:256)` by
    (first_x_assum (qspec_then `w` mp_tac) >> simp[] >> strip_tac >>
     fs[] >> decide_tac) >>
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  qspecl_then [`cenv`, `op`, `dst_op`, `dty`, `tr`, `sa`, `sb`, `dtv`, `func`, `s`,
      `w`, `w2n root + delta`, `ctx`, `cx`, `env`, `ee`, `mid`, `var_name`, `keys`,
      `root`, `tv`, `path`, `delta`, `writes`, `v`] mp_tac
    place_store_slots_suffix_run >>
  (impl_tac >- (fs[] >> metis_tac[])) >>
  strip_tac >> qexists_tac `t` >> gvs[]
QED
Resume place_store_value_storage_run[bytes]:
  fs[expr_val_rel_def] >>
  `val_in_memory stv v (w2n w) s.vs_memory` by metis_tac[] >>
  `~is_word_type sty` by
    (Cases_on `sty` >> fs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     fs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BaseT (BytesT bound)` >> Cases_on `bound` >>
     fs[is_bytestring_type_def, is_word_type_def]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `w2n w + type_memory_size stv < dimword (:256)` by
    (first_x_assum (qspec_then `w` mp_tac) >> simp[] >> strip_tac >>
     fs[] >> decide_tac) >>
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  qspecl_then [`cenv`, `op`, `dst_op`, `dty`, `sty`, `tr`, `sa`, `sb`, `stv`,
      `dtv`, `func`, `s`, `w`, `w2n root + delta`, `ctx`, `cx`, `env`, `ee`,
      `mid`, `var_name`, `keys`, `root`, `tv`, `path`, `delta`, `writes`, `v`]
    mp_tac place_store_slots_bytes_run >>
  (impl_tac >- (fs[] >> metis_tac[])) >>
  strip_tac >> qexists_tac `t` >> gvs[]
QED
Resume place_store_value_storage_run[normalize]:
  `~is_bytestring_type dty` by
    metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source] >>
  `~is_word_type sty` by
    (spose_not_then assume_tac >>
     qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     Cases_on `sty` >> Cases_on `dty` >>
     gvs[type_widens_to_def, is_word_type_def,
         arg_type_fits_def, is_bytestring_type_def] >>
     Cases_on `b` >> Cases_on `b'` >>
     gvs[arg_type_fits_def, is_word_type_def, is_bytestring_type_def] >>
     rename1 `arg_type_fits (BaseT (BytesT bd)) (BaseT (BytesT bd'))` >>
     Cases_on `bd` >> Cases_on `bd'` >>
     gvs[arg_type_fits_def, is_word_type_def, is_bytestring_type_def]) >>
  gvs[] >>
  drule_all place_store_destination_alloc_bound >> strip_tac >>
  fs[expr_val_rel_def] >>
  `?sw. eval_operand op s = SOME sw /\ val_in_memory stv v (w2n sw) s.vs_memory` by
    metis_tac[] >>
  `val_wf stv v /\ val_wf dtv v` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (qpat_x_assum `!sw. eval_operand op s = SOME sw ==> _` (qspec_then `sw` mp_tac) >>
     simp[] >> strip_tac >> gvs[] >> decide_tac) >>
  `cs_extends sa sm` by
    metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends sm sc` by
    (mp_tac (cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`cenv`, `a.buf_operand`, `dty`, `op`, `sty`, `sm`] mp_tac) >>
     simp[ci_mono_def]) >>
  `cs_extends sc sb` by
    (mp_tac (cj 1 stmtLoweringMonoTheory.ci_mono_compile_store_slots) >>
     disch_then (qspecl_then [`cenv`, `a.buf_operand`, `dst_op`, `dty`, `tr`, `sc`]
       mp_tac) >> simp[ci_mono_def]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sc func /\ fn_has_code sc sb func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields)` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next /\
   (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw)` by
    (qpat_assum `!sw. eval_operand op s = SOME sw ==> _` (qspec_then `sw` mp_tac) >>
     simp[arithmeticTheory.ADD_COMM]) >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) place_store_normalize_path >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`cx`, `ctx`, `func`, `ee`, `stv`, `v`, `sw`, `s`] mp_tac) >>
  (impl_tac >- (simp[arithmeticTheory.ADD_COMM] >> metis_tac[])) >>
  disch_then (qx_choose_then `u` (qx_choose_then `dw`
    (map_every assume_tac o CONJUNCTS))) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qspec_then `type_memory_size dtv` (qspec_then `sa` mp_tac)
       exprLoweringPropsTheory.ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
  `sm.cs_next_var <= sc.cs_next_var` by
    (mp_tac (cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`cenv`, `a.buf_operand`, `dty`, `op`, `sty`, `sm`] mp_tac) >>
     simp[ci_mono_def]) >>
  `sa.cs_next_var <= sc.cs_next_var` by decide_tac >>
  `local_ptrs_reserved cenv sc` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!x. a.buf_operand = Var x ==> not_fresh_at sm x` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       comp_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def, comp_ignore_bind_def] >> strip_tac >>
     gvs[not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  `!x. a.buf_operand = Var x \/ dst_op = Var x ==> not_fresh_at sc x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand dst_op u = SOME (root+n2w delta)` by
    (Cases_on `dst_op` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `~u.vs_call_ctx.cc_static` by
    (drule_at (Pat `stmt_state_rel _ _ _ _ _ u`) place_store_storage_write_inv >>
     disch_then drule >> simp[]) >>
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  `?t. gas_marked_path F ctx func u 0 (OK t) /\
    stmt_state_rel ctx func cenv cx
      (set_storage cx ee tr (apply_writes (n2w (w2n root+delta)) writes
        (get_storage cx ee tr))) t /\
    (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x u) /\
    t.vs_allocas = u.vs_allocas /\ t.vs_memory = u.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (qspecl_then [`cenv`, `a.buf_operand`, `dst_op`, `dty`, `tr`, `sc`, `sb`, `dtv`, `func`, `u`,
      `dw`, `w2n root + delta`, `ctx`, `cx`, `env`, `ee`, `mid`, `var_name`, `keys`,
      `root`, `tv`, `path`, `delta`, `writes`, `v`] mp_tac
       place_store_slots_suffix_run >>
     (impl_tac >- (fs[] >> metis_tac[])) >> simp[]) >>
  qexists_tac `t` >>
  conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
       gas_marked_path_then)) >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >> rpt strip_tac >>
  `not_fresh_at sc x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_x_assum `!x. not_fresh_at sc x ==> _` drule >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]
QED
Finalise place_store_value_storage_run
