(* Shared sparse-store contract. Only the slots in ks are written; all
   other storage taint is retained, including dead capacity of aggregates. *)
Theory storeSlotsPtrInterface
Ancestors
  placeStoreSlots stmtSimStoreCopy assignBasePtrStoragePath assignBasePtrStorageSemantic
  typedCopyLayoutPtr representationCleanPtr reasonCodeOffsetPtr valueEncodingDefs
  bodyPtrDefs fragGasPathPtr ptrDiscipline stateFrame
  compileEnv context loweringStateRelDefs venomState words list pred_set
  finite_map arithmetic rich_list

Definition store_slots_taint_def:
  store_slots_taint tr (sw:bytes32) dw tn ks =
    FOLDL (\ta j. key_update ta (dw + n2w j)
      (mem_word_taint tn.t_mem (w2n sw + 32*j)))
      (if tr then tn.t_trans else tn.t_stor) ks
End

Definition store_slots_ptr_frame_def:
  store_slots_ptr_frame tr sw dw s tn ks u tf <=>
    store_copy_normalize s u =
      FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
        (mload (w2n sw + 32*j) s) q) s ks /\
    u.vs_memory = s.vs_memory /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    (if tr then tf.t_trans else tf.t_stor) =
      store_slots_taint tr sw dw tn ks /\
    (if tr then tf.t_stor else tf.t_trans) =
      (if tr then tn.t_stor else tn.t_trans)
End

(* The coverage is the represented footprint, not unused dynamic capacity.
   Robustness is inherited by children using typedCopyLayoutPtr boundaries. *)
Definition store_slots_ptr_entry_def:
  store_slots_ptr_entry cenv D ctx PG ty tv v <=>
    !root slot tr sa sb func s sw dw writes G tn.
      compile_store_slots cenv (Var root) slot ty tr sa = ((),sb) /\
      not_fresh_at sa root /\
      (!x. slot = Var x ==> not_fresh_at sa x) /\
      lookup_var root s = SOME sw /\ eval_operand slot s = SOME dw /\
      op_taint tn slot = {} /\
      ptr_covers G tn root s (val_footprint tv v) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory tv v (w2n sw) m) /\
      w2n sw + type_memory_size tv < dimword (:256) /\
      w2n dw + type_slot_size tv <= dimword (:256) /\
      encode_value tv v = SOME writes /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx ==>
      ?Gf tf u ks.
        gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK u) /\
        store_slots_ptr_frame tr sw dw s tn ks u tf /\
        (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
        (!x. not_fresh_at sa x ==>
          lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
          op_taint tf (Var x) = op_taint tn (Var x)) /\
        u.vs_allocas = s.vs_allocas /\ u.vs_labels = s.vs_labels /\
        u.vs_call_ctx = s.vs_call_ctx /\
        ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
End

Theorem store_slots_ptr_frame_nil:
  store_slots_ptr_frame tr sw dw s tn [] s tn
Proof
  Cases_on `tr` >> simp[store_slots_ptr_frame_def, store_slots_taint_def,
    store_copy_normalize_def, venom_state_component_equality]
QED

Theorem store_slots_taint_append:
  store_slots_taint tr sw dw tn (xs ++ ys) =
    FOLDL (\ta j. key_update ta (dw + n2w j)
      (mem_word_taint tn.t_mem (w2n sw + 32*j)))
      (store_slots_taint tr sw dw tn xs) ys
Proof
  simp[store_slots_taint_def, FOLDL_APPEND]
QED

(* This exposes a nested header without demanding clean payload bytes. *)
Theorem store_slots_nested_dynarray_header:
  LENGTH vs = LENGTH tvs /\ i < LENGTH tvs /\
  EL i tvs = ArrayTV elem (Dynamic cap) /\
  EL i vs = ArrayV (DynArrayV elems) /\
  (!m. mem_agree_outside tn.t_mem mem m ==>
       tuple_in_memory vs tvs addr m) ==>
  !j. addr + SUM (MAP type_memory_size (TAKE i tvs)) <= j /\
      j < addr + SUM (MAP type_memory_size (TAKE i tvs)) + 32 ==>
      j NOTIN tn.t_mem
Proof
  strip_tac >> gen_tac >> disch_tac >> irule robust_mem_word_at_clean >>
  qexistsl_tac [`addr + SUM (MAP type_memory_size (TAKE i tvs))`,
    `mem`, `n2w (LENGTH elems):bytes32`] >> simp[] >>
  rpt strip_tac >>
  drule_all tuple_in_memory_robust_element >>
  simp[val_in_memory_def]
QED

Theorem store_slots_ptr_frame_compose:
  store_slots_ptr_frame tr sw dw s tn xs u tu /\
  store_slots_ptr_frame tr sw dw u tu ys v tv ==>
  store_slots_ptr_frame tr sw dw s tn (xs ++ ys) v tv
Proof
  simp[store_slots_ptr_frame_def] >> strip_tac >>
  conj_tac >-
    (fs[assign_base_store_backend_fold] >> Cases_on `tr` >>
     gvs[store_copy_normalize_def, venom_state_component_equality,
       mload_def, FOLDL_APPEND, contract_transient_def, contract_storage_def,
       vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM]) >>
  Cases_on `tr` >>
  gvs[store_slots_taint_def, FOLDL_APPEND]
QED

(* A robust word read is untainted even when bytes elsewhere in the same
   represented value are tainted. This is the control-input interface. *)
Theorem store_slots_robust_load_counted:
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [out]) /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\ src <> out /\
  ~ctx_has_dalloca ctx /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    mem_word_at (w2n a) m = w) ==>
  ?Gf tf u.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK u) /\
    lookup_var out u = SOME w /\ op_taint tf (Var out) = {} /\
    FLOOKUP Gf out = NONE /\ ptr_covers Gf tf src u 32 /\
    execution_frame u = execution_frame s /\
    u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = SUC s.vs_inst_idx /\
    ~u.vs_halted /\
    (!x. x <> out ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `mload (w2n a) s = w` by
    (qpat_x_assum `!m. mem_agree_outside _ _ m ==> _`
       (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, mload_def, mem_word_at_def]) >>
  `mem_word_taint tn.t_mem (w2n a) = {}` by
    (drule robust_mem_word_at_clean >>
     simp[mem_word_taint_def, EXTENSION] >> strip_tac >>
     gen_tac >> Cases_on `x < 32` >> simp[] >> first_x_assum irule >> decide_tac) >>
  drule_all assign_base_storage_load_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tf`, `u`] >> gvs[execution_frame_def]
QED

(* Probe the actual control sequence: read a robust length then add a
   constant. No provenance or taint is manufactured by erasing the path. *)
Theorem store_slots_robust_length_add:
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [len]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst (id+1) ADD [Var len; Lit c] [out]) /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\ src <> len /\
  ~ctx_has_dalloca ctx /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    mem_word_at (w2n a) m = w) ==>
  ?Gf tf u.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK u) /\
    lookup_var out u = SOME (w+c) /\ op_taint tf (Var out) = {} /\
    u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    u.vs_inst_idx = s.vs_inst_idx + 2 /\ ~u.vs_halted
Proof
  strip_tac >> drule_all store_slots_robust_load_counted >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 g1 t1 (OK s1)` >>
  `lookup_block s1.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx =
     SOME (mk_inst (id+1) ADD [Var len; Lit c] [out]) /\
   eval_operand (Var len) s1 = SOME w /\ eval_operand (Lit c) s1 = SOME c /\
   op_taint t1 (Lit c) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all assign_base_storage_add_counted >>
  disch_then (qspecl_then [`g1`, `D`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tf`, `u`] >> conj_tac
  >- (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
        (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  gvs[lookup_var_def, update_var_def, ADD1, FLOOKUP_UPDATE]
QED
