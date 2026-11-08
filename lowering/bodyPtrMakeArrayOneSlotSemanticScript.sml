(* A single copied storage word may contain tainted dead bytes. *)
Theory bodyPtrMakeArrayOneSlotSemantic
Ancestors
  bodyPtrMakeArrayOneSlotInstalled bodyPtrMakeArrayStorageProbe
  bodyPtrMakeArrayStorageEndpoint exprSimStorageCopy ptrDiscipline
  storageDecodeMemory valueEncodingProofs accountsRelProps venomState
  finite_map pred_set words

Theorem copied_storage_one_slot_robust_decode:
  well_formed_type_value tv /\ slots_in_range st (w2n a) tv /\
  decode_value st (w2n a) tv = SOME v /\ storage_range_agree st rt a tv /\
  type_slot_size tv <= 1 /\ mem_word_at b mem = lookup_storage a rt /\
  (!j. j < 32 /\ b+j IN tainted ==> j IN key_taint keys a) /\
  (!k j. w2n a <= w2n k /\ w2n k < w2n a+type_slot_size tv /\
    j < 32 /\ j IN key_taint keys k ==>
    dead_bytes rt (w2n a) tv (w2n k) j) ==>
  !m. mem_agree_outside tainted mem m ==> val_in_memory tv v b m
Proof
  strip_tac >>
  `!i. i < type_slot_size tv ==>
    mem_word_at (b+32*i) mem = lookup_storage (a+n2w i) rt` by
    (rpt strip_tac >> `i = 0` by decide_tac >> simp[WORD_ADD_0]) >>
  `!i j. i < type_slot_size tv /\ j < 32 /\ b+32*i+j IN tainted ==>
    j IN key_taint keys (a+n2w i)` by
    (rpt strip_tac >> `i = 0` by decide_tac >> gvs[WORD_ADD_0]) >>
  rpt strip_tac >>
  drule_all copied_storage_range_robust_decode >> simp[]
QED

Theorem external_one_slot_robust_ptr_endpoint:
  emit_op (if tr then TLOAD else SLOAD) [src] sa = (Var tmp,sl) /\
  emit_void MSTORE [Var dst; Var tmp] sl = ((),sb) /\ fn_has_code sa sb fn /\
  copy_old_operand sa src /\ not_fresh_at sa dst /\
  op_taint tn src = {} /\ allocas_from 0 s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ eval_operand src s = SOME key /\
  step_inst_base (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [src] [tmp]) s =
    OK (update_var tmp w s) /\
  ptr_covers G tn dst s 32 /\ lookup_var dst s = SOME (n2w b) /\
  b + 32 < dimword(:256) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  well_formed_type_value tv /\ slots_in_range st (w2n key) tv /\
  decode_value st (w2n key) tv = SOME v /\ type_slot_size tv <= 1 /\
  storage_range_agree st (if tr then contract_transient s else contract_storage s) key tv /\
  w = lookup_storage key (if tr then contract_transient s else contract_storage s) /\
  (!k j. w2n key <= w2n k /\ w2n k < w2n key+type_slot_size tv /\
    j < 32 /\ j IN key_taint (if tr then tn.t_trans else tn.t_stor) k ==>
    dead_bytes (if tr then contract_transient s else contract_storage s)
      (w2n key) tv (w2n k) j) ==>
  ?sf H tm.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\ sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    mem_word_at b sf.vs_memory = w /\
    lookup_var dst sf = SOME (n2w b) /\ ptr_covers H tm dst sf 32 /\
    mem_agree_outside {i | b <= i /\ i < b + 32} sf.vs_memory s.vs_memory /\
    tm.t_mem = (tn.t_mem DIFF {i | b <= i /\ i < b + 32}) UNION
      {b + k | k IN key_taint (if tr then tn.t_trans else tn.t_stor) key} /\
    (!i. i < b \/ b + 32 <= i ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sf = lookup_var x s /\ op_prov H (Var x) = op_prov G (Var x) /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    copy_static sf = copy_static s /\ LENGTH s.vs_memory <= LENGTH sf.vs_memory /\
    (!m. mem_agree_outside tm.t_mem sf.vs_memory m ==> val_in_memory tv v b m)
Proof
  strip_tac >> drule_all external_one_slot_installed >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `!j. j < 32 /\ b+j IN tm.t_mem ==>
    j IN key_taint (if tr then tn.t_trans else tn.t_stor) key` by
    (rpt strip_tac >>
     qpat_x_assum `tm.t_mem = _` (fn th => fs[th]) >> gvs[]) >>
  `!m. mem_agree_outside tm.t_mem sf.vs_memory m ==> val_in_memory tv v b m` by
    metis_tac[copied_storage_one_slot_robust_decode] >>
  qexistsl_tac [`sf`, `H`, `tm`] >> metis_tac[]
QED
