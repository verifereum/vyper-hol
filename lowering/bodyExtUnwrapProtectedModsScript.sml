(* Fixed-endpoint observations across an ExtCall row's unwrap. *)
Theory bodyExtUnwrapProtectedMods
Ancestors
  abiEncodeValuesPrefixFrame abiEncodeValuesRun abiEncodeValuesPhases
  localPtrsProps assignTuplePtrCopyLen memoryReadProps freshWrites
  exprLoweringProps loweringPosts bodyPtrDefs loweringStateRelDefs ptrDiscipline
  contractABI valueEncodingDefs compileEnv venomState venomInst
  finite_map pred_set arithmetic list

Theorem registered_clear_of_locals[local]:
  alloca_inv s /\ fn_inst_ids_distinct func /\
  local_ptrs_rel func ce ee.scopes s /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  not_local_ptr ce ee.scopes x /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) ==>
  !nm a n. local_region ce ee.scopes s nm a n ==> b+k <= a \/ a+n <= b
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_tac >>
  pure_rewrite_tac[GSYM loweringStateRelDefsTheory.regions_disjoint_def] >>
  drule_all_then ACCEPT_TAC local_ptrs_rel_alloca_disjoint
QED

Theorem unwrap_subwindow[local]:
  mem_bytes_at b k z.vs_memory = mem_bytes_at b k s.vs_memory /\
  (!j. b <= j /\ j < b+k /\ j IN tz.t_mem ==> j IN tp.t_mem) /\
  b <= q /\ q+n <= b+k ==>
  mem_bytes_at q n z.vs_memory = mem_bytes_at q n s.vs_memory /\
  (!j. q <= j /\ j < q+n /\ j IN tz.t_mem ==> j IN tp.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `q-b+n <= k /\ b+(q-b) = q` by decide_tac >>
  conj_tac
  >- (qspecl_then [`b`,`k`,`q-b`,`n`] mp_tac read_memory_subwindow >>
      asm_rewrite_tac[read_memory_eq_mem_bytes_at] >>
      disch_then (fn th => simp[th])) >>
  gen_tac >> strip_tac >>
  `b <= j /\ j < b+k` by decide_tac >>
  first_x_assum irule >> simp[]
QED

Theorem unwrap_keeps_sources[local]:
  wb_frame ce ee ee prepared s z /\ ghost_kept_at lo ce ee prepared Gp tp s Gz tz /\
  mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  (!j. j < lo /\ j IN tz.t_mem ==> j IN tp.t_mem) ==>
  !q n.
    (q+n <= lo \/
     (?nm b k. local_region ce ee.scopes s nm b k /\ b <= q /\ q+n <= b+k) \/
     (?aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) /\ aid < prepared.cs_next_id /\
       (!nm a m. local_region ce ee.scopes s nm a m ==> b+k <= a \/ a+m <= b) /\
       b <= q /\ q+n <= b+k)) ==>
    mem_bytes_at q n z.vs_memory = mem_bytes_at q n s.vs_memory /\
    (!j. q <= j /\ j < q+n /\ j IN tz.t_mem ==> j IN tp.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> strip_tac
  >- (irule unwrap_subwindow >> qexistsl [`0`,`lo`] >> simp[]) >-
    (irule unwrap_subwindow >> qexistsl [`b`,`k`] >> asm_rewrite_tac[] >>
     fs[wb_frame_def, locals_kept_def, ghost_kept_at_def] >> metis_tac[]) >>
  drule_all abi_encode_values_unwrap_window >> simp[]
QED

Theorem unwrap_keeps_operands[local]:
  wb_frame ce ee ee prepared s z /\ ghost_kept_at lo ce ee prepared Gp tp s Gz tz ==>
  (!op w. (!x. op = Var x ==> not_fresh_at prepared x) /\
    (!lbl. op = Label lbl ==> z.vs_labels = s.vs_labels) /\
    eval_operand op s = SOME w ==>
    eval_operand op z = SOME w /\ op_taint tz op = op_taint tp op) /\
  (!x w n. not_fresh_at prepared x /\ eval_operand (Var x) s = SOME w /\
    ptr_covers Gp tp x s n ==> eval_operand (Var x) z = SOME w /\ ptr_covers Gz tz x z n)
Proof
  simp[wb_frame_def, ghost_kept_at_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (Cases >> simp[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  simp[eval_operand_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_var x z = SOME w` by metis_tac[] >>
  simp[] >> irule ptr_covers_lookup_frame >> qexistsl [`Gp`,`s`,`tp`] >>
  asm_rewrite_tac[] >> metis_tac[]
QED

(* The shared owner and the cursor account for distinct protected windows.
   Source reads may instead be in the low region or a live local. *)
Theorem ext_unwrap_protected_mods:
  abi_encode_values_prefix_at ats avs hl d cursor loc slot i prepared s Gp tp /\
  wb_frame ce ee ee prepared s z /\ ghost_kept_at lo ce ee prepared Gp tp s Gz tz /\
  ci_mono prepared ready /\ alloca_inv s /\ alloca_inv z /\
  fn_inst_ids_distinct func /\ local_ptrs_rel func ce ee.scopes s /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [root] /\
  not_local_ptr ce ee.scopes root /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (pbase,capacity) /\
  inst.inst_id < prepared.cs_next_id /\
  MEM ci (fn_insts func) /\ ci.inst_id = loc /\ ci.inst_outputs = [croot] /\
  not_local_ptr ce ee.scopes croot /\
  pbase <= d /\ d + LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) <= pbase+capacity /\
  d+hl+LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) <= pbase+capacity /\
  32 <= capacity /\ read_memory (pbase+28) 4 s = selector /\
  (!j. pbase+28 <= j /\ j < pbase+32 ==> j NOTIN tp.t_mem) /\
  mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  (!j. j < lo /\ j IN tz.t_mem ==> j IN tp.t_mem) ==>
  abi_encode_values_prefix_at ats avs hl d cursor loc slot i ready z Gz tz /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP z.vs_allocas aid = SOME entry) /\
  read_memory (pbase+28) 4 z = selector /\
  (!j. pbase+28 <= j /\ j < pbase+32 ==> j NOTIN tz.t_mem) /\
  (!op w. (!x. op = Var x ==> not_fresh_at prepared x) /\
    (!lbl. op = Label lbl ==> z.vs_labels = s.vs_labels) /\
    eval_operand op s = SOME w ==>
    eval_operand op z = SOME w /\ op_taint tz op = op_taint tp op) /\
  (!x w n. not_fresh_at prepared x /\ eval_operand (Var x) s = SOME w /\
    ptr_covers Gp tp x s n ==> eval_operand (Var x) z = SOME w /\ ptr_covers Gz tz x z n) /\
  (!q n.
    (q+n <= lo \/
     (?nm b k. local_region ce ee.scopes s nm b k /\ b <= q /\ q+n <= b+k) \/
     (?aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) /\ aid < prepared.cs_next_id /\
       (!nm a m. local_region ce ee.scopes s nm a m ==> b+k <= a \/ a+m <= b) /\
       b <= q /\ q+n <= b+k)) ==>
    mem_bytes_at q n z.vs_memory = mem_bytes_at q n s.vs_memory /\
    (!j. q <= j /\ j < q+n /\ j IN tz.t_mem ==> j IN tp.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `FLOOKUP s.vs_allocas ci.inst_id = SOME (slot,32)` by
    fs[abi_encode_values_prefix_at_def] >>
  `!nm a n. local_region ce ee.scopes s nm a n ==>
      (pbase+capacity <= a \/ a+n <= pbase) /\ (slot+32 <= a \/ a+n <= slot)` by
    (rpt gen_tac >> disch_tac >> conj_tac >>
     (irule registered_clear_of_locals >> metis_tac[])) >>
  drule_all unwrap_keeps_operands >> strip_tac >>
  asm_rewrite_tac[] >> conj_tac
  >- (irule abi_encode_values_prefix_after_unwrap >> metis_tac[]) >>
  conj_tac >- fs[wb_frame_def] >>
  `pbase <= pbase+28 /\ pbase+28+4 <= pbase+capacity` by decide_tac >>
  `!nm a n. local_region ce ee.scopes s nm a n ==> pbase+capacity <= a \/ a+n <= pbase` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!nm a n. local_region _ _ _ nm a n ==> _` (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  drule_all (Q.INST [`q` |-> `pbase+28`, `len` |-> `4`] abi_encode_values_unwrap_window) >>
  strip_tac >>
  conj_tac >- fs[read_memory_eq_mem_bytes_at] >>
  conj_tac
  >- (gen_tac >> strip_tac >> `j < pbase+28+4` by decide_tac >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >> drule_all unwrap_keeps_sources >> simp[]
QED
