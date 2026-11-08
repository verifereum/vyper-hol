(* Robust memory representations constrain only the bytes they read. *)
Theory representationCleanPtr
Ancestors
  bodyPtrDefs valueEncoding valueEncodingProps valueEncodingProofs allocationPtr
  venomState venomMemProofs words list arithmetic vyperTypeABI loweringPosts exprSimProps

Theorem mem_agree_outside_write_byte:
  !m mem i b s.
    s.vs_memory = mem /\ i IN m ==>
    mem_agree_outside m mem
      (write_memory_with_expansion i [b] s).vs_memory
Proof
  rpt strip_tac >> gvs[] >> simp[mem_agree_outside_def] >> rpt strip_tac >>
  sym_tac >> irule write_memory_mem_bytes_at_disjoint >>
  simp[] >> `i <> i'` by metis_tac[] >> decide_tac
QED

Theorem mem_bytes_at_eq_byte:
  !a n mem1 mem2 i.
    mem_bytes_at a n mem1 = mem_bytes_at a n mem2 /\
    a <= i /\ i < a + n ==>
    mem_bytes_at i 1 mem1 = mem_bytes_at i 1 mem2
Proof
  rpt strip_tac >>
  `i - a < n /\ a + (i - a) = i` by decide_tac >>
  `EL (i - a) (mem_bytes_at a n mem1) =
   EL (i - a) (mem_bytes_at a n mem2)` by simp[] >>
  gvs[EL_mem_bytes_at] >>
  irule listTheory.LIST_EQ >> simp[EL_mem_bytes_at]
QED

Theorem robust_mem_bytes_at_clean:
  !m mem a n bs.
    (!mem'. mem_agree_outside m mem mem' ==>
            mem_bytes_at a n mem' = bs) ==>
    !i. a <= i /\ i < a+n ==> i NOTIN m
Proof
  rpt gen_tac >> disch_tac >> gen_tac >> strip_tac >>
  spose_not_then assume_tac >>
  qabbrev_tac `s = (ARB:venom_state) with vs_memory := mem` >>
  `mem_agree_outside m mem
     (write_memory_with_expansion i [0w] s).vs_memory /\
   mem_agree_outside m mem
     (write_memory_with_expansion i [1w] s).vs_memory` by
    (conj_tac >> irule mem_agree_outside_write_byte >> simp[Abbr `s`]) >>
  `mem_bytes_at a n (write_memory_with_expansion i [0w] s).vs_memory =
   mem_bytes_at a n (write_memory_with_expansion i [1w] s).vs_memory` by
    metis_tac[] >>
  drule_all mem_bytes_at_eq_byte >>
  simp[SRULE [] (Q.SPECL [`i`, `[0w]`, `s`] write_memory_mem_bytes_at_same),
       SRULE [] (Q.SPECL [`i`, `[1w]`, `s`] write_memory_mem_bytes_at_same)]
QED

Theorem robust_mem_word_at_clean:
  !m mem a w.
    (!mem'. mem_agree_outside m mem mem' ==>
            mem_word_at a mem' = w) ==>
    !i. a <= i /\ i < a+32 ==> i NOTIN m
Proof
  rpt gen_tac >> disch_tac >>
  `!mem'. mem_agree_outside m mem mem' ==>
     mem_bytes_at a 32 mem' = word_to_bytes w T` by
    (rpt strip_tac >>
     `word_of_bytes T (0w:bytes32) (mem_bytes_at a 32 mem') = w` by
       (first_x_assum drule >> simp[mem_word_at_def, mem_bytes_at_def]) >>
     `word_to_bytes (word_of_bytes T (0w:bytes32) (mem_bytes_at a 32 mem')) T =
       mem_bytes_at a 32 mem'` by
       (irule word_bytes_roundtrip_proof >>
        simp[mem_bytes_at_def, dividesTheory.divides_def]) >> metis_tac[]) >>
  drule robust_mem_bytes_at_clean >> simp[]
QED

Theorem robust_val_in_memory_prim_clean:
  !m mem ty v a.
    ((?b. v = BoolV b) \/ (?n. v = IntV n) \/
     (?k. v = FlagV k) \/ (?n. v = DecimalV n)) /\
    (!mem'. mem_agree_outside m mem mem' ==> val_in_memory ty v a mem') ==>
    !i. a <= i /\ i < a+32 ==> i NOTIN m
Proof
  rpt gen_tac >> strip_tac >> gvs[val_in_memory_def] >>
  drule robust_mem_word_at_clean >> simp[]
QED

Theorem val_in_memory_bytes_word:
  !ty bs a mem.
    val_in_memory ty (BytesV bs) a mem ==>
    mem_word_at a mem =
      (if ty = BaseTV AddressT \/ (?k. ty = BaseTV (BytesT (Fixed k)))
       then typed_val_to_w256 ty (BytesV bs) else n2w (LENGTH bs))
Proof
  Cases >> simp[val_in_memory_def]
  >- (Cases_on `b` >> simp[] >> Cases_on `b'` >> simp[])
QED

Theorem val_in_memory_bytes_payload:
  !ty bs a mem.
    ty <> BaseTV AddressT /\ (!k. ty <> BaseTV (BytesT (Fixed k))) /\
    val_in_memory ty (BytesV bs) a mem ==>
    mem_bytes_at (a+32) (LENGTH bs) mem = bs
Proof
  Cases >> simp[val_in_memory_def]
  >- (Cases_on `b` >> simp[] >> Cases_on `b'` >> simp[])
QED

Theorem robust_val_in_memory_bytes_clean:
  !m mem ty bs a.
    (!mem'. mem_agree_outside m mem mem' ==>
            val_in_memory ty (BytesV bs) a mem') ==>
    (!i. a <= i /\ i < a+32 ==> i NOTIN m) /\
    ((ty <> BaseTV AddressT /\
      (!k. ty <> BaseTV (BytesT (Fixed k)))) ==>
     !i. a+32 <= i /\ i < a+32+LENGTH bs ==> i NOTIN m)
Proof
  rpt gen_tac >> disch_tac >> conj_tac
  >- (`!mem'. mem_agree_outside m mem mem' ==>
         mem_word_at a mem' =
           (if ty = BaseTV AddressT \/ (?k. ty = BaseTV (BytesT (Fixed k)))
            then typed_val_to_w256 ty (BytesV bs) else n2w (LENGTH bs))` by
        metis_tac[val_in_memory_bytes_word] >>
      drule robust_mem_word_at_clean >> simp[]) >>
  strip_tac >>
  `!mem'. mem_agree_outside m mem mem' ==>
     mem_bytes_at (a+32) (LENGTH bs) mem' = bs` by
    metis_tac[val_in_memory_bytes_payload] >>
  drule robust_mem_bytes_at_clean >> simp[]
QED

Theorem robust_val_in_memory_string_clean:
  !m mem ty str a.
    (!mem'. mem_agree_outside m mem mem' ==>
            val_in_memory ty (StringV str) a mem') ==>
    (!i. a <= i /\ i < a+32 ==> i NOTIN m) /\
    (!i. a+32 <= i /\ i < a+32+LENGTH str ==> i NOTIN m)
Proof
  rpt gen_tac >> disch_tac >>
  `!mem'. mem_agree_outside m mem mem' ==>
     mem_word_at a mem' = n2w (LENGTH str)` by
    (gvs[val_in_memory_def] >> metis_tac[]) >>
  `!mem'. mem_agree_outside m mem mem' ==>
     mem_bytes_at (a+32) (LENGTH str) mem' = MAP (n2w o ORD) str` by
    (gvs[val_in_memory_def] >> metis_tac[]) >>
  conj_tac
  >- (drule robust_mem_word_at_clean >> simp[]) >>
  drule robust_mem_bytes_at_clean >> simp[]
QED

(* The static ABI theorem includes sparse defaults and all copied bytes. *)
Theorem robust_val_in_memory_static_clean:
  !env ty tv v m mem a.
    evaluate_type env ty = SOME tv /\
    ~is_dynamic (vyper_to_abi_type env ty) /\ value_has_type tv v /\
    (!mem'. mem_agree_outside m mem mem' ==> val_in_memory tv v a mem') ==>
    !i. a <= i /\ i < a + type_memory_size tv ==> i NOTIN m
Proof
  rpt gen_tac >> strip_tac >>
  `?av. vyper_to_abi env ty v = SOME av` by
    metis_tac[vyper_to_abi_total] >>
  `!mem'. mem_agree_outside m mem mem' ==>
     mem_bytes_at a (type_memory_size tv) mem' =
       enc (vyper_to_abi_type env ty) av` by
    (rpt strip_tac >> irule val_in_memory_static_abi >> metis_tac[]) >>
  drule robust_mem_bytes_at_clean >> simp[]
QED

Theorem ptr_val_ok_static_clean:
  !cx ty tv v op G tn s w.
    ptr_val_ok cx ty v op G tn s /\ ~is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    ~is_dynamic (vyper_to_abi_type (get_tenv cx) ty) /\
    value_has_type tv v /\ eval_operand op s = SOME w ==>
    !i. w2n w <= i /\ i < w2n w + type_memory_size tv ==> i NOTIN tn.t_mem
Proof
  rpt gen_tac >> strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem` by
    (gvs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]) >>
  metis_tac[robust_val_in_memory_static_clean]
QED

(* Nonempty reads obtain their operand and provenance from the expression
   ghost.  Empty values deliberately do not promise a pointer variable. *)
Theorem ptr_val_ok_read_covers:
  !cx ty v op G tn s tv w m.
    ptr_val_ok cx ty v op G tn s /\ ~is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w /\ val_footprint tv v <> 0 /\
    m <= val_footprint tv v ==>
    ?p. op = Var p /\ ptr_covers G tn p s m
Proof
  rpt strip_tac >>
  fs[ptr_val_ok_def, ptr_mem_ok_def] >>
  gvs[] >> simp[ptr_covers_def] >>
  qexists_tac `w` >>
  qspecl_then [`tv`, `v`] assume_tac exprSimPropsTheory.val_footprint_le_store_size >>
  gvs[eval_operand_def] >> decide_tac
QED

Theorem static_val_footprint:
  !env ty tv v.
    evaluate_type env ty = SOME tv /\
    ~is_dynamic (vyper_to_abi_type env ty) /\ value_has_type tv v ==>
    val_footprint tv v = type_memory_size tv
Proof
  rpt strip_tac >> Cases_on `v` >> simp[loweringPostsTheory.val_footprint_def] >>
  Cases_on `ty` >>
  gvs[vyperValueTheory.evaluate_type_def, vyperABITheory.vyper_to_abi_type_def,
      vyperTypingTheory.value_has_type_def, AllCaseEqs()] >>
  Cases_on `b` >>
  gvs[vyperABITheory.vyper_base_to_abi_type_def, loweringPostsTheory.val_footprint_def,
      contractABITheory.is_dynamic_def, vyperTypingTheory.value_has_type_def, AllCaseEqs()]
QED

(* Positive semantic reads are bounded by the actual allocation frontier. *)
Theorem expr_val_at_read_bound:
  !ctx func cenv cx ty sa sb es v op s tv w n.
    stmt_state_rel ctx func cenv cx es s /\
    expr_val_at cenv cx ty sa sb es v op s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    eval_operand op s = SOME w /\ 0 < n /\ n <= val_footprint tv v ==>
    w2n w + n <= dimword (:256)
Proof
  rpt strip_tac >>
  `w2n w <= w2n w + n - 1 /\
   w2n w + n - 1 < w2n w + val_footprint tv v` by decide_tac >>
  `w2n w + n - 1 < s.vs_alloca_next` by
    (drule_all expr_val_at_below_frontier >> simp[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule exprLoweringPropsTheory.alloca_room_next_lt >>
     fs[exprLoweringPropsTheory.stmt_state_rel_def] >> metis_tac[]) >>
  decide_tac
QED

Theorem raw_val_footprint_covers:
  !tv v n.
    val_wf tv v /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs /\
           tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k)))) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    32 + n <= val_footprint tv v
Proof
  rpt strip_tac >> gvs[val_wf_def, loweringPostsTheory.val_footprint_def] >>
  Cases_on `tv` >> gvs[] >> Cases_on `b` >> gvs[] >>
  Cases_on `b'` >> gvs[] >> Cases_on `b` >> gvs[]
QED

Theorem expr_val_at_raw_return_resources:
  !ctx func cenv cx ty sa sb es v op s tv w G tn n.
    stmt_state_rel ctx func cenv cx es s /\
    expr_val_at cenv cx ty sa sb es v op s /\
    ptr_val_ok cx ty v op G tn s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    eval_operand op s = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs /\
           tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k)))) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    ?src. op = Var src /\ lookup_var src s = SOME w /\
      ptr_covers G tn src s (32+n) /\ n < dimword (:256) /\
      w2n w + 32 + n <= dimword (:256) /\
      mem_word_at (w2n w) s.vs_memory = n2w n /\
      (!i. w2n w <= i /\ i < w2n w+32+n ==> i NOTIN tn.t_mem)
Proof
  rpt gen_tac >> strip_tac >>
  `val_wf tv v` by (fs[loweringPostsTheory.expr_val_at_def] >> metis_tac[]) >>
  `32 + n <= val_footprint tv v` by metis_tac[raw_val_footprint_covers] >>
  `0 < 32 + n /\ val_footprint tv v <> 0` by decide_tac >>
  `w2n w + (32+n) <= dimword (:256)` by
    (drule_all expr_val_at_read_bound >> simp[]) >>
  `?src. op = Var src /\ ptr_covers G tn src s (32+n)` by
    (drule_all ptr_val_ok_read_covers >> simp[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem` by
    (fs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]) >>
  `val_in_memory tv v (w2n w) s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  qexists_tac `src` >>
  `lookup_var src s = SOME w` by gvs[eval_operand_def] >>
  `n < dimword (:256) /\ w2n w + 32 + n <= dimword (:256)` by decide_tac >>
  gvs[]
  >- (conj_tac
      >- (drule val_in_memory_bytes_word >> simp[]) >>
      drule robust_val_in_memory_bytes_clean >> simp[] >>
      rpt strip_tac >> Cases_on `i < w2n w + 32` >> metis_tac[NOT_LESS]) >>
  conj_tac >- fs[val_in_memory_def] >>
  drule robust_val_in_memory_string_clean >>
  rpt strip_tac >>
  Cases_on `i < w2n w + 32`
  >- (qpat_x_assum `!i. w2n w <= i /\ i < w2n w + 32 ==> _`
        (qspec_then `i` mp_tac) >> simp[]) >>
  `w2n w + 32 <= i /\ i < w2n w + 32 + LENGTH str` by decide_tac >>
  qpat_x_assum `!i. w2n w + 32 <= i /\ _ ==> _`
    (qspec_then `i` mp_tac) >> simp[]
QED
