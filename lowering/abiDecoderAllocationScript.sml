(* Fixed instruction-site credit: loops reuse ALLOCA sites. *)
Theory abiDecoderAllocation
Ancestors
  abiDecoderTypedContract abiDecoderFrame venomExecSemantics venomState
  finite_map pred_set arithmetic words

Definition abi_decoder_ids_def:
  abi_decoder_ids first last = {i:num | first <= i /\ i < last}
End

Definition abi_decoder_missing_def:
  abi_decoder_missing first last s =
    abi_decoder_ids first last DIFF FDOM s.vs_allocas
End

Definition abi_decoder_budget_def:
  abi_decoder_budget first last b cap s <=>
    b + cap < dimword (:256) /\ b <= s.vs_alloca_next /\
    s.vs_alloca_next + 32 * CARD (abi_decoder_missing first last s) <= b + cap /\
    (!id off sz. id IN abi_decoder_ids first last /\
       FLOOKUP s.vs_allocas id = SOME (off,sz) ==>
       sz = 32 /\ b <= off /\ off + 32 <= s.vs_alloca_next) /\
    (!i j p q. i IN abi_decoder_ids first last /\
       j IN abi_decoder_ids first last /\ i <> j /\
       FLOOKUP s.vs_allocas i = SOME (p,32) /\
       FLOOKUP s.vs_allocas j = SOME (q,32) ==>
       p + 32 <= q \/ q + 32 <= p)
End

Theorem abi_decoder_ids_finite[simp]:
  FINITE (abi_decoder_ids first last)
Proof
  irule SUBSET_FINITE_I >> qexists_tac `count last` >>
  simp[abi_decoder_ids_def, SUBSET_DEF]
QED

Theorem abi_decoder_missing_finite[simp]:
  FINITE (abi_decoder_missing first last s)
Proof
  simp[abi_decoder_missing_def]
QED

Theorem abi_decoder_budget_reservation:
  abi_decoder_budget first last b cap s ==>
  abi_decoder_reservation first last b cap s
Proof
  pure_rewrite_tac[abi_decoder_budget_def, abi_decoder_reservation_def] >>
  strip_tac >> rpt conj_tac >> TRY decide_tac >>
  rpt gen_tac >> strip_tac >>
  `id IN abi_decoder_ids first last` by (simp_tac std_ss [abi_decoder_ids_def, GSPECIFICATION] >> asm_rewrite_tac[]) >>
  qpat_x_assum `!id off sz. _ ==> sz = 32 /\ _` drule >> disch_then drule >> strip_tac >> decide_tac
QED

Theorem abi_decoder_budget_empty:
  (!id. id IN abi_decoder_ids first last ==> FLOOKUP s.vs_allocas id = NONE) /\
  b <= s.vs_alloca_next /\
  s.vs_alloca_next + 32 * CARD (abi_decoder_ids first last) <= b + cap /\
  b + cap < dimword (:256) ==>
  abi_decoder_budget first last b cap s
Proof
  strip_tac >>
  `abi_decoder_missing first last s = abi_decoder_ids first last` by
    (rw[abi_decoder_missing_def, EXTENSION] >>
     eq_tac >- simp[] >> strip_tac >> simp[] >>
     first_x_assum drule >> simp[FLOOKUP_DEF] >>
     Cases_on `x IN FDOM s.vs_allocas` >> simp[]) >>
  rw[abi_decoder_budget_def] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem abi_decoder_missing_insert:
  abi_decoder_missing first last
    (s with vs_allocas := s.vs_allocas |+ (id,(p,32))) =
  abi_decoder_missing first last s DELETE id
Proof
  simp[abi_decoder_missing_def, EXTENSION] >> metis_tac[]
QED

Theorem abi_decoder_missing_credit:
  id IN abi_decoder_ids first last /\ FLOOKUP s.vs_allocas id = NONE ==>
  CARD (abi_decoder_missing first last s) =
    SUC (CARD (abi_decoder_missing first last s DELETE id))
Proof
  strip_tac >>
  `id IN abi_decoder_missing first last s` by
    (gvs[abi_decoder_missing_def, FLOOKUP_DEF] >>
     Cases_on `id IN FDOM s.vs_allocas` >> gvs[]) >>
  `abi_decoder_missing first last s =
    id INSERT (abi_decoder_missing first last s DELETE id)` by
    (simp[EXTENSION] >> metis_tac[]) >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  simp[CARD_INSERT]
QED

Theorem abi_decoder_budget_insert:
  abi_decoder_budget first last b cap s /\
  id IN abi_decoder_ids first last /\ FLOOKUP s.vs_allocas id = NONE ==>
  abi_decoder_budget first last b cap
    (s with <|vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,32));
              vs_alloca_next := s.vs_alloca_next + 32|>)
Proof
  strip_tac >> drule_all abi_decoder_missing_credit >> strip_tac >>
  `abi_decoder_missing first last
     (s with <|vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,32));
               vs_alloca_next := s.vs_alloca_next + 32|>) =
   abi_decoder_missing first last s DELETE id` by
    (simp[abi_decoder_missing_def, EXTENSION] >> metis_tac[]) >>
  qpat_x_assum `abi_decoder_budget _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_decoder_budget_def] >> strip_tac >>
  simp_tac (srw_ss()) [] >>
  rpt conj_tac >> TRY decide_tac
  >- (asm_rewrite_tac[] >> decide_tac)
  >- (rpt gen_tac >> simp_tac std_ss [FLOOKUP_UPDATE] >>
      Cases_on `id = id'` >> asm_rewrite_tac[] >> strip_tac
      >- (full_simp_tac std_ss [optionTheory.SOME_11, pairTheory.PAIR_EQ] >> decide_tac) >>
      qpat_x_assum `!id off sz. _ ==> sz = 32 /\ _` drule >>
      disch_then drule >> strip_tac >> decide_tac) >>
  qpat_x_assum `CARD _ = _` kall_tac >>
  qpat_x_assum `abi_decoder_missing _ _ _ = _` kall_tac >>
  rpt gen_tac >> simp_tac std_ss [FLOOKUP_UPDATE] >>
  Cases_on `id = i` >> Cases_on `id = j` >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  TRY (decide_tac >> NO_TAC) >>
  qpat_x_assum `s.vs_alloca_next + _ <= _` kall_tac >>
  qpat_assum `!id off sz. _ ==> sz = 32 /\ _` imp_res_tac >>
  TRY (qpat_x_assum `SOME _ = SOME _` mp_tac >>
       simp_tac std_ss [] >> strip_tac >> decide_tac >> NO_TAC) >>
  metis_tac[]
QED

Theorem abi_decoder_budget_update_var[simp]:
  abi_decoder_budget first last b cap (update_var out w s) <=>
  abi_decoder_budget first last b cap s
Proof
  simp[abi_decoder_budget_def, abi_decoder_missing_def, update_var_def]
QED

Theorem abi_decoder_alloca32_fresh:
  abi_decoder_budget first last b cap s /\
  inst.inst_id IN abi_decoder_ids first last /\ inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
  ?t. exec_alloca inst s (32w:bytes32) = OK t /\
      abi_decoder_budget first last b cap t /\
      lookup_var out t = SOME (n2w s.vs_alloca_next) /\
      b <= s.vs_alloca_next /\ s.vs_alloca_next + 32 <= b + cap /\
      t.vs_alloca_next = s.vs_alloca_next + 32 /\
      t.vs_allocas = s.vs_allocas |+ (inst.inst_id,(s.vs_alloca_next,32)) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section
Proof
  strip_tac >> drule_all abi_decoder_budget_insert >> strip_tac >>
  drule_all abi_decoder_missing_credit >> strip_tac >>
  simp_tac (srw_ss()) [exec_alloca_def, LET_THM, dimword_def,
                       fcpLib.INDEX_CONV ``dimindex (:256)``] >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- (qpat_x_assum `abi_decoder_budget first last b cap s` kall_tac >>
    qpat_x_assum `abi_decoder_budget _ _ _ _ _` mp_tac >>
    pure_rewrite_tac[abi_decoder_budget_def, abi_decoder_missing_def] >>
    pure_rewrite_tac[venom_state_accfupds, combinTheory.K_THM] >>
    rewrite_tac[]) >>
  qpat_x_assum `abi_decoder_budget first last b cap s` mp_tac >>
  pure_rewrite_tac[abi_decoder_budget_def] >> strip_tac >> decide_tac
QED

Theorem abi_decoder_alloca32_reuse:
  abi_decoder_budget first last b cap s /\
  inst.inst_id IN abi_decoder_ids first last /\ inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (p,sz) ==>
  sz = 32 /\ b <= p /\ p + 32 <= b + cap /\
  exec_alloca inst s (32w:bytes32) = OK (update_var out (n2w p) s) /\
  abi_decoder_budget first last b cap (update_var out (n2w p) s) /\
  (update_var out (n2w p) s).vs_allocas = s.vs_allocas /\
  (update_var out (n2w p) s).vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `sz = 32 /\ b <= p /\ p + 32 <= s.vs_alloca_next` by
    (qpat_assum `abi_decoder_budget _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[abi_decoder_budget_def] >> strip_tac >>
     qpat_x_assum `!id off sz. _ ==> sz = 32 /\ _` drule >>
     disch_then drule >> simp_tac std_ss []) >>
  drule abi_decoder_budget_reservation >> strip_tac >>
  `p + 32 <= b + cap` by
    (qpat_x_assum `abi_decoder_reservation _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[abi_decoder_reservation_def] >> strip_tac >> decide_tac) >>
  simp_tac (srw_ss()) [exec_alloca_def] >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [abi_decoder_budget_update_var] >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [update_var_def]
QED

(* This semantic frame applies to both allocation branches, including reuse. *)
Theorem abi_decoder_alloca_other_sites:
  exec_alloca inst s (32w:bytes32) = OK t /\ id <> inst.inst_id ==>
  FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id /\
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_data_section = s.vs_data_section
Proof
  Cases_on `inst.inst_outputs` >> simp[exec_alloca_def] >>
  Cases_on `t'` >> simp[exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >>
  simp[exec_alloca_def, LET_THM] >>
  TRY (rename1 `SOME pair` >> PairCases_on `pair`) >>
  rw[update_var_def, FLOOKUP_UPDATE] >>
  simp_tac (srw_ss()) [FLOOKUP_UPDATE] >> asm_rewrite_tac[] >>
  IF_CASES_TAC >> metis_tac[]
QED

Theorem abi_decoder_budget_frontier_full:
  abi_decoder_budget first last b cap s /\ s.vs_alloca_next = b + cap /\
  id IN abi_decoder_ids first last ==>
  ?p. FLOOKUP s.vs_allocas id = SOME (p,32)
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all abi_decoder_missing_credit >> strip_tac >>
      qpat_x_assum `abi_decoder_budget _ _ _ _ _` mp_tac >>
      pure_rewrite_tac[abi_decoder_budget_def] >> strip_tac >>
      spose_not_then kall_tac >> decide_tac) >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  qpat_x_assum `abi_decoder_budget _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_decoder_budget_def] >> strip_tac >>
  qpat_x_assum `!id off sz. _ ==> sz = 32 /\ _` drule >>
  disch_then drule >> strip_tac >> asm_rewrite_tac[] >>
  qexists_tac `pair0` >> asm_rewrite_tac[]
QED

(* A repeated site still succeeds when the arena has no fresh credit. *)
Theorem abi_decoder_alloca32_full_reuse:
  abi_decoder_budget first last b cap s /\ s.vs_alloca_next = b + cap /\
  inst.inst_id IN abi_decoder_ids first last /\ inst.inst_outputs = [out] ==>
  ?p. exec_alloca inst s (32w:bytes32) = OK (update_var out (n2w p) s) /\
      abi_decoder_budget first last b cap (update_var out (n2w p) s) /\
      b <= p /\ p + 32 <= b + cap /\
      (update_var out (n2w p) s).vs_alloca_next = b + cap
Proof
  strip_tac >> drule_all abi_decoder_budget_frontier_full >> strip_tac >>
  drule_all abi_decoder_alloca32_reuse >> strip_tac >>
  qexists_tac `p` >> asm_rewrite_tac[]
QED

Theorem abi_decoder_alloca32:
  abi_decoder_budget first last b cap s /\
  inst.inst_id IN abi_decoder_ids first last /\ inst.inst_outputs = [out] ==>
  ?t p. exec_alloca inst s (32w:bytes32) = OK t /\
    abi_decoder_budget first last b cap t /\
    lookup_var out t = SOME (n2w p) /\
    b <= p /\ p + 32 <= b + cap /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (p,32) /\
    (!id. id <> inst.inst_id ==>
       FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (drule_all abi_decoder_alloca32_fresh >> strip_tac >>
      qexistsl_tac [`t`, `s.vs_alloca_next`] >> asm_rewrite_tac[] >>
      simp_tac std_ss [FLOOKUP_UPDATE] >> rpt strip_tac >>
      IF_CASES_TAC >> metis_tac[]) >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  drule_all abi_decoder_alloca32_reuse >> strip_tac >>
  qexistsl_tac [`update_var out (n2w pair0) s`, `pair0`] >>
  asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  asm_rewrite_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_ALLOCATION_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder allocation not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderAllocation");
