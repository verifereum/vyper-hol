(* One future receipt, protected until the distinguished caller is popped.
   This local probe does not establish DFT independence at setup, a residual
   caller schedule relation after return, or a uniform raw-observation bound. *)
Theory dftOpenReservation
Ancestors
  dftOpenMachine pred_set arithmetic

Definition dft_reserve_index_def:
  dft_reserve_index (q:num) (j:num) =
    if j = 0 then q else if j <= q then j - 1 else j
End

Definition dft_reserve_oracle_def:
  dft_reserve_oracle q (a:num -> 256 word) j = a (dft_reserve_index q j)
End

Theorem dft_reserve_oracle_zero[simp]:
  dft_reserve_oracle q a 0 = a q
Proof
  simp[dft_reserve_oracle_def, dft_reserve_index_def]
QED

Theorem dft_reserve_oracle_inside:
  n < q ==> dft_reserve_oracle q a (SUC n) = a n
Proof
  simp[dft_reserve_oracle_def, dft_reserve_index_def]
QED

Theorem dft_reserve_oracle_after:
  q < n ==> dft_reserve_oracle q a n = a n
Proof
  simp[dft_reserve_oracle_def, dft_reserve_index_def]
QED

Theorem dft_reserve_index_bij:
  BIJ (dft_reserve_index q) UNIV UNIV
Proof
  simp[BIJ_DEF, INJ_DEF, SURJ_DEF, dft_reserve_index_def] >>
  gen_tac >> Cases_on `x < q`
  >- (qexists_tac `SUC x` >> simp[]) >>
  Cases_on `x = q`
  >- (qexists_tac `0` >> simp[]) >>
  qexists_tac `x` >> simp[]
QED

Theorem dft_reserve_support_bij:
  BIJ (dft_reserve_index q)
    {j | dft_reserve_oracle q a j <> 0w} {j | a j <> 0w}
Proof
  mp_tac dft_reserve_index_bij >>
  simp[BIJ_DEF, INJ_DEF, SURJ_DEF, dft_reserve_oracle_def] >>
  metis_tac[]
QED

Theorem dft_reserve_support_finite:
  FINITE {j | a j <> 0w} ==>
  FINITE {j | dft_reserve_oracle q a j <> 0w}
Proof
  metis_tac[dft_reserve_support_bij, BIJ_FINITE_IFF]
QED

Theorem dft_reserve_support_card:
  FINITE {j | a j <> 0w} ==>
  CARD {j | dft_reserve_oracle q a j <> 0w} = CARD {j | a j <> 0w}
Proof
  metis_tac[dft_reserve_support_finite, dft_reserve_support_bij, FINITE_BIJ_CARD]
QED

Definition dft_protected_pair_def:
  dft_protected_pair fs ft rs rt target source <=>
    ?c k n. target = DftOpen c (k ++ ft::rt) n /\
      source = DftOpen c (k ++ fs::rs) (SUC n)
End

Theorem dft_protected_deliver[local]:
  dft_open_deliver fn budget bb inst s (k ++ ft::rt) n r =
    DftOpen c' (k' ++ ft::rt) n' ==>
  dft_open_deliver fn budget bb inst s (k ++ fs::rs) (SUC n) r =
    DftOpen c' (k' ++ fs::rs) (SUC n')
Proof
  Cases_on `r` >> simp[dft_open_deliver_def] >> rpt strip_tac >> gvs[]
QED

Theorem dft_protected_step:
  dft_open_next a ctx (DftOpen c (k ++ ft::rt) n) =
    DftOpen c' (k' ++ ft::rt) n' /\ n' <= q /\
  ~(k = [] /\ ?r. c = DftDone r) ==>
  dft_open_next (dft_reserve_oracle q a) ctx
    (DftOpen c (k ++ fs::rs) (SUC n)) =
    DftOpen c' (k' ++ fs::rs) (SUC n')
Proof
  Cases_on `c`
  >- (rename1 `DftEnter fn fuel s` >>
      Cases_on `fuel` >> simp[dft_open_next_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >- (rename1 `DftAt fn budget bb s` >>
      Cases_on `get_instruction bb s.vs_inst_idx` >>
      simp[dft_open_next_def] >> rename1 `SOME inst` >>
      Cases_on `inst.inst_opcode = INVOKE`
      >- (simp[dft_open_invoke_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
      Cases_on `inst.inst_opcode = GAS`
      >- (simp[AllCaseEqs()] >> rpt strip_tac >>
          `n < q` by
            (qpat_x_assum `dft_open_deliver _ _ _ _ _ _ _ _ = _` mp_tac >>
             simp[dft_open_deliver_def] >> strip_tac >> gvs[]) >>
          gvs[dft_reserve_oracle_inside] >>
          drule dft_protected_deliver >> simp[]) >>
      simp[] >> rpt strip_tac >> drule dft_protected_deliver >> simp[]) >>
  rename1 `DftDone r` >> namedCases_on `k` ["", "frame inner"] >> simp[] >>
  Cases_on `frame` >> Cases_on `r` >>
  simp[dft_open_next_def, dft_open_return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> drule dft_protected_deliver >> simp[]
QED

Theorem dft_protected_prefixes:
  (!j. j <= t ==>
    FUNPOW (dft_open_next a ctx) j (DftOpen c0 (ft::rt) 0) =
      DftOpen (c j) (k j ++ ft::rt) (n j) /\ n j <= q) /\
  (!j. j < t ==> ~(k j = [] /\ ?r. c j = DftDone r)) ==>
  !j. j <= t ==>
    FUNPOW (dft_open_next (dft_reserve_oracle q a) ctx) j
      (DftOpen c0 (fs::rs) 1) =
      DftOpen (c j) (k j ++ fs::rs) (SUC (n j))
Proof
  strip_tac >> Induct
  >- (qpat_x_assum `!j. j <= t ==> _ /\ _`
        (qspec_then `0` mp_tac) >> simp[] >> strip_tac >> gvs[]) >>
  strip_tac >>
  `j <= t /\ j < t` by simp[] >>
  `FUNPOW (dft_open_next (dft_reserve_oracle q a) ctx) j
      (DftOpen c0 (fs::rs) 1) =
      DftOpen (c j) (k j ++ fs::rs) (SUC (n j))` by metis_tac[] >>
  simp[FUNPOW_SUC] >> irule dft_protected_step >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  qexistsl_tac [`ft`, `rt`] >>
  metis_tac[FUNPOW_SUC]
QED

Theorem dft_protected_pair_observe:
  dft_protected_pair fs ft rs rt target source ==>
  (dft_open_observe fn inst s target <=> dft_open_observe fn inst s source)
Proof
  simp[dft_protected_pair_def, dft_open_observe_def] >> rpt strip_tac >>
  Cases_on `c` >> simp[]
QED

Theorem dft_protected_pair_return:
  dft_protected_pair fs ft rs rt
    (DftOpen (DftDone (IntRet ret cs)) (ft::rt) q) source ==>
  source = DftOpen (DftDone (IntRet ret cs)) (fs::rs) (SUC q)
Proof
  simp[dft_protected_pair_def] >> rpt strip_tac >> gvs[]
QED

Theorem dft_reserve_receipt:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = GAS /\ inst.inst_outputs = [out] ==>
  dft_open_next a ctx (DftOpen (DftAt fn budget bb s) stack q) =
    DftOpen (DftAt fn budget bb
      ((update_var out (dft_reserve_oracle q a 0) s) with
        vs_inst_idx := SUC s.vs_inst_idx)) stack (SUC q) /\
  (!j. SUC q <= j ==> dft_reserve_oracle q a j = a j)
Proof
  strip_tac >> conj_tac
  >- (simp[] >> irule dft_open_single_gas >> simp[]) >>
  simp[dft_reserve_oracle_after]
QED

(* Setup premises deliberately expose the remaining DFT-independence task:
   both calls must set up the same cs despite the reserved caller-local GAS.
   No result after popping the distinguished frames is claimed. *)
Theorem dft_reserve_gas_call_setup:
  get_instruction bb s.vs_inst_idx = SOME gas /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [out] /\
  s1 = (update_var out (a q) s with vs_inst_idx := SUC s.vs_inst_idx) /\
  get_instruction bb s1.vs_inst_idx = SOME call /\
  call.inst_opcode = INVOKE /\ decode_invoke call = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s1 = SOME args /\ setup_callee callee args s1 = SOME cs /\
  get_instruction bt st.vs_inst_idx = SOME ct /\
  ct.inst_opcode = INVOKE /\ decode_invoke ct = SOME (nt, ot) /\
  lookup_function nt ctx.ctx_functions = SOME callee /\
  eval_operands ot st = SOME at /\ setup_callee callee at st = SOME cs ==>
  dft_protected_pair (DftCaller fn budget bb call s1)
    (DftCaller ft budget bt ct st) rs rt
    (dft_open_next a ctx (DftOpen (DftAt ft budget bt st) rt 0))
    (FUNPOW (dft_open_next (dft_reserve_oracle q a) ctx) 2
      (DftOpen (DftAt fn budget bb s) rs 0)) /\
  dft_open_next a ctx (DftOpen (DftAt ft budget bt st) rt 0) =
    DftOpen (DftEnter callee budget cs) (DftCaller ft budget bt ct st::rt) 0 /\
  FUNPOW (dft_open_next (dft_reserve_oracle q a) ctx) 2
    (DftOpen (DftAt fn budget bb s) rs 0) =
    DftOpen (DftEnter callee budget cs) (DftCaller fn budget bb call s1::rs) 1
Proof
  strip_tac >>
  `dft_open_next (dft_reserve_oracle q a) ctx
    (DftOpen (DftAt fn budget bb s) rs 0) =
    DftOpen (DftAt fn budget bb s1) rs 1` by
      (drule_all dft_open_single_gas >> simp[]) >>
  `dft_open_next (dft_reserve_oracle q a) ctx
    (DftOpen (DftAt fn budget bb s1) rs 1) =
    DftOpen (DftEnter callee budget cs) (DftCaller fn budget bb call s1::rs) 1` by
      (irule dft_open_invoke_push >> simp[] >> metis_tac[]) >>
  `dft_open_next a ctx (DftOpen (DftAt ft budget bt st) rt 0) =
    DftOpen (DftEnter callee budget cs) (DftCaller ft budget bt ct st::rt) 0` by
      (irule dft_open_invoke_push >> simp[] >> metis_tac[]) >>
  gvs[] >> simp[FUNPOW_2, dft_protected_pair_def]
QED
