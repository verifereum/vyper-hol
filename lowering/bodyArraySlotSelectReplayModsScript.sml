(* Counted replay of the reached storage/transient array selector. *)
Theory bodyArraySlotSelectReplayMods
Ancestors
  bodyFullSubscriptSlotRun bodyFullTargetArrayLoad exprSimSubscriptArraySuffix
  targetSubscriptStorage vyperStorageFootprint vyperStorageBackend
  vyperState vyperAST integer_word integer words

Theorem slot_index_word_range[local]:
  n < dimword (:256) /\ i = (if sgn then w2i iw else &(w2n iw)) ==>
  (idx_in_range sgn iw (n2w n) <=> 0 <= i /\ Num i < n)
Proof
  strip_tac >>
  drule idx_in_range_integer >>
  disch_then (qspecl_then [`iw`,`sgn`] mp_tac) >>
  qpat_x_assum `i = _` (SUBST1_TAC o SYM) >>
  Cases_on `0 <= i` >> simp[] >>
  `&(Num i) = i` by simp[] >>
  pop_assum (SUBST1_TAC o SYM) >> simp[]
QED

Theorem slot_index_nonnegative_word[local]:
  0 <= i /\ i = (if sgn then w2i iw else &(w2n iw)) ==>
  iw = n2w (Num i):256 word
Proof
  strip_tac >>
  `i2w i = iw` by
    (Cases_on `sgn` >- simp[i2w_w2i] >> simp[i2w_def]) >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  `~(i < 0)` by fs[INT_NOT_LT] >>
  qpat_x_assum `i2w i = iw` mp_tac >> simp[i2w_def]
QED

Theorem slot_index_live_range[local]:
  i = (if sgn then w2i iw else &(w2n iw)) /\
  bound_length bd < dimword (:256) /\
  nw = (case bd of Fixed n => n2w n | Dynamic _ => lw) /\
  (!cap. bd = Dynamic cap ==> w2n lw <= cap) ==>
  (idx_in_range sgn iw nw <=>
   0 <= i /\ Num i < bound_length bd /\
   (!cap. bd = Dynamic cap ==> Num i < w2n lw))
Proof
  Cases_on `bd` >> simp[] >> strip_tac
  >- (irule slot_index_word_range >> simp[]) >>
  `w2n lw < dimword (:256)` by simp[w2n_lt] >>
  drule_all slot_index_word_range >>
  simp[] >> strip_tac >> iff_tac >> strip_tac >> simp[] >> decide_tac
QED

Theorem slot_select_source[local]:
  let off = (case bd of Fixed _ => 0 | Dynamic _ => 1) +
            Num i * type_slot_size etv;
      good = (0 <= i /\ Num i < bound_length bd /\
              (!cap. bd = Dynamic cap ==>
                     Num i < w2n (lookup_storage slot (get_storage cx fin tr))))
  in
    ?res.
      (!tail. select_result cx (ArrayT et bd)
          (PlaceR (StoragePlace tr slot (ArrayTV etv bd)))
          (ValueSubscript (IntV i)) (fin with gas_obs := tail) =
        (res,fin with gas_obs := tail)) /\
      (good ==> res = INL (PlaceR (StoragePlace tr (slot + n2w off) etv))) /\
      (~good ==> ?msg. res = INR (Error (RuntimeError msg)))
Proof
  `!tail. get_storage cx (fin with gas_obs := tail) tr = get_storage cx fin tr` by
    (Cases_on `tr` >> simp[get_storage_def]) >>
  Cases_on `bd` >> simp[LET_THM, select_result_def, extend_place_storage_array_index] >>
  Cases_on `0 <= i` >> Cases_on `Num i < n` >> simp[] >>
  Cases_on `Num i < w2n (lookup_storage slot (get_storage cx fin tr))` >> simp[]
QED

Theorem array_slot_select_replay_mods:
  let dyn = (case bd of Fixed _ => F | Dynamic _ => T);
      cnt = (case bd of Fixed n => n | Dynamic _ => 0);
      sgn = is_signed_type (expr_type idx);
      ok = idx_in_range sgn iw nw;
      off = (if dyn then 1 else 0) + Num i * type_slot_size etv
  in
    compile_array_subscript bop iop dyn cnt 1 (type_slot_size etv) sgn
      (compile_ptr_load ctor imm (slot_loc tr)) st2 = (dst,sb) /\
    fn_has_code st2 sb func /\
    eval_operand bop it = SOME slot /\ eval_operand iop it = SOME iw /\
    nw = (if dyn then (if tr then tload slot it else sload slot it) else n2w cnt) /\
    op_taint tni bop = {} /\ op_taint tni iop = {} /\ op_prov Gi iop = NONE /\
    (dyn ==> key_taint (if tr then tni.t_trans else tni.t_stor) slot = {}) /\
    (!x. bop = Var x ==> not_fresh_at st2 x) /\
    (!x. iop = Var x ==> not_fresh_at st2 x) /\
    allocas_from lo it /\ alloca_history func it /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp it) /\
    ~it.vs_halted /\ it.vs_current_bb = st2.cs_current_bb /\
    it.vs_inst_idx = LENGTH st2.cs_current_insts /\
    key = IntV i /\ i = (if sgn then w2i iw else &(w2n iw)) /\
    bound_length bd < dimword (:256) /\ storage_trace_domain cx st0 fin.storage_trace /\
    (!cap. bd = Dynamic cap ==>
       (if tr then tload slot it else sload slot it) =
         lookup_storage slot (get_storage cx fin tr) /\
       w2n (lookup_storage slot (get_storage cx fin tr)) <= cap) ==>
    ?res q Gq tq.
      (!tail. select_result cx (ArrayT et bd)
          (PlaceR (StoragePlace tr slot (ArrayTV etv bd)))
          (ValueSubscript key) (fin with gas_obs := tail) =
        (res,fin with gas_obs := tail)) /\
      storage_trace_domain cx st0 fin.storage_trace /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (it,Gi,tni) []
        ((if ok then OK q else Abort Revert_abort q),Gq,tq)) /\
      (ok ==>
        res = INL (PlaceR (StoragePlace tr (slot + n2w off) etv)) /\
        0 <= i /\ Num i < bound_length bd /\
        (!cap. bd = Dynamic cap ==>
          Num i < w2n (lookup_storage slot (get_storage cx fin tr))) /\
        ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
        q.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func q /\
        array_length_frame st2 it Gi tni q Gq tq /\
        eval_operand dst q = SOME (slot + n2w off) /\
        op_prov Gq dst = op_prov Gi bop /\ op_taint tq dst = {}) /\
      (~ok ==> ?msg. res = INR (Error (RuntimeError msg)))
Proof
  pure_rewrite_tac[LET_THM] >> CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  qabbrev_tac `dyn = case bd of Fixed _ => F | Dynamic _ => T` >>
  qabbrev_tac `cnt = case bd of Fixed n => n | Dynamic _ => 0` >>
  qabbrev_tac `sgn = is_signed_type (expr_type idx)` >>
  strip_tac >>
  drule_all subscript_slot_array_execution >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  disch_then (qx_choose_then `q` (qx_choose_then `Gq` (qx_choose_then `tq`
    (map_every assume_tac o CONJUNCTS)))) >>
  qabbrev_tac `lw = lookup_storage slot (get_storage cx fin tr)` >>
  `nw = (case bd of Fixed n => n2w n | Dynamic _ => lw)` by
    (Cases_on `bd` >> fs[Abbr `dyn`, Abbr `cnt`, Abbr `lw`]) >>
  `!cap. bd = Dynamic cap ==> w2n lw <= cap` by simp[Abbr `lw`] >>
  drule_all_then assume_tac slot_index_live_range >>
  mp_tac slot_select_source >>
  pure_rewrite_tac[LET_THM] >> CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  disch_then (qx_choose_then `res` strip_assume_tac) >>
  qunabbrev_tac `lw` >>
  qexistsl [`res`,`q`,`Gq`,`tq`] >>
  conj_tac >- (qpat_assum `key = IntV i` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (strip_tac >>
      qpat_assum `idx_in_range sgn iw nw <=> _` (drule_then assume_tac o iffLR) >>
      qpat_assum `idx_in_range sgn iw nw ==> _` (drule_then strip_assume_tac) >>
      qpat_assum `_ ==> res = INL _` mp_tac >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      `iw = n2w (Num i)` by
        (qpat_assum `0 <= i /\ _` strip_assume_tac >>
         drule_all_then ACCEPT_TAC slot_index_nonnegative_word) >>
      qpat_x_assum `i = if _ then _ else _` kall_tac >>
      `((if dyn then slot + 1w else slot) + iw * n2w (type_slot_size etv)) =
        slot + n2w ((if dyn then 1 else 0) + Num i * type_slot_size etv)` by
        (qpat_assum `iw = n2w _` SUBST1_TAC >> Cases_on `dyn` >>
         simp[word_mul_n2w, GSYM WORD_ADD_ASSOC, word_add_n2w]) >>
      conj_tac >-
        (qpat_x_assum `res = INL _` mp_tac >> Cases_on `bd` >> simp[Abbr `dyn`]) >>
      qpat_x_assum `eval_operand dst q = SOME _` mp_tac >>
      qpat_assum `((_ + _) : 256 word) = _` (pure_once_rewrite_tac o single) >>
      fs[]) >>
  strip_tac >>
  qpat_assum `~(_ /\ _ /\ _) ==> ?msg. _` irule >>
  qpat_assum `idx_in_range sgn iw nw <=> _` (pure_once_rewrite_tac o single o GSYM) >>
  first_assum ACCEPT_TAC
QED
