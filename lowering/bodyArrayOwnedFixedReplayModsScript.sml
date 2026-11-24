(* A fixed-array selection uses the declared count and the already owned
   memory interval. Missing sparse entries still have their default value. *)
Theory bodyArrayOwnedFixedReplayMods
Ancestors
  bodyArrayOwnedSelectViewMods exprSimSubscriptArraySource
  exprSimSubscriptArraySuffix exprSimVVFrame exprSimCopy
  exprSimIfExpWidenedOwnedProvenance exprSimArrayIndex typedCopyLayoutPtr
  overflowElimHelpers exprLowering exprLoweringProps exprSimProps
  valueTypingMemoryProps vyperArray vyperValueOperation vyperValue
  vyperLookupStorage vyperAssignPreservesType valueEncoding integer_word
  vyperTyping loweringPosts bodyPtrDefs ptrDiscipline bodyFullTargetArrayLoad
  venomState context vyperState exprSimMemDefs vyperAST words

Theorem owned_fixed_bounds[local]:
  n < dimword (:256) /\ i = (if sgn then w2i iw else &(w2n iw)) ==>
  if idx_in_range sgn iw (n2w n) then
    0 <= i /\ Num i < n /\ iw = n2w (Num i) /\
    (?v. array_index (ArrayTV etv (Fixed n)) (SArrayV kvs) i = SOME v)
  else
    evaluate_subscripts (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs))
      [ValueSubscript (IntV i)] = INR (RuntimeError "evaluate_subscripts array_index")
Proof
  strip_tac >>
  `idx_in_range sgn iw (n2w n) <=> 0 <= i /\ i < &n` by
    (drule idx_in_range_integer >> disch_then (qspecl_then [`iw`,`sgn`] mp_tac) >> simp[]) >>
  Cases_on `idx_in_range sgn iw (n2w n)`
  >- (`0 <= i /\ i < &n` by metis_tac[] >>
      `Num i < n` by
        (qpat_assum `0 <= i` mp_tac >> qpat_assum `i < &n` mp_tac >>
         rpt (pop_assum kall_tac) >> intLib.COOPER_TAC) >>
      `iw = n2w (Num i)` by
        (Cases_on `sgn` >> gvs[] >>
         drule nonneg_w2i_eq_w2n >>
         disch_then (fn th => once_rewrite_tac [GSYM th]) >> simp[]) >>
      `valid_index (ArrayTV etv (Fixed n)) (SArrayV kvs) i` by
        simp[valid_index_def,array_length_def,IgnAsm `i = if _ then _ else _`] >>
      drule array_index_valid >>
      Cases_on `array_index (ArrayTV etv (Fixed n)) (SArrayV kvs) i` >>
      simp[IgnAsm `i = if _ then _ else _`]) >>
  simp[IgnAsm `idx_in_range _ _ _ <=> _`] >> irule evaluate_array_subscript_oob >>
  simp[valid_index_def,array_length_def] >> metis_tac[]
QED

Theorem owned_fixed_layout[local]:
  evaluate_type (get_tenv cx) et = SOME etv /\
  value_has_type (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  array_index (ArrayTV etv (Fixed n)) (SArrayV kvs) i = SOME v /\
  0 <= i /\ Num i < n /\
  j = Num i * type_memory_size etv /\
  w2n (a:256 word) + n * type_memory_size etv < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem u.vs_memory m ==>
       val_in_memory (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs)) (w2n a) m) ==>
  value_has_type etv v /\ val_wf etv v /\ j + type_memory_size etv <= n * type_memory_size etv /\
  w2n (a + n2w j) = w2n a + j /\
  (!m. mem_agree_outside tn.t_mem u.vs_memory m ==> val_in_memory etv v (w2n a + j) m)
Proof
  strip_tac >>
  `well_formed_type_value etv` by metis_tac[evaluate_type_well_formed] >>
  `value_has_type etv v` by metis_tac[array_index_has_type] >>
  `val_wf etv v /\ val_wf (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs))` by
    simp[value_has_type_memory_wf] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[array_index_element_end_bound,arithmeticTheory.ADD_COMM] >>
  conj_tac
  >- (qpat_assum `j = _` SUBST1_TAC >>
      irule fixed_array_element_nonwrapping >> qexistsl [`SArrayV kvs`,`n`,`v`] >>
      simp[val_footprint_def,type_memory_size_def]) >>
  `v = (case ALOOKUP kvs (Num i) of NONE => default_value etv | SOME x => x)` by
    (Cases_on `ALOOKUP kvs (Num i)` >> fs[array_index_sarray]) >>
  qpat_assum `j = _` SUBST1_TAC >> rpt strip_tac >>
  irule sarray_in_memory_robust_element >> qexistsl [`n`,`kvs`,`u.vs_memory`,`tn`] >> simp[]
QED

Theorem owned_fixed_readonly[local]:
  array_length_frame sn u G tn q Gq tq /\ local_ptrs_reserved ce sn ==>
  q.vs_memory = u.vs_memory /\ q.vs_allocas = u.vs_allocas /\
  q.vs_alloca_next = u.vs_alloca_next /\ tq.t_mem = tn.t_mem /\
  (!bop. (!x. bop = Var x ==> not_fresh_at sn x) ==> eval_operand bop q = eval_operand bop u) /\
  (!fin name b sz. local_region ce fin.scopes q name b sz ==>
                   local_region ce fin.scopes u name b sz)
Proof
  strip_tac >>
  `q = u with <|vs_vars := q.vs_vars; vs_inst_idx := q.vs_inst_idx|>` by
    (qpat_assum `array_length_frame _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [array_length_frame_def]) >>
     strip_tac >> qpat_assum `_ = u` (fn th =>
       CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) >> simp[]) >>
  `q.vs_labels = u.vs_labels /\ q.vs_memory = u.vs_memory /\
   q.vs_allocas = u.vs_allocas /\ q.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `q = u with <|vs_vars := _; vs_inst_idx := _|>` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  fs[array_length_frame_def] >> conj_tac
  >- (Cases >> simp[eval_operand_def]) >>
  `!x. not_fresh_at sn x ==> lookup_var x q = lookup_var x u` by simp[] >>
  rpt gen_tac >> disch_tac >>
  drule_all copy_buffer_local_region_frame >>
  disch_then (qspecl_then [`fin.scopes`,`name`,`b`,`sz`] (fn th => fs[th]))
QED

Theorem owned_fixed_child_region[local]:
  vv_own ce cx (ArrayT et (Fixed n)) sa sn fin (Value av)
    (LocatedValue (ArrayT et (Fixed n)) (mk_ptr bop LocMemory)) u /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  evaluate_type (get_tenv cx) et = SOME etv /\ val_wf etv v /\
  eval_operand bop u = SOME w /\ eval_operand bop q = SOME w /\
  eval_operand dst q = SOME dw /\ w2n dw = w2n w + j /\
  j + type_memory_size etv <= n * type_memory_size etv /\
  q.vs_allocas = u.vs_allocas /\ sn.cs_next_id <= sb.cs_next_id /\
  (!nm b sz. local_region ce fin.scopes q nm b sz ==> local_region ce fin.scopes u nm b sz) ==>
  vv_at ce cx et sa sb fin (Value v) (LocatedValue et (mk_ptr dst LocMemory)) q /\
  vv_own ce cx et sa sb fin (Value v) (LocatedValue et (mk_ptr dst LocMemory)) q
Proof
  strip_tac >>
  `vv_own ce cx (ArrayT et (Fixed n)) sa sb fin (Value av)
      (LocatedValue (ArrayT et (Fixed n)) (mk_ptr bop LocMemory)) q` by
    (irule vv_own_vars_frame >> qexistsl [`u`,`sn`] >> simp[vv_operand_def,mk_ptr_def]) >>
  `val_footprint etv v <= type_memory_size etv` by simp[val_footprint_le] >>
  `j + val_footprint etv v <= val_footprint (ArrayTV etv (Fixed n)) av` by
    (`val_footprint (ArrayTV etv (Fixed n)) av = n * type_memory_size etv` by
       (Cases_on `av` >> simp[val_footprint_def,type_memory_size_def]) >> decide_tac) >>
  `vv_own ce cx et sa sb fin (Value v) (LocatedValue et (mk_ptr dst LocMemory)) q` by
    (irule vv_own_memory_slice >>
     qpat_assum `vv_own _ _ _ _ sb _ _ _ _` (irule_at Any) >>
     simp[read_result_def,return_def] >>
     rpt (goal_assum (drule_at Any))) >>
  simp[] >> irule vv_own_memory_transport >>
  qpat_assum `vv_own _ _ et _ _ _ _ _ _` (irule_at Any) >>
  qexistsl [`v`,`etv`,`etv`] >> simp[read_result_def,return_def]
QED

Theorem owned_fixed_child_bytes[local]:
  evaluate_type (get_tenv cx) et = SOME etv /\
  value_has_type etv v /\ val_wf etv v /\
  eval_operand dst q = SOME dw /\ w2n dw = w2n (w:256 word) + j /\
  (!m. mem_agree_outside tq.t_mem q.vs_memory m ==> val_in_memory etv v (w2n dw) m) /\
  j + type_memory_size etv <= n * type_memory_size etv /\
  (type_memory_size etv <> 0 ==> w2n w + n * type_memory_size etv <= q.vs_alloca_next) /\
  (type_memory_size etv <> 0 ==>
   ?b sz. op_prov Gq dst = SOME (b,sz) /\ b <= w2n w /\
          w2n w + n * type_memory_size etv <= b + sz) /\
  op_taint tq dst = {} /\ type_memory_bytes ce et = type_memory_size etv ==>
  vv_holds ce cx et (Value v) (LocatedValue et (mk_ptr dst LocMemory)) fin q /\
  vv_store_bound cx et et fin (Value v) (LocatedValue et (mk_ptr dst LocMemory)) q /\
  ptr_vv_ok cx et (Value v) (LocatedValue et (mk_ptr dst LocMemory)) fin Gq tq q /\
  ptr_buf_ok ce (Subscript et obj idx) dst Gq q
Proof
  strip_tac >>
  `val_store_size etv v <= type_memory_size etv /\
   val_footprint etv v <= type_memory_size etv` by simp[val_store_size_le,val_footprint_le] >>
  `val_in_memory etv v (w2n dw) q.vs_memory` by fs[mem_agree_outside_def] >>
  conj_tac
  >- (simp[vv_holds_def,mk_ptr_def,read_result_def,return_def] >> strip_tac >>
      drule_all val_in_memory_word_type >> simp[]) >>
  `type_memory_size etv <> 0 ==> w2n dw + type_memory_size etv <= q.vs_alloca_next` by decide_tac >>
  conj_tac >- (simp[vv_store_bound_def,mk_ptr_def,read_result_def,return_def] >> decide_tac) >>
  `type_memory_size etv <> 0 ==>
    ?x b sz. dst = Var x /\ FLOOKUP Gq x = SOME (b,sz) /\
             b <= w2n dw /\ w2n dw + type_memory_size etv <= b + sz` by
    (strip_tac >> Cases_on `dst` >> gvs[op_prov_def] >>
     qexistsl [`b`,`sz`] >> simp[] >> decide_tac) >>
  conj_tac
  >- (simp[ptr_vv_ok_def,mk_ptr_def,ptr_mem_ok_def,read_result_def,return_def,IgnAsm `w2n dw = _`] >>
      strip_tac >> `type_memory_size etv <> 0` by decide_tac >>
      first_x_assum drule >> strip_tac >> qexistsl [`x`,`b`,`sz`] >> simp[] >> decide_tac) >>
  simp[ptr_buf_ok_def,lowered_value_type_def,expr_type_def] >> gvs[]
QED

Theorem array_owned_fixed_replay_mods:
  array_owned_memory_view_mods ce cx (et,Fixed n,etv) (sa,st2)
    (fin,v) (bop,it,Gi,tni,a) /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  n < dimword (:256) /\ type_memory_bytes ce et = type_memory_size etv /\
  local_ptrs_reserved ce st2 /\ st2.cs_next_id <= sb.cs_next_id /\
  (!x. bop = Var x ==> not_fresh_at st2 x) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (it,Gi,tni) []
     (if idx_in_range (is_signed_type (expr_type idx)) iw (n2w n)
      then OK q else Abort Revert_abort q,Gq,tq)) /\
  (idx_in_range (is_signed_type (expr_type idx)) iw (n2w n) ==>
     ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
     q.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func q /\
     eval_operand dst q = SOME (a + iw * n2w (type_memory_size etv)) /\
     op_prov Gq dst = op_prov Gi bop /\ op_taint tq dst = {} /\
     array_length_frame st2 it Gi tni q Gq tq) ==>
  array_owned_select_run_mods (lo,explicit,ctx,func,PG) ce cx
    (et,Fixed n,obj,idx) (sa,st2,sb,dst) (v,IntV i) (fin,it,Gi,tni)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `array_owned_memory_view_mods`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [array_owned_memory_view_mods_def,LET_THM,type_memory_size_def]) >>
  `?kvs. v = ArrayV (SArrayV kvs)` by
    (qpat_assum `value_has_type (ArrayTV _ (Fixed _)) _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `v` >> simp[value_has_type_inv] >>
     rename1 `ArrayV av` >> Cases_on `av` >> simp[value_has_type_inv]) >>
  qpat_x_assum `v = ArrayV _` SUBST_ALL_TAC >>
  `!es. select_result cx (ArrayT et (Fixed n)) (Value (ArrayV (SArrayV kvs)))
     (ValueSubscript (IntV i)) es =
     bind (lift_sum (evaluate_subscripts (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs))
       [ValueSubscript (IntV i)])) (\w. return (Value w)) es` by
    simp[select_value_result,IgnAsm `i = _`] >>
  `if idx_in_range (is_signed_type (expr_type idx)) iw (n2w n) then
     0 <= i /\ Num i < n /\ iw = n2w (Num i) /\
     (?v. array_index (ArrayTV etv (Fixed n)) (SArrayV kvs) i = SOME v)
   else evaluate_subscripts (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs))
          [ValueSubscript (IntV i)] = INR (RuntimeError "evaluate_subscripts array_index")` by
    (irule owned_fixed_bounds >> asm_rewrite_tac[]) >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  rewrite_tac[array_owned_select_run_mods_def] >>
  reverse (Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw (n2w n)`)
  >- (qexistsl [`INR (Error (RuntimeError "evaluate_subscripts array_index"))`,
                `Abort Revert_abort q`,`Gq`,`tq`] >>
      fs[bind_def,lift_sum_def,raise_def]) >>
  fs[] >> rename1 `array_index _ _ i = SOME child` >>
  `evaluate_subscripts (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs))
      [ValueSubscript (IntV i)] = INL child` by simp[evaluate_array_subscript_result] >>
  qexistsl [`INL (Value child)`,`OK q`,`Gq`,`tq`] >>
  simp[bind_def,lift_sum_def,return_def] >>
  qabbrev_tac `j = Num i * type_memory_size etv` >>
  `j = Num i * type_memory_size etv` by simp[Abbr `j`] >>
  drule_all owned_fixed_layout >> strip_tac >>
  drule_all owned_fixed_readonly >> strip_tac >>
  `eval_operand bop q = SOME a` by metis_tac[] >>
  `eval_operand dst q = SOME (a + n2w j)` by
    (qpat_assum `eval_operand dst q = SOME _` mp_tac >>
     asm_rewrite_tac[word_mul_n2w]) >>
  qpat_x_assum `!fin name b sz. local_region _ _ q _ _ _ ==> _`
    (qspec_then `fin` assume_tac) >>
  drule_all owned_fixed_child_region >> strip_tac >> simp[] >>
  `!m. mem_agree_outside tq.t_mem q.vs_memory m ==>
        val_in_memory etv child (w2n (a + n2w j)) m` by
    (qpat_assum `w2n (a + _) = _` SUBST1_TAC >>
     qpat_assum `q.vs_memory = _` SUBST1_TAC >>
     qpat_assum `tq.t_mem = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `type_memory_size etv <> 0 ==>
   w2n a + n * type_memory_size etv <= q.vs_alloca_next /\
   ?base len. op_prov Gq dst = SOME (base,len) /\ base <= w2n a /\
     w2n a + n * type_memory_size etv <= base + len` by simp[] >>
  irule owned_fixed_child_bytes >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`a + n2w j`,`etv`,`j`,`n`,`a`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (disch_tac >> qpat_assum `type_memory_size etv <> 0 ==> _` drule >> simp[]))
QED
