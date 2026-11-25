(* Split a native caller spine at its first intermediate operand exit. *)
Theory entryCreateNativeFirstExit
Ancestors
  entryCreateFocusSpec entryCreateOperandReplay createSizeCutRegion
  createSizePrefixReplay dftGasFromListTraceDefs entryCreateBodyCut
  fragGasOrigin compileEnv bodySim relation pair list

Theorem create_region_at_entry[local]:
  create_cut_code {} a b /\ fn_has_code a b fn /\ create_operand_at a s ==>
  create_cut_region a b s
Proof
  rw[create_operand_at_def] >> metis_tac[cj 1 create_cut_region_rules]
QED

Theorem create_region_fetch[local]:
  create_cut_code {} a b /\ fn_has_code a b fn /\
  create_cut_region a b s /\ ~create_operand_at b s /\
  create_operand_fetch l r fn s i ==>
  create_operand_fetch a b fn s i
Proof
  rw[create_operand_fetch_def,create_operand_at_def] >>
  metis_tac[cj 2 create_cut_region_rules]
QED

(* Rebasing changes only the accumulated visits, not the selected edge. *)
Theorem create_native_restrict_rebase[local]:
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  create_cut_code {} a b /\ fn_has_code a b fn /\
  create_cut_region a b u /\ ~create_operand_at b u /\
  create_operand_native_step l r E ctx fn p (d,k,u,front ++ left) (d',k',v,whole) ==>
  ?right. whole = front ++ right /\ create_cut_region a b v /\
    create_operand_native_step a b E ctx fn p (d,k,u,left) (d',k',v,right)
Proof
  simp_tac bool_ss [create_operand_native_step_def,LET_THM] >> strip_tac >>
  drule_all create_region_fetch >> strip_tac >>
  qmatch_asmsub_abbrev_tac `create_prefix_step l r E ctx fn u ms v` >>
  `gas_origin_edge F E ctx fn u ms (OK v)` by fs[create_prefix_step_def] >>
  `create_prefix_step a b E ctx fn u ms v /\ create_cut_region a b v` by
    (irule operand_cut_region_edge >> simp[] >>
     fs[create_operand_at_def] >> metis_tac[]) >>
  qexists_tac `left ++ ((p,d,inst.inst_id),fn,inst,u)::trace_step p d k ctx fn inst u` >>
  simp[] >> qexists_tac `inst` >> gvs[Abbr `ms`,APPEND_ASSOC]
QED

Theorem create_native_before_exit[local]:
  create_operand_native_step a b E ctx fn p (d,k,u,left) (d',k',v,whole) ==>
  ~create_operand_at b u
Proof
  rw[create_operand_native_step_def,create_operand_fetch_def,LET_THM]
QED

Theorem create_native_trace_append[local]:
  !x y. RTC (create_operand_native_step a b E ctx fn p) x y ==>
  !d k u left d' k' v whole.
    x = (d,k,u,left) /\ y = (d',k',v,whole) ==>
    ?chunk. whole = left ++ chunk /\
      create_trace_from p d k ctx fn u = chunk ++ create_trace_from p d' k' ctx fn v
Proof
  ho_match_mp_tac RTC_INDUCT_RIGHT1 >> conj_tac
  >- (simp[] >> metis_tac[APPEND]) >>
  simp_tac bool_ss [FORALL_PROD,create_operand_native_step_def,LET_THM] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[APPEND_ASSOC]
QED

Theorem create_native_prefix_first_exit[local]:
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m fn /\
  create_cut_code {} m b /\ fn_has_code m b fn ==>
  !x y. RTC (create_operand_native_step a b E ctx fn p) x y ==>
  !d k s d' k' u whole.
    x = (d,k,s,[]) /\ y = (d',k',u,whole) /\ create_operand_at a s ==>
    (RTC (create_operand_native_step a m E ctx fn p) x y /\ create_cut_region a m u) \/
    ?dm km t front back.
      whole = front ++ back /\ create_operand_at m t /\
      RTC (create_operand_native_step a m E ctx fn p) x (dm,km,t,front) /\
      RTC (create_operand_native_step m b E ctx fn p) (dm,km,t,[]) (d',k',u,back) /\
      create_cut_region m b u
Proof
  strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >> conj_tac
  >- (simp[] >> metis_tac[create_region_at_entry]) >>
  simp_tac bool_ss [FORALL_PROD] >> rpt strip_tac >> gvs[]
  >- (rename1 `create_operand_native_step a b E ctx fn p (dc,kc,c,pre) (dv,kv,v,out)` >>
      Cases_on `create_operand_at m c`
      >- (disj2_tac >>
          `create_cut_region m b c` by metis_tac[create_region_at_entry] >>
          `~create_operand_at b c` by metis_tac[create_native_before_exit] >>
          `?right. out = pre ++ right /\ create_cut_region m b v /\
             create_operand_native_step m b E ctx fn p (dc,kc,c,[]) (dv,kv,v,right)` by
             (irule create_native_restrict_rebase >> simp[] >> metis_tac[]) >>
          qexistsl_tac [`dc`,`kc`,`c`,`pre`,`right`] >> simp[RTC_SINGLE]) >>
      disj1_tac >>
      `?right. out = [] ++ right /\ create_cut_region a m v /\
         create_operand_native_step a m E ctx fn p (dc,kc,c,pre) (dv,kv,v,right)` by
         (irule create_native_restrict_rebase >> simp[] >> metis_tac[]) >>
      gvs[] >> metis_tac[RTC_RULES_RIGHT1]) >>
  rename1 `create_operand_native_step a b E ctx fn p (dc,kc,c,front ++ back) (dv,kv,v,out)` >>
  disj2_tac >> `~create_operand_at b c` by metis_tac[create_native_before_exit] >>
  `?right. out = front ++ right /\ create_cut_region m b v /\
     create_operand_native_step m b E ctx fn p (dc,kc,c,back) (dv,kv,v,right)` by
     (irule create_native_restrict_rebase >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`dm`,`km`,`t`,`front`,`right`] >> simp[] >>
  metis_tac[RTC_RULES_RIGHT1]
QED

(* Once a selected PC is in a closed suffix, keep all the native edges,
   rebasing just the accumulator.  The original stop does not change. *)
Theorem create_native_closed_suffix_rebase:
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  create_cut_code {} a b /\ fn_has_code a b fn ==>
  !x y. RTC (create_operand_native_step l b E ctx fn p) x y ==>
  !d k s front d' k' u whole.
    x = (d,k,s,front) /\ y = (d',k',u,whole) /\ create_operand_at a s ==>
    ?tail. whole = front ++ tail /\ create_cut_region a b u /\
      RTC (create_operand_native_step a b E ctx fn p) (d,k,s,[]) (d',k',u,tail)
Proof
  strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >> conj_tac
  >- (simp[] >> metis_tac[create_region_at_entry]) >>
  simp_tac bool_ss [FORALL_PROD] >> rpt strip_tac >> gvs[] >>
  rename1 `create_operand_native_step l b E ctx fn p (dc,kc,c,front ++ tail) (dv,kv,v,out)` >>
  `~create_operand_at b c` by metis_tac[create_native_before_exit] >>
  `?right. out = front ++ right /\ create_cut_region a b v /\
     create_operand_native_step a b E ctx fn p (dc,kc,c,tail) (dv,kv,v,right)` by
     (irule create_native_restrict_rebase >> simp[] >> metis_tac[]) >>
  qexists_tac `right` >> simp[] >> metis_tac[RTC_RULES_RIGHT1]
QED

(* Preserve the original suffix by cancelling the completed left trace. *)
Theorem create_native_right_visit[local]:
  RTC (create_operand_native_step a m E ctx fn p) (d,k,s,[]) (d1,k1,t,front) /\
  create_operand_at m t /\
  RTC (create_operand_native_step m b E ctx fn p) (d1,k1,t,[]) (d',k',u,left) /\
  create_operand_fetch m b fn u inst /\
  create_trace_from p d k ctx fn s = before ++ hit::after /\
  (before = front ++ left /\ hit = ((p,d',inst.inst_id),fn,inst,u) \/
   ?inside suffix. before = (front ++ left) ++ ((p,d',inst.inst_id),fn,inst,u)::inside /\
                   trace_step p d' k' ctx fn inst u = inside ++ hit::suffix) ==>
  ?back. before = front ++ back /\
    create_expr_prefix a m E ctx fn s (create_cut_marks E front) t /\
    create_interior_visit m b E ctx fn (p,d1,k1) t (back,hit,after)
Proof
  rpt (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  `create_trace_from p d k ctx fn s = front ++ create_trace_from p d1 k1 ctx fn t`
    by metis_tac[create_native_trace_append,APPEND] >>
  `create_expr_prefix a m E ctx fn s (create_cut_marks E front) t`
    by metis_tac[create_operand_native_prefix] >>
  disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- (qexists_tac `left` >> simp[create_interior_visit_def] >>
      `create_trace_from p d1 k1 ctx fn t = left ++ hit::after`
        by metis_tac[APPEND_ASSOC,APPEND_11] >>
      simp[] >> qexistsl_tac [`d'`,`k'`,`u`,`left`,`inst`] >> simp[]) >>
  qexists_tac `left ++ ((p,d',inst.inst_id),fn,inst,u)::inside` >>
  conj_tac >- metis_tac[APPEND_ASSOC] >>
  simp_tac bool_ss [create_interior_visit_def,LET_THM] >>
  asm_simp_tac bool_ss [] >>
  conj_tac >- metis_tac[APPEND_ASSOC,APPEND_11] >>
  qexistsl_tac [`d'`,`k'`,`u`,`left`,`inst`] >>
  asm_simp_tac bool_ss [] >> disj2_tac >> qexistsl_tac [`inside`,`suffix`] >>
  asm_simp_tac bool_ss []
QED

Theorem create_interior_visit_first_exit:
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m fn /\
  create_cut_code {} m b /\ fn_has_code m b fn /\
  create_interior_visit a b E ctx fn (p,d,k) s (before,hit,after) ==>
  create_interior_visit a m E ctx fn (p,d,k) s (before,hit,after) \/
  ?t d1 k1 front back.
    before = front ++ back /\ create_operand_at m t /\
    RTC (create_operand_native_step a m E ctx fn p) (d,k,s,[]) (d1,k1,t,front) /\
    create_expr_prefix a m E ctx fn s (create_cut_marks E front) t /\
    create_interior_visit m b E ctx fn (p,d1,k1) t (back,hit,after)
Proof
  rpt (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_then (mp_tac o SIMP_RULE bool_ss [create_interior_visit_def,LET_THM]) >>
  rpt (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_then (REPEAT_TCL CHOOSE_THEN mp_tac) >>
  rpt (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >> disch_tac >>
  rename1 `RTC (create_operand_native_step a b E ctx fn p) (d,k,s,[]) (dc,kc,u,left)` >>
  rename1 `create_operand_fetch a b fn u inst` >>
  `(RTC (create_operand_native_step a m E ctx fn p) (d,k,s,[]) (dc,kc,u,left) /\
     create_cut_region a m u) \/
     (?dm km t front back. left = front ++ back /\ create_operand_at m t /\
       RTC (create_operand_native_step a m E ctx fn p) (d,k,s,[]) (dm,km,t,front) /\
       RTC (create_operand_native_step m b E ctx fn p) (dm,km,t,[]) (dc,kc,u,back) /\
       create_cut_region m b u)` by metis_tac[create_native_prefix_first_exit]
  >- (Cases_on `create_operand_at m u`
      >- (disj2_tac >>
          `create_cut_region m b u` by metis_tac[create_region_at_entry] >>
          `create_operand_fetch m b fn u inst` by
            metis_tac[create_region_fetch,create_operand_fetch_def] >>
          qexistsl_tac [`u`,`dc`,`kc`,`left`] >> simp[] >>
          irule create_native_right_visit >> metis_tac[APPEND_NIL,RTC_REFL]) >>
      disj1_tac >>
      `create_operand_fetch a m fn u inst` by metis_tac[create_region_fetch] >>
      asm_simp_tac bool_ss [create_interior_visit_def,LET_THM] >>
      qexistsl_tac [`dc`,`kc`,`u`,`left`,`inst`] >> asm_simp_tac bool_ss []) >>
  disj2_tac >>
  `create_operand_fetch m b fn u inst` by metis_tac[create_region_fetch,create_operand_fetch_def] >>
  qexistsl_tac [`t`,`dm`,`km`,`front`] >> simp[] >>
  irule create_native_right_visit >> metis_tac[]
QED
