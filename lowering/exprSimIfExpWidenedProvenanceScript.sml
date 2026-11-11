Theory exprSimIfExpWidenedProvenance
Ancestors
  exprSimIfExpWidenedAdapter exprSimIfExp loweringPosts loweringStateRelDefs
  compileEnv vyperState context venomState finite_map

Theorem vv_at_assigned_root_frame:
  vv_at ce cx ty sc sd es tv (LocatedValue ty (mk_ptr op LocMemory)) u /\
  eval_operand op u = SOME w /\ local_ptrs_reserved ce sa /\
  (!x. not_fresh_at sa x ==> x <> rv) /\
  sa.cs_next_id <= sc.cs_next_id /\ sd.cs_next_id <= sb.cs_next_id ==>
  vv_at ce cx ty sa sb es tv (LocatedValue ty (mk_ptr (Var rv) LocMemory))
    (jump_to xl (update_var rv w u with vs_inst_idx := k))
Proof
  strip_tac >>
  qabbrev_tac `ss = jump_to xl (update_var rv w u with vs_inst_idx := k)` >>
  `ss.vs_allocas = u.vs_allocas /\ lookup_var rv ss = SOME w /\
   (!x. x <> rv ==> lookup_var x ss = lookup_var x u)` by
    simp[Abbr `ss`, jump_to_def, update_var_def, lookup_var_def,
         FLOOKUP_UPDATE] >>
  `!n b sz. local_region ce es.scopes ss n b sz <=>
            local_region ce es.scopes u n b sz` by
    (rpt gen_tac >> simp[local_region_def] >> eq_tac >> rpt strip_tac >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ u` mp_tac >>
  simp[vv_at_def, mk_ptr_def, eval_operand_def] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >> gvs[]
  >~ [`FLOOKUP u.vs_allocas aid = SOME _`]
  >- (disj1_tac >> qexistsl [`aid`, `b`, `sz`] >>
      `sa.cs_next_id <= aid /\ aid < sb.cs_next_id` by decide_tac >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl [`n`, `b`, `sz`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem allocated_vv_at:
  read_result cx raw es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\ val_wf tvt v /\
  eval_operand op s = SOME w /\
  FLOOKUP s.vs_allocas aid = SOME (b,N) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  b <= w2n w /\ w2n w + val_footprint tvt v <= b + N /\
  (!n lb len. local_region ce es.scopes s n lb len ==> b + N <= lb \/ lb + len <= b) ==>
  vv_at ce cx ty sa sb es raw (LocatedValue t (mk_ptr op LocMemory)) s
Proof
  strip_tac >> simp[vv_at_def, mk_ptr_def] >> rpt strip_tac >> gvs[] >>
  disj1_tac >>
  qexistsl [`aid`, `b`, `N`] >> simp[] >> metis_tac[]
QED

Theorem vv_at_conditional_result:
  conditional_result cx raw st = (INL tv,st') /\
  read_result cx raw es = (INL v,es) /\
  read_result cx tv es = (INL v,es) /\
  vv_at ce cx ty sa sb es raw vv s ==>
  vv_at ce cx ty sa sb es tv vv s
Proof
  strip_tac >>
  `tv = raw \/ ?v'. tv = Value v'` by
    (qpat_x_assum `conditional_result _ _ _ = _` mp_tac >>
     Cases_on `raw` >>
     rw[conditional_result_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
     gvs[] >> pop_assum mp_tac >> IF_CASES_TAC >>
     simp[bind_def, return_def, AllCaseEqs()] >> rw[] >> simp[]) >>
  gvs[] >>
  Cases_on `vv` >> gvs[vv_at_def, read_result_def, return_def] >>
  rpt strip_tac >> first_x_assum drule_all >> metis_tac[]
QED

Theorem vv_at_of_val_at_nonplace:
  ~is_word_type ty /\ expr_val_at ce cx ty sa sb es v op s /\
  read_result cx raw es = (INL v,es) /\
  (!id path. raw <> PlaceR (MemoryPlace id path)) ==>
  vv_at ce cx ty sa sb es raw (LocatedValue t (mk_ptr op LocMemory)) s
Proof
  strip_tac >>
  `!n k ptv. local_place_at ce cx n k ptv raw` by simp[local_place_at_def] >>
  simp[vv_at_def, mk_ptr_def] >> rpt gen_tac >> strip_tac >>
  gvs[expr_val_at_def] >> metis_tac[]
QED
