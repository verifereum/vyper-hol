(* Preserve the payload's older-allocation or local-region origin at the
   normal endpoint already selected by the setup proof. *)
Theory bodyFullAbiDecodeCallerSetupOrigin
Ancestors
  bodyFullAbiDecodeCallerSetupObserved bodyFullAbiDecodeInputOrigin
  fragGasOriginPtr forPtrAllocationFrame finite_map words

val (setup_pre, observed_post) =
  dest_imp (#2 (strip_forall (concl abi_decode_caller_setup_observed)));
val (witnesses, observed_core) = strip_exists observed_post;
val (path, rest) = dest_conj observed_core;
val (observer, cases) = dest_conj rest;
val (rejected, normal) = dest_disj cases;
val (t, normal_core) = dest_exists normal;

val input_origin = ``\s.
  (?aid ib isz.
     aid < abi_builtin_decode_output_site st min_size max_size /\
     FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\
     ib <= w2n (n2w (b+32) : 256 word) /\
     w2n (n2w (b+32) : 256 word) + LENGTH (input_bytes : word8 list) <= ib+isz) \/
  (?name ib isz.
     local_region ce es.scopes s name ib isz /\
     ib <= w2n (n2w (b+32) : 256 word) /\
     w2n (n2w (b+32) : 256 word) + LENGTH (input_bytes : word8 list) <= ib+isz)``;
val post = list_mk_exists (witnesses,
  ``^path /\ ^observer /\ (^rejected \/ (? ^t. ^normal_core /\ (^input_origin) ^t))``);
val stmt = ``(^setup_pre /\ (^input_origin) s) ==> ^post``;

Theorem abi_decode_caller_setup_origin_observed:
  ^(list_mk_forall (free_vars stmt, stmt))
Proof
  rpt gen_tac >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 (map_every assume_tac o CONJUNCTS) assume_tac) >>
  mp_tac (SPEC_ALL (BETA_RULE abi_decode_caller_setup_observed)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `r` (qx_choose_then `Gf` (qx_choose_then `tnf`
    (map_every assume_tac o CONJUNCTS)))) >>
  qexistsl_tac [`r`, `Gf`, `tnf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `(?u. r = Abort Revert_abort u) \/ _`
    (DISJ_CASES_THEN2 assume_tac (qx_choose_then `t` (CONJUNCTS_THEN2 assume_tac assume_tac)))
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> qexists_tac `t` >>
  conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `r = OK t` SUBST_ALL_TAC >>
  qpat_assum `?H. V H` (qx_choose_then `h` assume_tac) >>
  `gas_origin_ptr_path (DF h,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tnf)` by
    (qpat_assum `!H. V H ==> gas_origin_ptr_path _ _ _ _`
       (qspec_then `h` mp_tac) >> simp[]) >>
  drule (cj 2 gas_origin_ptr_path_projections) >> strip_tac >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP t.vs_allocas aid = SOME entry` by
    (rpt strip_tac >> drule gas_path_ptr_old_allocations >>
     disch_then (qspecl_then [`t`, `aid`, `entry`] mp_tac) >> simp[]) >>
  qpat_x_assum `?output input. ~t.vs_halted /\ _`
    (qx_choose_then `output` (qx_choose_then `input` (assume_tac o List.last o CONJUNCTS))) >>
  irule abi_decode_input_origin_transport >>
  qexistsl_tac [`s`, `st`] >>
  conj_tac >-
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at st x ==> _` drule >> simp[]) >>
  conj_tac >- simp[] >>
  conj_tac >> first_assum ACCEPT_TAC
QED
