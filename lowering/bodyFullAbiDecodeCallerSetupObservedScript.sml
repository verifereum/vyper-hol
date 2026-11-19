(* Compose the header and allocation certificates without changing their
   choice of physical endpoint or ghosts. *)
Theory bodyFullAbiDecodeCallerSetupObserved
Ancestors
  bodyFullAbiDecodeCallerHeader bodyFullAbiDecodeCallerAllocation
  abiBuiltinDecodeSetup abiBuiltinDecodeHeader abiEncoderChildContext
  loweringHalt fragExec fragGasPath fragGasOriginPtrLoop

(* Use exactly the installed setup entry and success propositions, as
   instantiated by the allocation theorem. *)
val (alloc_pre, alloc_post) =
  dest_imp (#2 (strip_forall (concl abi_decode_caller_allocation_joint)));
val setup_pre = #1 (dest_conj alloc_pre);
val (alloc_witnesses, alloc_core) = strip_exists alloc_post;
val success = #2 (dest_conj (#2 (dest_conj alloc_core)));
val t = hd alloc_witnesses;
val (g, tn') = (List.nth (alloc_witnesses,1), List.nth (alloc_witnesses,2));

Theorem abi_decode_caller_setup_observed:
  ^setup_pre ==>
  ?r ^g ^tn'.
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (r,^g,^tn')) /\
    (!obs. fn_has_code st ready obs ==> gas_path ctx obs s 0 r) /\
    ((?u. r = Abort Revert_abort u) \/ (? ^t. r = OK ^t /\ ^success))
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_builtin_decode_setup_trace >>
  disch_then (qx_choose_then `inputs` (qx_choose_then `header_st`
    (qx_choose_then `buf` (map_every assume_tac o CONJUNCTS)))) >>
  `cs_extends st header_st /\ cs_extends header_st ready` by
    (conj_tac >- (drule abi_builtin_decode_header_shape >> strip_tac >>
                  irule abi_encoder_straight_extends >> simp[]) >>
     drule compile_alloc_buffer_extends >> simp[]) >>
  drule_all abi_decode_caller_header_joint >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `rh` (qx_choose_then `Gh` (qx_choose_then `tnh`
      (map_every assume_tac o CONJUNCTS))))) >>
  qpat_x_assum `(?u. rh = Abort Revert_abort u) \/ _` strip_assume_tac
  >- (qexistsl_tac [`rh`, `Gh`, `tnh`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (qx_gen_tac `obs` >> strip_tac >>
                   drule_all fn_has_code_split >> simp[]) >>
      disj1_tac >> goal_assum (drule_at Any)) >>
  mp_tac (SPEC_ALL (BETA_RULE abi_decode_caller_allocation_joint)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >>
  qexistsl_tac [`OK t`, `Gf`, `tnf`] >>
  conj_tac >-
    (qx_gen_tac `horizon` >> strip_tac >>
     irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gh`, `u`, `tnh`] >>
     fs[]) >>
  conj_tac >-
    (qx_gen_tac `obs` >> strip_tac >> drule_all fn_has_code_split >> strip_tac >>
     `gas_path ctx obs s 0 (OK u) /\ gas_path ctx obs u 0 (OK t)` by fs[] >>
     drule_all gas_path_then >> simp[]) >>
  disj2_tac >> qexists_tac `t` >> simp[]
QED
