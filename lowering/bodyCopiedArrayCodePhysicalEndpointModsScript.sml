(* Qualified code unwrap at the cursor after the snapshot destination ALLOCA. *)
Theory bodyCopiedArrayCodePhysicalEndpointMods
Ancestors
  bodyCopiedArrayCutDefsMods bodyCopySlotRhsEndpointMods
  bodyLocalCopyPhysicalRhsMods bodyCopyCtorRhsRunMods bodyCopyRuntimeRhsRunMods
  exprPtrUnwrapAllocation bufferAllocationExecution loweringHalt
  exprLoweringProps exprSimCopy loweringPosts bodyFullPostsMods
  bodyFullShadowBodyInv gasExplicitSites vyperStorageFootprint
  compileEnv context venomExecSemantics venomState venomInst words finite_map arithmetic

Theorem copied_code_address_bound[local]:
  immutable_holds ce cx tag raw addr mid a /\
  evaluate_type (get_tenv cx) tag = SOME atv ==>
  w2n addr + type_memory_size atv < dimword (:256)
Proof
  rw[immutable_holds_def,sub_layout_def] >>
  `off + k < dimword (:256)` by decide_tac >>
  `atv = tvt` by fs[] >>
  simp[w2n_n2w,LESS_MOD] >> decide_tac
QED

(* An already executed site returns its original offset. A new site records
   the old frontier, even for a zero-sized buffer. *)
Theorem copied_code_alloc_base[local]:
  exec_alloca (mk_inst aid ALLOCA [Lit (n2w n)] [root]) a (n2w n : bytes32) = OK u /\
  FLOOKUP u.vs_allocas aid = SOME (w2n dst,n) ==>
  buffer_allocation_base a aid = w2n dst
Proof
  Cases_on `FLOOKUP a.vs_allocas aid` >>
  simp[buffer_allocation_base_def,exec_alloca_def,mk_inst_def,AllCaseEqs()] >>
  strip_tac >> gvs[update_var_def,FLOOKUP_UPDATE]
QED

val code_physical_result =
  snd (dest_imp (concl (Q.INST
    [`sm` |-> `k`,`s` |-> `a`,`G` |-> `Ga`,`tn` |-> `ta`,
     `sc` |-> `l`,`op` |-> `src`,`rt` |-> `atv`,`v` |-> `saved`,
     `ee` |-> `mid`,`func` |-> `fn`,`explicit` |-> `gas_explicit_sites ctx shctx`]
    copy_slot_rhs_endpoint_mods)));

Theorem copied_array_code_physical_endpoint_mods:
  copied_alloc_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
    (sm,s,G,tn) (k,a,Ga,ta) (l,src,sc,cvv,bvv) (q,w) /\
  bvv = LocatedValue tag p /\ p.ptr_location = LocCode ==>
  ^code_physical_result
Proof
  disch_then (CONJUNCTS_THEN2
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [copied_alloc_cut_mods_def])
    (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac)) >>
  qpat_assum `copied_array_type_mods _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [copied_array_type_mods_def]) >>
  qpat_assum `copied_cursor_mods _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [copied_cursor_mods_def]) >>
  qpat_assum `copied_parent_frame_mods _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [copied_parent_frame_mods_def]) >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `ce.ce_is_ctor ==> ?v. read_result cx raw mid = (INL v,mid) /\
     !rt addr. evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME rt /\
         eval_operand p.ptr_operand a = SOME addr ==>
       w2n addr + type_memory_size rt <= lo /\
       (!m. mem_agree_outside ta.t_mem a.vs_memory m ==> val_in_memory rt v (w2n addr) m)` by
    (disch_tac >> qexists `saved` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `evaluate_type _ (post_value_type ce obj) = SOME rt`
       (mp_tac) >> asm_rewrite_tac[optionTheory.SOME_11] >>
     disch_then (SUBST_ALL_TAC o SYM) >>
     qpat_assum `ce.ce_is_ctor /\ vv_location _ = _ ==> _`
       (mp_tac o REWRITE_RULE [vv_location_def,vv_operand_def]) >>
     asm_rewrite_tac[] >> disch_then (qspec_then `addr` mp_tac) >>
     asm_rewrite_tac[]) >>
  `evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME atv` by simp[] >>
  qhdtm_assum `vv_post_mods` (mp_then Any mp_tac local_copy_raw_code_source_mods) >>
  disch_then (qspecl_then [`saved`,`ta`,`atv`,`lo`,`Ga`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`owner`,`tops`,`addr`] (map_every assume_tac o CONJUNCTS))))) >>
  `evaluate_type (get_tenv cx) tag = SOME atv /\
   ~is_word_type tag /\ type_memory_bytes ce tag = type_memory_size atv` by
    simp[is_word_type_def] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at k x` by fs[vv_operand_def] >>
  `type_memory_size atv < dimword (:256)` by
    (irule LESS_TRANS >> qexists `2 ** 64` >> simp[wordsTheory.dimword_def]) >>
  Cases_on `ce.ce_is_ctor`
  >- suspend "ctor" >>
  suspend "runtime"
QED

val finish_code_physical =
  Cases_on `compile_alloc_buffer (type_memory_size atv) k` >>
  rename1 `compile_alloc_buffer _ k = (buf,km)` >>
  drule_then strip_assume_tac compile_alloc_buffer_parts >>
  drule_all_then assume_tac copied_code_alloc_base >>
  qexistsl [`root`,`dst`,`km`,`buf`,`u`,`z`,`Gf`,`tf`] >>
  asm_rewrite_tac[];

Resume copied_array_code_physical_endpoint_mods[ctor]:
  qpat_assum `ce.ce_is_ctor ==> w2n addr + _ <= lo /\ _`
    (drule_then strip_assume_tac) >>
  drule_all (Q.INST [`sb` |-> `k`,`sc` |-> `l`] copy_ctor_rhs_endpoint_mods) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shctx`,`PG`] mp_tac) >>
  disch_then (qx_choosel_then [`z`,`Gf`,`tf`,`root`,`dst`,`u`]
    (map_every assume_tac o CONJUNCTS)) >>
  finish_code_physical >>
  qx_gen_tac `i` >> strip_tac >> disch_tac >>
  qpat_assum `!j. _ ==> (j IN tf.t_mem <=> _)` (qspec_then `i` mp_tac) >>
  simp[ADD_COMM]
QED

Resume copied_array_code_physical_endpoint_mods[runtime]:
  qpat_assum `~ce.ce_is_ctor ==> _ /\ _` (drule_then strip_assume_tac) >>
  drule_all_then assume_tac copied_code_address_bound >>
  drule_all (Q.INST [`sm` |-> `k`,`sc` |-> `l`] copy_runtime_rhs_endpoint_mods) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shctx`,`PG`,`Ga`] mp_tac) >>
  disch_then (qx_choosel_then [`z`,`Gf`,`tf`,`root`,`dst`,`u`]
    (map_every assume_tac o CONJUNCTS)) >>
  finish_code_physical >>
  conj_tac >-
    (qpat_assum `!name b len. local_region _ _ _ _ _ _ ==> _` mp_tac >>
     pure_rewrite_tac[Once DISJ_COMM] >> disch_then ACCEPT_TAC) >>
  simp[pred_setTheory.IN_DIFF]
QED

Finalise copied_array_code_physical_endpoint_mods
