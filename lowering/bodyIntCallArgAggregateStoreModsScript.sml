(* The store starts after the argument buffer has been allocated and the
   source operand unwrapped.  Its source and formal layouts may differ. *)
Theory bodyIntCallArgAggregateStoreMods
Ancestors
  bodyStructFieldAggregateStoreMods bodyStructFieldSmallStoreMods bodyStructFieldCutsMods
  bodyInvCodeProps exprSimHypsDefs typedMemoryCopy venomMemDefs
  venomState arithmetic

val _ = Parse.hide "base";

Theorem aggregate_store_older_allocas[local]:
  alloca_inv s /\ FLOOKUP s.vs_allocas aid = SOME (base,cap) /\ len <= cap /\
  typed_copy_state_frame sa base len s t ==>
  t.vs_allocas = s.vs_allocas /\
  !old b n. old < aid /\ FLOOKUP s.vs_allocas old = SOME (b,n) ==>
    mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [typed_copy_state_frame_def]) >>
  conj_tac
  >- (qpat_assum `_ with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
          vs_current_bb := _; vs_inst_idx := _|> = s`
        (mp_tac o Q.AP_TERM `\u. u.vs_allocas`) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `old <> aid` by decide_tac >>
  `b + n <= base \/ base + cap <= b` by
    (qpat_x_assum `alloca_inv s`
      (strip_assume_tac o PURE_REWRITE_RULE [alloca_inv_def]) >>
     qpat_x_assum `allocas_non_overlapping s` mp_tac >>
     pure_rewrite_tac[allocas_non_overlapping_def] >>
     disch_then (qspecl_then [`old`,`aid`,`b`,`n`,`base`,`cap`] mp_tac) >> simp[]) >>
  qpat_x_assum `typed_copy_frame _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [typed_copy_frame_def]) >>
  first_x_assum irule >> decide_tac
QED

Theorem intcall_arg_aggregate_store_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  compile_store_memory cenv op (Var dst) dty sty sa = ((),sb) /\
  struct_operand_mods (cenv,get_tenv cx,sty,dty,stv,dtv) (op,v) (dst,base) (sa,G,tn,s) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  FLOOKUP s.vs_allocas aid = SOME (base,MAX 32 (type_memory_bytes cenv dty)) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    struct_store_effects func (sa,G,tn,s) (sb,Gf,tnf,t) (base,dtv,v) /\
    value_has_type dtv v /\ type_memory_size dtv <= MAX 32 (type_memory_bytes cenv dty) /\
    t.vs_allocas = s.vs_allocas /\
    (!old b n. old < aid /\ FLOOKUP s.vs_allocas old = SOME (b,n) ==>
      mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `value_has_type dtv v /\ type_memory_size dtv <= MAX 32 (type_memory_bytes cenv dty)` by
    (qhdtm_assum `struct_operand_mods`
       (strip_assume_tac o PURE_REWRITE_RULE [struct_operand_mods_def]) >> simp[]) >>
  `?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    struct_store_effects func (sa,G,tn,s) (sb,Gf,tnf,t) (base,dtv,v)` by
    (Cases_on `type_memory_size stv = 0`
     >- (irule struct_field_small_store_mods >>
         qhdtm_assum `struct_operand_mods` (irule_at Any) >> simp[]) >>
     drule_then assume_tac contract_inv_acyclic_struct_metadata >>
     qhdtm_x_assum `expr_sim_inv_mods`
       (strip_assume_tac o PURE_REWRITE_RULE [expr_sim_inv_mods_def]) >>
     irule struct_field_aggregate_store_mods >>
     qhdtm_assum `struct_operand_mods` (irule_at Any) >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> simp[] >>
  qhdtm_x_assum `struct_store_effects`
    (strip_assume_tac o PURE_REWRITE_RULE [struct_store_effects_def, pairTheory.FORALL_PROD]) >>
  irule aggregate_store_older_allocas >>
  qhdtm_assum `typed_copy_state_frame` (irule_at Any) >>
  qexists_tac `MAX 32 (type_memory_bytes cenv dty)` >> simp[]
QED
