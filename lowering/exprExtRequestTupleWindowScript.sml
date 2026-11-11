(* The stored request tuple and its two registered buffers supply window entry. *)
Theory exprExtRequestTupleWindow
Ancestors
  exprExtRequestEncoderEntry exprExtRequestPlanEntry exprExtRequestEncoderResource
  abiEncoderWindowContract abiCallerAllocation allocaSiteResource
  exprSimHypsDefs exprLoweringProps compileEnv venomMemDefs valueEncoding
  words list

Theorem extrequest_tuple_window_entry:
  expr_sim_inv cenv cx env ee /\
  assignable_type (get_tenv cx) (TupleT tys) /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
  vyper_to_abi (get_tenv cx) (TupleT tys) (ArrayV (TupleV vs)) = SOME av /\
  tuple_in_memory vs tvs source_base s.vs_memory /\
  ei = type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT tys) /\
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx ee s /\
  source_id < st.cs_next_id /\ dest_id < st.cs_next_id /\
  source_id <> dest_id /\
  FLOOKUP s.vs_allocas source_id = SOME (source_base,source_size) /\
  FLOOKUP s.vs_allocas dest_id = SOME (dest_base,dest_size) /\
  type_memory_size (TupleTV tvs) <= source_size /\
  dest_base <= d /\
  d + LENGTH (enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av) <=
    dest_base + dest_size /\
  eval_operand src s = SOME (n2w source_base) /\
  eval_operand dst s = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?at rv.
    enc at rv = enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av /\
    abi_encoder_window_pre ctx func st en dst src ei at rv source_base
      (type_memory_size (TupleTV tvs)) d s
Proof
  strip_tac >>
  `abi_enc_plan (get_tenv cx) (TupleT tys) ei` by
    (gvs[] >> irule extrequest_encoding_plan >> metis_tac[]) >>
  drule_all extrequest_encoder_source_window >> strip_tac >>
  `alloca_inv s /\ alloca_room ctx func s` by fs[stmt_state_rel_def] >>
  `source_base + type_memory_size (TupleTV tvs) <= s.vs_alloca_next` by
    (irule abi_caller_allocation_end >> simp[] >>
     qexistsl_tac [`source_size`, `source_id`, `source_base`] >> simp[]) >>
  `d + LENGTH (enc at rv) <= s.vs_alloca_next` by
    (irule abi_caller_allocation_end >> simp[] >>
     qexistsl_tac [`dest_size`, `dest_id`, `dest_base`] >> fs[]) >>
  `venomMemDefs$regions_disjoint
     (source_base,type_memory_size (TupleTV tvs)) (d,LENGTH (enc at rv))` by
    (drule_all alloca_site_registered_disjoint >>
     pure_rewrite_tac[venomMemDefsTheory.regions_disjoint_def] >>
     strip_tac >> fs[] >>
     pure_rewrite_tac[GSYM LENGTH_NIL] >> decide_tac) >>
  qexistsl_tac [`at`, `rv`] >> simp[abi_encoder_window_pre_def] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  conj_tac >- (drule_all extrequest_encoder_registered_size >> simp[]) >>
  conj_tac
  >- (irule extrequest_encoder_registered_window >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`en`, `source_size`, `source_id`, `source_base`, `st`] >>
      simp[]) >>
  irule extrequest_encoder_registered_window >>
      goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`en`, `dest_size`, `dest_id`, `dest_base`, `st`] >> fs[]
QED
