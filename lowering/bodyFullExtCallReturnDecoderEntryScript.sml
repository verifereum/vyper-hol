(* Allocated decoder entry for the sufficient-size external return branch. *)
Theory bodyFullExtCallReturnDecoderEntry
Ancestors
  abiDecodePtrMemberFrame decoderGhostFramePtr
  abiReturnSuccessSource abiReturnReject abiValidAllocatedContract
  abiWidthInhabited extcallReturnDefaultTypes extcallReturnEntryBridge
  fragGasPathFrameMem bodyMemAggregatePath bodyPtrDefs ptrDiscipline
  vyperABIValid vyperABI contractABI venomMemDefs venomState words list
  finite_map pred_set arithmetic

(* The allocation row bounds the window by the original frontier.  The
   clean interval itself uses the copied byte count, not the row size. *)
Triviality extcall_return_clipped_window:
  lookup_var source t = SOME ro /\
  FLOOKUP G source = SOME (prov_base,span) /\
  op_taint tn (Var source) = {} /\
  prov_base <= w2n ro /\ w2n ro + cap <= prov_base + span /\
  alloca_inv t /\ FLOOKUP t.vs_allocas live = SOME (w2n ro,bufsz) /\
  cap <= bufsz /\
  (!i. w2n ro <= i /\ i < w2n ro + MIN cap (LENGTH bs) ==>
    i NOTIN tn.t_mem) /\
  lookup_var source u = lookup_var source t /\
  FLOOKUP Gf source = FLOOKUP G source /\
  op_taint tm (Var source) = op_taint tn (Var source) /\
  (!i. i < t.vs_alloca_next ==> (i IN tm.t_mem <=> i IN tn.t_mem)) ==>
  abi_decode_ptr_window Gf tm u source ro (LENGTH (TAKE cap bs))
Proof
  strip_tac >>
  `LENGTH (TAKE cap bs) = MIN cap (LENGTH bs)` by
    (Cases_on `cap <= LENGTH bs` >> simp[LENGTH_TAKE_EQ, MIN_DEF] >> decide_tac) >>
  `LENGTH (TAKE cap bs) <= cap` by simp[MIN_LE] >>
  `w2n ro + bufsz <= t.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[ADD_COMM]) >>
  `abi_decode_ptr_window G tn t source ro (LENGTH (TAKE cap bs))` by
    (simp[abi_decode_ptr_window_def,ptr_covers_def] >>
     qexistsl_tac [`ro`,`prov_base`,`span`] >> simp[] >> decide_tac) >>
  irule abi_decode_ptr_window_frame >>
  qexistsl_tac [`G`,`t`,`tn`] >> simp[] >>
  rpt strip_tac >>
  `i < t.vs_alloca_next` by decide_tac >> simp[]
QED

(* Here entry is after destination allocation and before the size test;
   u is the actual entry to the decoder. No decoder run is assumed. *)
Theorem extcall_return_allocated_decoder_entry:
  rt = (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type) /\
  cap = vyper_abi_size_bound env rt /\
  (~is_dynamic (vyper_to_abi_type env rt) ==>
    cap = static_length (vyper_to_abi_type env rt)) /\
  abi_static_size cenv.ce_struct_fields rt = abi_static_length (vyper_to_abi_type env rt) /\
  abi_static_size cenv.ce_struct_fields rt <= cap /\
  abi_static_size cenv.ce_struct_fields rt <= LENGTH bs /\
  abi_decoder_coherent cenv env cenv.ce_struct_fields rt tv /\
  abi_decode_bytes_widths env rt /\ assignable_type env rt /\
  type_memory_size tv < dimword (:256) /\
  compile_abi_decode_to_buf (Var output) (Lit 0w) MLOAD (Var source) hi
    (type_to_abi_dec_info cenv.ce_struct_fields cenv rt) st = ((),en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  abi_malformed_entry H0 ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live
    (Var source) hi (Lit 0w) (Var output) (w2n ro) (LENGTH (TAKE cap bs)) (TAKE cap bs) 0 dest
    (type_memory_bytes cenv rt) u /\
  ~u.vs_halted /\ u.vs_current_bb = st.cs_current_bb /\
  u.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand (Var source) t = SOME ro /\
  FLOOKUP G source = SOME (prov_base,span) /\
  op_taint tn (Var source) = {} /\
  prov_base <= w2n ro /\ w2n ro + cap <= prov_base + span /\
  alloca_inv t /\ FLOOKUP t.vs_allocas live = SOME (w2n ro,bufsz) /\
  cap <= bufsz /\
  (!i. w2n ro <= i /\ i < w2n ro + MIN cap (LENGTH bs) ==>
     i NOTIN tn.t_mem) /\
  lookup_var source u = lookup_var source t /\
  FLOOKUP Gf source = FLOOKUP G source /\
  op_taint tm (Var source) = op_taint tn (Var source) /\
  (!i. i < t.vs_alloca_next ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  ptr_covers GP tp output entry (type_memory_bytes cenv rt) /\
  lookup_var output u = lookup_var output entry /\
  FLOOKUP Gf output = FLOOKUP GP output /\
  op_taint tm (Var output) = op_taint tp (Var output) /\
  op_prov Gf hi = NONE /\ op_taint tm hi = {} /\
  alloca_history func entry /\ alloca_inv entry /\
  gas_path_mem ctx func entry 0 (OK u) /\
  ghost_inv_at D lo rb cenv cx es Gf tm u ==>
  abi_decode_ptr_window Gf tm u source ro (LENGTH (TAKE cap bs)) /\
  ptr_covers Gf tm output u (type_memory_bytes cenv rt) /\
  op_prov Gf (Lit 0w) = NONE /\ op_prov Gf hi = NONE /\
  op_taint tm (Lit 0w) = {} /\ op_taint tm hi = {} /\
  alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next /\
  ?ceiling. fresh_vars_wrt ceiling u /\ en.cs_next_var <= ceiling.cs_next_var /\
    (!v. evaluate_abi_decode_return env ret_type bs = INL v ==>
      abi_valid_allocated_entry H0 cenv env cenv.ce_struct_fields rt tv
        (if needs_external_call_wrap ret_type then ArrayV (TupleV [v]) else v)
        ctx func cenv cx es st en (Var source) hi (Lit 0w) (Var output)
        (w2n ro) (LENGTH (TAKE cap bs)) (TAKE cap bs) 0 dest dstid live ceiling u) /\
    (!err. evaluate_abi_decode_return env ret_type bs = INR err ==>
      (?av. has_type (vyper_to_abi_type env rt) av) /\
      (case type_to_abi_dec_info cenv.ce_struct_fields cenv rt of
        DecPrimWord clamp => 32 <= (LENGTH (TAKE cap bs)) | _ => T) /\
      ~(vyper_decode_valid_enc (vyper_to_abi_type env rt) (if is_dynamic (vyper_to_abi_type env rt)
        then (TAKE cap bs) else TAKE (static_length (vyper_to_abi_type env rt)) (TAKE cap bs)) /\
        abi_vyper_admissible env rt (dec (vyper_to_abi_type env rt) (if is_dynamic (vyper_to_abi_type
          env rt) then (TAKE cap bs) else TAKE (static_length (vyper_to_abi_type env rt)) (TAKE cap
          bs)))))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `lookup_var source t = SOME ro` by fs[eval_operand_def] >>
  conj_tac >- (drule_all extcall_return_clipped_window >> simp[]) >>
  conj_tac >- (drule_all ptr_covers_frame >> simp[]) >>
  simp[op_prov_def,op_taint_def] >>
  conj_tac >- metis_tac[gas_path_mem_zero_history,aggregate_mem_path_alloca_inv] >>
  conj_tac >- fs[ghost_inv_at_def] >>
  conj_tac >- fs[ghost_inv_at_def] >>
  qspecl_then [`u`,`en`] (qx_choose_then `ceiling` strip_assume_tac)
    return_decoder_ceiling_exists >>
  qexists_tac `ceiling` >> simp[] >>
  conj_tac
  >- ((rpt strip_tac >>
      `evaluate_abi_decode env rt (TAKE cap bs) =
        INL (if needs_external_call_wrap ret_type then ArrayV (TupleV [v]) else v)` by
        (irule abi_return_source_capped_success >>
         conj_tac >- simp[] >> qexistsl_tac [`ret_type`,`v`] >> simp[]) >>
      drule_then assume_tac evaluate_abi_decode_vyper_valid_enc >>
      drule_then assume_tac vyper_valid_enc_static_length_lower >>
      qpat_assum `evaluate_abi_decode _ _ _ = INL _` mp_tac >>
      simp[evaluate_abi_decode_def,decode_abi_value_def,AllCaseEqs()] >>
      strip_tac >>
      fs[vyper_valid_enc_def] >> simp[abi_valid_allocated_entry_def] >> (gvs[evaluate_abi_decode_def, decode_abi_value_def, AllCaseEqs(), vyper_valid_enc_def, abi_valid_allocated_entry_def, evaluate_abi_decode_vyper_valid_enc, vyper_valid_enc_static_length_lower, abi_return_source_capped_success]))) >>
  `abi_static_length (vyper_to_abi_type env rt) <= LENGTH (TAKE cap bs)` by
    (Cases_on `cap <= LENGTH bs` >> gvs[LENGTH_TAKE_EQ]) >>
  rpt gen_tac >> disch_tac >>
  conj_tac >- metis_tac[abi_width_coherent_inhabited] >>
  conj_tac
  >- (`(case type_to_abi_dec_info cenv.ce_struct_fields cenv rt of
           DecPrimWord clamp => 32 <= abi_static_size cenv.ce_struct_fields rt
         | _ => T)` by metis_tac[return_default_primitive_minimum] >>
      gvs[] >>
      Cases_on `type_to_abi_dec_info cenv.ce_struct_fields cenv
        (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)` >>
      gvs[] >> decide_tac) >>
  CCONTR_TAC >> gvs[] >>
  metis_tac[abi_return_reflected_success, sumTheory.sum_distinct]
QED
