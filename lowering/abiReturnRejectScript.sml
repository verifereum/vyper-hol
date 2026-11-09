(* Source-return acceptance at the exact capped decoder reflection boundary. *)
Theory abiReturnReject
Ancestors
  abiReturnConversion abiWidthInhabited abiMalformedWidthOutcome abiMalformedOutcomeContract
  abiMalformedRecursiveInterface abiCallerAbiBound abiDecoderCoherence
  vyperABI contractABI fragExec list rich_list words

Theorem abi_return_reflected_success:
  rt = (if needs_external_call_wrap ty then TupleT [ty] else ty) /\
  cap = vyper_abi_size_bound env rt /\
  (~is_dynamic (vyper_to_abi_type env rt) ==>
    cap = static_length (vyper_to_abi_type env rt)) /\
  abi_static_length (vyper_to_abi_type env rt) <= LENGTH (TAKE cap bs) /\
  vyper_decode_valid_enc (vyper_to_abi_type env rt)
    (if is_dynamic (vyper_to_abi_type env rt) then TAKE cap bs
     else TAKE (static_length (vyper_to_abi_type env rt)) (TAKE cap bs)) /\
  abi_vyper_admissible env rt (dec (vyper_to_abi_type env rt)
    (if is_dynamic (vyper_to_abi_type env rt) then TAKE cap bs
     else TAKE (static_length (vyper_to_abi_type env rt)) (TAKE cap bs))) ==>
  ?v. evaluate_abi_decode_return env ty bs = INL v
Proof
  strip_tac >>
  `vyper_decode_valid_enc (vyper_to_abi_type env rt) (TAKE cap bs) /\
   abi_vyper_admissible env rt (dec (vyper_to_abi_type env rt) (TAKE cap bs))` by
    (Cases_on `is_dynamic (vyper_to_abi_type env rt)` >>
     fs[] >> gvs[TAKE_TAKE_MIN]) >>
  irule (SIMP_RULE bool_ss [LET_THM] abi_return_admissible_success) >>
  gvs[vyper_valid_enc_returndata_def]
QED

Theorem abi_return_bounded_decode_reject:
  rt = (if needs_external_call_wrap ty then TupleT [ty] else ty) /\
  cap = vyper_abi_size_bound env rt /\
  (~is_dynamic (vyper_to_abi_type env rt) ==>
    cap = static_length (vyper_to_abi_type env rt)) /\
  abi_static_length (vyper_to_abi_type env rt) <= LENGTH (TAKE cap bs) /\
  evaluate_abi_decode_return env ty bs = INR err /\
  abi_decoder_coherent ce env sf rt tv /\ abi_decode_bytes_widths env rt /\
  assignable_type env rt /\ type_memory_size tv < dimword (:256) /\
  abi_size_bound sf rt < dimword (:256) /\
  type_to_abi_dec_info sf ce rt = di /\
  compile_abi_decode_to_buf dst (Lit 0w) MLOAD base_op hi di st = ((),en) /\
  fn_inst_ids_distinct func /\ fn_has_code st en func /\
  type_memory_bytes ce rt <= outsz /\
  en.cs_next_var <= ceiling.cs_next_var /\
  (case di of DecPrimWord clamp => 32 <= LENGTH (TAKE cap bs) | _ => T) /\
  abi_malformed_entry ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live
    base_op hi (Lit 0w) dst B (LENGTH (TAKE cap bs)) (TAKE cap bs) 0 d outsz incoming /\
  fresh_vars_wrt ceiling incoming /\
  ~incoming.vs_halted /\ incoming.vs_current_bb = st.cs_current_bb /\
  incoming.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?fuel u. run_from fuel ctx func incoming = Abort Revert_abort u
Proof
  strip_tac >>
  `abi_malformed_bounded_type_outcome ce env sf rt tv` by
    metis_tac[abi_malformed_width_coherent_outcome] >>
  `?av. has_type (vyper_to_abi_type env rt) av` by
    (irule abiWidthInhabitedTheory.abi_width_coherent_inhabited >> metis_tac[]) >>
  `abi_malformed_constructor_outcome env rt di ctx func cenv cx es st en
     base_op hi (Lit 0w) dst outsz` by
    (fs[abi_malformed_bounded_type_outcome_def] >> metis_tac[]) >>
  qpat_x_assum `abi_malformed_constructor_outcome _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_malformed_constructor_outcome_def] >>
  disch_then drule >> disch_then (drule_at (Pos (el 3))) >> simp[] >>
  disch_then (qspec_then `ceiling` mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  fs[frag_outcome_def, abi_malformed_reflected_post_def]
  >- (`?v. evaluate_abi_decode_return env ty bs = INL v` by
        (irule abi_return_reflected_success >>
         qexistsl_tac [`cap`, `rt`] >> gvs[TAKE_TAKE_MIN]) >> gvs[]) >>
  metis_tac[]
QED
