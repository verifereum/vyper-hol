Theory abiReturnCombinedReject
Ancestors
  abiReturnPrefixTransport abiReturnPrefixExec abiReturnReject abiReturnSize
  exprLoweringProps abiDecoderAppend abiMalformedRecursiveInterface
  fragExec compileEnv venomState list rich_list arithmetic words

Theorem abi_return_decode_reject:
  rt = (if needs_external_call_wrap ty then TupleT [ty] else ty) /\
  cap = vyper_abi_size_bound env rt /\ lo = abi_static_length (vyper_to_abi_type env rt) /\
  (~is_dynamic (vyper_to_abi_type env rt) ==> cap = lo) /\ lo <= cap /\
  lo < dimword (:256) /\ cap < dimword (:256) /\
  evaluate_abi_decode_return env ty bs = INR err /\
  abi_decoder_coherent ce env sf rt tv /\ abi_decode_bytes_widths env rt /\
  assignable_type env rt /\ type_memory_size tv < dimword (:256) /\
  abi_size_bound sf rt < dimword (:256) /\ type_to_abi_dec_info sf ce rt = di /\
  compile_return_value_decode lo cap a = (hi,b) /\
  compile_abi_decode_to_buf dst (Lit 0w) MLOAD base_op hi di b = ((),en) /\
  fn_inst_ids_distinct func /\ fn_has_code a en func /\
  type_memory_bytes ce rt <= outsz /\
  (case di of DecPrimWord clamp => 32 <= lo | _ => T) /\
  abi_return_decode_ready ctx func cenv cx es a
    (abi_malformed_scratch_sites b en func) dstid live base_op dst
    B cap bs d outsz s /\
  fresh_vars_wrt a s /\ s.vs_returndata = bs /\ LENGTH bs < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?fuel u. run_from fuel ctx func s = Abort Revert_abort u
Proof
  strip_tac >>
  `ci_mono a b` by
    (mp_tac (Q.SPECL [`lo`, `cap`, `a`] ci_mono_compile_return_value_decode) >> simp[]) >>
  `ci_mono b en` by
    (mp_tac (Q.SPECL [`dst`, `Lit 0w`, `MLOAD`, `base_op`, `hi`, `di`, `b`]
       (cj 1 ci_mono_compile_abi_decode)) >> simp[]) >>
  `fn_has_code a b func /\ fn_has_code b en func` by
    (irule fn_has_code_split >> fs[ci_mono_def] >> goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `LENGTH bs < lo`
  >- (`LENGTH s.vs_returndata < dimword (:256)` by simp[] >>
      `?u. run_inst_seq (emitted_insts a b) s = Abort Revert_abort u` by
        (drule_all abi_return_size_run >> gvs[]) >>
      drule_at (Pat `run_inst_seq _ _ = _`) abi_return_prefix_abort >>
      disch_then irule >> simp[] >> qexistsl_tac [`cap`, `hi`, `lo`] >> simp[]) >>
  `lo <= LENGTH bs` by decide_tac >>
  drule_all abi_return_prefix_transport >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `fresh_vars_wrt en (u with vs_inst_idx := LENGTH b.cs_current_insts)` by
    (fs[fresh_vars_wrt_def, ci_mono_def] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  `lo <= LENGTH (TAKE cap bs)` by
    (pure_rewrite_tac[LENGTH_TAKE_EQ] >> Cases_on `cap <= LENGTH bs` >>
     gvs[]) >>
  `?fuel z. run_from fuel ctx func (u with vs_inst_idx := LENGTH b.cs_current_insts) =
       Abort Revert_abort z` by
    (drule_at (Pat `abi_malformed_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
       abi_return_bounded_decode_reject >>
     disch_then irule >>
     simp[] >>
     conj_tac >- (drule abi_return_size_code >> gvs[same_blocks_def]) >>
     conj_tac >- (qexists_tac `en` >> gvs[]) >>
     gvs[] >>
     first_assum (irule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
     qexists_tac `err` >> simp[] >>
     qmatch_goalsub_abbrev_tac `case info of DecPrimWord clamp => _ | _ => _` >>
     Cases_on `info` >> gvs[] >> decide_tac) >>
  irule abi_return_prefix_then_abort >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED
