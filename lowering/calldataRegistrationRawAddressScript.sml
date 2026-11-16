(* Raw source addresses at the top-level registration boundary. *)
Theory calldataRegistrationRawAddress
Ancestors
  calldataSourceCorrespondence vyperCalldata arithmetic words

(* A top-level dynamic offset is one word: adding four can wrap only
   into [0,4), exactly the interval rejected by the source guard. *)
Theorem calldata_argument_pointer_nonwrap:
  !delta. delta < dimword(:256) ==>
  (4 <= (4 + delta) MOD dimword(:256) <=>
   4 + delta < dimword(:256)) /\
  (4 <= (4 + delta) MOD dimword(:256) ==>
   (4 + delta) MOD dimword(:256) = 4 + delta)
Proof
  gen_tac >> disch_tac >> Cases_on `4 + delta < dimword(:256)`
  >- simp[LESS_MOD] >>
  `4 < dimword(:256)` by simp[dimword_def] >>
  `(4 + delta) MOD dimword(:256) = 4 + delta - dimword(:256)` by
    (irule MOD_UNIQUE >> qexists `1` >> simp[] >> decide_tac) >>
  simp[] >> decide_tac
QED

(* The load and the guarded source alternatives share the same raw pointer.
   The static case uses the head bound, not a dynamic-payload bound. *)
Theorem calldata_decode_args_step_exact:
  cd = s.vs_call_ctx.cc_calldata /\
  delta = w2n (cd_word cd (4 + ofs)) /\
  p = (if tv_abi_dynamic tv then
         (4 + delta) MOD dimword(:256) else 4 + ofs) /\
  4 + ofs < dimword(:256) ==>
  abi_decode_load CALLDATALOAD (n2w (4 + ofs) : bytes32) s = n2w delta /\
  (4 <= p ==>
    (tv_abi_dynamic tv ==> 4 + delta < dimword(:256)) /\
    p = 4 + (if tv_abi_dynamic tv then delta else ofs)) /\
  (calldata_decode_args cd (tv::tvs) ofs = NONE <=>
    p < 4 \/
    (4 <= p /\ cd_decode F cd tv p = NONE) \/
    (?x. 4 <= p /\ cd_decode F cd tv p = SOME x /\
         calldata_decode_args cd tvs (ofs + tv_abi_size tv) = NONE)) /\
  (!vals. calldata_decode_args cd (tv::tvs) ofs = SOME vals <=>
    ?x xs. 4 <= p /\ cd_decode F cd tv p = SOME x /\
      calldata_decode_args cd tvs (ofs + tv_abi_size tv) = SOME xs /\
      vals = x::xs)
Proof
  rpt strip_tac
  >- simp[calldata_decode_load_word, w2n_n2w, LESS_MOD, n2w_w2n]
  >- (Cases_on `tv_abi_dynamic tv` >> gvs[] >>
      qspec_then `w2n (cd_word s.vs_call_ctx.cc_calldata (4 + ofs))`
        mp_tac calldata_argument_pointer_nonwrap >> simp[w2n_lt])
  >- (Cases_on `tv_abi_dynamic tv` >> gvs[] >>
      qspec_then `w2n (cd_word s.vs_call_ctx.cc_calldata (4 + ofs))`
        mp_tac calldata_argument_pointer_nonwrap >> simp[w2n_lt])
  >- (simp[Once calldata_decode_args_def] >> gvs[AllCaseEqs(), NOT_LESS] >> metis_tac[])
  >> simp[Once calldata_decode_args_def] >> gvs[AllCaseEqs(), NOT_LESS] >> metis_tac[]
QED
