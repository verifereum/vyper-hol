Theory calldataExactDynIteration
Ancestors
  calldataDynStep vyperCalldataProps vyperCalldata valueEncodingDefs
  valueEncodingProps arithmetic list venomState

Theorem calldata_exact_owned_iteration_prefix[local]:
  !left j vs s.
  j+left = bound /\ H j s /\ LENGTH vs = j /\
  cd_decode_elems F cd tv srcbase 0 j = SOME vs /\
  EVERY P vs /\ EVERY (val_wf tv) vs /\
  (!k. k < j ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) s.vs_memory) /\
  (!u. Rel u u) /\
  (!u v w. Rel u v /\ Rel v w ==> Rel u w) /\
  (!u v. Rel u v /\ X v ==> X u) /\
  (!i u. i < bound /\ H i u ==>
    (cd_decode F cd tv (cd_member_ptr F cd tv srcbase (i*tv_abi_size tv)) = NONE /\ X u) \/
    ?v x. cd_decode F cd tv (cd_member_ptr F cd tv srcbase (i*tv_abi_size tv)) = SOME x /\
      H (SUC i) v /\ P x /\ val_wf tv x /\
      val_in_memory tv x (d+32+i*type_memory_size tv) v.vs_memory /\
      mem_bytes_at d (32+i*type_memory_size tv) v.vs_memory =
        mem_bytes_at d (32+i*type_memory_size tv) u.vs_memory /\ Rel u v) /\
  (!u xs. H bound u /\ LENGTH xs = bound /\
    cd_decode_elems F cd tv srcbase 0 bound = SOME xs /\
    EVERY P xs /\ EVERY (val_wf tv) xs /\
    (!k. k < bound ==> val_in_memory tv (EL k xs)
      (d+32+k*type_memory_size tv) u.vs_memory) ==>
    ?t. Q xs t /\ Rel u t) ==>
  (cd_decode_elems F cd tv srcbase 0 bound = NONE /\ X s) \/
  ?xs t. cd_decode_elems F cd tv srcbase 0 bound = SOME xs /\ Q xs t /\ Rel s t
Proof
  Induct >- (rpt gen_tac >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `j < bound` by decide_tac >>
  qpat_assum `!i u. _` drule_all >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac strip_assume_tac)
  >- suspend "rejected" >>
  suspend "accepted"
QED
Resume calldata_exact_owned_iteration_prefix[rejected]:
  disj1_tac >> asm_rewrite_tac [] >>
  `bound = j + SUC left` by decide_tac >>
  qpat_x_assum `bound = _` (fn th => once_rewrite_tac [th]) >>
  once_rewrite_tac [cd_decode_elems_add] >>
  pure_asm_rewrite_tac [] >>
  simp[Once cd_decode_def]
QED
Resume calldata_exact_owned_iteration_prefix[accepted]:
  `!k. k < j ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) v.vs_memory` by
    (rpt strip_tac >> irule (cj 2 calldata_prefix_window_transport) >>
     conj_tac >- simp[] >>
     reverse conj_tac >- simp[] >>
     qexistsl [`j`, `s`] >> asm_rewrite_tac[]) >>
  `LENGTH (vs ++ [x]) = SUC j /\ EVERY P (vs ++ [x]) /\
    EVERY (val_wf tv) (vs ++ [x]) /\
    (!k. k < SUC j ==> val_in_memory tv (EL k (vs ++ [x]))
      (d+32+k*type_memory_size tv) v.vs_memory)` by
    (irule calldata_prefix_snoc >> asm_rewrite_tac[]) >>
  `cd_decode_elems F cd tv srcbase 0 (SUC j) = SOME (vs ++ [x])` by
    (rewrite_tac[ADD1, cd_decode_elems_add] >>
     simp[Once cd_decode_def] >>
     once_rewrite_tac[ONE] >> simp[Once cd_decode_def] >>
     simp[Once cd_decode_def]) >>
  first_x_assum (qspecl_then [`SUC j`, `vs ++ [x]`, `v`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> asm_rewrite_tac[] >> decide_tac)) >>
  strip_tac >> metis_tac[]
QED
Finalise calldata_exact_owned_iteration_prefix

Theorem calldata_exact_owned_iteration:
  H 0 start /\
  (!u. Rel u u) /\
  (!u v w. Rel u v /\ Rel v w ==> Rel u w) /\
  (!u v. Rel u v /\ X v ==> X u) /\
  (!i u. i < bound /\ H i u ==>
    (cd_decode F cd tv (cd_member_ptr F cd tv srcbase (i*tv_abi_size tv)) = NONE /\ X u) \/
    ?v x. cd_decode F cd tv (cd_member_ptr F cd tv srcbase (i*tv_abi_size tv)) = SOME x /\
      H (SUC i) v /\ P x /\ val_wf tv x /\
      val_in_memory tv x (d+32+i*type_memory_size tv) v.vs_memory /\
      mem_bytes_at d (32+i*type_memory_size tv) v.vs_memory =
        mem_bytes_at d (32+i*type_memory_size tv) u.vs_memory /\ Rel u v) /\
  (!u xs. H bound u /\ LENGTH xs = bound /\
    cd_decode_elems F cd tv srcbase 0 bound = SOME xs /\
    EVERY P xs /\ EVERY (val_wf tv) xs /\
    (!k. k < bound ==> val_in_memory tv (EL k xs)
      (d+32+k*type_memory_size tv) u.vs_memory) ==>
    ?t. Q xs t /\ Rel u t) ==>
  (cd_decode_elems F cd tv srcbase 0 bound = NONE /\ X start) \/
  ?xs t. cd_decode_elems F cd tv srcbase 0 bound = SOME xs /\ Q xs t /\ Rel start t
Proof
  strip_tac >> irule calldata_exact_owned_iteration_prefix >>
  asm_rewrite_tac[] >>
  qexistsl [`H`, `P`, `d`, `0`, `bound`, `[]`] >>
  simp[Once cd_decode_def]
QED
