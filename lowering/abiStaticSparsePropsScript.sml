(* Indexed canonical ABI chunks for sparse fixed arrays. No execution claims. *)
Theory abiStaticSparseProps
Ancestors
  vyperABI vyperTyping sorting alist

Theorem sorted_sparse_ALOOKUP:
  SORTED $< (MAP FST (sparse : (num # value) list)) /\
  MEM (k,v) sparse ==>
  ALOOKUP sparse k = SOME v
Proof
  strip_tac >> irule ALOOKUP_ALL_DISTINCT_MEM >> simp[] >>
  irule SORTED_ALL_DISTINCT >>
  qexists_tac `$<` >>
  simp[relationTheory.irreflexive_def, relationTheory.transitive_def] >>
  metis_tac[arithmeticTheory.LESS_TRANS]
QED

Theorem canonical_sparse_length:
  !n sparse avs. vyper_to_abi_sparse tenv ty tv n sparse = SOME avs ==>
    LENGTH avs = n
Proof
  Induct >> simp[Once vyper_to_abi_def] >>
  rpt gen_tac >>
  simp[Once vyper_to_abi_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> res_tac >> gvs[]
QED

Theorem canonical_sparse_lookup:
  !n sparse avs k v.
    vyper_to_abi_sparse tenv ty tv n sparse = SOME avs /\
    k < n /\ ALOOKUP sparse k = SOME v ==>
    vyper_to_abi tenv ty v = SOME (EL k avs)
Proof
  Induct >- simp[] >>
  rpt gen_tac >>
  simp[Once vyper_to_abi_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `k = n` >> gvs[] >>
  imp_res_tac canonical_sparse_length >>
  simp[listTheory.EL_APPEND_EQN] >>
  `k < n` by decide_tac >> gvs[] >>
  metis_tac[]
QED

Theorem typed_sparse_key_bound:
  !sparse. sparse_has_type tv n sparse /\ MEM (k,v) sparse ==> k < n
Proof
  Induct >> simp[value_has_type_def] >>
  Cases_on `h` >> simp[value_has_type_def] >> metis_tac[]
QED

Theorem canonical_typed_sparse_index:
  SORTED $< (MAP FST sparse) /\ sparse_has_type tv n sparse /\
  vyper_to_abi_sparse tenv ty tv n sparse = SOME avs ==>
  LENGTH avs = n /\
  (!k v. MEM (k,v) sparse ==>
     k < n /\ vyper_to_abi tenv ty v = SOME (EL k avs))
Proof
  strip_tac >> conj_tac
  >- metis_tac[canonical_sparse_length] >>
  rpt strip_tac
  >- metis_tac[typed_sparse_key_bound] >>
  irule canonical_sparse_lookup >>
  metis_tac[typed_sparse_key_bound, sorted_sparse_ALOOKUP]
QED

(* All exported bridges must be independent of admitted compiler correctness. *)
val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SPARSE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI sparse bridge not kernel closed: " ^ n)
  end) (DB.thms "abiStaticSparseProps");
