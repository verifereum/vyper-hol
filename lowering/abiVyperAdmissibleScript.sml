(* Independent per-value conversion guards for reflected ABI decoding. *)
Theory abiVyperAdmissible
Ancestors
  vyperABI vyperValue contractABI finite_map words list

Inductive abi_vyper_admissible:
[uint:]
  within_int_bound (Unsigned n) (&k) ==>
  abi_vyper_admissible env (BaseT (UintT n)) (NumV k)
[int:]
  within_int_bound (Signed n) i ==>
  abi_vyper_admissible env (BaseT (IntT n)) (contractABI$IntV i)
[address:]
  within_int_bound (Unsigned 160) (&k) ==>
  abi_vyper_admissible env (BaseT AddressT) (NumV k)
[bool:]
  k <= 1 ==> abi_vyper_admissible env (BaseT BoolT) (NumV k)
[bytes:]
  compatible_bound b (LENGTH bs) ==>
  abi_vyper_admissible env (BaseT (BytesT b)) (contractABI$BytesV bs)
[string:]
  LENGTH bs <= n ==>
  abi_vyper_admissible env (BaseT (StringT n)) (contractABI$BytesV bs)
[decimal:]
  within_int_bound decimal_bound i ==>
  abi_vyper_admissible env (BaseT DecimalT) (contractABI$IntV i)
[tuple:]
  abi_vyper_admissible_list env tys avs ==>
  abi_vyper_admissible env (TupleT tys) (ListV avs)
[array:]
  compatible_bound b (LENGTH avs) /\ evaluate_type env ty = SOME tv /\
  abi_vyper_admissible_list env (REPLICATE (LENGTH avs) ty) avs ==>
  abi_vyper_admissible env (ArrayT ty b) (ListV avs)
[none:]
  abi_vyper_admissible env NoneT (ListV [])
[struct_case:]
  FLOOKUP env nsid = SOME (StructArgs fields) /\
  abi_vyper_admissible_list (env \\ nsid) (MAP SND fields) avs ==>
  abi_vyper_admissible env (StructT nsid) (ListV avs)
[flag:]
  FLOOKUP env nsid = SOME (FlagArgs n) /\ n <= 256 /\ k < 2 ** n ==>
  abi_vyper_admissible env (FlagT nsid) (NumV k)
[list_empty:]
  abi_vyper_admissible_list env [] []
[cons:]
  abi_vyper_admissible env ty av /\ abi_vyper_admissible_list env tys avs ==>
  abi_vyper_admissible_list env (ty::tys) (av::avs)
End

Theorem abi_vyper_admissible_list_nil:
  abi_vyper_admissible_list env [] avs <=> avs = []
Proof
  simp[Once abi_vyper_admissible_cases]
QED

Theorem abi_vyper_admissible_list_cons:
  abi_vyper_admissible_list env (ty::tys) avs <=>
  ?av rest. avs = av::rest /\ abi_vyper_admissible env ty av /\
    abi_vyper_admissible_list env tys rest
Proof
  simp[Once abi_vyper_admissible_cases] >> metis_tac[]
QED

Theorem abi_vyper_admissible_singleton:
  abi_vyper_admissible env (TupleT [ty]) (ListV [av]) <=>
  abi_vyper_admissible env ty av
Proof
  simp[Once abi_vyper_admissible_cases,
       abi_vyper_admissible_list_cons, abi_vyper_admissible_list_nil]
QED

Theorem abi_vyper_admissible_array_iff:
  abi_vyper_admissible env (ArrayT ty b) av <=>
  ?avs tv. av = ListV avs /\ compatible_bound b (LENGTH avs) /\
    evaluate_type env ty = SOME tv /\
    abi_vyper_admissible_list env (REPLICATE (LENGTH avs) ty) avs
Proof
  simp[Once abi_vyper_admissible_cases] >> metis_tac[]
QED

Theorem abi_vyper_admissible_struct_iff:
  abi_vyper_admissible env (StructT nsid) av <=>
  ?fields avs. av = ListV avs /\ FLOOKUP env nsid = SOME (StructArgs fields) /\
    abi_vyper_admissible_list (env \\ nsid) (MAP SND fields) avs
Proof
  simp[Once abi_vyper_admissible_cases] >> metis_tac[]
QED

Theorem abi_vyper_admissible_convert_mutual:
  (!env ty av. abi_vyper_admissible env ty av ==>
    ?v. abi_to_vyper env ty av = SOME v) /\
  (!env tys avs. abi_vyper_admissible_list env tys avs ==>
    ?vs. abi_to_vyper_list env tys avs = SOME vs)
Proof
  ho_match_mp_tac abi_vyper_admissible_ind >>
  rpt strip_tac >> simp[abi_to_vyper_def, check_IntV_def] >>
  gvs[abi_to_vyper_def, check_IntV_def]
QED

Theorem abi_vyper_admissible_convert:
  abi_vyper_admissible env ty av ==>
  ?v. abi_to_vyper env ty av = SOME v
Proof
  metis_tac[abi_vyper_admissible_convert_mutual]
QED

Theorem abi_vyper_admissible_list_convert:
  abi_vyper_admissible_list env tys avs ==>
  ?vs. abi_to_vyper_list env tys avs = SOME vs
Proof
  metis_tac[abi_vyper_admissible_convert_mutual]
QED
