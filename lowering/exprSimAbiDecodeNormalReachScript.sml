(* Normal paths preserve predicates closed under every normal edge. *)
Theory exprSimAbiDecodeNormalReach
Ancestors fragGasPath fragExec

Theorem abi_decode_normal_path_invariant:
  (!s n t. P s /\ gas_path_edge ctx fn s n (OK t) ==> P t) ==>
  !s n t. P s /\ gas_path ctx fn s n (OK t) ==> P t
Proof
  strip_tac >>
  `!cx f s n r. gas_path cx f s n r ==>
     cx = ctx ==> f = fn ==> !t. r = OK t ==> P s ==> P t`
    suffices_by metis_tac[] >>
  ho_match_mp_tac gas_path_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[])
  >- (rpt strip_tac >> gvs[] >> metis_tac[])
  >> rpt strip_tac >> gvs[exit_result_def]
QED

Theorem abi_decode_normal_path_exclusion:
  P s0 /\
  (!s n t. P s /\ gas_path_edge ctx fn s n (OK t) ==> P t) /\
  (!t. P t ==> ~End t) ==>
  ~(?n t. gas_path ctx fn s0 n (OK t) /\ End t)
Proof
  metis_tac[abi_decode_normal_path_invariant]
QED
