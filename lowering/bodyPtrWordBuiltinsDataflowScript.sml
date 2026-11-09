(* Opaque-edge invariant transport; the gas count is not a step measure. *)
Theory bodyPtrWordBuiltinsDataflow
Ancestors fragGasPathPtr fragExec

Theorem gas_path_ptr_normal_invariant:
  !D lo ctx fn PG G0 tn0 s0 n G tn r.
    gas_path_ptr D lo ctx fn PG G0 tn0 s0 n G tn r ==>
    !I t. r = OK t /\ I G0 s0 /\
      (!H un s k J vn u.
        I H s /\ gas_path_ptr_edge D lo ctx fn PG H un s k J vn (OK u) ==>
        I J u) ==>
      I G t
Proof
  ho_match_mp_tac gas_path_ptr_ind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >>
      qpat_x_assum `!Inv u. r = OK u /\ _ ==> _`
        (qspecl_then [`I'`, `t`] mp_tac) >>
      impl_tac >- (simp[] >> metis_tac[]) >> simp[])
  >> rpt strip_tac >> gvs[exit_result_def]
QED
