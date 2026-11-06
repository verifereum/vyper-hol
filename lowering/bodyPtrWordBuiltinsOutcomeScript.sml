(* Strengthen the normal post on the existing counted pointer-path witness.
   The path premise is a separate obligation, not supplied by a weak post. *)
Theory bodyPtrWordBuiltinsOutcome
Ancestors fragGasPathPtr

Theorem gas_outcome_ptr_path_strengthen:
  gas_outcome_ptr D tops (ctx,fn) PG source (es,s0,G0,tn0) Q R /\
  (!n G tn t res ee.
    gas_path_ptr D 0 ctx fn PG G0 tn0 s0 n G tn (OK t) /\
    Q res ee G tn t ==> P res ee G tn t) ==>
  gas_outcome_ptr D tops (ctx,fn) PG source (es,s0,G0,tn0)
    (\res ee G tn t. Q res ee G tn t /\ P res ee G tn t) R
Proof
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_def] >>
  metis_tac[]
QED
