(* Scratch writes are authorized by actual sites or by the new frontier,
   never by an envelope inferred from instruction ids. *)
Theory abiMalformedSiteFrame
Ancestors
  abiMalformedIndexState abiMalformedResources abiMalformedCopyState
  abiMalformedPruneState abiDecoderReentry abiDecoderIndexInit
  exprLoweringProps localPtrsProps compileEnv loweringStateRelDefs valueCopy valueEncoding valueEncodingDefs
  venomState venomMemDefs venomMemProps venomExecSemantics finite_map
  pred_set list arithmetic

Definition abi_malformed_site_range_def:
  abi_malformed_site_range sites s t at n <=>
    (?aid b sz. aid IN sites /\
       FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
       b <= at /\ at + n <= b + sz) \/
    (s.vs_alloca_next <= at /\ at + n <= t.vs_alloca_next)
End

Theorem abi_malformed_site_range_protected:
  alloca_inv s /\ aid NOTIN sites /\
  FLOOKUP s.vs_allocas aid = SOME (B,cap) /\ L <= cap /\
  abi_malformed_site_range sites s t at n ==>
  B + L <= at \/ at + n <= B
Proof
  rw[abi_malformed_site_range_def]
  >- (fs[alloca_inv_def, allocas_non_overlapping_def] >>
      `aid <> aid'` by metis_tac[] >>
      qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule_all >> decide_tac) >>
  fs[alloca_inv_def, alloca_next_valid_def] >>
  first_x_assum drule >> decide_tac
QED
