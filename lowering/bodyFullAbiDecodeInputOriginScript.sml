Theory bodyFullAbiDecodeInputOrigin
Ancestors
  loweringStateRelDefs finite_map words

(* The input interval can belong either to an older allocation or to a live
   local region.  Transport needs only inclusion of the old allocation
   entries and equality of the reserved local pointer variables. *)
Theorem abi_decode_input_origin_transport:
  !ce start t s output_id scopes (input_word:256 word) (input_bytes:8 word list).
    local_ptrs_reserved ce start /\
    (!x. not_fresh_at start x ==> lookup_var x t = lookup_var x s) /\
    (!aid ib isz. aid < output_id /\
      FLOOKUP s.vs_allocas aid = SOME (ib,isz) ==>
      FLOOKUP t.vs_allocas aid = SOME (ib,isz)) /\
    ((?aid ib isz.
        aid < output_id /\ FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\
        ib <= w2n input_word /\
        w2n input_word + LENGTH input_bytes <= ib + isz) \/
     (?name ib isz.
        local_region ce scopes s name ib isz /\
        ib <= w2n input_word /\
        w2n input_word + LENGTH input_bytes <= ib + isz)) ==>
    ((?aid ib isz.
        aid < output_id /\ FLOOKUP t.vs_allocas aid = SOME (ib,isz) /\
        ib <= w2n input_word /\
        w2n input_word + LENGTH input_bytes <= ib + isz) \/
     (?name ib isz.
        local_region ce scopes t name ib isz /\
        ib <= w2n input_word /\
        w2n input_word + LENGTH input_bytes <= ib + isz))
Proof
  rpt gen_tac >> strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >> qexistsl_tac [`name`, `ib`, `isz`] >> simp[] >>
  `!name entry p sz.
     lookup_scopes name scopes = SOME entry /\
     FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     lookup_var p t = lookup_var p s`
    by metis_tac[local_ptrs_reserved_def] >>
  drule local_region_lookup_cong >> metis_tac[]
QED
