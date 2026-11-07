(* Keep physical ownership separate from ghost coverage. *)
Theory abiDecodePtrInputWindow
Ancestors
  bodyPtrHashBuiltinsInputWindow exprSimHash loweringPosts compileEnv
  exprLoweringProps arithmetic words

Theorem abi_decode_bytes_physical_window:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa sb es (BytesV bs) op s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic cap))) /\
  ~is_word_type ty /\ eval_operand op s = SOME w /\
  sb.cs_next_id <= sc.cs_next_id ==>
  ((?aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) /\
       aid < sc.cs_next_id /\ b <= w2n w /\
       w2n w + (32 + LENGTH bs) <= b+k) \/
   (?name b k. local_region cenv es.scopes s name b k /\
       b <= w2n w /\ w2n w + (32 + LENGTH bs) <= b+k)) /\
  w2n w + (32 + LENGTH bs) < dimword (:256)
Proof
  strip_tac >>
  `((?aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) /\
       aid < sc.cs_next_id /\ b <= w2n w /\
       w2n w + (32 + LENGTH bs) <= b+k) \/
    (?name b k. local_region cenv es.scopes s name b k /\
       b <= w2n w /\ w2n w + (32 + LENGTH bs) <= b+k))` by
    (drule (Q.INST [`a` |-> `w2n w`, `n` |-> `32 + LENGTH (bs:word8 list)`]
       hash_expr_val_at_input_window) >>
     disch_then (qspecl_then [`w`, `BaseTV (BytesT (Dynamic cap))`, `sc`, `bs`] mp_tac) >>
     simp[val_footprint_def]) >>
  conj_tac >- metis_tac[] >>
  metis_tac[hash_live_footprint_bound]
QED

Theorem abi_decode_physical_window_disjoint:
  ((?aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) /\
       aid < sc.cs_next_id /\ b <= a /\ a+n <= b+k) \/
   (?name b k. local_region cenv es.scopes s name b k /\
       b <= a /\ a+n <= b+k)) /\
  (!aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) /\
       aid < sc.cs_next_id ==> regions_disjoint d m b k) /\
  (!name b k. local_region cenv es.scopes s name b k ==>
       regions_disjoint d m b k) ==>
  regions_disjoint d m a n
Proof
  simp[compileEnvTheory.regions_disjoint_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> decide_tac
QED
