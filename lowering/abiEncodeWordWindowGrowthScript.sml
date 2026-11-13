(* Same-endpoint memory growth for the singleton word encoder. *)
Theory abiEncodeWordWindowGrowth
Ancestors abiEncodeWindowLift

Theorem lower_abi_encode_word_window_mem_growth:
  let k = (case mid of NONE => 0 | SOME _ => 4) in
  let n = 32+32*word_size (maxlen+k) in
  let ids = window_alloca_sites func (frag_ids st final) in
  let bytes = (case mid of NONE => enc at av | SOME m => abi_builtin_encode_method_bytes m ++ enc at av) in
  lower_abi_encode ensure mid src (AbiCopy 32) maxlen st = (out,final) /\
  abi_encoder_admissible (AbiCopy 32) /\ abi_encoder_window_input (AbiCopy 32) at av sb cap s.vs_memory /\
  LENGTH (enc at av) <= maxlen /\ eval_operand src s = SOME (n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\ n < dimword (:256) /\
  ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas st.cs_next_id = SOME (p,n)) /\
  (cap=0 \/ sb+cap <= s.vs_alloca_next) /\ venomMemDefs$regions_disjoint (sb,cap) (p,n) /\
  (!i b sz. i IN ids /\ i <> st.cs_next_id /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st final ids [(p,n)] s t /\ mem_cont_sim ctx func s t /\
    window_mem_frame ctx func s t /\
    eval_operand out t = SOME (n2w p) /\ FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,n) /\
    p+n <= t.vs_alloca_next /\ p+n < dimword (:256) /\
    mem_bytes_at (p+32) (LENGTH bytes) t.vs_memory = bytes /\
    val_in_memory (BaseTV (BytesT (Dynamic (maxlen+k)))) (vyperValue$BytesV bytes) p t.vs_memory /\
    (!i r. FLOOKUP s.vs_allocas i = SOME r ==> FLOOKUP t.vs_allocas i = SOME r) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (mp_tac o MATCH_MP (BETA_RULE (PURE_REWRITE_RULE [LET_THM] lower_abi_encode_window_mem_frame_growth))) >>
  simp_tac bool_ss [] >> strip_tac >> qexists `t` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
