(* The bytestring argument-store suffix, exported for the linked IntCall
   staging proof.  The generic path theorem already isolates the length
   rounded copy and its frame; this satellite gives that interface a name
   owned by the IntCall argument stage. *)
Theory bodyIntCallArgBytesStoreMods
Ancestors
  bodyLocalBytesCopyPathMods

Theorem intcall_arg_bytes_store_mods:
  compile_store_memory ce (Var xs) (Var xd) dty sty sa = ((),sb) /\
  ~is_word_type dty /\ is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory stv v (w2n sw) m) /\
  n = 32 + 32 * word_size len /\ n < dimword (:256) /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  ptr_covers G tn xs s n /\ ptr_covers G tn xd s n /\
  w2n sw + n <= s.vs_alloca_next /\ w2n dw + n <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    n <= type_memory_size stv /\ n <= type_memory_size dtv /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
         val_in_memory dtv v (w2n dw) m) /\
    typed_copy_state_frame sa (w2n dw) n s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + n) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x)) /\
    (lo <= w2n dw ==>
       mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
       !i. i < lo ==> (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  ACCEPT_TAC bodyLocalBytesCopyPathModsTheory.local_bytes_copy_path_mods
QED
