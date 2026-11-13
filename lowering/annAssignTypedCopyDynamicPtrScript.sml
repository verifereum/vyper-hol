(* Assembly boundaries for dynamic aggregate normalization. *)
Theory annAssignTypedCopyDynamicPtr
Ancestors
  annAssignTypedCopyDynamicAdmissiblePtr
  annAssignTypedCopyDynamicCompilerResourcesPtr
  annAssignTypedCopyDynamicHeaderPtr annAssignTypedCopyDynamicBulkPtr
  annAssignTypedCopyDynamicTestPtr annAssignTypedCopyDynamicLoopPtr
  annAssignTypedCopyDynamicBulkAdapterPtr annAssignTypedCopyDynamicLoopAdapterPtr
  fragGasPathPtr valueEncodingDefs valueEncoding typedCopyRobustTransportPtr
  reasonCopySourcePtr
  typedNormalizeDynarray typedMemoryCopy normalizationPrefixPtr
  annAssignTypedCopyFixedMetadataPtr exprLoweringProps fragExec
  bodyPtrDefs context compileEnv emitHelper venomState venomInst
  venomExecSemantics words arithmetic list rich_list freshWrites ASCIInumbers loweringStateRelDefs

Theorem annassign_dynarray_counted_ptr:
 !ce tenv dt st dtv stv C S vs dst src sa sb fn s b a G tn D ctx PG.
 compile_copy_dynarray_typed ce (Var dst) dt C (Var src) st sa = ((),sb) /\
 type_memory_bytes ce dt = type_memory_size dtv /\
 type_memory_bytes ce st = type_memory_size stv /\
 type_widens_to tenv st dt /\
 evaluate_type tenv (ArrayT st (Dynamic S)) = SOME (ArrayTV stv (Dynamic S)) /\
 evaluate_type tenv (ArrayT dt (Dynamic C)) = SOME (ArrayTV dtv (Dynamic C)) /\
 value_has_type (ArrayTV dtv (Dynamic C)) (ArrayV (DynArrayV vs)) /\
 val_wf (ArrayTV stv (Dynamic S)) (ArrayV (DynArrayV vs)) /\
 val_wf (ArrayTV dtv (Dynamic C)) (ArrayV (DynArrayV vs)) /\
 not_fresh_at sa src /\ not_fresh_at sa dst /\
 fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
 ~ctx_has_dalloca ctx /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 ptr_covers G tn src s (32 + S * type_memory_size stv) /\
 ptr_covers G tn dst s (32 + C * type_memory_size dtv) /\
 C < dimword (:256) /\
 w2n a + (32 + S * type_memory_size stv) < dimword (:256) /\
 w2n b + (32 + C * type_memory_size dtv) < dimword (:256) /\
 (w2n a + (32 + S * type_memory_size stv) <= w2n b \/
  w2n b + (32 + C * type_memory_size dtv) <= w2n a) /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
   val_in_memory (ArrayTV stv (Dynamic S)) (ArrayV (DynArrayV vs)) (w2n a) m) /\
 (!sc se xr yr u aw bw H tm v.
   compile_store_memory_typed ce (Var yr) dt (Var xr) st sc = ((),se) /\
   fn_has_code sc se fn /\ not_fresh_at sc xr /\ not_fresh_at sc yr /\
   u.vs_current_bb = sc.cs_current_bb /\
   u.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~u.vs_halted /\
   lookup_var xr u = SOME aw /\ lookup_var yr u = SOME bw /\
   ptr_covers H tm xr u (type_memory_size stv) /\
   ptr_covers H tm yr u (type_memory_size dtv) /\
   w2n aw + type_memory_size stv < dimword(:256) /\
   w2n bw + type_memory_size dtv < dimword(:256) /\
   (w2n aw + type_memory_size stv <= w2n bw \/
    w2n bw + type_memory_size dtv <= w2n aw) /\
   val_wf stv v /\ val_wf dtv v /\
   (!m. mem_agree_outside tm.t_mem u.vs_memory m ==>
     val_in_memory stv v (w2n aw) m) ==>
   ?K tk z. gas_path_ptr D 0 ctx fn PG H tm u 0 K tk (OK z) /\
     z.vs_current_bb = se.cs_current_bb /\
     z.vs_inst_idx = LENGTH se.cs_current_insts /\ ~z.vs_halted /\
     typed_copy_state_frame sc (w2n bw) (type_memory_size dtv) u z /\
     (!m. mem_agree_outside tk.t_mem z.vs_memory m ==>
       val_in_memory dtv v (w2n bw) m) /\
     tk.t_stor = tm.t_stor /\ tk.t_trans = tm.t_trans /\ tk.t_imm = tm.t_imm /\
     (!x. not_fresh_at sc x ==>
       lookup_var x z = lookup_var x u /\ FLOOKUP K x = FLOOKUP H x /\
       op_taint tk (Var x) = op_taint tm (Var x)) /\
     (!i. ~(w2n bw <= i /\ i < w2n bw + type_memory_size dtv) ==>
       mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 u.vs_memory /\
       (i IN tk.t_mem <=> i IN tm.t_mem))) ==>
 ?H tm t. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
   t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
   typed_copy_state_frame sa (w2n b) (32 + C * type_memory_size dtv) s t /\
   (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
     val_in_memory (ArrayTV dtv (Dynamic C)) (ArrayV (DynArrayV vs)) (w2n b) m) /\
   tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
   (!x. not_fresh_at sa x ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
     op_taint tm (Var x) = op_taint tn (Var x)) /\
   (!i. ~(w2n b <= i /\ i < w2n b + (32 + C * type_memory_size dtv)) ==>
     mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
     (i IN tm.t_mem <=> i IN tn.t_mem))
Proof
 rpt gen_tac >> strip_tac >> rename1 `ArrayTV stv (Dynamic scap)` >>
 match_mp_tac (Q.INST [`P` |-> `\v:value. T`, `S'` |-> `scap:num`]
   (SPEC_ALL annassign_dynarray_admissible_counted_ptr)) >>
 gvs[arithmeticTheory.ADD_COMM] >> gvs[]
QED
