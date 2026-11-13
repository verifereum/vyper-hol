(* Conditional recursive producers feed the shared callback-driven iterator. *)
Theory entryReachBodyConditionalArray
Ancestors
  valueEncodingDefs entryReachBodyCanonicalArrayIteration entryReachBodyConditionalArrayChild

Theorem entry_conditional_dynamic_array_iteration:
  cfg = ((ce,env,ty,tv,maxn,parent_di,avs,xs),
     (ip,src,dst,st,ops,mid,last,limit_st,next,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,reserve,prepared,p,sb,ambient),
     (hdr,body_lbl,exit,hid,bb)) /\ iteration_static_config cfg /\
  (!k. k < LENGTH xs ==> entry_conditional_array_child_producer ce env ty tv
    (EL k avs) (EL k xs) ctx fn oid root extent ambient b reserve site limit_st) /\
  entry_owned_loop_inv ctx fn site hdr ip src p (n2w sb) tv xs d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) cid oid root extent j s /\
  iteration_frame next limit_st prepared ambient b reserve
    (\m. mem_word_at d m = n2w (LENGTH xs)) s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) t /\
    iteration_frame next limit_st prepared ambient b reserve
      (\m. mem_word_at d m = n2w (LENGTH xs)) t /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d t.vs_memory /\
    entry_loop_trace ctx fn
      (cid INSERT window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id))
      [(d,32+LENGTH xs*type_memory_size tv)] s t
Proof
  strip_tac >> drule_all iteration_conditional_semantic_callback >> strip_tac >>
  drule_all entry_array_callback_iteration >> simp[]
QED
