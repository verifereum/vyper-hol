Theory extRetDynamicArrayEntryPtr
Ancestors
  extRetDynamicBodyPtr extRetRecursiveResourcePtr extRetFramedChildPtr
  robustCopyTransportPtr bodyPtrDefs ptrDiscipline venomState venomMemDefs
  valueEncoding words finite_map pred_set arithmetic list

(* Entry is independent of the compiler PC: the initial jump and header
   can share these initialized physical facts. *)
Theorem encoder_dynamic_loop_inv_init:
  ~s.vs_halted /\
  lookup_var ip s = SOME (n2w p) /\ lookup_var cursor s = SOME (n2w c) /\
  lookup_var src s = SOME (n2w a) /\ lookup_var dst s = SOME (n2w b) /\
  lookup_var cv s = SOME (n2w N) /\
  ptr_covers G tn ip s 32 /\ ptr_covers G tn cursor s 32 /\
  ptr_covers G tn src s scap /\ ptr_covers G tn dst s dcap /\
  mload p s = 0w /\ mload c s = n2w (32*N) /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) /\
  (!i. c <= i /\ i < c+32 ==> i NOTIN tn.t_mem) /\
  op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v a mem) /\
  encoder_resource ctx fn sites a scap protected s ==>
  encoder_dynamic_loop_inv ctx fn sites protected
    ip cursor src dst cv p c a b scap dcap tv v N ns 0 G tn s
Proof
  simp[encoder_dynamic_loop_inv_def]
QED

(* A concrete union of prefix/scratch writes may be narrower than the
   recursive envelope. Exact outside-site maps remain a separate premise. *)
Theorem encoder_dynamic_effect_from_footprint:
  writes SUBSET encoder_write_envelope sites sf b cap /\
  mem_agree_outside writes sf.vs_memory s.vs_memory /\
  (!i. i NOTIN writes ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
  s.vs_alloca_next <= sf.vs_alloca_next /\
  (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
    FLOOKUP sf.vs_allocas aid = SOME (p,sz)) /\
  (!aid. aid NOTIN sites ==> FLOOKUP sf.vs_allocas aid = FLOOKUP s.vs_allocas aid) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)) /\
  encoder_ambient_frame tn s tnf sf ==>
  encoder_dynamic_effect sa sites b cap G tn s Gf tnf sf
Proof
  simp[encoder_dynamic_effect_def, mem_agree_outside_def, SUBSET_DEF] >>
  metis_tac[]
QED
