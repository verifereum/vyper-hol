(* Dynamic bytes expose a clean length word even for an empty payload. *)
Theory bodyFullRawCallHeaderView
Ancestors
  representationCleanPtr exprSimMemDefs bodyPtrDefs loweringPosts exprSimProps

Theorem raw_call_header_bytes_view:
  !cx ty max bs data G tn s b.
    evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic max))) /\
    ~is_word_type ty /\
    ptr_val_ok cx ty (BytesV bs) data G tn s /\
    expr_store_bound cx ty (BytesV bs) data s /\
    eval_operand data s = SOME (n2w b) /\
    b+32+LENGTH bs < dimword (:256) ==>
    ?x base cap.
      data = Var x /\ FLOOKUP G x = SOME (base,cap) /\
      base <= b /\ b+32+LENGTH bs <= base+cap /\
      b+32 <= s.vs_alloca_next /\
      b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
      op_taint tn data = {} /\
      (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
      mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
      mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        mem_word_at b mem = n2w (LENGTH bs) /\
        mem_bytes_at (b+32) (LENGTH bs) mem = bs)
Proof
  rpt gen_tac >> strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `w2n ((n2w b):bytes32) = b` by simp[] >>
  `op_taint tn data = {} /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory (BaseTV (BytesT (Dynamic max))) (BytesV bs) b mem) /\
   ?x base cap. data = Var x /\ FLOOKUP G x = SOME (base,cap) /\
      base <= b /\ b+32+32*word_size (LENGTH bs) <= base+cap` by
    (gvs[ptr_val_ok_def, ptr_mem_ok_def,
         val_footprint_def, val_store_size_def]) >>
  `b+32 <= s.vs_alloca_next` by
    (gvs[expr_store_bound_def, val_store_size_def]) >>
  drule robust_val_in_memory_bytes_clean >> simp[] >> strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     mem_word_at b mem = n2w (LENGTH bs) /\
     mem_bytes_at (b+32) (LENGTH bs) mem = bs` by
    (gen_tac >> disch_tac >>
     qpat_x_assum `!mem. _ ==> val_in_memory _ _ _ mem` drule >>
     disch_tac >> conj_tac
     >- (drule val_in_memory_bytes_word >> simp[]) >>
     irule val_in_memory_bytes_payload >>
     qexists_tac `BaseTV (BytesT (Dynamic max))` >> simp[]) >>
  `mem_agree_outside tn.t_mem s.vs_memory s.vs_memory` by
    simp[mem_agree_outside_def] >>
  qspec_then `LENGTH bs` assume_tac le_word_size_mul >>
  conj_tac >- decide_tac >>
  conj_tac >- (gen_tac >> strip_tac >>
    Cases_on `i < b+32` >> metis_tac[arithmeticTheory.NOT_LESS]) >>
  metis_tac[]
QED
