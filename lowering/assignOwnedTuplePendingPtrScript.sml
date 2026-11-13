(* Pending tuple values keep their representation inside a saved owned window. *)
Theory assignOwnedTuplePendingPtr
Ancestors
  logValueFramePtr assignTuplePtrCopyLen exprSimProps bodyPtrDefs
  valueEncodingTyping valueEncodingProps valueEncodingProofs
  venomState venomExecSemantics ptrDiscipline emitHelperProps
  context compileEnv freshWrites finite_map list arithmetic words

Theorem owned_tuple_pending_values_frame_ptr:
  LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) stys stvs /\
  LIST_REL value_has_type stvs vs /\ LENGTH ops = LENGTH stys /\
  sa.cs_next_var <= sb.cs_next_var /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w) /\
  (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
    op_taint tt (Var x) = op_taint tn (Var x)) /\
  (!i. own_base <= i /\ i < own_base+own_size ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tt.t_mem ==> i IN tn.t_mem)) /\
  (!i. i < LENGTH stys ==>
    ?src sw. EL i ops = Var src /\ not_fresh_at sa src /\
      lookup_var src s = SOME sw /\
      ptr_val_ok cx (EL i stys) (EL i vs) (Var src) G tn s /\
      (is_word_type (EL i stys) ==> sw = typed_val_to_w256 (EL i stvs) (EL i vs)) /\
      (~is_word_type (EL i stys) ==>
        ptr_covers G tn src s (type_memory_size (EL i stvs)) /\
        own_base <= w2n sw /\
        w2n sw+type_memory_size (EL i stvs) <= own_base+own_size)) ==>
  !i. i < LENGTH stys ==>
    ?src sw. EL i ops = Var src /\ not_fresh_at sb src /\
      lookup_var src t = SOME sw /\
      ptr_val_ok cx (EL i stys) (EL i vs) (Var src) H tt t /\
      (is_word_type (EL i stys) ==> sw = typed_val_to_w256 (EL i stvs) (EL i vs)) /\
      (~is_word_type (EL i stys) ==>
        ptr_covers H tt src t (type_memory_size (EL i stvs)) /\
        own_base <= w2n sw /\
        w2n sw+type_memory_size (EL i stvs) <= own_base+own_size)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gen_tac >> strip_tac >>
  qpat_assum `!i. i < LENGTH stys ==> ?src sw. _`
    (fn th => qpat_assum `i < LENGTH stys`
      (fn bound => mp_tac (MATCH_MP (Q.SPEC `i` th) bound))) >>
  disch_then (qx_choosel_then [`src`,`sw`] strip_assume_tac) >>
  `evaluate_type (get_tenv cx) (EL i stys) = SOME (EL i stvs) /\
   value_has_type (EL i stvs) (EL i vs)` by
    fs[LIST_REL_EL_EQN] >>
  `val_wf (EL i stvs) (EL i vs)` by metis_tac[value_has_type_val_wf] >>
  `lookup_var src t = SOME sw /\
   FLOOKUP H src = FLOOKUP G src /\
   op_taint tt (Var src) = op_taint tn (Var src)` by metis_tac[] >>
  `lookup_var src t = lookup_var src s` by metis_tac[] >>
  `not_fresh_at sb src` by
    metis_tac[not_fresh_at_mono] >>
  `~is_word_type (EL i stys) ==>
   val_wf (EL i stvs) (EL i vs) /\
   mem_bytes_at (w2n sw) (val_footprint (EL i stvs) (EL i vs)) t.vs_memory =
     mem_bytes_at (w2n sw) (val_footprint (EL i stvs) (EL i vs)) s.vs_memory /\
   (!j. w2n sw <= j /\ j < w2n sw+val_footprint (EL i stvs) (EL i vs) /\
        j IN tt.t_mem ==> j IN tn.t_mem)` by
    (strip_tac >>
     `own_base <= w2n sw /\
      w2n sw+type_memory_size (EL i stvs) <= own_base+own_size` by metis_tac[] >>
     `val_footprint (EL i stvs) (EL i vs) <= type_memory_size (EL i stvs)` by
       metis_tac[val_footprint_le] >>
     asm_rewrite_tac[] >> conj_tac
     >- (irule LIST_EQ >> simp[] >> rpt strip_tac >>
         rename1 `j < val_footprint (EL i stvs) (EL i vs)` >>
         `own_base <= w2n sw+j /\ w2n sw+j < own_base+own_size` by decide_tac >>
         `mem_bytes_at (w2n sw+j) 1 t.vs_memory =
          mem_bytes_at (w2n sw+j) 1 s.vs_memory` by metis_tac[] >>
         pop_assum mp_tac >> simp[LIST_EQ_REWRITE,EL_mem_bytes_at]) >>
     rpt strip_tac >>
     `own_base <= j /\ j < own_base+own_size` by decide_tac >>
     metis_tac[]) >>
  `ptr_val_ok cx (EL i stys) (EL i vs) (Var src) H tt t` by
    (mp_tac (Q.INST [
       `ty` |-> `EL i stys`,`v` |-> `EL i vs`,`op` |-> `Var src`,
       `G'` |-> `H`,`tn'` |-> `tt`]
       (SPEC_ALL ptr_val_ok_footprint_frame)) >>
     (impl_tac >- simp[eval_operand_def]) >> simp[]) >>
  qexistsl_tac [`src`,`sw`] >> asm_rewrite_tac[] >>
  metis_tac[ptr_covers_lookup_frame]
QED

