(* Source bounds used by the memory-labelled concat head bridge. *)
Theory bodyMemBiConcatHead
Ancestors
  bodyMemBiConcatArms bodyMemBiConcatBounds exprSimMemDefs exprLoweringProps
  exprSimDefs exprSimProps words arithmetic

Theorem concat_bytestring_source_nowrap_mem[local]:
  expr_store_bound cx ty v op t /\ is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  eval_operand op t = SOME sw /\ stmt_state_rel ctx func cenv cx es t ==>
  w2n sw + 32 < dimword (:256) /\
  w2n sw + 32 + LENGTH (case v of BytesV bs => bs
    | StringV str => MAP (n2w o ORD) str | _ => []) <= t.vs_alloca_next
Proof
  strip_tac >>
  drule_all concat_bytestring_source_bound_mem >> strip_tac >>
  `alloca_room ctx func t` by fs[stmt_state_rel_def] >>
  drule alloca_room_next_lt >> decide_tac
QED

Theorem concat_head_endpoint_frame_mem[local]:
  local_ptrs_reserved cenv s1 /\ local_ptrs_rel func cenv es1.scopes t /\
  not_fresh_at s1 dv /\ not_fresh_at s1 ov /\
  lookup_var dv t = SOME (n2w (B + 32)) /\ lookup_var ov t = SOME ow /\
  FLOOKUP t.vs_allocas binst.inst_id = SOME (B,bsz) /\
  FLOOKUP t.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
  (!name lb lsz. local_region cenv es1.scopes t name lb lsz ==>
    (B + bsz <= lb \/ lb + lsz <= B) /\
    (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow)) /\
  t2.vs_allocas = t.vs_allocas /\
  (!z. not_fresh_at s1 z ==> lookup_var z t2 = lookup_var z t) ==>
  lookup_var dv t2 = SOME (n2w (B + 32)) /\ lookup_var ov t2 = SOME ow /\
  FLOOKUP t2.vs_allocas binst.inst_id = SOME (B,bsz) /\
  FLOOKUP t2.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
  (!name lb lsz. local_region cenv es1.scopes t2 name lb lsz ==>
    (B + bsz <= lb \/ lb + lsz <= B) /\
    (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow))
Proof
  strip_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  `local_region cenv es1.scopes t name lb lsz` by
    (irule local_region_frame >>
     conj_tac >- (qexists_tac `func` >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`s1`, `es1.scopes`, `t2`] >> simp[]) >>
  qpat_x_assum `!name lb lsz. local_region _ _ t _ _ _ ==> _` drule >> simp[]
QED
