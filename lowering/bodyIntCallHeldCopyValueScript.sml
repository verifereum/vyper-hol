(* Semantic observations of held arguments across fresh copies. *)
Theory bodyIntCallHeldCopyValue
Ancestors
  bodyIntCallHeldArgs bodyIntCallHeldCopyFrame bodyIntCallProducerInterface
  exprSimProps loweringPosts valueEncodingProps context venomState

Theorem held_memory_footprint_frame:
  vv_holds ce cx ty raw vv es s /\
  ((?sty op. vv = StackValue sty op) \/
   (?sty p. vv = LocatedValue sty p /\ p.ptr_location = LocMemory)) /\
  (!v tv. read_result cx raw es = (INL v,es) /\
          evaluate_type (get_tenv cx) ty = SOME tv ==>
          val_wf tv v /\ value_has_type tv v) /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  (!v tv w. read_result cx raw es = (INL v,es) /\
            evaluate_type (get_tenv cx) ty = SOME tv /\
            eval_operand (vv_operand vv) s = SOME w ==>
       mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory) ==>
  vv_holds ce cx ty raw vv es t
Proof
  strip_tac >> Cases_on `vv` >>
  gvs[vv_holds_def, vv_operand_def, expr_val_rel_def]
  >- (rpt strip_tac >> Cases_on `is_word_type ty` >> gvs[] >>
      irule val_in_memory_footprint_agree >>
      metis_tac[]) >>
  rpt strip_tac >>
  `val_in_memory tvt v (w2n w) t.vs_memory` by
    (irule val_in_memory_footprint_agree >> metis_tac[]) >>
  metis_tac[exprSimPropsTheory.val_in_memory_word_type]
QED
