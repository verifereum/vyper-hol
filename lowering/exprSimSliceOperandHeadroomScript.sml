(* Preserve reachable DALLOCA headroom across a completed slice operand. *)
Theory exprSimSliceOperandHeadroom
Ancestors
  bodyFullIfExpReach vyperInterpreter
Libs
  monadsyntax

Theorem slice_operand_outcome_headroom:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) Q R /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (\H res ee J tz t. Q H res ee J tz t /\
        (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z)) R
Proof
  strip_tac >> irule gas_outcome_full_post_path >>
  first_assum (irule_at Any) >> simp[] >>
  metis_tac[gas_origin_ptr_path_dalloca_fmp_headroom]
QED
