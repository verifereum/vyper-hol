Theory bodyPtrIfExpSummaryProbe
Ancestors fragGasPathPtr

Theorem ifexp_summary_zero_extension:
  !D ctx fn PG marks source es s0 G0 tn0 Q R Q'.
    gas_summary_ptr_at D (ctx,fn) PG marks source (es,s0,G0,tn0) Q R /\
    (!res ee G tn t. Q res ee G tn t ==>
      ?G' tn' u. gas_path_ptr D 0 ctx fn PG G tn t 0 G' tn' (OK u) /\
                  Q' res ee G' tn' u) ==>
    gas_summary_ptr_at D (ctx,fn) PG marks source (es,s0,G0,tn0) Q' R
Proof
  rpt gen_tac >> simp[gas_summary_ptr_at_def] >> rpt strip_tac
  >- (first_x_assum drule >> strip_tac >>
      qexistsl [`res`, `es_end`, `G'`, `tn'`, `OK u`] >> simp[] >>
      gvs[] >> drule_all gas_path_ptr_then >> simp[]) >>
  qexistsl [`res`, `es_end`, `G`, `tn`, `r`] >> simp[]
QED
