(* Join the reached runtime-code selector with its linked post. *)
Theory bodyArrayFramedCodeSelectMods
Ancestors
  bodyArrayFramedCodeSelectTypedMods bodyArrayFramedCodeSelectSuccessMods
  bodyArrayFramedCodeSelectRejectMods bodyArrayFramedCodeSelectInputsDefsMods
  bodySubscriptArrayRouteDefsMods bodyArrayNoCopyCutsMods
  vyperAST vyperTypeSystem vyperArray

Theorem framed_code_select_cut_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  subscript_array_framed_code_case_mods cenv cx obj idx bd /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) ==>
  array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
    cenv cx ann obj idx et bd st0
    (es,s0,G0,tn0) (sa,sb,dst,loc) (raw,key) (fin,it,Gi,tni)
Proof
  strip_tac >>
  drule_all_then (qx_choosel_then [`p`,`etv`,`av`,`i`,`iw`,`w`] assume_tac)
    framed_code_select_inputs_mods >>
  Cases_on `valid_index (ArrayTV etv bd) av i`
  >- (drule_all_then mp_tac framed_code_select_valid_mods >>
      `loc = LocCode /\ key = IntV i` by fs[framed_code_select_inputs_mods_def] >>
      asm_rewrite_tac[]) >>
  drule_all_then ACCEPT_TAC framed_code_select_invalid_mods
QED
