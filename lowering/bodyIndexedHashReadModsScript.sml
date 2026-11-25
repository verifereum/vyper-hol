(* Linked indexed hash simulation, with both physical suffixes supplied. *)
Theory bodyIndexedHashReadMods
Ancestors
  bodyIndexedHashComposeMods bodyBlockHashReadSuffixMods bodyBlobHashReadSuffixMods

Theorem indexed_hash_read_sim_mods:
  (!DF lo d ctx sh PG f sf cenv cx ty e es.
    is_word_type (post_value_type cenv e) /\
    expr_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty e es /\
    (!sa. ?a op sb. compile_expr cenv ty e sa = (StackValue a op,sb)) /\
    (!s tv t. eval_expr cx e s = (INL tv,t) ==> ?v. tv = Value v) ==>
    expr_vv_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty e es) ==>
  !exps src tops DF lo d ctx shadow_ctx PG func shadow_func cenv env cx ty a bt args es.
    (bt = vyperAST$BlockHash \/ bt = BlobHash) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok_mods mods exps cx args) /\
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin a bt args) es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty (Builtin a bt args) es
Proof
  match_mp_tac indexed_hash_read_from_suffixes_mods >>
  conj_tac
  >- ACCEPT_TAC blockhash_read_physical_suffix >>
  ACCEPT_TAC blobhash_read_physical_suffix
QED
