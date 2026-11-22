(* Apply the common route theorem to the linked compiler and ABI tables. *)
Theory dispatchedClassifiedRouteMods
Ancestors
  defaultDispatchModsRoute defaultDispatchModsSignatures defaultDispatchModsGetter
  e2eModsDefs vyperTypeContract

Theorem linked_classified_linear_routes:
  source_typing_ok_mods mods exps am tx /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,ics) ==>
  ((LENGTH cd < 4 \/ FIND (\(name,tys). abi_method_id (type_env_all_modules mods) name tys =
    cd_selector cd) (abi_deployed_signatures mods exps) = NONE ==>
    !fl. linear_dispatch_target cd (MAP (\(sel,lbl,z). (sel,lbl)) (build_selectors
      (type_env_all_modules mods) (MAP SND exts))) fl = fl) /\
   (!s mut nr rr name args ds ret b.
     MEM (s,(mut,nr,rr,name,args,ds,ret,b)) exts /\ 4 <= LENGTH cd /\
     FIND (\(name,tys). abi_method_id (type_env_all_modules mods) name tys = cd_selector cd)
       (abi_deployed_signatures mods exps) = SOME (name,MAP SND args) ==>
     !fl. linear_dispatch_target cd (MAP (\(sel,lbl,z). (sel,lbl)) (build_selectors
       (type_env_all_modules mods) (MAP SND exts))) fl = "fn_" ++ name))
Proof
  simp[LET_THM] >> strip_tac >>
  qabbrev_tac `tenv = type_env_all_modules mods` >>
  qabbrev_tac `sigs = abi_deployed_signatures mods exps` >>
  qabbrev_tac `hit = \(name,tys). abi_method_id tenv name tys = cd_selector cd` >>
  qabbrev_tac `fs = MAP SND exts` >>
  qabbrev_tac `sels = MAP (\(sel,lbl,z). (sel,lbl)) (build_selectors tenv fs)` >>
  `ALL_DISTINCT (MAP (\(name,tys). abi_method_id tenv name tys) sigs)` by
    fs[Abbr `tenv`,Abbr `sigs`,source_typing_ok_mods_def,exports_ok_def] >>
  `!mut nr rr name args ds ret b.
      MEM (mut,nr,rr,name,args,ds,ret,b) fs ==> MEM (name,MAP SND args) sigs` by
    (simp[Abbr `fs`,Abbr `sigs`,listTheory.MEM_MAP,pairTheory.EXISTS_PROD] >> rpt strip_tac >>
     metis_tac[compiled_entry_deployed_signature,tagged_getter_decl_signature]) >>
  `!fl. (LENGTH cd < 4 \/ FIND hit sigs = NONE ==>
         linear_dispatch_target cd sels fl = fl) /\
        (!mut nr rr name args ds ret b.
          MEM (mut,nr,rr,name,args,ds,ret,b) fs /\ 4 <= LENGTH cd /\
          FIND hit sigs = SOME (name,MAP SND args) ==>
          linear_dispatch_target cd sels fl = "fn_" ++ name)` by
    (simp[Abbr `hit`,Abbr `sels`] >> gen_tac >>
     irule (SRULE [LET_THM] default_linear_routes) >> asm_rewrite_tac[]) >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `MEM (mut,nr,rr,name,args,ds,ret,b) fs` by
    (simp[Abbr `fs`,listTheory.MEM_MAP] >> metis_tac[pairTheory.SND]) >>
  fs[] >> metis_tac[]
QED
