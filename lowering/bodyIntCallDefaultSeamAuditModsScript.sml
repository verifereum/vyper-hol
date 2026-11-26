Theory bodyIntCallDefaultSeamAuditMods
Ancestors
  vyperTypeContract vyperAST alist list

(* Allocation of an exported root is not a premise about every selected
   callee. Treat closure liveness as a separate case. *)
Theorem selected_default_seam_cases_mods:
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops /\
  function_live layouts target mods (linked_live_functions mods exps) (src,fn) ==>
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops /\
  (module_allocated layouts target src tops \/
   MEM (src,fn) (linked_live_functions mods exps))
Proof
  strip_tac >>
  qpat_x_assum `function_live _ _ _ _ _` mp_tac >>
  asm_simp_tac (srw_ss()) [function_live_def]
QED
