signature jsonToVyperCVLib = sig
  val register_first_order_induction :
    string -> Thm.thm -> Abbrev.tactic -> Thm.thm
end
