(* a type constructor generates an infinite type if either it is tagged by
   meta_infinite or one of its "material" arguments is an infinite type *)

let meta_infinite = register_meta "infinite_type" [MTtysymbol]
  ~desc:"Specify@ that@ the@ given@ type@ has@ always@ an@ infinite@ \
         cardinality."

let meta_material = register_meta "material_type_arg" [MTtysymbol;MTint]
  ~desc:"If@ the@ given@ type@ argument@ is@ instantiated@ by@ an@ infinite@ \
         type@ then@ the@ associated@ type@ constructor@ is@ infinite"

let meta_alg_kept = register_meta "algebraic:kept" [MTty]
  ~desc:"Keep@ primitive@ operations@ over@ this@ algebraic@ type."
