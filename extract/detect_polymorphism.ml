(* exclusive meta that is set by the transformation when no
   polymorphic definition is found *)

   let meta_monomorphic_types_only =
    Theory.register_meta_excl "encoding:monomorphic_only" []
    ~desc:"Set@ when@ no@ occurrences@ of@ type@ variables@ occur."