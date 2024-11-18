open Theory


let meta_syntax_logic = register_meta "syntax_logic" [MTlsymbol; MTstring; MTint]
  ~desc:"Specify@ the@ syntax@ used@ to@ pretty-print@ a@ function/predicate@ \
         symbol.@ \
         Can@ be@ specified@ in@ the@ driver@ with@ the@ 'syntax function'@ \
         or@ 'syntax predicate'@ rules."

let meta_remove_prop = register_meta "remove_prop" [MTprsymbol]
    ~desc:"Remove@ a@ logical@ proposition@ from@ proof@ obligations.@ \
           Can@ be@ specified@ in@ the@ driver@ with@ the@ 'remove prop'@ rule."

           let meta_remove_type = register_meta "remove_type" [MTtysymbol]
           ~desc:"Remove@ a@ type@ symbol@ from@ proof@ obligations.@ \
                  Used@ in@ bisection."

           let meta_remove_logic = register_meta "remove_logic" [MTlsymbol]
~desc:"Remove@ a@ function/predicate@ symbol@ from@ proof@ obligations.@ \
      Used@ in@ bisection."

      let meta_remove_def = register_meta "remove_def" [MTlsymbol]
      ~desc:"Remove@ the@ definition@ of@ a@ function/predicate@ symbol@ but@ keep@ \
             its@ declaration."

(*for compilation*)
let unsupportedTerm : 'a -> 'b -> 'c = fun _ _ -> raise (Invalid_argument "unsupported")