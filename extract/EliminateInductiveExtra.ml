let () = Trans.register_transform "eliminate_inductive" eliminate_inductive
  ~desc:"Replace@ inductive@ predicates@ by@ (incomplete)@ axiomatic@ \
         definitions,@ i.e.@ construction@ axioms@ and@ an@ inversion@ axiom."
