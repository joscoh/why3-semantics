open TyDefs

exception BadTypeArity of tysymbol * BigInt.t
exception DuplicateTypeVar of tvsymbol
exception UnboundTypeVar of tvsymbol
exception IllegalTypeParameters
exception BadFloatSpec
exception EmptyRange
exception UnexpectedProp
exception TypeMismatch of ty * ty
